#![allow(non_camel_case_types)]

use crate::lazy::any_encoding::{IonEncoding, IonVersion};
use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::compiler::TemplateCompiler;
use crate::lazy::expanded::encoding_module::EncodingModule;
use crate::lazy::expanded::macro_table::MacroTable;
use crate::lazy::expanded::template::TemplateMacro;
use crate::lazy::expanded::{ExpandingReader, LazyExpandedValue};
use crate::lazy::sequence::SExpIterator;
use crate::lazy::streaming_raw_reader::{IonInput, StreamingRawReader};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
use crate::lazy::value::LazyValue;
use crate::read_config::ReadConfig;
use crate::result::IonFailure;
use crate::{
    AnyEncoding, Catalog, Int, IonError, IonResult, IonType, LazyField, LazySExp, LazyStruct,
    RawSymbolRef, Symbol, SymbolTable, ValueRef,
};
use std::ops::Deref;
use std::sync::Arc;

// Symbol IDs used for processing symbol table structs
const ION_SYMBOL_TABLE: RawSymbolRef = RawSymbolRef::SymbolId(3);
const IMPORTS: RawSymbolRef = RawSymbolRef::SymbolId(6);
const SYMBOLS: RawSymbolRef = RawSymbolRef::SymbolId(7);

/// A binary reader that only reads each value that it visits upon request (that is: lazily).
///
/// Unlike [`crate::lazy::reader::Reader`], which only exposes values that are part
/// of the application data model, [`SystemReader`] also yields Ion version markers
/// (as [`SystemStreamItem::VersionMarker`]) and structs representing a symbol table (as
/// [`SystemStreamItem::SymbolTable`]).
///
/// Each time [`SystemReader::next_item`] is called, the reader will advance to the next top-level
/// value in the input stream. Once positioned on a top-level value, users may visit nested values by
/// calling [`LazyValue::read`] and working with the resulting [`ValueRef`],
/// which may contain either a scalar value or a lazy container that may itself be traversed.
///
/// The values that the reader yields ([`LazyValue`],
/// [`LazyList`](crate::LazyList), [`LazySExp`] and [`LazyStruct`]), are immutable references to the data stream,
/// and remain valid until [`SystemReader::next_item`] is called again to advance the reader to
/// the next top level value. This means that these references can be stored, read, and re-read as
/// long as the reader remains on the same top-level value.
/// ```
///# use ion_rs::IonResult;
///# #[cfg(feature="experimental-reader-writer")]
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::{Element, ion_list, Reader};
/// use ion_rs::v1_0::Binary;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.encode_as(Binary)?;
///
/// let mut lazy_reader = Reader::new(Binary, binary_ion)?;
///
/// // Get the first value from the stream and confirm that it's a list.
/// let lazy_list = lazy_reader.expect_next()?.read()?.expect_list()?;
///
/// // Visit the values in the list
/// let mut sum = 0;
/// for lazy_value in &lazy_list {
///     // Read each lazy value in the lazy list as an int (i64) and
///     // add it to the running total
///     sum += lazy_value?.read()?.expect_i64()?;
/// }
///
/// assert_eq!(sum, 60);
///
/// // Note that we can re-read any of the lazy values. Here we'll step into the list again and
/// // read the first child value.
/// let first_int = lazy_list.iter().next().unwrap()?.read()?.expect_i64()?;
/// assert_eq!(first_int, 10);
///
///# Ok(())
///# }
///# #[cfg(not(feature = "experimental-reader-writer"))]
///# fn main() -> IonResult<()> { Ok(()) }
/// ```
pub struct SystemReader<Encoding: Decoder, Input: IonInput> {
    pub(crate) expanding_reader: ExpandingReader<Encoding, Input>,
}

// If the reader encounters a symbol table in the stream, it will store all of the symbols that
// the table defines in this structure so that they may be applied when the reader next advances.
#[derive(Default)]
pub struct PendingContextChanges {
    pub(crate) switch_to_version: Option<IonVersion>,
    pub(crate) has_changes: bool,
    pub(crate) is_lst_append: bool,
    pub(crate) imported_symbols: Vec<Symbol>,
    pub(crate) symbols: Vec<Symbol>,
    // A new encoding modules defined in the current encoding directive.
    // TODO: Support for defining several modules
    pub(crate) new_active_module: Option<EncodingModule>,
}

impl PendingContextChanges {
    pub fn new() -> Self {
        Self {
            switch_to_version: None,
            has_changes: false,
            is_lst_append: false,
            symbols: Vec::new(),
            imported_symbols: Vec::new(),
            new_active_module: None,
        }
    }
    pub fn local_symbols(&self) -> &[Symbol] {
        &self.symbols
    }
    pub fn imported_symbols(&self) -> &[Symbol] {
        &self.imported_symbols
    }
    pub fn has_changes(&self) -> bool {
        self.has_changes
    }
    pub fn new_active_module(&self) -> Option<&EncodingModule> {
        self.new_active_module.as_ref()
    }
    /// If there's a new module defined, returns `Some(new_module)` and sets `self.new_module`
    /// to `None`. If there is no new module defined, returns `None`.
    pub(crate) fn take_new_active_module(&mut self) -> Option<EncodingModule> {
        self.new_active_module.take()
    }
}

impl<Encoding: Decoder, Input: IonInput> SystemReader<Encoding, Input> {
    pub fn new(
        config: impl Into<ReadConfig<Encoding>>,
        input: Input,
    ) -> SystemReader<Encoding, Input> {
        let config = config.into();
        let raw_reader = StreamingRawReader::new(config.encoding(), input);
        let expanding_reader = ExpandingReader::new(raw_reader, config.catalog);
        SystemReader { expanding_reader }
    }

    pub fn register_template_src(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        self.expanding_reader
            .register_template_src(template_definition)
    }

    pub fn register_template(&mut self, template_macro: TemplateMacro) -> IonResult<MacroAddress> {
        self.expanding_reader.register_template(template_macro)
    }

    /// Returns `true` if the provided `LazyRawValue` is a struct whose first annotation is
    /// `$ion_symbol_table`. Caller is responsible for confirming the struct appeared at the top
    /// level.
    pub(crate) fn is_symbol_table_struct(
        expanded_value: &'_ LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<bool> {
        if expanded_value.ion_type() != IonType::Struct || !expanded_value.has_annotations() {
            return Ok(false);
        }
        let lazy_value = LazyValue::new(*expanded_value);
        if let Some(symbol_ref) = lazy_value.annotations().next() {
            return Ok(symbol_ref? == "$ion_symbol_table");
        };
        Ok(false)
    }

    /// Returns `true` if the provided `LazyRawValue` is an s-expression whose first annotation
    /// is `$ion_encoding`. Caller is responsible for confirming the sexp appeared at the top
    /// level AND that this stream is encoded using Ion 1.1.
    pub(crate) fn is_encoding_directive_sexp(
        lazy_value: &'_ LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<bool> {
        if lazy_value.ion_type() != IonType::SExp {
            return Ok(false);
        }
        if !lazy_value.has_annotations() {
            return Ok(false);
        }
        // At this point, we've confirmed it's an annotated s-expression. We need to see if its
        // first annotation has the text `$ion_encoding`, which may involve a lookup in the
        // encoding context. We'll promote this LazyExpandedValue to a LazyValue to enable that.
        let lazy_value = LazyValue::new(*lazy_value);
        let first_annotation = lazy_value
            .annotations()
            .next()
            .expect("already confirmed that there are annotations")?;
        Ok(first_annotation.text() == Some("$ion_encoding"))
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        self.expanding_reader.context().symbol_table()
    }

    pub fn pending_context_changes(&self) -> &PendingContextChanges {
        self.expanding_reader.pending_context_changes()
    }

    /// Returns the next top-level stream item (IVM, Symbol Table, Value, or Nothing) as a
    /// [`SystemStreamItem`].
    pub fn next_item(&mut self) -> IonResult<SystemStreamItem<'_, Encoding>> {
        self.expanding_reader.next_item()
    }

    /// Returns the next value that is part of the application data model, bypassing all encoding
    /// artifacts (IVMs, symbol tables).
    pub fn next_value(&mut self) -> IonResult<Option<LazyValue<Encoding>>> {
        self.expanding_reader.next_value()
    }

    /// Like [`next_value`](Self::next_value) but returns an error if there is not another
    /// application value in the stream.
    pub fn expect_next_value(&mut self) -> IonResult<LazyValue<Encoding>> {
        self.next_value()?.ok_or_else(|| {
            IonError::decoding_error("expected another application value but found none")
        })
    }

    pub(crate) fn process_encoding_directive(
        pending_changes: &mut PendingContextChanges,
        directive: LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<()> {
        // We've already confirmed this is an annotated sexp
        let directive = directive.read()?.expect_sexp()?;
        for step in directive.iter() {
            Self::process_encoding_directive_operation(pending_changes, step?)?;
        }
        Ok(())
    }

    pub(crate) fn process_encoding_directive_operation(
        pending_changes: &mut PendingContextChanges,
        value: LazyExpandedValue<Encoding>,
    ) -> IonResult<()> {
        let operation_sexp = LazyValue::new(value).read()?.expect_sexp().map_err(|_| {
            IonError::decoding_error(format!(
                "found an encoding directive step that was not an s-expression: {value:?}"
            ))
        })?;

        let mut values = operation_sexp.iter();
        let first_value =
            Self::expect_next_sexp_value("encoding directive operation name", &mut values)?;
        let step_name_text =
            Self::expect_symbol_text("encoding directive operation name", first_value)?;

        match step_name_text {
            "module" => todo!("defining a new named module"),
            "symbol_table" => {
                let symbol_table = Self::process_symbol_table_definition(operation_sexp)?;
                let new_encoding_module = match pending_changes.take_new_active_module() {
                    None => EncodingModule::new(
                        "$ion_encoding".to_owned(),
                        MacroTable::new(),
                        symbol_table,
                    ),
                    Some(mut module) => {
                        module.set_symbol_table(symbol_table);
                        module
                    }
                };
                pending_changes.new_active_module = Some(new_encoding_module);
            }
            "macro_table" => {
                let macro_table = Self::process_macro_table_definition(operation_sexp)?;
                let new_encoding_module = match pending_changes.take_new_active_module() {
                    None => EncodingModule::new(
                        "$ion_encoding".to_owned(),
                        macro_table,
                        SymbolTable::new(IonVersion::v1_1),
                    ),
                    Some(mut module) => {
                        module.set_macro_table(macro_table);
                        module
                    }
                };
                pending_changes.new_active_module = Some(new_encoding_module);
            }
            _ => {
                return IonResult::decoding_error(format!(
                    "unsupported encoding directive step '{step_name_text}'"
                ))
            }
        }
        Ok(())
    }

    fn process_module_definition(
        _pending_changes: &mut PendingContextChanges,
        module: LazySExp<Encoding>,
    ) -> IonResult<()> {
        let mut args = module.iter();
        // We've already looked at and validated the `name` to get to this point. We can skip it.
        let _operation = args.next(); // 'module'
        let module_name = Self::expect_next_sexp_value("a module name", &mut args)?;
        let module_name_text = Self::expect_symbol_text("a module name", module_name)?;
        let symbol_table_value =
            Self::expect_next_sexp_value("a `symbol_table` operation", &mut args)?;
        let symbol_table_operation =
            Self::expect_sexp("a `symbol_table` operation", symbol_table_value)?;
        let macro_table_value =
            Self::expect_next_sexp_value("a `macro_table` operation", &mut args)?;
        let macro_table_operation =
            Self::expect_sexp("a `macro_table` operation", macro_table_value)?;

        let symbol_table = Self::process_symbol_table_definition(symbol_table_operation)?;
        let macro_table = Self::process_macro_table_definition(macro_table_operation)?;

        // TODO: Register the new module in `pending_changes`.
        let _encoding_module =
            EncodingModule::new(module_name_text.to_owned(), macro_table, symbol_table);

        Ok(())
    }

    fn process_symbol_table_definition(operation: LazySExp<Encoding>) -> IonResult<SymbolTable> {
        let mut args = operation.iter();
        let operation_name_value =
            Self::expect_next_sexp_value("a `symbol_table` operation name", &mut args)?;
        let operation_name =
            Self::expect_symbol_text("the operation name `symbol_table`", operation_name_value)?;
        if operation_name != "symbol_table" {
            return IonResult::decoding_error(format!(
                "expected a symbol table definition operation, but found: {operation:?}"
            ));
        }
        let mut symbol_table = SymbolTable::new(IonVersion::v1_1);
        for arg in args {
            let symbol_list = arg?.read()?.expect_list()?;
            for value in symbol_list {
                match value?.read()? {
                    ValueRef::String(s) => symbol_table.add_symbol_for_text(s.text()),
                    ValueRef::Symbol(s) => symbol_table.add_symbol(s.to_owned()),
                    other => {
                        return IonResult::decoding_error(format!(
                            "found a non-text value in symbols list: {other:?}"
                        ))
                    }
                };
            }
        }
        Ok(symbol_table)
    }

    fn process_macro_table_definition(operation: LazySExp<Encoding>) -> IonResult<MacroTable> {
        let mut args = operation.iter();
        let operation_name_value =
            Self::expect_next_sexp_value("a `macro_table` operation name", &mut args)?;
        let operation_name =
            Self::expect_symbol_text("the operation name `macro_table`", operation_name_value)?;
        if operation_name != "macro_table" {
            return IonResult::decoding_error(format!(
                "expected a macro table definition operation, but found: {operation:?}"
            ));
        }
        let mut macro_table = MacroTable::new();
        for arg in args {
            let arg = arg?;
            let context = operation.expanded_sexp.context;
            let macro_def_sexp = arg.read()?.expect_sexp().map_err(|_| {
                IonError::decoding_error(format!(
                    "macro_table had a non-sexp parameter: {}",
                    arg.ion_type()
                ))
            })?;
            let new_macro = TemplateCompiler::compile_from_sexp(context, macro_def_sexp)?;
            macro_table.add_macro(new_macro)?;
        }
        Ok(macro_table)
    }

    fn expect_next_sexp_value<'a>(
        label: &str,
        iter: &mut SExpIterator<'a, Encoding>,
    ) -> IonResult<LazyValue<'a, Encoding>> {
        iter.next().transpose()?.ok_or_else(|| {
            IonError::decoding_error(format!(
                "expected {label} but found no more values in the s-expression"
            ))
        })
    }

    fn expect_sexp<'a>(
        label: &str,
        value: LazyValue<'a, Encoding>,
    ) -> IonResult<LazySExp<'a, Encoding>> {
        value.read()?.expect_sexp().map_err(|_| {
            IonError::decoding_error(format!(
                "expected an s-expression representing {label} but found a {}",
                value.ion_type()
            ))
        })
    }

    fn expect_symbol_text<'a>(
        label: &str,
        lazy_value: LazyValue<'a, Encoding>,
    ) -> IonResult<&'a str> {
        lazy_value
            .read()?
            .expect_symbol()
            .map_err(|_| {
                IonError::decoding_error(format!(
                    "found {label} with non-symbol type: {}",
                    lazy_value.ion_type()
                ))
            })?
            .text()
            .ok_or_else(|| {
                IonError::decoding_error(format!("found {label} that had undefined text ($0)"))
            })
    }

    // Traverses a symbol table, processing the `symbols` and `imports` fields as needed to
    // populate the `PendingLst`.
    pub(crate) fn process_symbol_table(
        pending_lst: &mut PendingContextChanges,
        catalog: &dyn Catalog,
        symbol_table: &LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<()> {
        // We've already confirmed this is an annotated struct
        let symbol_table = symbol_table.read()?.expect_struct()?;

        // We're interested in the `imports` field and the `symbols` field. Both are optional;
        // however, it is illegal to specify either field more than once.
        let mut imports_field: Option<LazyField<Encoding>> = None;
        let mut symbols_field: Option<LazyField<Encoding>> = None;

        let symbol_table = LazyStruct {
            expanded_struct: symbol_table,
        };

        // Iterate through the fields of the symbol table struct, taking note of `imports` and `symbols`
        // if we encounter them.
        for field_result in symbol_table.iter() {
            let field = field_result?;
            let Some(name) = field.name()?.text() else {
                // If the field is $0, we don't care about it.
                continue;
            };
            match name {
                "imports" => {
                    if imports_field.is_some() {
                        return IonResult::decoding_error(
                            "found symbol table with multiple 'imports' fields",
                        );
                    }
                    imports_field = Some(field);
                }
                "symbols" => {
                    if symbols_field.is_some() {
                        return IonResult::decoding_error(
                            "found symbol table with multiple 'symbols' fields",
                        );
                    }
                    symbols_field = Some(field);
                }
                // Other fields are ignored
                _ => {}
            };
        }

        if let Some(imports_field) = imports_field {
            let lazy_value = imports_field.value();
            Self::clear_pending_lst_if_needed(pending_lst, lazy_value)?;
            Self::process_imports(pending_lst, catalog, lazy_value)?;
        }
        if let Some(symbols_field) = symbols_field {
            Self::process_symbols(pending_lst, symbols_field.value())?;
        }

        Ok(())
    }

    fn clear_pending_lst_if_needed(
        pending_lst: &mut PendingContextChanges,
        imports_value: LazyValue<'_, Encoding>,
    ) -> IonResult<()> {
        match imports_value.read()? {
            // If this is an LST append, there's nothing to do.
            ValueRef::Symbol(symbol) if symbol == "$ion_symbol_table" => {}
            // If this is NOT an LST append, it will eventually cause the SymbolTable to reset.
            // However, at this point in the processing the PendingLst may have symbols that have
            // not yet made it to the SymbolTable. This can happen when a single top-level e-expression
            // produces multiple LSTs.
            //
            //   // Top-level e-expression produces multiple LSTs
            //   (:values
            //     $ion_symbol_table::{imports: $ion_symbol_table, symbols: ["foo"]}
            //     $ion_symbol_table::{imports: $ion_symbol_table, symbols: ["bar"]}
            //     $ion_symbol_table::{symbols: ["baz"]}
            //   )
            //   // The reader does not apply their collective changes to its symbol table
            //   // until it is done processing the complete output of the expression.
            //   // That means that "foo" and "bar" get appended to the pending LST,
            //   // but get discarded when the reader is parked on the third LST in the stream.
            //   $10 // <-- 'baz'
            _ => {
                pending_lst.symbols.clear();
                pending_lst.imported_symbols.clear();
            }
        };
        Ok(())
    }

    // Store any strings defined in the `symbols` field in the `PendingLst` for future application.
    fn process_symbols(
        pending_lst: &mut PendingContextChanges,
        symbols: LazyValue<'_, Encoding>,
    ) -> IonResult<()> {
        if let ValueRef::List(list) = symbols.read()? {
            for symbol_text_result in list.iter() {
                if let ValueRef::String(str_ref) = symbol_text_result?.read()? {
                    pending_lst
                        .symbols
                        .push(Symbol::shared(Arc::from(str_ref.deref())))
                } else {
                    // If the value is null or a non-string, we reserve a spot for it in the symbol
                    // table (i.e. it gets a symbol ID) but there is no text associated with it.
                    // See: https://amazon-ion.github.io/ion-docs/docs/symbols.html
                    pending_lst.symbols.push(Symbol::unknown_text())
                }
            }
        }
        // Nulls and non-list values are ignored.
        Ok(())
    }

    // Check for `imports: $ion_symbol_table`.
    fn process_imports(
        pending_lst: &mut PendingContextChanges,
        catalog: &dyn Catalog,
        imports: LazyValue<'_, Encoding>,
    ) -> IonResult<()> {
        match imports.read()? {
            // Any symbol other than `$ion_symbol_table` is ignored.
            ValueRef::Symbol(symbol_ref) if symbol_ref == "$ion_symbol_table" => {
                pending_lst.is_lst_append = true;
            }
            ValueRef::List(list) => {
                for value in list.iter() {
                    let ValueRef::Struct(import) = value?.read()? else {
                        // If there's a value in the imports list that isn't a struct, it's malformed.
                        // Ignore that value.
                        continue;
                    };
                    let name = match import.get("name")? {
                        // If `name` is missing, a non-string, or the empty string, ignore this import.
                        Some(ValueRef::String(s)) if !s.is_empty() => s,
                        _ => continue,
                    };
                    let version: usize = match import.get("version")? {
                        Some(ValueRef::Int(i)) if i > Int::ZERO => usize::try_from(i)
                            .map_err(|_|
                            IonError::decoding_error(format!("found a symbol table import (name='{name}') with a version number too high to support: {i}")),
                        ),
                        // If there's no version, a non-int version, or a version <= 0, we treat it
                        // as version 1.
                        _ => Ok(1),
                    }?;

                    let shared_table = match catalog.get_table_with_version(name.as_ref(), version) {
                        Some(table) => table,
                        None => return IonResult::decoding_error(
                            format!("symbol table import failed, could not find table with name='{name}' and version={version}")
                        ),
                    };

                    let max_id = match import.get("max_id")? {
                        Some(ValueRef::Int(i)) if i >= Int::ZERO => {
                            usize::try_from(i).map_err(|_| {
                                IonError::decoding_error(
                                    "found a `max_id` beyond the range of usize",
                                )
                            })?
                        }
                        // If the max_id is unspecified, negative, or an invalid data type, we'll import all of the symbols from the requested table.
                        _ => shared_table.symbols().len(),
                    };

                    let num_symbols_to_import = shared_table.symbols().len().min(max_id);

                    pending_lst
                        .imported_symbols
                        .extend_from_slice(&shared_table.symbols()[..num_symbols_to_import]);

                    if max_id > shared_table.symbols().len() {
                        let num_pending_symbols = pending_lst.imported_symbols().len();
                        let num_placeholders = max_id - shared_table.symbols().len();
                        pending_lst.imported_symbols.resize(
                            num_pending_symbols + num_placeholders,
                            Symbol::unknown_text(),
                        );
                    }
                }
            }
            _ => {
                // Nulls and other types are ignored
            }
        }

        Ok(())
    }
}

impl<Input: IonInput> SystemReader<AnyEncoding, Input> {
    pub fn detected_encoding(&self) -> IonEncoding {
        self.expanding_reader.detected_encoding()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::decoder::RawVersionMarker;
    use crate::lazy::system_stream_item::SystemStreamItem;
    use crate::{
        v1_0, AnyEncoding, Catalog, IonResult, SequenceWriter, SymbolRef, ValueWriter, Writer,
    };

    use super::*;

    #[test]
    fn try_it() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        foo
        bar
        $ion_symbol_table
        baz
        name
        gary
        imports
        hello
        "#,
        )?;
        let mut system_reader = SystemReader::new(v1_0::Binary, ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::VersionMarker(marker) => {
                    println!("ivm => v{}.{}", marker.major(), marker.minor())
                }
                SystemStreamItem::SymbolTable(ref s) => println!("symtab => {:?}", s),
                SystemStreamItem::EncodingDirective(ref s) => {
                    println!("encoding directive => {:?}", s)
                }
                SystemStreamItem::Value(ref v) => println!("value => {:?}", v.read()?),
                SystemStreamItem::EndOfStream(_) => break,
            }
        }
        Ok(())
    }

    #[test]
    fn sequence_iter() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        (
          (foo baz baz)
          (1 2 3)
          (a b c)
        )
        "#,
        )?;
        let mut system_reader = SystemReader::new(v1_0::Binary, ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::Value(value) => {
                    for value in &value.read()?.expect_sexp()? {
                        println!("{:?}", value?.read()?);
                    }
                }
                SystemStreamItem::EndOfStream(_) => break,
                _ => {}
            }
        }
        Ok(())
    }

    #[test]
    fn struct_iter() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        {
          foo: 1,
          bar: true,
          baz: null.symbol,
          quux: "hello"
        }
        "#,
        )?;
        let mut system_reader = SystemReader::new(v1_0::Binary, ion_data);
        loop {
            match system_reader.next_item()? {
                SystemStreamItem::Value(value) => {
                    for field in &value.read()?.expect_struct()? {
                        let field = field?;
                        println!("{:?}: {:?},", field.name()?, field.value().read()?);
                    }
                }
                SystemStreamItem::EndOfStream(_) => break,
                _ => {}
            }
        }
        Ok(())
    }

    // === Shared Symbol Tables ===

    use crate::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
    use crate::lazy::encoder::value_writer::AnnotatableWriter;
    use crate::{MapCatalog, SharedSymbolTable};

    fn system_reader_for<I: IonInput>(ion: I) -> SystemReader<AnyEncoding, I> {
        SystemReader::new(AnyEncoding, ion)
    }

    fn system_reader_with_catalog_for<Input: IonInput>(
        input: Input,
        catalog: impl Catalog + 'static,
    ) -> SystemReader<AnyEncoding, Input> {
        SystemReader::new(AnyEncoding.with_catalog(catalog), input)
    }

    #[test]
    fn shared_and_local_symbols() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // "foo"
                $11 // "local_symbol"
            "#,
            map_catalog,
        );
        // We step over the LST...
        let _symtab = reader.next_item()?.expect_symbol_table()?;
        // ...but expect all of the symbols we encounter after it to be in the symbol table,
        // indicating that the SystemReader processed the LST even though we skipped it with `next()`
        assert_eq!(
            reader
                .next_item()?
                .expect_value()?
                .read()?
                .expect_symbol()?,
            "foo"
        );
        assert_eq!(
            reader
                .next_item()?
                .expect_value()?
                .read()?
                .expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn multiple_shared_symbol_table_imports() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_1", 1, ["foo"])?);
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_2", 1, ["bar"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
                // This symbol table will be overwritten by the following one
                $ion_symbol_table::{
                    symbols: [ "potato salad" ]
                }
                // This LST does not import `$ion_symbol_table`, so it resets rather than appending
                $ion_symbol_table::{
                    imports: [ { name:"shared_table_1", version: 1 }, { name:"shared_table_2", version: 1 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // "foo"
                $11 // "bar"
                $12 // "local_symbol"
          "#,
            map_catalog,
        );
        // We step over the first LST, processing it but not yet applying it.
        let _symtab = reader.next_item()?.expect_symbol_table()?;
        // There are 10 symbols in the symbol table, $0 to $9 inclusive. $10 is not defined yet
        // because we're still parked on the symtab.
        assert_eq!(reader.symbol_table().len(), 10);
        // The reader has analyzed the symtab struct and identified what symbols will be added when
        // it advances beyond it.
        assert_eq!(
            reader.pending_context_changes().local_symbols()[0].text(),
            Some("potato salad")
        );

        // We advance to the second LST, which causes the previous one to be applied.
        let _symtab = reader.next_item()?.expect_symbol_table()?;
        assert_eq!(reader.symbol_table().len(), 11);
        assert_eq!(reader.symbol_table().text_for(10), Some("potato salad"));
        // We can peak at the symbols that will be added by the second LST before they are applied.
        assert_eq!(
            reader.pending_context_changes().imported_symbols(),
            &[Symbol::from("foo"), Symbol::from("bar")]
        );
        assert_eq!(
            reader.pending_context_changes().local_symbols(),
            &[Symbol::from("local_symbol")]
        );
        // Now we advance to the application data, confirming that the symbol IDs align with the
        // expected text.
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "foo");
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "bar");
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn shared_symbol_table_import_binary() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        // add a table with system symbol `name` and a new symbol `foo`
        // reader should still add this system symbol `name` again($10), but whenever writing this symbol
        // smallest ID($4) will be used
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["name", "foo"])?);
        // The stream contains a shared symbol table import
        let mut reader = system_reader_with_catalog_for(
            [
                0xe0, 0x01, 0x00, 0xea, // Ion 1.0 Version Marker
                0xee, 0x9d, 0x81, 0x83, // '$ion_symbol_table'::
                0xde, 0x99, // 26 bytes struct
                0x86, // Field $6 `imports`
                0xbe, 0x96, // List
                0xde, 0x94, // 21 bytes struct
                0x84, // Field $4 `name`
                0x8c, 0x73, 0x68, 0x61, 0x72, 0x65, 0x64, 0x5f, 0x74, 0x61, 0x62, 0x6c,
                0x65, // "shared_table"
                0x85, // Field $5 `version`
                0x21, 0x01, // INT 1
                0x88, // $8 `max_id`
                0x21, 0x02, // INT 2
                0x71, 0x04, // $4 `name`
                0x71, 0x0a, // $10 `name`
                0x71, 0x0b, // $11 `foo`
            ]
            .as_slice(),
            map_catalog,
        );
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 0));
        let _symtab = reader.next_item()?.expect_symbol_table()?;
        let pending_imported_symbols = reader.pending_context_changes().imported_symbols();
        // This symbol table imports the symbols 'name' and 'foo'.
        assert_eq!(pending_imported_symbols[0].text(), Some("name"));
        assert_eq!(pending_imported_symbols[1].text(), Some("foo"));
        // The new symbols have not been applied yet.
        assert_eq!(reader.symbol_table().len(), 10);
        // The application values have the expected text
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?.text(),
            Some("name")
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?.text(),
            Some("name")
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?.text(),
            Some("foo")
        );
        Ok(())
    }

    #[test]
    fn non_existent_shared_symbol_table_imports() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_1", 1, ["foo"])?);
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_2", 1, ["bar"])?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table_3", version: 1, max_id: 3 }, { name:"shared_table_2", version: 1 }, { name:"shared_table_4", version: 1, max_id: 1 } ],
                    symbols: [ "local_symbol" ]
                }
                $13 // "bar"
            "#,
            map_catalog,
        );
        // We step over the LST...
        assert!(
            matches!(reader.next_item(), Err(IonError::Decoding(_))),
            "expected a decoding error because shared_table_3 does not exist"
        );
        Ok(())
    }

    #[test]
    fn pad_with_max_id() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    // This imports 3 symbols from shared_table v1, which only has a single symbol.
                    // The reader will add symbols with unknown text ($0) for the other two.
                    imports: [ { name:"shared_table", version: 1, max_id: 3 } ],
                    // The symbol 'bar' will be assigned the first symbol ID following the import padding.
                    symbols: [ "bar" ]
                }
                $10 // "foo"
                $11 // == $0
                $12 // == $0
                $13 // "bar"
            "#,
            map_catalog,
        );
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "foo");
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            SymbolRef::with_unknown_text()
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            SymbolRef::with_unknown_text()
        );
        assert_eq!(
            reader
                .next_item()?
                .expect_value()?
                .read()?
                .expect_symbol()?,
            "bar"
        );
        Ok(())
    }

    #[test]
    fn truncate_with_max_id() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new(
            "shared_table",
            1,
            ["foo", "bar", "baz", "quux"],
        )?);
        // The stream contains a local symbol table that is not an append.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 2 } ],
                    symbols: ["quuz"]
                }
                $10 // foo
                $11 // bar
                $12 // quuz
            "#,
            map_catalog,
        );
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "foo");
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "bar");
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "quuz");
        Ok(())
    }

    #[test]
    fn detect_encoding_directive_text() -> IonResult<()> {
        let text = r#"
            $ion_1_1
            $ion_encoding::((symbol_table ["foo", "bar", "baz"]))
        "#;

        let mut reader = SystemReader::new(AnyEncoding, text);
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 1));
        reader.next_item()?.expect_encoding_directive()?;
        Ok(())
    }

    #[test]
    fn detect_encoding_directive_binary() -> IonResult<()> {
        let mut writer = LazyRawBinaryWriter_1_1::new(Vec::new())?;
        let mut directive = writer
            .value_writer()
            .with_annotations("$ion_encoding")?
            .sexp_writer()?;
        let mut symbol_table = directive.sexp_writer()?;
        symbol_table.write_symbol("symbol_table")?;
        symbol_table.write_list(["foo", "bar", "baz"])?;
        symbol_table.close()?;
        directive.close()?;
        let binary_ion = writer.close()?;

        let mut reader = SystemReader::new(AnyEncoding, binary_ion);
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 1));
        reader.next_item()?.expect_encoding_directive()?;
        Ok(())
    }

    #[test]
    fn ignore_encoding_directive_text_1_0() -> IonResult<()> {
        let text = r#"
            $ion_1_0
            // In Ion 1.0, this is just an annotated s-expression.
            $ion_encoding::((symbol_table ["foo", "bar", "baz"]))
        "#;

        let mut reader = SystemReader::new(AnyEncoding, text);
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 0));
        let sexp = reader.next_item()?.expect_value()?.read()?.expect_sexp()?;
        assert!(sexp.annotations().are(["$ion_encoding"])?);
        Ok(())
    }

    #[test]
    fn ignore_encoding_directive_binary_1_0() -> IonResult<()> {
        let mut writer = Writer::new(v1_0::Binary, Vec::new())?;
        let mut directive = writer
            .value_writer()
            .with_annotations("$ion_encoding")?
            .sexp_writer()?;
        let mut symbol_table = directive.sexp_writer()?;
        symbol_table.write_symbol("symbol_table")?;
        symbol_table.write_list(["foo", "bar", "baz"])?;
        symbol_table.close()?;
        directive.close()?;
        let bytes = writer.close()?;

        let mut reader = SystemReader::new(AnyEncoding, bytes);
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 0));
        let _ = reader.next_item()?.expect_symbol_table()?;
        let sexp = reader.next_item()?.expect_value()?.read()?.expect_sexp()?;
        assert!(sexp.annotations().are(["$ion_encoding"])?);
        Ok(())
    }

    #[test]
    fn read_encoding_directive_new_active_module() -> IonResult<()> {
        let ion = r#"
            $ion_1_1
            $ion_encoding::(
                (symbol_table ["foo", "bar", "baz"])
                (macro_table
                    (macro seventeen () 17)
                    (macro twelve () 12)))
            (:seventeen)
            (:twelve)
        "#;
        let mut reader = SystemReader::new(AnyEncoding, ion);
        // Before reading any data, the reader defaults to expecting the Text v1.0 encoding,
        // the only encoding that doesn't have to start with an IVM.
        assert_eq!(reader.detected_encoding(), IonEncoding::Text_1_0);

        // The first thing the reader encounters is an IVM. Verify that all of its accessors report
        // the expected values.
        let ivm = reader.next_item()?.expect_ivm()?;
        assert_eq!(ivm.major_minor(), (1, 1));
        assert_eq!(ivm.stream_encoding_before_marker(), IonEncoding::Text_1_0);
        assert_eq!(ivm.stream_encoding_after_marker()?, IonEncoding::Text_1_1);
        assert!(ivm.is_text());
        assert!(!ivm.is_binary());

        // After encountering the IVM, the reader will have changed its detected encoding to Text v1.1.
        assert_eq!(reader.detected_encoding(), IonEncoding::Text_1_1);

        // The next stream item is an encoding directive that defines some symbols and some macros.
        let _directive = reader.next_item()?.expect_encoding_directive()?;

        // === Make sure it has the expected symbol definitions ===
        let pending_changes = reader
            .pending_context_changes()
            .new_active_module()
            .expect("this directive defines a new active module");
        let new_symbol_table = pending_changes.symbol_table();
        assert_eq!(
            new_symbol_table.symbols_tail(3),
            &[
                Symbol::from("foo"),
                Symbol::from("bar"),
                Symbol::from("baz")
            ]
        );

        // === Make sure it has the expected macro definitions ====
        let new_macro_table = pending_changes.macro_table();
        // There are currently 3 supported system macros: void, values, and make_string.
        // This directive defines two more.
        assert_eq!(new_macro_table.len(), 2 + MacroTable::NUM_SYSTEM_MACROS);
        assert_eq!(
            new_macro_table.macro_with_id(4),
            new_macro_table.macro_with_name("seventeen")
        );
        assert_eq!(
            new_macro_table.macro_with_id(5),
            new_macro_table.macro_with_name("twelve")
        );

        // Expand the e-expressions to make sure the macro definitions work as expected.
        assert_eq!(reader.expect_next_value()?.read()?.expect_i64()?, 17);
        assert_eq!(reader.expect_next_value()?.read()?.expect_i64()?, 12);
        Ok(())
    }
}
