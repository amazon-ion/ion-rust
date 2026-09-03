#![allow(non_camel_case_types)]

use crate::catalog::Catalog;
use crate::constants::v1_1;
use crate::lazy::any_encoding::{IonEncoding, IonVersion};
use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::compiler::TemplateCompiler;
use crate::lazy::expanded::encoding_module::EncodingModule;
use crate::lazy::expanded::macro_table::{MacroTable, ION_1_1_SYSTEM_MACROS};
use crate::lazy::expanded::template::TemplateMacro;
use crate::lazy::expanded::{ExpandedStreamItem, ExpandingReader, LazyExpandedValue};
use crate::lazy::sequence::SExpIterator;
use crate::lazy::streaming_raw_reader::{IonInput, StreamingRawReader};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
use crate::lazy::value::LazyValue;
use crate::read_config::ReadConfig;
use crate::result::IonFailure;
use crate::{
    AnyEncoding, Int, IonError, IonResult, IonType, LazyField, LazySExp, LazyStruct, Symbol,
    SymbolTable, ValueRef,
};
use std::ops::Deref;
use std::sync::Arc;

/// The maximum number of placeholder (unknown-text) symbols that the reader is willing to
/// materialize while processing a single symbol table directive's `imports` list.
///
/// When a shared symbol table import cannot be resolved, the Ion 1.0 spec requires the reader
/// to reserve exactly `max_id` symbol IDs for it, padding with unknown-text placeholders as
/// needed. Because `max_id` is attacker-controlled and each placeholder occupies memory, a
/// tiny stream could otherwise instruct the reader to allocate an enormous symbol table (for
/// example, a `max_id` of 2^31 would materialize billions of placeholder symbols). Capping
/// the number of placeholders bounds that amplification: streams whose unresolvable imports
/// require more placeholders than this limit produce a decoding error instead.
///
/// One million placeholder symbols occupy tens of megabytes--far more than any known
/// legitimate use of substituted imports requires, but small enough to keep a malicious
/// stream from exhausting memory. Symbols that are actually present in a matching catalog
/// entry do not count against this limit.
pub(crate) const MAX_IMPORT_PLACEHOLDER_SYMBOLS: usize = 1_000_000;

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
#[cfg_attr(feature = "experimental-tooling-apis", visibility::make(pub))]
pub(crate) struct SystemReader<Encoding: Decoder, Input: IonInput> {
    pub(crate) expanding_reader: ExpandingReader<Encoding, Input>,
}

// If the reader encounters a symbol table in the stream, it will store all of the symbols that
// the table defines in this structure so that they may be applied when the reader next advances.
#[derive(Default)]
#[cfg_attr(feature = "experimental-tooling-apis", visibility::make(pub))]
pub(crate) struct PendingContextChanges {
    pub(crate) switch_to_version: Option<IonVersion>,
    pub(crate) has_changes: bool,
    pub(crate) is_lst_append: bool,
    pub(crate) imported_symbols: Vec<Symbol>,
    pub(crate) symbols: Vec<Symbol>,
    // A new encoding modules defined in the current encoding directive.
    // TODO: Support for defining several modules
    pub(crate) new_active_module: Option<EncodingModule>,
}

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
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

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
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

    /// Returns `true` if the provided `LazyRawValue` is an s-expression whose only annotation
    /// is `$ion`. Caller is responsible for confirming the sexp appeared at the top
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
        // At this point, we've confirmed it's an annotated s-expression. We need to see if:
        //   1. It only has one annotation
        //   2. That annotation is `$ion`
        // This may involve a lookup in the encoding context.
        // We'll promote this LazyExpandedValue to a LazyValue to facilitate that.
        let lazy_value = LazyValue::new(*lazy_value);
        lazy_value.annotations().are(["$ion"])
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        self.expanding_reader.context().symbol_table()
    }

    pub fn macro_table(&self) -> &MacroTable {
        self.expanding_reader.context().macro_table()
    }

    pub fn pending_context_changes(&self) -> &PendingContextChanges {
        self.expanding_reader.pending_context_changes()
    }

    /// Returns the next top-level stream item (IVM, symbol table, encoding directive, Value, or nothing)
    /// as an [`ExpandedStreamItem`].
    ///
    /// This method exists largely for tooling; most applications will want to
    /// use [`next_item`](Self::next_item).
    pub fn next_expanded_item(&mut self) -> IonResult<ExpandedStreamItem<'_, Encoding>> {
        self.expanding_reader.next_item()
    }

    /// Returns the next top-level stream item (IVM, symbol table, encoding directive, Value, or nothing)
    /// as a [`SystemStreamItem`].
    pub fn next_item(&mut self) -> IonResult<SystemStreamItem<'_, Encoding>> {
        self.expanding_reader.next_system_item()
    }

    /// Returns the next value that is part of the application data model, bypassing all encoding
    /// artifacts (IVMs, symbol tables).
    pub fn next_value(&mut self) -> IonResult<Option<LazyValue<'_, Encoding>>> {
        self.expanding_reader.next_value()
    }

    /// Like [`next_value`](Self::next_value) but returns an error if there is not another
    /// application value in the stream.
    pub fn expect_next_value(&mut self) -> IonResult<LazyValue<'_, Encoding>> {
        self.next_value()?.ok_or_else(|| {
            IonError::decoding_error("expected another application value but found none")
        })
    }

    pub(crate) fn process_encoding_directive(
        pending_changes: &mut PendingContextChanges,
        directive: LazyExpandedValue<'_, Encoding>,
    ) -> IonResult<()> {
        // We've already confirmed this is an annotated sexp
        let directive = LazyValue::new(directive).read()?.expect_sexp()?;
        let mut exprs = directive.iter();
        let operation = Self::expect_next_sexp_value("operation name", &mut exprs)?;
        let operation_name = Self::expect_symbol_text("operation name", operation)?;
        // For now, the only supported directive is `$ion::(module _ /*...*/)`.
        match operation_name {
            "module" => {}
            todo_operation @ ("encoding" | "import") => {
                return IonResult::decoding_error(format!(
                    "directive operation `{todo_operation}` is not yet supported"
                ));
            }
            invalid_operation => {
                return IonResult::decoding_error(format!(
                    "unrecognized directive operation `{invalid_operation}`"
                ));
            }
        }

        let module_name = Self::expect_next_sexp_value("module name", &mut exprs)?;
        let module_name = Self::expect_symbol_text("module name", module_name)?;

        if module_name != v1_1::constants::DEFAULT_MODULE_NAME {
            return IonResult::decoding_error("only the default module `_` is currently supported");
        }

        for step in exprs {
            Self::process_encoding_directive_operation(pending_changes, step?)?;
        }
        Ok(())
    }

    pub(crate) fn process_encoding_directive_operation(
        pending_changes: &mut PendingContextChanges,
        value: LazyValue<'_, Encoding>,
    ) -> IonResult<()> {
        let operation_sexp = value.read()?.expect_sexp().map_err(|_| {
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
                        v1_1::constants::DEFAULT_MODULE_NAME.to_owned(),
                        MacroTable::with_system_macros(IonVersion::v1_1),
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
                        v1_1::constants::DEFAULT_MODULE_NAME.to_owned(),
                        macro_table,
                        SymbolTable::empty(IonVersion::v1_1),
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

    fn process_symbol_table_definition(
        operation: LazySExp<'_, Encoding>,
    ) -> IonResult<SymbolTable> {
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
        // If we're processing a `(symbol_table ...)`, the stream must be Ion v1.1.
        let mut symbol_table = SymbolTable::empty(IonVersion::v1_1);
        for arg in args {
            match arg?.read()? {
                ValueRef::Symbol(symbol) if symbol == v1_1::constants::DEFAULT_MODULE_NAME => {
                    let active_symtab = operation.expanded().context.symbol_table();
                    for symbol in active_symtab.application_symbols() {
                        symbol_table.add_symbol(symbol.clone());
                    }
                }
                ValueRef::Symbol(symbol) => {
                    todo!("modules other than _ (found symbol '{symbol:?}')")
                }
                ValueRef::List(symbol_list) => {
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
                other => {
                    return IonResult::decoding_error(format!(
                        "found an unexpected value in the (symbol_table ...): {other:?}"
                    ));
                }
            };
        }
        Ok(symbol_table)
    }

    fn process_macro_table_definition(operation: LazySExp<'_, Encoding>) -> IonResult<MacroTable> {
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
        let mut new_macro_table = MacroTable::empty();
        for arg in args {
            let arg = arg?;
            let context = operation.expanded_sexp.context;
            match arg.read()? {
                ValueRef::SExp(macro_def_sexp) => {
                    let new_macro = TemplateCompiler::compile_from_sexp(
                        context.macro_table(),
                        &new_macro_table,
                        macro_def_sexp,
                    )?;
                    new_macro_table.add_template_macro(new_macro)?;
                }
                ValueRef::Symbol(module_name)
                    if module_name == v1_1::constants::DEFAULT_MODULE_NAME =>
                {
                    let active_mactab = operation.expanded().context.macro_table();
                    new_macro_table.append_all_macros_from(active_mactab)?;
                }
                ValueRef::Symbol(module_name)
                    if module_name == v1_1::system_symbols::ION.text() =>
                {
                    new_macro_table.append_all_macros_from(&ION_1_1_SYSTEM_MACROS)?;
                }
                ValueRef::Symbol(_module_name) => {
                    todo!("re-exporting macros from a module other than _")
                }
                _other => {
                    return IonResult::decoding_error(format!(
                        "macro_table was passed an unsupported argument type ({})",
                        arg.ion_type()
                    ));
                }
            }
        }
        Ok(new_macro_table)
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
        let mut imports_field: Option<LazyField<'_, Encoding>> = None;
        let mut symbols_field: Option<LazyField<'_, Encoding>> = None;

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
        // The number of placeholder symbols materialized for unresolvable imports so far
        // while processing this symbol table directive's `imports` list.
        let mut total_placeholders: usize = 0;
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
                        Some(ValueRef::Int(i)) if i > Int::ZERO => usize::try_from(i.clone())
                            .map_err(|_|
                                         IonError::decoding_error(format!("found a symbol table import (name='{name}') with a version number too high to support: {i}")),
                            ),
                        // If there's no version, a non-int version, or a version <= 0, we treat it
                        // as version 1.
                        _ => Ok(1),
                    }?;

                    // If the max_id is unspecified, null, negative, or an invalid data type,
                    // we treat it as undefined.
                    // See: https://amazon-ion.github.io/ion-docs/docs/symbols.html
                    let max_id: Option<usize> = match import.get("max_id")? {
                        Some(ValueRef::Int(i)) if i >= Int::ZERO => {
                            Some(usize::try_from(i).map_err(|_| {
                                IonError::decoding_error(
                                    "found a `max_id` beyond the range of usize",
                                )
                            })?)
                        }
                        _ => None,
                    };

                    // Look for an exact match in the catalog. If the requested version is not
                    // available and `max_id` is defined, fall back to the highest available
                    // version of the named table; if the catalog has no table with that name,
                    // substitute a dummy table by padding with `max_id` unknown-text symbols.
                    // If there is no exact match and `max_id` is undefined, the reader cannot
                    // know how many symbol IDs the import occupies; this is an error.
                    let shared_table = match catalog.get_table_with_version(name.as_ref(), version)
                    {
                        Some(table) => Some(table),
                        None if max_id.is_none() => return IonResult::decoding_error(
                            format!("symbol table import failed, could not find table with name='{name}' and version={version} and no valid max_id was specified")
                        ),
                        None => catalog.get_table(name.as_ref()),
                    };

                    let table_symbols: &[Symbol] =
                        shared_table.map(|table| table.symbols()).unwrap_or(&[]);

                    // If `max_id` is undefined, import all of the found table's symbols.
                    // (An exact match is guaranteed to have been found in that case.)
                    let max_id = max_id.unwrap_or(table_symbols.len());

                    // Import up to `max_id` symbols from the table...
                    let num_symbols_to_import = table_symbols.len().min(max_id);

                    pending_lst
                        .imported_symbols
                        .extend_from_slice(&table_symbols[..num_symbols_to_import]);

                    // ...and if the table did not have enough symbols (or was not found at all),
                    // pad the remaining symbol IDs with unknown text.
                    if max_id > num_symbols_to_import {
                        let num_pending_symbols = pending_lst.imported_symbols().len();
                        let num_placeholders = max_id - num_symbols_to_import;
                        // Placeholder symbols are materialized eagerly, so `max_id` values
                        // (which are attacker-controlled) must be capped to keep a small
                        // stream from demanding an enormous allocation. See the doc comment
                        // on `MAX_IMPORT_PLACEHOLDER_SYMBOLS` for details.
                        total_placeholders = total_placeholders
                            .checked_add(num_placeholders)
                            .filter(|&total| total <= MAX_IMPORT_PLACEHOLDER_SYMBOLS)
                            .ok_or_else(|| {
                                IonError::decoding_error(format!(
                                    "symbol table import (name='{name}', max_id={max_id}) requires \
                                     padding with more placeholder symbols than this implementation \
                                     is willing to materialize (limit: {MAX_IMPORT_PLACEHOLDER_SYMBOLS})"
                                ))
                            })?;
                        // In practice this addition cannot overflow: `num_placeholders` was
                        // just capped at `MAX_IMPORT_PLACEHOLDER_SYMBOLS` (above), and
                        // `num_pending_symbols` is the length of an existing `Vec<Symbol>`,
                        // which is far smaller than `usize::MAX - MAX_IMPORT_PLACEHOLDER_SYMBOLS`.
                        // The checked arithmetic is retained purely as defense in depth.
                        let num_symbols_after_import = num_pending_symbols
                            .checked_add(num_placeholders)
                            .ok_or_else(|| {
                                IonError::decoding_error(
                                    "internal error: combined symbol table size overflowed usize",
                                )
                            })?;
                        // The cap above bounds the allocation to a modest size; reserve the
                        // space fallibly anyway so that allocation failure (e.g. under severe
                        // memory pressure) surfaces as a decoding error instead of aborting
                        // the process.
                        pending_lst
                            .imported_symbols
                            .try_reserve(num_placeholders)
                            .map_err(|_| {
                                IonError::decoding_error(format!(
                                    "could not allocate space for a symbol table import with max_id {max_id}"
                                ))
                            })?;
                        pending_lst.imported_symbols.resize(
                            num_symbols_after_import,
                            Symbol::unknown_import_placeholder(),
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

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
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
    use crate::{v1_0, AnyEncoding, IonResult, SequenceWriter, SymbolRef, ValueWriter, Writer};

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
                SystemStreamItem::SymbolTable(ref s) => println!("symtab => {s:?}"),
                SystemStreamItem::EncodingDirective(ref s) => {
                    println!("encoding directive => {s:?}")
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

    use crate::catalog::MapCatalog;
    use crate::lazy::encoder::value_writer::AnnotatableWriter;
    use crate::shared_symbol_table::SharedSymbolTable;

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
    fn non_existent_shared_symbol_table_imports_with_max_id() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_1", 1, ["foo"])?);
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_2", 1, ["bar"])?);
        // `shared_table_3` and `shared_table_4` do not exist in the catalog, but their imports
        // declare a `max_id`. Per the spec, the reader substitutes a dummy table containing
        // `max_id` symbols with unknown text for each of them and continues.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table_3", version: 1, max_id: 3 }, { name:"shared_table_2", version: 1 }, { name:"shared_table_4", version: 1, max_id: 1 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // == $0
                $11 // == $0
                $12 // == $0
                $13 // "bar"
                $14 // == $0
                $15 // "local_symbol"
            "#,
            map_catalog,
        );
        // $10 through $12 are the placeholders for `shared_table_3`.
        for _ in 0..3 {
            assert_eq!(
                reader.expect_next_value()?.read()?.expect_symbol()?,
                SymbolRef::with_unknown_text()
            );
        }
        // $13 comes from `shared_table_2`, which was found in the catalog.
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "bar");
        // $14 is the placeholder for `shared_table_4`.
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            SymbolRef::with_unknown_text()
        );
        // $15 is the first local symbol following the imports.
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn resolved_import_with_overstated_max_id_pads_with_placeholders() -> IonResult<()> {
        use crate::{Element, Value};
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 1, ["foo"])?);
        // `shared_table` v1 IS in the catalog, but it only defines one symbol while the
        // import declares `max_id: 3`. Per the spec, the two extra symbol IDs are padded
        // with unknown-text symbols. Like the padding for an entirely unresolvable import,
        // these gap SIDs are substitute symbols: a later version of the table could define
        // their text, so they are placeholders (which the transcription layer refuses to
        // write), not genuine `$0`s.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 3 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // "foo"
                $11 // gap SID (padding placeholder)
                $13 // "local_symbol"
            "#,
            map_catalog,
        );
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "foo");
        // Reading the gap SID succeeds; the symbol has unknown text (equivalent to `$0`).
        let gap_symbol = reader.expect_next_value()?.read()?.expect_symbol()?;
        assert_eq!(gap_symbol, SymbolRef::with_unknown_text());
        // ...but transcribing it as an Element refuses with the placeholder error.
        let element: Element = Value::Symbol(gap_symbol.to_owned()).into();
        let result: IonResult<String> = element.encode_as(v1_0::Text);
        let error = result.expect_err("expected the writer to refuse the padding placeholder");
        assert!(matches!(error, IonError::Encoding(_)));
        assert!(
            error.to_string().contains("placeholder"),
            "unexpected error message: {error}"
        );
        // The local symbol that follows the padded gap still resolves correctly.
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn ion_1_1_unresolvable_import_with_max_id_takes_substitution_path() -> IonResult<()> {
        // An Ion 1.1 stream can still carry a 1.0-style `$ion_symbol_table` local symbol
        // table; its `imports` list is processed by the same resolution path as in Ion 1.0
        // (`process_imports` is not version-gated), so an unresolvable import with a
        // defined `max_id` is substituted with placeholder symbols. In Ion 1.1 the active
        // table's permanent prefix is only `$0`, so the import occupies $1-$2 and the
        // local symbol is $3.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_1_1
                $ion_symbol_table::{
                    imports: [ { name:"missing_table", version: 1, max_id: 2 } ],
                    symbols: [ "local_symbol" ]
                }
                $1 // gap SID (placeholder)
                $3 // "local_symbol"
            "#,
            map_catalog,
        );
        // The gap SID reads successfully as a symbol with unknown text...
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            SymbolRef::with_unknown_text()
        );
        // ...and the local symbol that follows the substituted import still resolves.
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn non_existent_shared_symbol_table_import_without_max_id() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        map_catalog.insert_table(SharedSymbolTable::new("shared_table_2", 1, ["bar"])?);
        // `shared_table_3` does not exist in the catalog and its import does not declare a
        // `max_id`, so the reader cannot know how many symbol IDs the import occupies.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table_3", version: 1 }, { name:"shared_table_2", version: 1 } ],
                    symbols: [ "local_symbol" ]
                }
                $10
            "#,
            map_catalog,
        );
        // We step over the LST...
        assert!(
            matches!(reader.next_item(), Err(IonError::Decoding(_))),
            "expected a decoding error because shared_table_3 does not exist and its import has no max_id"
        );
        Ok(())
    }

    #[test]
    fn non_existent_shared_symbol_table_import_with_zero_max_id() -> IonResult<()> {
        let map_catalog = MapCatalog::new();
        // A `max_id` of 0 means the unresolvable import occupies no symbol IDs at all.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 0 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // "local_symbol"
            "#,
            map_catalog,
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn non_existent_shared_symbol_table_import_with_invalid_max_id() -> IonResult<()> {
        // Per the spec, a `max_id` that is null, not an int, or less than zero is treated as
        // though it were undefined. An undefined `max_id` on an unresolvable import is an error.
        for max_id in ["null", "null.int", "-2", "max", "2.5"] {
            let map_catalog = MapCatalog::new();
            let mut reader = system_reader_with_catalog_for(
                format!(
                    r#"
                        $ion_symbol_table::{{
                            imports: [ {{ name:"shared_table", version: 1, max_id: {max_id} }} ],
                            symbols: [ "local_symbol" ]
                        }}
                        $10
                    "#
                ),
                map_catalog,
            );
            assert!(
                matches!(reader.next_item(), Err(IonError::Decoding(_))),
                "expected a decoding error for an unresolvable import with max_id: {max_id}"
            );
        }
        Ok(())
    }

    #[test]
    fn shared_symbol_table_imports_with_max_ids_summing_past_usize() -> IonResult<()> {
        // Each import's `max_id` fits in a usize on its own, but together they describe more
        // symbol IDs than a usize can represent. The reader must detect this and return a
        // decoding error rather than silently wrapping (which would truncate the previously
        // imported symbols and misalign all subsequent SIDs). In practice the placeholder
        // cap check catches this case: its running total is computed with `checked_add`, so
        // the sum either overflows (an error) or exceeds `MAX_IMPORT_PLACEHOLDER_SYMBOLS`
        // (also an error).
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            format!(
                r#"
                    $ion_symbol_table::{{
                        imports: [
                            {{ name:"shared_table_a", version: 1, max_id: 1 }},
                            {{ name:"shared_table_b", version: 1, max_id: {} }},
                        ],
                        symbols: [ "local_symbol" ]
                    }}
                    $10
                "#,
                usize::MAX
            ),
            map_catalog,
        );
        assert!(
            matches!(reader.next_item(), Err(IonError::Decoding(_))),
            "expected a decoding error when imports' max_id values sum past usize::MAX"
        );
        Ok(())
    }

    #[test]
    fn shared_symbol_table_import_with_absurd_max_id_fails_cleanly() -> IonResult<()> {
        // A `max_id` of usize::MAX is representable, but the placeholder symbols it describes
        // could never be materialized. The placeholder cap (`MAX_IMPORT_PLACEHOLDER_SYMBOLS`)
        // rejects the import with a decoding error before any allocation is attempted.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            format!(
                r#"
                    $ion_symbol_table::{{
                        imports: [ {{ name:"shared_table", version: 1, max_id: {} }} ],
                        symbols: [ "local_symbol" ]
                    }}
                    $10
                "#,
                usize::MAX
            ),
            map_catalog,
        );
        assert!(
            matches!(reader.next_item(), Err(IonError::Decoding(_))),
            "expected a decoding error for an import with max_id = usize::MAX"
        );
        Ok(())
    }

    #[test]
    fn import_placeholders_exceeding_cap_fail_cleanly() -> IonResult<()> {
        // A single unresolvable import whose `max_id` requires more placeholder symbols than
        // `MAX_IMPORT_PLACEHOLDER_SYMBOLS` is rejected with a decoding error that mentions
        // the cap, before any placeholders are materialized.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            format!(
                r#"
                    $ion_symbol_table::{{
                        imports: [ {{ name:"shared_table", version: 1, max_id: {} }} ],
                        symbols: [ "local_symbol" ]
                    }}
                    $10
                "#,
                MAX_IMPORT_PLACEHOLDER_SYMBOLS + 1
            ),
            map_catalog,
        );
        let error = reader
            .next_item()
            .expect_err("expected a decoding error for an import exceeding the placeholder cap");
        assert!(matches!(error, IonError::Decoding(_)));
        assert!(
            error
                .to_string()
                .contains(&MAX_IMPORT_PLACEHOLDER_SYMBOLS.to_string()),
            "the error message should mention the placeholder cap: {error}"
        );
        Ok(())
    }

    #[test]
    fn import_placeholder_cap_applies_across_imports() -> IonResult<()> {
        // Each import's `max_id` is under the cap on its own, but the total number of
        // placeholder symbols required by the directive's `imports` list exceeds it.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            format!(
                r#"
                    $ion_symbol_table::{{
                        imports: [
                            {{ name:"shared_table_a", version: 1, max_id: {max_id} }},
                            {{ name:"shared_table_b", version: 1, max_id: {max_id} }},
                        ]
                    }}
                    $10
                "#,
                max_id = (MAX_IMPORT_PLACEHOLDER_SYMBOLS / 2) + 1
            ),
            map_catalog,
        );
        assert!(
            matches!(reader.next_item(), Err(IonError::Decoding(_))),
            "expected a decoding error when imports' combined placeholder count exceeds the cap"
        );
        Ok(())
    }

    #[test]
    fn refuse_to_transcribe_unknown_import_placeholder_symbols() -> IonResult<()> {
        // Symbol IDs in the range of an unresolvable import can be read (as symbols with
        // unknown text), but the writer refuses to transcribe them: encoding them as `$0`
        // would silently discard the fact that they have text in the (unavailable) shared
        // table.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 1 } ]
                }
                $10
            "#,
            map_catalog,
        );
        let value = reader.expect_next_value()?;
        // Reading the placeholder works; it is equivalent to `$0`.
        assert_eq!(
            value.read()?.expect_symbol()?,
            SymbolRef::with_unknown_text()
        );
        // Writing it does not.
        let mut writer = Writer::new(v1_0::Text, Vec::new())?;
        let result = writer.write(value);
        assert!(
            matches!(result, Err(IonError::Encoding(_))),
            "expected an encoding error when transcribing a placeholder symbol"
        );
        Ok(())
    }

    #[test]
    fn refuse_to_transcribe_placeholders_nested_in_containers() -> IonResult<()> {
        // Placeholder symbols nested inside containers are also refused when the containing
        // `Element` is transcribed.
        use crate::element::element_writer::ElementWriter;
        use crate::element::reader::ElementReader;
        use crate::lazy::reader::Reader;
        for document in [
            "[1, $10, 3]",   // list
            "(foo $10 bar)", // s-expression
        ] {
            let input = format!(
                r#"
                    $ion_symbol_table::{{
                        imports: [ {{ name:"shared_table", version: 1, max_id: 1 }} ]
                    }}
                    {document}
                "#
            );
            let mut reader = Reader::new(AnyEncoding.with_catalog(MapCatalog::new()), input)?;
            let element = reader
                .read_next_element()?
                .expect("expected to read an element");
            let mut writer = Writer::new(v1_0::Text, Vec::new())?;
            let result = writer.write_element(&element);
            assert!(
                matches!(result, Err(IonError::Encoding(_))),
                "expected an encoding error transcribing {document}, got {result:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn refuse_to_transcribe_placeholder_annotations_lazily() -> IonResult<()> {
        // Lazy transcription refuses placeholder symbols in annotation position, not just in
        // value position.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 1 } ]
                }
                $10::5
            "#,
            map_catalog,
        );
        let value = reader.expect_next_value()?;
        let mut writer = Writer::new(v1_0::Text, Vec::new())?;
        let result = writer.write(value);
        assert!(
            matches!(result, Err(IonError::Encoding(_))),
            "expected an encoding error when transcribing a placeholder annotation"
        );
        Ok(())
    }

    #[test]
    fn refuse_to_transcribe_placeholder_field_names_lazily() -> IonResult<()> {
        // Lazy transcription refuses placeholder symbols in struct field name position, not
        // just in value position.
        let map_catalog = MapCatalog::new();
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 1 } ]
                }
                { $10: 5 }
            "#,
            map_catalog,
        );
        let value = reader.expect_next_value()?;
        let mut writer = Writer::new(v1_0::Text, Vec::new())?;
        let result = writer.write(value);
        assert!(
            matches!(result, Err(IonError::Encoding(_))),
            "expected an encoding error when transcribing a placeholder field name"
        );
        Ok(())
    }

    #[test]
    fn value_writer_apis_emit_placeholders_as_sid_zero() -> IonResult<()> {
        // The typed transcription layer (`WriteAsIon`) refuses to encode placeholder symbols
        // (see the tests above), but the value writer APIs accept symbol tokens through
        // infallible conversions to `RawSymbolRef`. Those conversions are an intentional lossy
        // escape hatch: the placeholder flag is discarded and the token is written as `$0`.
        // This test pins that documented behavior for all three symbol token positions.
        use crate::lazy::encoder::value_writer::StructWriter;
        let placeholder = Symbol::unknown_import_placeholder();

        // Value position: both the `Symbol` and `SymbolRef` conversions are lossy.
        let mut writer = Writer::new(v1_0::Text, Vec::new())?;
        writer.value_writer().write_symbol(&placeholder)?;
        writer
            .value_writer()
            .write_symbol(SymbolRef::from(&placeholder))?;
        let output = String::from_utf8(writer.close()?).unwrap();
        assert_eq!(output.split_whitespace().collect::<Vec<_>>(), ["$0", "$0"]);

        // Struct field name position
        let mut writer = Writer::new(v1_0::Text, Vec::new())?;
        let mut struct_writer = writer.value_writer().struct_writer()?;
        struct_writer
            .field_writer(SymbolRef::from(&placeholder))
            .write_i64(1)?;
        struct_writer.close()?;
        let output = String::from_utf8(writer.close()?).unwrap();
        assert!(
            output.contains("$0"),
            "expected a $0 field name in the output: {output}"
        );

        // Annotation position
        let mut writer = Writer::new(v1_0::Text, Vec::new())?;
        writer
            .value_writer()
            .with_annotations(vec![SymbolRef::from(&placeholder)])?
            .write_i64(1)?;
        let output = String::from_utf8(writer.close()?).unwrap();
        assert!(
            output.contains("$0::"),
            "expected a $0 annotation in the output: {output}"
        );
        Ok(())
    }

    #[test]
    fn shared_symbol_table_import_falls_back_to_highest_version() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        // The catalog has v2 of `shared_table` but the import requests v1. Because the import
        // declares a `max_id`, the reader falls back to the highest available version of the
        // table and sizes its symbol subsequence to exactly `max_id` (truncating here).
        map_catalog.insert_table(SharedSymbolTable::new(
            "shared_table",
            2,
            ["foo", "bar", "baz"],
        )?);
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 2 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // "foo"
                $11 // "bar"
                $12 // "local_symbol"
            "#,
            map_catalog,
        );
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "foo");
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "bar");
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn shared_symbol_table_version_fallback_pads_to_max_id() -> IonResult<()> {
        let mut map_catalog = MapCatalog::new();
        // The catalog has v2 of `shared_table` (with a single symbol) but the import requests
        // v1 with a max_id of 3. The reader falls back to v2 and pads its symbols with unknown
        // text to reach exactly `max_id` symbols.
        map_catalog.insert_table(SharedSymbolTable::new("shared_table", 2, ["foo"])?);
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 3 } ],
                    symbols: [ "local_symbol" ]
                }
                $10 // "foo"
                $11 // == $0
                $12 // == $0
                $13 // "local_symbol"
            "#,
            map_catalog,
        );
        assert_eq!(reader.expect_next_value()?.read()?.expect_symbol()?, "foo");
        for _ in 0..2 {
            assert_eq!(
                reader.expect_next_value()?.read()?.expect_symbol()?,
                SymbolRef::with_unknown_text()
            );
        }
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        Ok(())
    }

    #[test]
    fn lst_append_after_substituted_import() -> IonResult<()> {
        let map_catalog = MapCatalog::new();
        // `shared_table` is not in the catalog, so the reader substitutes a dummy table with
        // two placeholder symbols ($10 and $11). The second LST imports `$ion_symbol_table`,
        // appending to the current table: the placeholders must keep their positions and the
        // appended symbol must be assigned the next available symbol ID.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 2 } ],
                    symbols: [ "local_symbol" ]
                }
                $ion_symbol_table::{
                    imports: $ion_symbol_table,
                    symbols: [ "appended_symbol" ]
                }
                $10 // == $0
                $11 // == $0
                $12 // "local_symbol"
                $13 // "appended_symbol"
            "#,
            map_catalog,
        );
        for _ in 0..2 {
            assert_eq!(
                reader.expect_next_value()?.read()?.expect_symbol()?,
                SymbolRef::with_unknown_text()
            );
        }
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "appended_symbol"
        );
        Ok(())
    }

    #[test]
    fn ivm_discards_substituted_import_context() -> IonResult<()> {
        let map_catalog = MapCatalog::new();
        // Before the IVM, $10 and $11 are placeholders from the substituted import and $12 is
        // the local symbol that follows them. The IVM resets the symbol table to the system
        // symbols; after a fresh LST (with no imports), $10 is the first new local symbol
        // rather than a placeholder from the discarded import context.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 2 } ],
                    symbols: [ "local_symbol" ]
                }
                $12 // "local_symbol"
                $ion_1_0
                $ion_symbol_table::{
                    symbols: [ "fresh_symbol" ]
                }
                $10 // "fresh_symbol"
            "#,
            map_catalog,
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "local_symbol"
        );
        assert_eq!(
            reader.expect_next_value()?.read()?.expect_symbol()?,
            "fresh_symbol"
        );
        Ok(())
    }

    #[test]
    fn substituted_import_symbols_as_field_name_and_annotation() -> IonResult<()> {
        let map_catalog = MapCatalog::new();
        // $10 and $11 are placeholders from the substituted import. Using them as a field
        // name and as an annotation must parse successfully and surface unknown text.
        let mut reader = system_reader_with_catalog_for(
            r#"
                $ion_symbol_table::{
                    imports: [ { name:"shared_table", version: 1, max_id: 3 } ],
                    symbols: [ "local_symbol" ]
                }
                { $10: 1 }
                $11::true
            "#,
            map_catalog,
        );
        let struct_ = reader.expect_next_value()?.read()?.expect_struct()?;
        let field = struct_
            .iter()
            .next()
            .expect("the struct should have a field")?;
        assert_eq!(field.name()?, SymbolRef::with_unknown_text());
        assert_eq!(field.value().read()?.expect_i64()?, 1);

        let annotated = reader.expect_next_value()?;
        let annotation = annotated
            .annotations()
            .next()
            .expect("the value should have an annotation")?;
        assert_eq!(annotation, SymbolRef::with_unknown_text());
        assert!(annotated.read()?.expect_bool()?);
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

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn detect_encoding_directive_text() -> IonResult<()> {
        let text = r#"
            $ion_1_1
            $ion::
            (module _
                (symbol_table ["foo", "bar", "baz"]))
        "#;

        let mut reader = SystemReader::new(AnyEncoding, text);
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 1));
        reader.next_item()?.expect_encoding_directive()?;
        Ok(())
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn detect_encoding_directive_binary() -> IonResult<()> {
        use crate::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
        let mut writer = LazyRawBinaryWriter_1_1::new(Vec::new())?;
        let mut directive = writer
            .value_writer()
            .with_annotations("$ion")?
            .sexp_writer()?;
        directive
            .write_symbol(v1_1::system_symbols::MODULE)?
            .write_symbol(v1_1::constants::DEFAULT_MODULE_NAME)?;

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
            $ion::
            (encoding _
                (symbol_table ["foo", "bar", "baz"]))
        "#;

        let mut reader = SystemReader::new(AnyEncoding, text);
        assert_eq!(reader.next_item()?.expect_ivm()?.major_minor(), (1, 0));
        let sexp = reader.next_item()?.expect_value()?.read()?.expect_sexp()?;
        assert!(sexp.annotations().are(["$ion"])?);
        Ok(())
    }

    #[test]
    fn ignore_encoding_directive_binary_1_0() -> IonResult<()> {
        let mut writer = Writer::new(v1_0::Binary, Vec::new())?;
        let mut directive = writer
            .value_writer()
            .with_annotations("$ion")?
            .sexp_writer()?;
        // We avoid using 1.1 text constants here because access to them is feature gated.
        directive.write_symbol("module")?.write_symbol("_")?;
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
        assert!(sexp.annotations().are(["$ion"])?);
        Ok(())
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn read_encoding_directive_new_active_module() -> IonResult<()> {
        let ion = r#"
            $ion_1_1
            $ion::
            (module _
                (symbol_table ["foo", "bar", "baz"])
                (macro_table
                    _
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
                Symbol::from("baz"),
            ]
        );

        // === Make sure it has the expected macro definitions ====
        let new_macro_table = pending_changes.macro_table();
        // This directive defines two new macros in addition to the existing system macros.
        assert_eq!(new_macro_table.len(), 2 + MacroTable::NUM_SYSTEM_MACROS);
        assert_eq!(
            new_macro_table.macro_with_id(MacroTable::FIRST_USER_MACRO_ID),
            new_macro_table.macro_with_name("seventeen")
        );
        assert_eq!(
            new_macro_table.macro_with_id(MacroTable::FIRST_USER_MACRO_ID + 1),
            new_macro_table.macro_with_name("twelve")
        );

        // Expand the e-expressions to make sure the macro definitions work as expected.
        assert_eq!(reader.expect_next_value()?.read()?.expect_i64()?, 17);
        assert_eq!(reader.expect_next_value()?.read()?.expect_i64()?, 12);
        Ok(())
    }
}
