use delegate::delegate;
use ice_code::ice as cold_path;
use std::io::Write;
use std::ops::Deref;
use std::sync::Arc;

use crate::constants::v1_0::system_symbol_ids;
use crate::constants::v1_1;
use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::binary::v1_1::value_writer::BinaryValueWriter_1_1;
use crate::lazy::encoder::value_writer::internal::{
    EExpWriterInternal, FieldEncoder, MakeValueWriter,
};
use crate::lazy::encoder::value_writer::{
    AnnotatableWriter, EExpWriter, FieldWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::value_writer_config::{
    AnnotationsEncoding, ContainerEncoding, FieldNameEncoding, SymbolValueEncoding,
    ValueWriterConfig,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::{
    BinaryEncoding_1_0, BinaryEncoding_1_1, Encoding, TextEncoding_1_0, TextEncoding_1_1,
};
use crate::lazy::expanded::macro_table::{Macro, MacroRef, ION_1_1_SYSTEM_MACROS};
use crate::lazy::expanded::template::{Parameter, ParameterEncoding};
use crate::lazy::text::raw::v1_1::reader::{MacroIdLike, MacroIdRef, ModuleKind, QualifiedAddress};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::write_config::WriteConfig;
use crate::{
    ContextWriter, Decimal, Element, ElementWriter, Int, IonError, IonInput, IonResult, IonType,
    IonVersion, MacroDef, MacroTable, RawSymbolRef, Symbol, SymbolId, SymbolTable, TemplateMacro,
    Timestamp, UInt, Value,
};

/// A thin wrapper around a `SymbolTable` that tracks the number of symbols whose definition has
/// not yet been written to output.
pub(crate) struct WriterSymbolTable {
    symbols: SymbolTable,
    num_pending: usize,
}

impl WriterSymbolTable {
    pub fn reset_num_pending(&mut self) {
        self.num_pending = 0;
    }

    pub fn num_pending(&self) -> usize {
        self.num_pending
    }

    pub fn pending(&self) -> &[Symbol] {
        self.symbols.symbols_tail(self.num_pending)
    }

    pub fn add_symbol_for_text<A: AsRef<str>>(&mut self, text: A) -> SymbolId {
        self.num_pending += 1;
        self.symbols.add_symbol_for_text(text)
    }

    pub fn new(symbols: SymbolTable) -> Self {
        Self {
            symbols,
            num_pending: 0,
        }
    }
}

// Read-only methods on the underlying SymbolTable can be invoked directly.
impl Deref for WriterSymbolTable {
    type Target = SymbolTable;

    fn deref(&self) -> &Self::Target {
        &self.symbols
    }
}

/// A thin wrapper around a `MacroTable` that tracks the number of macros whose definition has
/// not yet been written to output.
pub struct WriterMacroTable {
    macros: MacroTable,
    num_pending: usize,
}

impl WriterMacroTable {
    pub fn new(macros: MacroTable) -> Self {
        Self {
            macros,
            num_pending: 0,
        }
    }

    pub fn add_template_macro(&mut self, template_macro: TemplateMacro) -> IonResult<usize> {
        let address = self.macros.add_template_macro(template_macro)?;
        self.num_pending += 1;
        Ok(address)
    }

    pub(crate) fn add_macro(&mut self, macro_ref: &Arc<MacroDef>) -> IonResult<usize> {
        let address = self.macros.len();
        self.macros.append_macro(macro_ref)?;
        self.num_pending += 1;
        Ok(address)
    }

    pub fn reset_num_pending(&mut self) {
        self.num_pending = 0;
    }

    pub fn num_pending(&self) -> usize {
        self.num_pending
    }

    pub fn pending(&self) -> &[Arc<MacroDef>] {
        self.macros.macros_tail(self.num_pending)
    }
}

// Read-only methods on the underlying MacroTable can be invoked directly.
impl Deref for WriterMacroTable {
    type Target = MacroTable;

    fn deref(&self) -> &Self::Target {
        &self.macros
    }
}

/// An Ion writer that maintains a symbol table and creates new entries as needed.
pub struct Writer<E: Encoding, Output: Write> {
    symbols: WriterSymbolTable,
    data_writer: E::Writer<Vec<u8>>,
    directive_writer: E::Writer<Vec<u8>>,
    output: Output,
    value_writer_config: ValueWriterConfig,
}

// These aliases are used for selectively re-exporting writer types in lib.rs.
#[allow(dead_code)]
pub type TextWriter_1_0<Output> = Writer<TextEncoding_1_0, Output>;
#[allow(dead_code)]
pub type BinaryWriter_1_0<Output> = Writer<BinaryEncoding_1_0, Output>;
#[allow(dead_code)]
pub type TextWriter_1_1<Output> = Writer<TextEncoding_1_1, Output>;
#[allow(dead_code)]
pub type BinaryWriter_1_1<Output> = Writer<BinaryEncoding_1_1, Output>;

impl<E: Encoding, Output: Write> Writer<E, Output> {
    /// Constructs a writer for the requested encoding using the provided configuration.
    pub fn new(config: impl Into<WriteConfig<E>>, output: Output) -> IonResult<Self> {
        let config = config.into();
        let directive_writer = E::Writer::build(config.clone(), vec![])?;
        let mut data_writer = E::Writer::build(config, vec![])?;
        // Erase the IVM that's created by default
        data_writer.output_mut().clear();
        // TODO: LazyEncoder should define a method to construct a new symtab and/or macro table
        let ion_version = E::ion_version();
        let symbols = WriterSymbolTable::new(SymbolTable::new(ion_version));
        let mut writer = Writer {
            symbols,
            data_writer,
            directive_writer,
            output,
            value_writer_config: E::default_value_writer_config(),
        };
        writer.flush()?;
        Ok(writer)
    }

    pub(crate) fn macro_table(&self) -> &WriterMacroTable {
        self.data_writer.macro_table()
    }

    pub(crate) fn macro_table_mut(&mut self) -> Option<&mut WriterMacroTable> {
        self.data_writer.macro_table_mut()
    }

    /// Takes a TDL expression representing a macro definition and returns a `Macro` that can
    /// later be invoked by passing it to [`Writer::eexp_writer()`].
    pub fn compile_macro(&mut self, source: impl IonInput) -> IonResult<Macro> {
        self.data_writer.compile_macro(source)
    }

    /// Register a previously compiled `Macro` for use in this `Writer`.
    pub fn register_macro(&mut self, macro_: &Macro) -> IonResult<Macro> {
        self.data_writer.register_macro(macro_.definition())
    }

    /// Gets a macro with the provided ID from the default module.
    pub fn get_macro<'a>(&self, id: impl Into<MacroIdRef<'a>>) -> IonResult<Macro> {
        let id = id.into();
        let macro_table = self.macro_table();

        let qualified_address = match id {
            MacroIdRef::LocalName(name) => {
                let address = macro_table.address_for_id(id).ok_or_else(|| {
                    IonError::illegal_operation(format!(
                        "macro table does not contain a macro named '{name}'"
                    ))
                })?;
                QualifiedAddress::new(ModuleKind::Default, address)
            }
            MacroIdRef::LocalAddress(address) => {
                QualifiedAddress::new(ModuleKind::Default, address)
            }
            MacroIdRef::SystemAddress(address) => {
                QualifiedAddress::new(ModuleKind::System, address.as_usize())
            }
        };

        let macro_table: &MacroTable = match qualified_address.module() {
            ModuleKind::Default => self.macro_table(),
            ModuleKind::System => &ION_1_1_SYSTEM_MACROS,
        };

        let macro_def = macro_table
            .clone_macro_with_address(qualified_address.address())
            .ok_or_else(|| {
                IonError::encoding_error(format!("no macro with the specified ID ({id:?}) found"))
            })?;

        Ok(Macro::new(macro_def, qualified_address))
    }

    pub fn output(&self) -> &Output {
        &self.output
    }

    pub fn output_mut(&mut self) -> &mut Output {
        &mut self.output
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        // This method forwards the call to the trait method implementation. It's here so
        // you can call `write()` on an ApplicationWriter without having to import SequenceWriter
        // separately.
        <Self as SequenceWriter>::write(self, value)
    }

    /// Writes bytes of previously encoded values to the output stream.
    pub fn flush(&mut self) -> IonResult<()> {
        if self.symbols.num_pending() > 0 {
            match E::ion_version() {
                IonVersion::v1_0 => self.write_lst_append()?,
                IonVersion::v1_1 => self.write_append_symbols_directive()?,
            }
            self.symbols.reset_num_pending();
        }

        // TODO: In Ion 1.1, new symbols and new macros could be added using the same directive.
        if self.macro_table().num_pending() > 0 {
            self.write_append_macros_directive()?;
            self.macro_table_mut()
                .expect("the pending macro count is >0")
                .reset_num_pending();
        }

        self.directive_writer.flush()?;
        self.output
            .write_all(self.directive_writer.output().as_slice())?;
        self.directive_writer.output_mut().clear();

        self.data_writer.flush()?;
        self.output
            .write_all(self.data_writer.output().as_slice())?;
        self.data_writer.output_mut().clear();

        self.output.flush()?;
        Ok(())
    }

    pub fn close(mut self) -> IonResult<Output> {
        self.flush()?;
        Ok(self.output)
    }

    #[inline]
    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbols
    }

    /// Helper method to encode an LST append containing pending symbols.
    fn write_lst_append(&mut self) -> IonResult<()> {
        let Self {
            symbols,
            directive_writer,
            ..
        } = self;

        let mut lst = directive_writer
            .value_writer()
            .with_annotations(system_symbol_ids::ION_SYMBOL_TABLE)?
            .struct_writer()?;

        lst.field_writer(system_symbol_ids::IMPORTS)
            .write_symbol(system_symbol_ids::ION_SYMBOL_TABLE)?;

        let mut new_symbol_list = lst.field_writer(system_symbol_ids::SYMBOLS).list_writer()?;

        let pending_symbols = symbols.pending().iter().map(Symbol::text);

        new_symbol_list.write_all(pending_symbols)?;
        new_symbol_list.close()?;

        lst.close()
    }

    fn write_append_macros_directive(&mut self) -> IonResult<()> {
        let Self {
            data_writer,
            directive_writer,
            ..
        } = self;

        let macros = data_writer.macro_table();

        // TODO: Once expression group serialization is complete, this can be replaced by a call
        //       to the `add_macros` system macro.
        let mut directive = directive_writer
            .value_writer()
            .with_annotations("$ion")?
            .sexp_writer()?;

        directive
            .write_symbol(v1_1::system_symbols::MODULE)?
            .write_symbol(v1_1::constants::DEFAULT_MODULE_NAME)?;

        let mut symbols_sexp = directive.sexp_writer()?;
        symbols_sexp
            .write_symbol(v1_1::system_symbols::SYMBOL_TABLE)?
            .write_symbol(v1_1::constants::DEFAULT_MODULE_NAME)?;
        symbols_sexp.close()?;

        let pending_macros = macros
            .pending()
            .iter()
            // Only user-defined template macros can be added to the macro table.
            .map(|m| m.require_template());

        let mut macro_table = directive.sexp_writer()?;
        macro_table
            .write_symbol(v1_1::system_symbols::MACRO_TABLE)?
            .write_symbol(v1_1::constants::DEFAULT_MODULE_NAME)?
            .write_all(pending_macros)?;
        macro_table.close()?;
        directive.close()
    }

    /// Helper method to encode an LST append containing pending symbols.
    fn write_append_symbols_directive(&mut self) -> IonResult<()> {
        let Self {
            symbols,
            directive_writer,
            ..
        } = self;

        let mut directive = directive_writer
            .value_writer()
            .with_annotations(v1_1::system_symbols::ION)?
            .sexp_writer()?;

        directive
            .write_symbol(v1_1::system_symbols::MODULE)?
            .write_symbol(v1_1::constants::DEFAULT_MODULE_NAME)?;

        let pending_symbols = symbols.pending().iter().map(Symbol::text);

        let mut symbol_table = directive.sexp_writer()?;
        symbol_table
            .write_symbol(v1_1::system_symbols::SYMBOL_TABLE)?
            .write_symbol(v1_1::constants::DEFAULT_MODULE_NAME)?
            .write_list(pending_symbols)?;
        symbol_table.close()?;
        directive.close()
    }
}

impl<E: Encoding, Output: Write> ContextWriter for Writer<E, Output> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <E::Writer<Vec<u8>> as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<E: Encoding, Output: Write> MakeValueWriter for Writer<E, Output> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        let raw_value_writer = self.data_writer.make_value_writer();
        let symbols = &mut self.symbols;

        ApplicationValueWriter {
            raw_value_writer,
            symbols,
            value_writer_config: self.value_writer_config,
        }
    }
}

impl<E: Encoding, Output: Write> SequenceWriter for Writer<E, Output> {
    type Resources = Output;

    fn close(mut self) -> IonResult<Self::Resources> {
        self.flush()?;
        Ok(self.output)
    }
}

pub struct ApplicationValueWriter<'a, V: ValueWriter> {
    symbols: &'a mut WriterSymbolTable,
    raw_value_writer: V,
    value_writer_config: ValueWriterConfig,
}

impl<'a, V: ValueWriter> ApplicationValueWriter<'a, V> {
    pub(crate) fn new(
        symbols: &'a mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_value_writer: V,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_value_writer,
        }
    }

    #[inline]
    pub fn symbol_table(&self) -> &SymbolTable {
        self.symbols
    }
}

// Generally useful methods, but currently only called in unit tests.
impl ApplicationValueWriter<'_, BinaryValueWriter_1_1<'_, '_>> {
    pub fn with_container_encoding(mut self, container_encoding: ContainerEncoding) -> Self {
        self.value_writer_config = self
            .value_writer_config
            .with_container_encoding(container_encoding);
        self
    }

    pub fn with_annotations_encoding(mut self, annotations_encoding: AnnotationsEncoding) -> Self {
        self.value_writer_config = self
            .value_writer_config
            .with_annotations_encoding(annotations_encoding);
        self
    }

    pub fn with_symbol_value_encoding(
        mut self,
        symbol_value_encoding: SymbolValueEncoding,
    ) -> Self {
        self.value_writer_config = self
            .value_writer_config
            .with_symbol_value_encoding(symbol_value_encoding);
        self
    }

    pub fn with_field_name_encoding(
        mut self,
        field_name_encoding: FieldNameEncoding,
    ) -> Self {
        self.value_writer_config = self
            .value_writer_config
            .with_field_name_encoding(field_name_encoding);
        self
    }
}

impl<V: ValueWriter> AnnotatableWriter for ApplicationValueWriter<'_, V> {
    type AnnotatedValueWriter<'a>
        = ApplicationValueWriter<'a, V::AnnotatedValueWriter<'a>>
    where
        Self: 'a;

    fn with_annotations<'a>(
        mut self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        let mut annotations = annotations.into_annotations_vec();
        match self.value_writer_config.annotations_encoding() {
            AnnotationsEncoding::SymbolIds => {
                // Intern all text so everything we write is a symbol ID
                self.intern_all_annotations(&mut annotations)?
            }
            AnnotationsEncoding::InlineText => {
                // Validate the symbol IDs, write the text as-is
                self.validate_all_symbol_ids(&mut annotations)?
            }
            AnnotationsEncoding::NewSymbolsAsInlineText => {
                // Map all known strings to symbol IDs, leave new text as is.
                self.map_known_symbols_to_symbol_ids(&mut annotations)?
            }
        };

        Ok(ApplicationValueWriter {
            symbols: self.symbols,
            raw_value_writer: self.raw_value_writer.with_annotations(annotations)?,
            value_writer_config: self.value_writer_config,
        })
    }
}

impl<V: ValueWriter> ApplicationValueWriter<'_, V> {
    /// Converts each annotation in `annotations` to a symbol ID, adding symbols to the symbol table
    /// as necessary. If one of the annotations is a symbol ID that is not in the symbol table,
    /// returns an `Err`.
    fn intern_all_annotations<'a>(&mut self, annotations: &mut AnnotationsVec<'a>) -> IonResult<()>
    where
        Self: 'a,
    {
        for annotation in annotations {
            match annotation.as_raw_symbol_ref() {
                // The token is already a symbol ID.
                RawSymbolRef::SymbolId(sid) => {
                    if !self.symbol_table().sid_is_valid(sid) {
                        return IonResult::encoding_error(format!(
                            "annotation symbol ID {sid} is out of range"
                        ));
                    }
                }
                RawSymbolRef::SystemSymbol_1_1(_symbol) => {
                    // The system symbol was validated on creation.
                }
                // The token is text...
                RawSymbolRef::Text(text) => {
                    let sid = match self.symbol_table().sid_for(text) {
                        Some(sid) => {
                            //...that was already in the symbol table.
                            sid
                        }
                        None => {
                            // ...that we need to add to the symbol table.
                            self.symbols.add_symbol_for_text(text)
                        }
                    };
                    *annotation = RawSymbolRef::SymbolId(sid);
                }
            };
        }
        Ok(())
    }

    /// Confirms all SIDs are in the symbol table while leaving text annotations as-is.
    pub(crate) fn validate_all_symbol_ids<'a>(
        &mut self,
        annotations: &mut AnnotationsVec<'a>,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        for annotation in annotations {
            if let RawSymbolRef::SymbolId(sid) = annotation.as_raw_symbol_ref() {
                if !self.symbol_table().sid_is_valid(sid) {
                    return IonResult::encoding_error(format!(
                        "annotation symbol ID {sid} is not in the symbol table"
                    ));
                }
            }
        }
        Ok(())
    }

    /// Converts annotations with known text to their corresponding symbol ID. Annotations with
    /// text not yet in the symbol table are left as-is. If a symbol ID is not in the symbol table,
    /// returns an `Err`.
    fn map_known_symbols_to_symbol_ids<'a>(
        &mut self,
        annotations: &mut AnnotationsVec<'a>,
    ) -> IonResult<()>
    where
        Self: 'a,
    {
        for annotation in annotations {
            match annotation.as_raw_symbol_ref() {
                // The token is already a symbol ID.
                RawSymbolRef::SymbolId(sid) => {
                    if !self.symbol_table().sid_is_valid(sid) {
                        return IonResult::encoding_error(format!(
                            "annotation symbol ID {sid} is out of range"
                        ));
                    }
                }
                RawSymbolRef::SystemSymbol_1_1(_symbol) => {
                    // Symbol was validated on creation, nothing to do.
                }
                // The token is text...
                RawSymbolRef::Text(text) => {
                    match self.symbols.sid_for(text) {
                        Some(sid) => {
                            //...that was already in the symbol table.
                            *annotation = RawSymbolRef::SymbolId(sid);
                        }
                        None => {
                            // ...that is not in the symbol table. Leave it as-is.
                        }
                    };
                }
            };
        }
        Ok(())
    }
}

impl<'value, V: ValueWriter> ValueWriter for ApplicationValueWriter<'value, V> {
    type ListWriter = ApplicationListWriter<'value, V>;
    type SExpWriter = ApplicationSExpWriter<'value, V>;
    type StructWriter = ApplicationStructWriter<'value, V>;
    type EExpWriter = ApplicationEExpWriter<'value, V>;

    delegate! {
        to self.raw_value_writer {
            fn write_null(self, ion_type: IonType) -> IonResult<()> ;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
        }
    }

    fn write_symbol(self, value: impl AsRawSymbolRef) -> IonResult<()> {
        use RawSymbolRef::*;
        use SymbolValueEncoding::*;

        let Self {
            symbols,
            raw_value_writer,
            value_writer_config,
            ..
        } = self;

        // Depending on the symbol value encoding config option, map the provided symbol reference
        // from text to SID or vice versa, performing any validation needed.
        let symbol_ref = match value.as_raw_symbol_ref() {
            SymbolId(symbol_id) => {
                // We can write the symbol ID as-is. Make sure it's in the symbol table.
                if !symbols.sid_is_valid(symbol_id) {
                    return cold_path!(IonResult::encoding_error(format!(
                        "symbol value ID ${symbol_id} is not in the symbol table"
                    )));
                }
                SymbolId(symbol_id)
            }
            SystemSymbol_1_1(symbol) => SystemSymbol_1_1(symbol),
            Text(text) => {
                match value_writer_config.symbol_value_encoding() {
                    SymbolIds => {
                        // Map the text to a symbol ID.
                        match symbols.sid_for(text) {
                            // If it's already in the symbol table, use that SID.
                            Some(symbol_id) => SymbolId(symbol_id),
                            // Otherwise, add it to the symbol table.
                            None => SymbolId(symbols.add_symbol_for_text(text)),
                        }
                    }
                    NewSymbolsAsInlineText => {
                        // If the text is in the symbol table, use the symbol ID. Otherwise, use the text itself.
                        match symbols.sid_for(text) {
                            Some(symbol_id) => SymbolId(symbol_id),
                            None => Text(text),
                        }
                    }
                    // We have text and we want to write text. Nothing to do.
                    InlineText => Text(text),
                }
            }
        };

        raw_value_writer.write_symbol(symbol_ref)
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        Ok(ApplicationListWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_value_writer.list_writer()?,
        ))
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        Ok(ApplicationSExpWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_value_writer.sexp_writer()?,
        ))
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        let config = self.value_writer_config;
        Ok(ApplicationStructWriter::new(
            self.symbols,
            config,
            self.raw_value_writer.struct_writer()?,
        ))
    }

    fn eexp_writer<'a>(self, macro_id: impl MacroIdLike<'a>) -> IonResult<Self::EExpWriter>
    where
        Self: 'a,
    {
        Ok(ApplicationEExpWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_value_writer.eexp_writer(macro_id)?,
        ))
    }
}

pub struct ApplicationStructWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_struct_writer: V::StructWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationStructWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        config: ValueWriterConfig,
        raw_struct_writer: V::StructWriter,
    ) -> Self {
        Self {
            symbols,
            raw_struct_writer,
            value_writer_config: config,
        }
    }

    // Generally useful, but currently only called in unit tests.
    pub fn with_field_name_encoding(mut self, field_name_encoding: FieldNameEncoding) -> Self {
        self.value_writer_config = self
            .value_writer_config
            .with_field_name_encoding(field_name_encoding);
        self
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationStructWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <V::StructWriter as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationStructWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_struct_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> FieldEncoder for ApplicationStructWriter<'_, V> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        let text = match name.as_raw_symbol_ref() {
            // This is an application-level struct writer. It is expected that method calls will
            // almost always be provided text; if the user passes in a symbol ID, it means they have
            // special knowledge of the encoding environment and are bypassing the 'managed' layer.
            // We range check the SID and write it as-is. In the unusual circumstance that the user
            // has a SID at the application level and wants to write text, they can and should
            // resolve the SID in the symbol table before calling this method.
            RawSymbolRef::SymbolId(symbol_id) => {
                if !self.symbols.sid_is_valid(symbol_id) {
                    return cold_path!(IonResult::encoding_error(format!(
                        "symbol ID ${symbol_id} is not in the symbol table"
                    )));
                }
                return self.raw_struct_writer.encode_field_name(symbol_id);
            }
            RawSymbolRef::SystemSymbol_1_1(symbol) => {
                return self.raw_struct_writer.encode_field_name(symbol);
            }
            // Otherwise, get its associated text.
            RawSymbolRef::Text(text) => text,
        };

        // From here on, we're dealing with text.

        // If the struct writer is configured to write field names as text, do that.
        if self.value_writer_config.field_name_encoding() == FieldNameEncoding::InlineText {
            return self.raw_struct_writer.encode_field_name(text);
        }

        // Otherwise, see if the symbol is already in the symbol table.
        let token: RawSymbolRef<'_> = match self.symbols.sid_for(text) {
            // If so, use the existing ID.
            Some(sid) => sid.into(),
            // If it's not but the struct writer is configured to intern new text, add it to the
            // symbol table.
            None if self.value_writer_config.field_name_encoding()
                == FieldNameEncoding::SymbolIds =>
            {
                self.symbols.add_symbol_for_text(text).into()
            }
            // Otherwise, we'll write the text as-is.
            None => text.into(),
        };

        // Finally, encode the field name using the selected token representation
        self.raw_struct_writer.encode_field_name(token)
    }
}

impl<V: ValueWriter> StructWriter for ApplicationStructWriter<'_, V> {
    fn field_writer<'a>(&'a mut self, name: impl Into<RawSymbolRef<'a>>) -> FieldWriter<'a, Self> {
        FieldWriter::new(name.into(), self.value_writer_config, self)
    }

    fn close(self) -> IonResult<()> {
        self.raw_struct_writer.close()
    }

    fn config(&self) -> ValueWriterConfig {
        self.value_writer_config
    }
}

pub struct ApplicationListWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_list_writer: V::ListWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationListWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_list_writer: V::ListWriter,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_list_writer,
        }
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationListWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <V::ListWriter as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationListWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_list_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> SequenceWriter for ApplicationListWriter<'_, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_list_writer.close()
    }
}

pub struct ApplicationSExpWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_sexp_writer: V::SExpWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationSExpWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_sexp_writer: V::SExpWriter,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_sexp_writer,
        }
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationSExpWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<'a, <V::SExpWriter as ContextWriter>::NestedValueWriter<'a>>
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationSExpWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_sexp_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> SequenceWriter for ApplicationSExpWriter<'_, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_sexp_writer.close()
    }
}

pub struct ApplicationEExpWriter<'value, V: ValueWriter> {
    symbols: &'value mut WriterSymbolTable,
    raw_eexp_writer: V::EExpWriter,
    value_writer_config: ValueWriterConfig,
}

impl<'value, V: ValueWriter> ApplicationEExpWriter<'value, V> {
    pub(crate) fn new(
        symbols: &'value mut WriterSymbolTable,
        value_writer_config: ValueWriterConfig,
        raw_eexp_writer: V::EExpWriter,
    ) -> Self {
        Self {
            symbols,
            value_writer_config,
            raw_eexp_writer,
        }
    }

    /// Returns a reference to the macro signature parameter for which the next argument corresponds.
    /// If no more parameters remain in the signature, returns `None`.
    pub fn current_parameter(&self) -> Option<&Parameter> {
        self.raw_eexp_writer.current_parameter()
    }

    /// Helper method. If there are no more parameters, returns `Err`. Otherwise, returns
    /// `Ok(next_parameter)`.
    #[inline]
    fn expect_next_parameter(&mut self) -> IonResult<&Parameter> {
        self.raw_eexp_writer.expect_next_parameter()
    }
}

impl<V: ValueWriter> SequenceWriter for ApplicationEExpWriter<'_, V> {
    type Resources = ();

    /// Writes a value in the current context (list, s-expression, or stream) and upon success
    /// returns another reference to `self` to enable method chaining.
    fn write<Value: WriteAsIon>(&mut self, value: Value) -> IonResult<&mut Self> {
        value.write_as_ion(self.make_value_writer())?;
        Ok(self)
    }

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_eexp_writer.close()
    }
}

impl<V: ValueWriter> ContextWriter for ApplicationEExpWriter<'_, V> {
    type NestedValueWriter<'a>
        = ApplicationValueWriter<
        'a,
        <<V as ValueWriter>::EExpWriter as ContextWriter>::NestedValueWriter<'a>,
    >
    where
        Self: 'a;
}

impl<V: ValueWriter> MakeValueWriter for ApplicationEExpWriter<'_, V> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        ApplicationValueWriter::new(
            self.symbols,
            self.value_writer_config,
            self.raw_eexp_writer.make_value_writer(),
        )
    }
}

impl<V: ValueWriter> EExpWriterInternal for ApplicationEExpWriter<'_, V> {
    fn expect_next_parameter(&mut self) -> IonResult<&Parameter> {
        Self::expect_next_parameter(self) // Delegate to the inherent impl
    }
}

impl<V: ValueWriter> EExpWriter for ApplicationEExpWriter<'_, V> {
    type ExprGroupWriter<'group>
        = <V::EExpWriter as EExpWriter>::ExprGroupWriter<'group>
    where
        Self: 'group;

    fn invoked_macro(&self) -> MacroRef<'_> {
        self.raw_eexp_writer.invoked_macro()
    }

    fn current_parameter(&self) -> Option<&Parameter> {
        Self::current_parameter(self) // Delegate to the inherent impl
    }

    fn write_flex_uint(&mut self, value: impl Into<UInt>) -> IonResult<()> {
        self.expect_next_parameter()
            .and_then(|p| p.expect_encoding(&ParameterEncoding::FlexUInt))?;
        self.raw_eexp_writer.write_flex_uint(value)
    }

    fn write_fixed_uint8(&mut self, value: impl Into<u8>) -> IonResult<()> {
        self.expect_next_parameter()
            .and_then(|p| p.expect_encoding(&ParameterEncoding::UInt8))?;
        self.raw_eexp_writer.write_fixed_uint8(value)
    }

    fn expr_group_writer(&mut self) -> IonResult<Self::ExprGroupWriter<'_>> {
        let _param = self.expect_next_parameter()
            .and_then(|p| p.expect_variadic())?;
        // TODO: Pass `Parameter` to group writer so it can do its own validation
        self.raw_eexp_writer.expr_group_writer()
    }
}

impl<S: SequenceWriter> ElementWriter for S {
    fn write_value(&mut self, value: &Value) -> IonResult<()> {
        self.write(value)?;
        Ok(())
    }

    fn write_element(&mut self, element: &Element) -> IonResult<()> {
        self.write(element)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::value_writer::AnnotatableWriter;
    use crate::lazy::encoder::value_writer_config::{AnnotationsEncoding, SymbolValueEncoding};
    use crate::raw_symbol_ref::AsRawSymbolRef;
    use crate::{
        v1_0, v1_1, EExpWriter, Element, FieldNameEncoding, HasSpan, IonResult, LazyRawValue,
        RawSymbolRef, SequenceWriter, StructWriter, SystemReader, TextFormat, ValueWriter, Writer,
    };
    use std::io::BufWriter;

    fn symbol_value_encoding_test<const N: usize, A: AsRawSymbolRef>(
        encoding: SymbolValueEncoding,
        symbol_and_encoding_pairs: [(A, &[u8]); N],
    ) -> IonResult<()> {
        let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
        for (symbol, _expected_bytes) in &symbol_and_encoding_pairs {
            writer
                .value_writer()
                .with_symbol_value_encoding(encoding)
                .write_symbol(symbol)?;
        }
        let bytes = writer.close()?;
        let mut reader = SystemReader::new(v1_1::Binary, bytes.as_slice());
        for (symbol, expected_bytes) in &symbol_and_encoding_pairs {
            let value = reader.expect_next_value()?;
            let raw_value = value.raw().unwrap();
            let actual_bytes = raw_value.span().bytes();
            assert_eq!(
                actual_bytes, *expected_bytes,
                "actual {actual_bytes:02X?} != expected {expected_bytes:02X?}",
            );
            println!(
                "{:?} {:02X?} == {:02X?}",
                symbol.as_raw_symbol_ref(),
                actual_bytes,
                expected_bytes
            )
        }
        Ok(())
    }

    #[test]
    fn intern_new_symbol_values() -> IonResult<()> {
        use RawSymbolRef::*;
        symbol_value_encoding_test(
            SymbolValueEncoding::SymbolIds,
            [
                (Text("$ion_symbol_table"), &[0xE1, 0x03]),
                (Text("name"), &[0xE1, 0x04]),
                (SymbolId(6), &[0xE1, 0x06]), // SIDs are written as-is
                (Text("foo"), &[0xE1, 0x40]), // Text is added to the symbol table and encoded as a SID
            ],
        )
    }

    #[test]
    fn do_not_intern_new_symbol_values() -> IonResult<()> {
        use RawSymbolRef::*;
        symbol_value_encoding_test(
            SymbolValueEncoding::NewSymbolsAsInlineText,
            [
                // Known text symbols are written as SIDs
                (Text("$ion_symbol_table"), &[0xE1, 0x03]),
                (Text("name"), &[0xE1, 0x04]),
                // SIDs are written as-is
                (SymbolId(6), &[0xE1, 0x06]),
                // New text symbols are written as inline text
                //                 f     o     o
                (Text("foo"), &[0xA3, 0x66, 0x6F, 0x6F]),
            ],
        )
    }

    #[test]
    fn encode_all_text_as_is() -> IonResult<()> {
        use RawSymbolRef::*;
        symbol_value_encoding_test(
            SymbolValueEncoding::InlineText,
            [
                // Known text symbols are written as inline text
                (Text("name"), &[0xA4, 0x6E, 0x61, 0x6D, 0x65]),
                // SIDs are written as-is
                (SymbolId(6), &[0xE1, 0x06]),
                // New text symbols are written as inline text
                //                 f     o     o
                (Text("foo"), &[0xA3, 0x66, 0x6F, 0x6F]),
            ],
        )
    }

    fn annotations_sequence_encoding_test(
        encoding: AnnotationsEncoding,
        sequence: &[RawSymbolRef<'_>],
        expected_encoding: &[u8],
    ) -> IonResult<()> {
        let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
        writer
            .value_writer()
            .with_annotations_encoding(encoding)
            .with_annotations(sequence)?
            .write_string("foo")?;
        let bytes = writer.close()?;
        let mut reader = SystemReader::new(v1_1::Binary, bytes.as_slice());
        let value = reader.expect_next_value()?;
        let raw_value = value.raw().unwrap();
        let annotations = raw_value.annotations_span();
        assert_eq!(
            annotations.bytes(),
            expected_encoding,
            "{:02X?} != {:02X?}",
            annotations.bytes(),
            expected_encoding
        );
        Ok(())
    }

    #[test]
    fn intern_new_annotations() -> IonResult<()> {
        use RawSymbolRef::*;
        annotations_sequence_encoding_test(
            AnnotationsEncoding::SymbolIds,
            &[
                Text("$ion_symbol_table"),
                Text("name"),
                SymbolId(6),
                Text("foo"),
            ],
            &[
                0xE9, // Opcode: FlexUInt follows with byte length of sequence
                0x0B, // FlexUInt byte length: 4
                0x07, // FlexSym SID $3
                0x09, // FlexSym SID $4
                0x0D, // FlexSym SID $6
                0x02, 0x01, // FlexSym SID $64
            ],
        )
    }

    #[test]
    fn write_new_annotations_as_text() -> IonResult<()> {
        use RawSymbolRef::*;
        annotations_sequence_encoding_test(
            AnnotationsEncoding::NewSymbolsAsInlineText,
            &[
                Text("$ion_symbol_table"),
                Text("name"),
                SymbolId(6),
                Text("foo"),
            ],
            &[
                0xE9, // Opcode: FlexUInt follows with byte length of sequence
                0x0F, // FlexUInt byte length: 7
                0x07, // FlexSym: SID $3
                0x09, // FlexSym: SID $4
                0x0D, // FlexSym: SID $6
                0xFB, // FlexSym: 3 UTF-8 bytes
                // f     o     o
                0x66, 0x6F, 0x6F,
            ],
        )
    }

    #[test]
    #[rustfmt::skip]
    fn write_text_annotations_as_is() -> IonResult<()> {
        use RawSymbolRef::*;
        annotations_sequence_encoding_test(
            AnnotationsEncoding::InlineText,
            &[Text("name"), SymbolId(6), Text("foo")],
            &[
                0xE9, // Opcode: FlexUInt follows with byte length of sequence
                0x15, // FlexUInt byte length: 10
                0xF9, // FlexSym: 4 UTF-8 bytes
                // n     a     m     e
                0x6E, 0x61, 0x6D, 0x65,
                0x0D, // FlexSym: SID $6
                0xFB, // FlexSym: 3 UTF-8 bytes
                // f     o     o
                0x66, 0x6F, 0x6F,
            ],
        )
    }

    /// Writes a struct with all of the provided field names using the requested field name encoding.
    /// For simplicity, the value for each field is the integer 0.
    fn struct_field_encoding_test(
        encoding: FieldNameEncoding,
        field_names_and_encodings: &[(RawSymbolRef<'_>, &[u8])],
    ) -> IonResult<()> {
        // Configure a struct writer that uses the requested field name encoding
        let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
        let mut struct_writer = writer
            .value_writer()
            .struct_writer()?
            .with_field_name_encoding(encoding);

        for (name, _) in field_names_and_encodings {
            struct_writer.write(name, /* same value for every field*/ 0)?;
        }
        struct_writer.close()?;
        let bytes = writer.close()?;

        println!("encoded bytes: {bytes:02X?}");

        let mut reader = SystemReader::new(v1_1::Binary, bytes.as_slice());
        let struct_ = reader.expect_next_value()?.read()?.expect_struct()?;
        for (field, (_name, expected_encoding)) in
            struct_.iter().zip(field_names_and_encodings.iter())
        {
            let raw_name = field?.raw_name().unwrap();
            let raw_name_encoding = raw_name.span().bytes();
            assert_eq!(
                raw_name_encoding, *expected_encoding,
                "actual {:#02X?}\n!=\nexpected {:#02X?}",
                raw_name_encoding, *expected_encoding
            );
        }

        Ok(())
    }

    #[test]
    fn intern_all_field_names() -> IonResult<()> {
        struct_field_encoding_test(
            FieldNameEncoding::SymbolIds,
            &[
                // New symbols
                (RawSymbolRef::Text("foo"), &[0x81]), // FlexUInt SID $64,
                (RawSymbolRef::Text("bar"), &[0x83]), // FlexUInt SID $65,
                (RawSymbolRef::Text("baz"), &[0x85]), // FlexUInt SID $66,
                // Symbols that are already in the symbol table
                (RawSymbolRef::Text("name"), &[0x09]), // FlexUInt SID $4,
                (RawSymbolRef::Text("foo"), &[0x81]),  // FlexUInt SID $64,
            ],
        )
    }

    #[test]
    fn write_all_field_names_as_text() -> IonResult<()> {
        struct_field_encoding_test(
            FieldNameEncoding::InlineText,
            &[
                // New symbols
                (RawSymbolRef::Text("foo"), &[0xFB, 0x66, 0x6F, 0x6F]), // FlexSym -3, "foo"
                (RawSymbolRef::Text("bar"), &[0xFB, 0x62, 0x61, 0x72]), // FlexSym -3, "bar"
                (RawSymbolRef::Text("baz"), &[0xFB, 0x62, 0x61, 0x7A]), // FlexSym -3, "baz"
                // Symbols that are already in the symbol table are still written as text
                (RawSymbolRef::Text("name"), &[0xF9, 0x6E, 0x61, 0x6D, 0x65]), // FlexSym -4, "name"
            ],
        )
    }

    #[test]
    fn write_new_field_names_as_text() -> IonResult<()> {
        struct_field_encoding_test(
            FieldNameEncoding::NewSymbolsAsInlineText,
            &[
                // New symbols
                (RawSymbolRef::Text("foo"), &[0xFB, 0x66, 0x6F, 0x6F]), // FlexSym -3, "foo"
                (RawSymbolRef::Text("bar"), &[0xFB, 0x62, 0x61, 0x72]), // FlexSym -3, "bar"
                (RawSymbolRef::Text("baz"), &[0xFB, 0x62, 0x61, 0x7A]), // FlexSym -3, "baz"
                // Symbols that are already in the symbol table are written as SIDs
                (RawSymbolRef::Text("name"), &[0x09]), // FlexSym 4, SID $4,
            ],
        )
    }

    #[test]
    fn define_new_macro() -> IonResult<()> {
        let mut writer = Writer::new(v1_1::Text.with_format(TextFormat::Lines), Vec::new())?;

        // Define a macro
        let identity = writer.compile_macro("(macro identity (x*) (%x))")?;

        // Invoke that macro
        let mut eexp_writer = writer.eexp_writer(&identity)?;
        let mut group_writer = eexp_writer.expr_group_writer()?;
        group_writer.write_all(["foo", "bar", "baz"])?;
        group_writer.close()?;
        eexp_writer.close()?;

        writer.flush()?;

        // Confirm the output is as expected
        let output = writer.output().as_slice();

        println!("output:\n{}", std::str::from_utf8(output).unwrap());

        let actual = Element::read_all(output)?;

        let expected = Element::read_all(
            r#"
            "foo"
            "bar"
            "baz"
        "#,
        )?;

        assert_eq!(
            actual, expected,
            "// actual\n{actual:?}\n// !=\n// expected\n{expected:?}"
        );

        Ok(())
    }

    #[test]
    fn flush_underlying_sink() -> IonResult<()> {
        // The final output destination
        let mut buffer: Vec<u8> = Vec::new();
        // A BufWriter that, when flushed, writes bytes to the final output destination
        let buf_writer = BufWriter::new(&mut buffer);
        // An Ion Writer that writes bytes to the buf_writer
        let mut writer = Writer::new(v1_0::Binary, buf_writer)?;
        let len_before_flush = writer.output().get_ref().len();
        // Write some data
        writer.write([1, 2, 3, 4, 5])?;
        // At this point, we've written some data but haven't flushed the inner `buf_writer`,
        // so the length of its underlying `Vec<u8>` should remain unchanged.
        assert_eq!(writer.output().get_ref().len(), len_before_flush);
        // Flush the Ion writer. This should in turn flush the buf_writer, causing bytes to be
        // written to the underlying `Vec<u8>`.
        writer.flush()?;
        // Make sure that this caused the encoded bytes to reach the `Vec<u8>`.
        assert!(writer.output().get_ref().len() > len_before_flush);
        Ok(())
    }

    mod eexp_parameter_validation {
        use super::*;
        use num_traits::{PrimInt, Unsigned};
        use rstest::*;

        #[test]
        fn accept_valid_parameter_encoding() -> IonResult<()> {
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro("(macro foo (a flex_uint::b) (.values (%a) (%b)))")?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // The argument passed as parameter `a` is "hello"
            eexp_writer.write("hello")?;
            // The argument passed as parameter `b` is 42
            eexp_writer.write_flex_uint(42usize)?;
            eexp_writer.close()?;
            let bytes = writer.close()?;
            // Reading the encoded data back, we get the expected output.
            let actual = Element::read_all(&bytes)?;
            let expected = Element::read_all("\"hello\" 42")?;
            assert_eq!(actual, expected);
            Ok(())
        }

        #[test]
        fn tagged_parameter_rejects_flex_uint() -> IonResult<()> {
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro("(macro foo (a flex_uint::b) (.values (%a) (%b)))")?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // Attempt to write a FlexUInt where a tagged value is required, resulting in an error.
            assert!(eexp_writer.write_flex_uint(42usize).is_err());
            Ok(())
        }

        #[test]
        fn flex_uint_parameter_rejects_tagged_value() -> IonResult<()> {
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro("(macro foo (a flex_uint::b) (.values (%a) (%b)))")?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            eexp_writer.write("hello")?;
            // Attempt to write a tagged value where a FlexUInt is required, resulting in an error.
            assert!(eexp_writer.write("world").is_err());
            Ok(())
        }

        #[test]
        fn exactly_one_parameter_rejects_expr_group() -> IonResult<()> {
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro("(macro foo (a) (%a)))")?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // Attempt to start an expression group for parameter `a`, which has a cardinality of
            // exactly-one.
            assert!(eexp_writer.expr_group_writer().is_err());
            Ok(())
        }

        #[test]
        fn zero_or_more_parameter_rejects_tagged_value() -> IonResult<()> {
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro("(macro foo (a*) (%a)))")?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // Attempt to write a tagged value for parameter `a`, which has a cardinality of
            // zero-or-more, and therefore requires an expression group.
            assert!(eexp_writer.write("hello").is_err());
            Ok(())
        }

        #[test]
        fn tagless_uint8_encoding() -> IonResult<()> {
            let macro_source = "(macro foo (uint8::x) (%x))";
            let expected: &[u8] = &[
                0xE0, 0x01, 0x01, 0xEA,                       // IVM
                0xE7, 0xF9, 0x24, 0x69, 0x6F, 0x6E,           // $ion::
                0xFC, 0x55, 0xEE, 0x10, 0xA1, 0x5F,           // (module _
                0xC4, 0xEE, 0x0F, 0xA1, 0x5F,                 //   (symbol_table _ )
                0xFC, 0x3F, 0xEE, 0x0E, 0xA1, 0x5F,           //   (macro_table _
                0xFC, 0x33,                                   //      (
                0xA5, 0x6d, 0x61, 0x63, 0x72, 0x6F,           //        macro
                0xA3, 0x66, 0x6F, 0x6F,                       //        foo
                0xC9,                                         //        (
                0xE7, 0xF7, 0x75, 0x69, 0x6E, 0x74, 0x38,     //          uint8::
                0xA1, 0x78,                                   //          x )
                0xC4, 0xA1, 0x25, 0xA1, 0x78,                 //        ('%' x))))
                0x18, 0x05,                                   //  (:foo 5)

            ];

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // eexp_writer should do the "right thing" given the parameter's encoding.
            eexp_writer.write_int(&5.into())?;
            let _ = eexp_writer.close();
            let output = writer.close()?;
            assert_eq!(output.as_slice(), expected);

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // eexp_writer should do the "right thing" given the parameter's encoding.
            eexp_writer.write_i64(5i64)?;
            let _ = eexp_writer.close();
            let output = writer.close()?;
            assert_eq!(output.as_slice(), expected);

            Ok(())
        }

        #[test]
        fn tagless_uint8_encoding_fails() -> IonResult<()> {
            let macro_source = "(macro foo (uint8::x) (%x))";

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // eexp_writer should do the "right thing" given the parameter's encoding.
            let result = eexp_writer.write_int(&1024.into());
            // the "right thing" should be to error, since `x` can only be an 8bit unsigned int.
            assert!(result.is_err(), "unexpected success");

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // eexp_writer should do the "right thing" given the parameter's encoding.
            let result = eexp_writer.write_i64(1024.into());
            // the "right thing" should be to error, since `x` can only be an 8bit unsigned int.
            assert!(result.is_err(), "unexpected success");

            Ok(())
        }

        #[rstest]
        #[case::uint8("(macro foo (uint8::x) (%x))", 5, "5")]
        #[case::uint16("(macro foo (uint16::x) (%x))", 5, "5")]
        #[case::uint32("(macro foo (uint32::x) (%x))", 5, "5")]
        #[case::uint64("(macro foo (uint64::x) (%x))", 5, "5")]
        fn tagless_uint_encoding(#[case] macro_source: &str, #[case] input: i64, #[case] expected: &str) -> IonResult<()> {
            use crate::{Int, Element};

            // write_int

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            let int: Int = input.into();
            eexp_writer.write_int(&int)?;
            eexp_writer.close()?;

            let output = writer.close()?;
            let actual = Element::read_all(&output)?;
            let exp_elem = Element::read_all(expected)?;
            assert_eq!(actual, exp_elem);

            // write_i64

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            eexp_writer.write_i64(input)?;
            eexp_writer.close()?;

            let output = writer.close()?;
            let actual = Element::read_all(&output)?;
            let exp_elem = Element::read_all(expected)?;
            assert_eq!(actual, exp_elem);

            Ok(())
        }

        #[rstest]
        #[case::uint8("(macro foo (uint8::x) (%x))", 5u8)]
        #[case::uint16("(macro foo (uint16::x) (%x))", 5u16)]
        #[case::uint32("(macro foo (uint32::x) (%x))", 5u32)]
        #[case::uint64("(macro foo (uint64::x) (%x))", 5u64)]
        fn tagless_uint_encoding_write_int_fails<T: PrimInt + Unsigned>(#[case] macro_source: &str, #[case] input: T) -> IonResult<()> {
            let max_int = T::max_value();
            let max_int_plus_one = num_traits::cast::cast::<_, i128>(max_int).unwrap() + 1i128;
            let neg_input = -num_traits::cast::cast::<_, i128>(input).unwrap();

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            let result = eexp_writer.write_int(&max_int_plus_one.into());
            assert!(result.is_err(), "unexpected success");

            // Ensure we cannot write a negative value..
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            let result = eexp_writer.write_int(&neg_input.into());
            assert!(result.is_err(), "unexpected success");

            Ok(())
        }

        #[rstest]
        #[case::uint8("(macro foo (uint8::x) (%x))", 5u8)]
        #[case::uint16("(macro foo (uint16::x) (%x))", 5u16)]
        #[case::uint32("(macro foo (uint32::x) (%x))", 5u32)]
        fn tagless_uint_encoding_write_i64_fails<T: PrimInt + Unsigned>(#[case] macro_source: &str, #[case] input: T) -> IonResult<()> {
            let max_int = T::max_value();
            let max_int_plus_one = num_traits::cast::cast::<_, i128>(max_int).unwrap() + 1i128;
            let neg_input = -num_traits::cast::cast::<_, i128>(input).unwrap();

            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            // eexp_writer should do the "right thing" given the parameter's encoding.
            let result = eexp_writer.write_i64(max_int_plus_one.try_into().unwrap());
            // the "right thing" should be to error, since `x` can only be an 8bit unsigned int.
            assert!(result.is_err(), "unexpected success");

            // Ensure we cannot write a negative value..
            let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
            let foo = writer.compile_macro(macro_source)?;
            let mut eexp_writer = writer.eexp_writer(&foo)?;
            let result = eexp_writer.write_i64(neg_input.try_into().unwrap());
            assert!(result.is_err(), "unexpected success");

            Ok(())
        }
    }
}
