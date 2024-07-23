use std::io::Write;

use delegate::delegate;
use ice_code::ice as cold_path;

use crate::constants::v1_0::system_symbol_ids;
use crate::lazy::encoder::annotation_seq::AnnotationSeq;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{
    AnnotatableWriter, EExpWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::{LazyRawWriter, SymbolCreationPolicy};
use crate::lazy::encoding::{
    BinaryEncoding_1_0, BinaryEncoding_1_1, Encoding, TextEncoding_1_0, TextEncoding_1_1,
};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::write_config::WriteConfig;
use crate::{
    Decimal, Element, ElementWriter, Int, IonResult, IonType, RawSymbolRef, Symbol, SymbolId,
    SymbolTable, Timestamp, UInt, Value,
};

pub(crate) struct WriteContext {
    symbol_table: SymbolTable,
    num_pending_symbols: usize,
    symbol_creation_policy: SymbolCreationPolicy,
    supports_text_tokens: bool,
}

impl WriteContext {
    pub fn new(
        symbol_table: SymbolTable,
        symbol_creation_policy: SymbolCreationPolicy,
        supports_text_tokens: bool,
    ) -> Self {
        Self {
            symbol_table,
            num_pending_symbols: 0,
            symbol_creation_policy,
            supports_text_tokens,
        }
    }
}

/// An Ion writer that maintains a symbol table and creates new entries as needed.
pub struct Writer<E: Encoding, Output: Write> {
    write_context: WriteContext,
    data_writer: E::Writer<Vec<u8>>,
    directive_writer: E::Writer<Vec<u8>>,
    output: Output,
}

pub type TextWriter_1_0<Output> = Writer<TextEncoding_1_0, Output>;
pub type BinaryWriter_1_0<Output> = Writer<BinaryEncoding_1_0, Output>;
pub type TextWriter_1_1<Output> = Writer<TextEncoding_1_1, Output>;
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
        let symbol_table = SymbolTable::new(ion_version);
        let encoding_context = WriteContext::new(
            symbol_table,
            E::DEFAULT_SYMBOL_CREATION_POLICY,
            E::SUPPORTS_TEXT_TOKENS,
        );
        let mut writer = Writer {
            write_context: encoding_context,
            data_writer,
            directive_writer,
            output,
        };
        writer.flush()?;
        Ok(writer)
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
        if self.write_context.num_pending_symbols > 0 {
            self.write_lst_append()?;
            self.write_context.num_pending_symbols = 0;
        }

        self.directive_writer.flush()?;
        self.output
            .write_all(self.directive_writer.output().as_slice())?;
        self.directive_writer.output_mut().clear();

        self.data_writer.flush()?;
        self.output
            .write_all(self.data_writer.output().as_slice())?;
        self.data_writer.output_mut().clear();
        Ok(())
    }

    pub fn close(mut self) -> IonResult<Output> {
        self.flush()?;
        Ok(self.output)
    }

    /// Helper method to encode an LST append containing pending symbols.
    fn write_lst_append(&mut self) -> IonResult<()> {
        let Self {
            write_context: encoding_context,
            directive_writer,
            ..
        } = self;

        let num_pending_symbols = encoding_context.num_pending_symbols;
        let mut lst = directive_writer
            .value_writer()
            .with_annotations(system_symbol_ids::ION_SYMBOL_TABLE)?
            .struct_writer()?;

        lst.field_writer(system_symbol_ids::IMPORTS)
            .write_symbol(system_symbol_ids::ION_SYMBOL_TABLE)?;

        let mut new_symbol_list = lst.field_writer(system_symbol_ids::SYMBOLS).list_writer()?;

        let pending_symbols = encoding_context
            .symbol_table
            .symbols_tail(num_pending_symbols)
            .iter()
            .map(Symbol::text);

        new_symbol_list.write_all(pending_symbols)?;
        new_symbol_list.close()?;

        lst.close()
    }
}

impl<E: Encoding, Output: Write> MakeValueWriter for Writer<E, Output> {
    type ValueWriter<'a> = ApplicationValueWriter<'a, <E::Writer<Vec<u8>> as MakeValueWriter>::ValueWriter<'a>>
    where
        Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        let raw_value_writer = self.data_writer.make_value_writer();

        ApplicationValueWriter {
            raw_value_writer,
            encoding: &mut self.write_context,
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
    encoding: &'a mut WriteContext,
    raw_value_writer: V,
}

impl<'a, V: ValueWriter> ApplicationValueWriter<'a, V> {
    pub(crate) fn new(encoding_context: &'a mut WriteContext, raw_value_writer: V) -> Self {
        Self {
            encoding: encoding_context,
            raw_value_writer,
        }
    }

    fn symbol_table(&mut self) -> &mut SymbolTable {
        &mut self.encoding.symbol_table
    }
}

impl<'value, V: ValueWriter> AnnotatableWriter for ApplicationValueWriter<'value, V> {
    type AnnotatedValueWriter<'a> = ApplicationValueWriter<'a, V::AnnotatedValueWriter<'a>> where Self: 'a;

    fn with_annotations<'a>(
        mut self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        if self.encoding.symbol_creation_policy == SymbolCreationPolicy::WriteProvidedToken {
            // Store the tokens as they are. Text will be written as text, symbol IDs will be written
            // as symbol IDs. TODO: Lookup SIDs to see if they have text?
            return Ok(ApplicationValueWriter {
                encoding: self.encoding,
                raw_value_writer: self.raw_value_writer.with_annotations(annotations)?,
            });
        }

        // Otherwise, we're going to write everything as a symbol ID. Replace all text tokens in the
        // annotations with the corresponding symbol ID, creating a new one if necessary.
        let mut annotations = annotations.into_annotations_vec();
        for annotation in &mut annotations {
            let sid: SymbolId = match annotation.as_raw_symbol_token_ref() {
                // The token is already a symbol ID.
                RawSymbolRef::SymbolId(sid) => sid,
                // The token is text...
                RawSymbolRef::Text(text) => {
                    if let Some(sid) = self.symbol_table().sid_for(&text) {
                        //...that was already in the symbol table.
                        sid
                    } else {
                        // ...that we need to add to the symbol table.
                        self.encoding.num_pending_symbols += 1;
                        self.symbol_table().add_symbol_for_text(text)
                    }
                }
            };
            *annotation = RawSymbolRef::SymbolId(sid);
        }

        Ok(ApplicationValueWriter {
            encoding: self.encoding,
            raw_value_writer: self.raw_value_writer.with_annotations(annotations)?,
        })
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

    fn write_symbol(mut self, value: impl AsRawSymbolRef) -> IonResult<()> {
        // If it's a symbol ID, do a bounds check and then write it.
        // Otherwise, get its associated text.
        let text = match value.as_raw_symbol_token_ref() {
            RawSymbolRef::SymbolId(symbol_id) => {
                if !self.symbol_table().sid_is_valid(symbol_id) {
                    return cold_path!(IonResult::encoding_error(format!(
                        "symbol ID ${symbol_id} is out of bounds"
                    )));
                }
                return self.raw_value_writer.write_symbol(symbol_id);
            }
            RawSymbolRef::Text(text) => text,
        };

        // If the writer can write it as inline text, do so.
        if self.encoding.supports_text_tokens
            && self.encoding.symbol_creation_policy == SymbolCreationPolicy::WriteProvidedToken
        {
            return self.raw_value_writer.write_symbol(text);
        }

        // Otherwise, see if the symbol is already in the symbol table.
        let symbol_id = match self.symbol_table().sid_for(&text) {
            // If so, use the existing ID.
            Some(sid) => sid,
            // If not, add it to the symbol table and make a note to add it to the LST on the next
            // call to `flush()`. Use the new ID.
            None => {
                self.encoding.num_pending_symbols += 1;
                self.symbol_table().add_symbol_for_text(text)
            }
        };

        // Finally, write out the SID.
        self.raw_value_writer.write_symbol(symbol_id)
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        Ok(ApplicationListWriter::new(
            self.encoding,
            self.raw_value_writer.list_writer()?,
        ))
    }

    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        Ok(ApplicationSExpWriter::new(
            self.encoding,
            self.raw_value_writer.sexp_writer()?,
        ))
    }

    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        Ok(ApplicationStructWriter::new(
            self.encoding,
            self.raw_value_writer.struct_writer()?,
        ))
    }

    fn eexp_writer<'a>(self, macro_id: impl Into<MacroIdRef<'a>>) -> IonResult<Self::EExpWriter> {
        Ok(ApplicationEExpWriter::new(
            self.encoding,
            self.raw_value_writer.eexp_writer(macro_id)?,
        ))
    }
}

pub struct ApplicationStructWriter<'value, V: ValueWriter> {
    encoding: &'value mut WriteContext,
    raw_struct_writer: V::StructWriter,
}

impl<'value, V: ValueWriter> ApplicationStructWriter<'value, V> {
    pub(crate) fn new(
        encoding_context: &'value mut WriteContext,
        raw_struct_writer: V::StructWriter,
    ) -> Self {
        Self {
            encoding: encoding_context,
            raw_struct_writer,
        }
    }
}

impl<'value, V: ValueWriter> MakeValueWriter for ApplicationStructWriter<'value, V> {
    type ValueWriter<'a> = ApplicationValueWriter<'a, <V::StructWriter as MakeValueWriter>::ValueWriter<'a>>
    where
        Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        ApplicationValueWriter::new(self.encoding, self.raw_struct_writer.make_value_writer())
    }
}

impl<'value, V: ValueWriter> FieldEncoder for ApplicationStructWriter<'value, V> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        // If it's a symbol ID, do a bounds check and then write it.
        // Otherwise, get its associated text.
        let text = match name.as_raw_symbol_token_ref() {
            RawSymbolRef::SymbolId(symbol_id) => {
                if !self.encoding.symbol_table.sid_is_valid(symbol_id) {
                    return cold_path!(IonResult::encoding_error(format!(
                        "symbol ID ${symbol_id} is out of bounds"
                    )));
                }
                return self.raw_struct_writer.encode_field_name(symbol_id);
            }
            RawSymbolRef::Text(text) => text,
        };

        // If the writer can write it as inline text, do so.
        if self.encoding.supports_text_tokens
            && self.encoding.symbol_creation_policy == SymbolCreationPolicy::WriteProvidedToken
        {
            return self.raw_struct_writer.encode_field_name(text);
        }

        // Otherwise, see if the symbol is already in the symbol table.
        let symbol_id = match self.encoding.symbol_table.sid_for(&text) {
            // If so, use the existing ID.
            Some(sid) => sid,
            // If not, add it to the symbol table and make a note to add it to the LST on the next
            // call to `flush()`. Use the new ID.
            None => {
                self.encoding.num_pending_symbols += 1;
                self.encoding.symbol_table.add_symbol_for_text(text)
            }
        };

        // Finally, write out the SID.
        self.raw_struct_writer.encode_field_name(symbol_id)
    }
}

impl<'value, V: ValueWriter> StructWriter for ApplicationStructWriter<'value, V> {
    fn close(self) -> IonResult<()> {
        self.raw_struct_writer.close()
    }
}

pub struct ApplicationListWriter<'value, V: ValueWriter> {
    encoding: &'value mut WriteContext,
    raw_list_writer: V::ListWriter,
}

impl<'value, V: ValueWriter> ApplicationListWriter<'value, V> {
    pub(crate) fn new(
        encoding_context: &'value mut WriteContext,
        raw_list_writer: V::ListWriter,
    ) -> Self {
        Self {
            encoding: encoding_context,
            raw_list_writer,
        }
    }
}

impl<'value, V: ValueWriter> MakeValueWriter for ApplicationListWriter<'value, V> {
    type ValueWriter<'a> = ApplicationValueWriter<'a, <V::ListWriter as MakeValueWriter>::ValueWriter<'a>>
    where
        Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        ApplicationValueWriter::new(self.encoding, self.raw_list_writer.make_value_writer())
    }
}

impl<'value, V: ValueWriter> SequenceWriter for ApplicationListWriter<'value, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_list_writer.close()
    }
}

pub struct ApplicationSExpWriter<'value, V: ValueWriter> {
    encoding: &'value mut WriteContext,
    raw_sexp_writer: V::SExpWriter,
}

impl<'value, V: ValueWriter> ApplicationSExpWriter<'value, V> {
    pub(crate) fn new(encoding: &'value mut WriteContext, raw_sexp_writer: V::SExpWriter) -> Self {
        Self {
            encoding,
            raw_sexp_writer,
        }
    }
}

impl<'value, V: ValueWriter> MakeValueWriter for ApplicationSExpWriter<'value, V> {
    type ValueWriter<'a> =
        ApplicationValueWriter<'a, <V::SExpWriter as MakeValueWriter>::ValueWriter<'a>> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        ApplicationValueWriter::new(self.encoding, self.raw_sexp_writer.make_value_writer())
    }
}

impl<'value, V: ValueWriter> SequenceWriter for ApplicationSExpWriter<'value, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_sexp_writer.close()
    }
}

pub struct ApplicationEExpWriter<'value, V: ValueWriter> {
    encoding: &'value mut WriteContext,
    raw_eexp_writer: V::EExpWriter,
}

impl<'value, V: ValueWriter> ApplicationEExpWriter<'value, V> {
    pub(crate) fn new(encoding: &'value mut WriteContext, raw_eexp_writer: V::EExpWriter) -> Self {
        Self {
            encoding,
            raw_eexp_writer,
        }
    }
}

impl<'value, V: ValueWriter> SequenceWriter for ApplicationEExpWriter<'value, V> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.raw_eexp_writer.close()
    }
}

impl<'value, V: ValueWriter> MakeValueWriter for ApplicationEExpWriter<'value, V> {
    type ValueWriter<'a> = ApplicationValueWriter<'a, <<V as ValueWriter>::EExpWriter as MakeValueWriter>::ValueWriter<'a>> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        ApplicationValueWriter::new(self.encoding, self.raw_eexp_writer.make_value_writer())
    }
}

impl<'value, V: ValueWriter> EExpWriter for ApplicationEExpWriter<'value, V> {
    // Default methods
    fn write_flex_uint(&mut self, value: impl Into<UInt>) -> IonResult<()> {
        self.raw_eexp_writer.write_flex_uint(value)
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
