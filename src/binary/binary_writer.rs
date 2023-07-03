use crate::binary::raw_binary_writer::{RawBinaryWriter, RawBinaryWriterBuilder};
use crate::constants::v1_0::system_symbol_ids;
use crate::ion_writer::IonWriter;
use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{IonFailure, IonResult};
use crate::types::{Decimal, Int, IonType, SymbolId, Timestamp};
use crate::SymbolTable;
use delegate::delegate;
use std::io::Write;

pub struct BinaryWriterBuilder {
    // Nothing yet
}

impl BinaryWriterBuilder {
    pub fn new() -> Self {
        BinaryWriterBuilder {}
    }

    pub fn build<W: Write>(self, sink: W) -> IonResult<BinaryWriter<W>> {
        let mut raw_writer = RawBinaryWriterBuilder::new().build(sink)?;
        let symbol_table_writer = RawBinaryWriterBuilder::new().build(Vec::new())?;
        // TODO: Track whether we've written an IVM and emit it at flush time instead
        raw_writer.write_ion_version_marker(1, 0)?;
        let binary_writer = BinaryWriter {
            raw_writer,
            symbol_table: Default::default(),
            num_pending_symbols: 0,
            symbol_table_writer,
        };
        Ok(binary_writer)
    }
}

impl Default for BinaryWriterBuilder {
    fn default() -> Self {
        BinaryWriterBuilder::new()
    }
}

/**
 * An application-level binary Ion writer. This writer manages a symbol table and so can convert
 * symbol IDs to their corresponding text.
 */
pub struct BinaryWriter<W: Write> {
    raw_writer: RawBinaryWriter<W>,
    symbol_table: SymbolTable,
    // The number of symbols that have been added to the in-memory symbol table but
    // whose definitions have not yet been written to the output stream.
    num_pending_symbols: usize,
    // The BinaryWriter uses the `symbol_table_writer` to encode local symbol tables to a buffer
    // and then flush them to output before flushing the contents of the `raw_writer`. This guarantees
    // that any symbols referenced in the `raw_writer`'s contents will be defined in the Ion stream
    // before the reference appears.
    symbol_table_writer: RawBinaryWriter<Vec<u8>>,
}

impl<W: Write> BinaryWriter<W> {
    fn get_or_create_symbol_id(&mut self, text: &str) -> SymbolId {
        if let Some(symbol_id) = self.symbol_table.sid_for(&text) {
            // If the provided text is in the symbol table, use the associated symbol ID...
            symbol_id
        } else {
            // ...otherwise, add it to the symbol table and return the new symbol ID.
            self.num_pending_symbols += 1;
            self.symbol_table.intern(text)
        }
    }

    fn write_symbol_table_for_pending_symbols(&mut self) -> IonResult<()> {
        let pending_symbols_starting_index = self.symbol_table.len() - self.num_pending_symbols;
        let pending_symbols = self
            .symbol_table
            .symbols_tail(pending_symbols_starting_index);

        self.symbol_table_writer
            .add_annotation(system_symbol_ids::ION_SYMBOL_TABLE);
        self.symbol_table_writer.step_in(IonType::Struct)?;

        self.symbol_table_writer
            .set_field_name(system_symbol_ids::IMPORTS);
        self.symbol_table_writer
            .write_symbol(system_symbol_ids::ION_SYMBOL_TABLE)?;

        self.symbol_table_writer
            .set_field_name(system_symbol_ids::SYMBOLS);
        self.symbol_table_writer.step_in(IonType::List)?;
        for symbol in pending_symbols {
            match symbol.text() {
                Some(text) => self.symbol_table_writer.write_string(text),
                None => self.symbol_table_writer.write_null(IonType::Null),
            }?;
        }
        self.symbol_table_writer.step_out()?; // End symbols list

        self.symbol_table_writer.step_out()?; // End $ion_symbol_table::{...}
        self.symbol_table_writer.flush()?;

        // Write the symbol_table_writer's encoded bytes to the raw_writer's output
        let bytes = &self.symbol_table_writer.output()[..];
        self.raw_writer.output_mut().write_all(bytes)?;
        self.symbol_table_writer.output_mut().clear();

        Ok(())
    }
}

impl<W: Write> IonWriter for BinaryWriter<W> {
    type Output = W;

    fn supports_text_symbol_tokens(&self) -> bool {
        // The BinaryWriter can always write text field names, annotations, and symbols
        // after first adding the provided text to the symbol table.
        true
    }

    fn set_annotations<I, A>(&mut self, annotations: I)
    where
        A: AsRawSymbolTokenRef,
        I: IntoIterator<Item = A>,
    {
        for annotation in annotations {
            let symbol_id = match annotation.as_raw_symbol_token_ref() {
                RawSymbolTokenRef::SymbolId(symbol_id) => {
                    if self.symbol_table.sid_is_valid(symbol_id) {
                        symbol_id
                    } else {
                        panic!("Cannot set symbol ID ${symbol_id} as annotation. It is undefined.");
                    }
                }
                RawSymbolTokenRef::Text(text) => self.get_or_create_symbol_id(text),
            };
            self.raw_writer.add_annotation(symbol_id);
        }
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()> {
        let symbol_id = match value.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(symbol_id) => {
                if self.symbol_table.sid_is_valid(symbol_id) {
                    symbol_id
                } else {
                    return IonResult::illegal_operation(format!(
                        "Cannot write symbol ID ${symbol_id} as a symbol value. It is undefined."
                    ));
                }
            }
            RawSymbolTokenRef::Text(text) => self.get_or_create_symbol_id(text),
        };
        self.raw_writer.write_symbol(symbol_id)
    }

    fn set_field_name<A: AsRawSymbolTokenRef>(&mut self, name: A) {
        let text = match name.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(symbol_id) => {
                if self.symbol_table.sid_is_valid(symbol_id) {
                    symbol_id
                } else {
                    panic!("Cannot set symbol ID ${symbol_id} as field name. It is undefined.");
                }
            }
            RawSymbolTokenRef::Text(text) => self.get_or_create_symbol_id(text),
        };
        self.raw_writer.set_field_name(text);
    }

    fn flush(&mut self) -> IonResult<()> {
        // Check to see if there are any pending symbols.
        if self.num_pending_symbols > 0 {
            self.write_symbol_table_for_pending_symbols()?;
            self.num_pending_symbols = 0;
        }
        self.raw_writer.flush()
    }

    delegate! {
        to self.raw_writer {
            fn ion_version(&self) -> (u8, u8);
            fn write_ion_version_marker(&mut self, major: u8, minor: u8) -> IonResult<()>;
            fn write_null(&mut self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(&mut self, value: bool) -> IonResult<()>;
            fn write_i64(&mut self, value: i64) -> IonResult<()>;
            fn write_int(&mut self, value: &Int) -> IonResult<()>;
            fn write_f32(&mut self, value: f32) -> IonResult<()>;
            fn write_f64(&mut self, value: f64) -> IonResult<()>;
            fn write_decimal(&mut self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()>;
            fn write_string<A: AsRef<str>>(&mut self, value: A) -> IonResult<()>;
            fn write_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()>;
            fn write_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()>;
            fn step_in(&mut self, container_type: IonType) -> IonResult<()>;
            fn parent_type(&self) -> Option<IonType>;
            fn depth(&self) -> usize;
            fn step_out(&mut self) -> IonResult<()>;
            fn output(&self) -> &Self::Output;
            fn output_mut(&mut self) -> &mut Self::Output;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ion_reader::IonReader;
    use crate::reader::ReaderBuilder;

    use crate::reader::StreamItem::Value;

    #[test]
    fn intern_field_names() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut binary_writer = BinaryWriterBuilder::new().build(&mut buffer)?;
        binary_writer.step_in(IonType::Struct)?;
        binary_writer.set_field_name("foo");
        binary_writer.write_symbol("bar")?;
        binary_writer.step_out()?;
        binary_writer.flush()?;

        let mut reader = ReaderBuilder::new().build(buffer)?;
        assert_eq!(Value(IonType::Struct), reader.next()?);
        reader.step_in()?;
        assert_eq!(Value(IonType::Symbol), reader.next()?);
        assert_eq!("foo", reader.field_name()?);
        assert_eq!("bar", reader.read_symbol()?.text_or_error()?);

        Ok(())
    }

    #[test]
    fn intern_annotations() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut binary_writer = BinaryWriterBuilder::new().build(&mut buffer)?;
        binary_writer.set_annotations(["foo", "bar"]);
        binary_writer.write_i64(5)?;
        binary_writer.flush()?;

        let mut reader = ReaderBuilder::new().build(buffer)?;
        assert_eq!(Value(IonType::Int), reader.next()?);
        let mut annotations = reader.annotations();
        assert_eq!("foo", annotations.next().unwrap()?);
        assert_eq!("bar", annotations.next().unwrap()?);

        Ok(())
    }

    #[test]
    fn intern_symbols() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut binary_writer = BinaryWriterBuilder::new().build(&mut buffer)?;
        binary_writer.write_symbol("foo")?;
        binary_writer.write_symbol("bar")?;
        binary_writer.write_symbol("baz")?;
        binary_writer.flush()?;

        let mut reader = ReaderBuilder::new().build(buffer)?;
        assert_eq!(Value(IonType::Symbol), reader.next()?);
        assert_eq!("foo", reader.read_symbol()?);
        assert_eq!(Value(IonType::Symbol), reader.next()?);
        assert_eq!("bar", reader.read_symbol()?);
        assert_eq!(Value(IonType::Symbol), reader.next()?);
        assert_eq!("baz", reader.read_symbol()?);

        Ok(())
    }
}
