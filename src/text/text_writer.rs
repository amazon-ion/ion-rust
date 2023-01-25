use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{illegal_operation, IonResult};
use crate::text::raw_text_writer::RawTextWriter;
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::value::writer::TextKind;
use crate::writer::IonWriter;
use crate::{Integer, IonType, RawTextWriterBuilder, SymbolTable};
use delegate::delegate;
use std::io::Write;

pub struct TextWriterBuilder {
    text_kind: TextKind,
}

impl TextWriterBuilder {
    /// Constructs a text Ion writer with modest (but not strictly minimal) spacing.
    ///
    /// For example:
    /// ```ignore
    /// {foo: 1, bar: 2, baz: 3} [1, 2, 3] true "hello"
    /// ```
    pub fn new() -> TextWriterBuilder {
        TextWriterBuilder {
            text_kind: TextKind::Compact,
        }
    }

    /// Constructs a newline-delimited text Ion writer that adds UNIX and human-friendly newlines
    /// between top-level values.
    ///
    /// For example:
    /// ```ignore
    /// {foo: 1, bar: 2, baz: 3}
    /// [1, 2, 3]
    /// true
    /// "hello"
    /// ```
    pub fn lines() -> TextWriterBuilder {
        TextWriterBuilder {
            text_kind: TextKind::Lines,
        }
    }

    /// Constructs a 'pretty' text Ion writer that adds human-friendly spacing between values.
    ///
    /// For example:
    /// ```ignore
    /// {
    ///     foo: 1,
    ///     bar: 2,
    ///     baz: 3
    /// }
    /// [
    ///     1,
    ///     2,
    ///     3
    /// ]
    /// true
    /// "hello"
    /// ```
    pub fn pretty() -> TextWriterBuilder {
        TextWriterBuilder {
            text_kind: TextKind::Pretty,
        }
    }

    /// Constructs a new instance of TextWriter that writes values to the provided io::Write
    /// implementation.
    pub fn build<W: Write>(self, sink: W) -> IonResult<TextWriter<W>> {
        let builder = match self.text_kind {
            TextKind::Compact => RawTextWriterBuilder::new(),
            TextKind::Pretty => RawTextWriterBuilder::pretty(),
            TextKind::Lines => RawTextWriterBuilder::lines(),
        };
        let raw_writer = builder.build(sink)?;
        let text_writer = TextWriter {
            raw_writer,
            symbol_table: SymbolTable::new(),
        };
        Ok(text_writer)
    }
}

impl Default for TextWriterBuilder {
    fn default() -> Self {
        TextWriterBuilder::new()
    }
}

/**
 * An application-level text Ion writer. This writer manages a symbol table and so can convert
 * symbol IDs to their corresponding text. However, unlike the BinaryWriter, it is capable of writing
 * text to the output stream without first adding it to the symbol table.
 */
pub struct TextWriter<W: Write> {
    raw_writer: RawTextWriter<W>,
    symbol_table: SymbolTable,
}

impl<W: Write> IonWriter for TextWriter<W> {
    fn supports_text_symbol_tokens(&self) -> bool {
        // The TextWriter can always write text field names, annotations, and symbols.
        true
    }

    fn set_annotations<I, A>(&mut self, annotations: I)
    where
        A: AsRawSymbolTokenRef,
        I: IntoIterator<Item = A>,
    {
        for annotation in annotations {
            let text = match annotation.as_raw_symbol_token_ref() {
                RawSymbolTokenRef::SymbolId(symbol_id) => {
                    // Get the text associated with this symbol ID
                    if let Some(text) = self.symbol_table.text_for(symbol_id) {
                        text
                    } else {
                        // TODO: TextWriter is intended to be an application-level interface, so
                        //       dealing with undefined symbols is out of scope for it. Users
                        //       wishing to write a symbol ID literal could use a RawTextWriter
                        //       instead. However, we could consider allowing this via a config
                        //       option.
                        panic!(
                            "Cannot use symbol ID ${} as an annotation; it is undefined.",
                            symbol_id
                        );
                    }
                }
                RawSymbolTokenRef::Text(text) => text,
            };
            self.raw_writer.add_annotation(text);
        }
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()> {
        let text = match value.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(symbol_id) => {
                // Get the text associated with this symbol ID
                if let Some(text) = self.symbol_table.text_for(symbol_id) {
                    text
                } else {
                    return illegal_operation(format!(
                        "Cannot write symbol ID ${} as a symbol value; it is undefined.",
                        symbol_id
                    ));
                }
            }
            RawSymbolTokenRef::Text(text) => text,
        };
        self.raw_writer.write_symbol(text)
    }

    fn set_field_name<A: AsRawSymbolTokenRef>(&mut self, name: A) {
        let text = match name.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(symbol_id) => {
                // Get the text associated with this symbol ID
                if let Some(text) = self.symbol_table.text_for(symbol_id) {
                    text
                } else {
                    panic!(
                        "Cannot use symbol ID ${} as a field name; it is undefined.",
                        symbol_id
                    );
                }
            }
            RawSymbolTokenRef::Text(text) => text,
        };
        self.raw_writer.set_field_name(text);
    }

    delegate! {
        to self.raw_writer {
            fn ion_version(&self) -> (u8, u8);
            fn write_ion_version_marker(&mut self, major: u8, minor: u8) -> IonResult<()>;
            fn write_null(&mut self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(&mut self, value: bool) -> IonResult<()>;
            fn write_i64(&mut self, value: i64) -> IonResult<()>;
            fn write_integer(&mut self, value: &Integer) -> IonResult<()>;
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
            fn flush(&mut self) -> IonResult<()>;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::ReaderBuilder;
    use crate::IonReader;
    use crate::StreamItem::Value;

    #[test]
    fn resolve_symbol_ids() -> IonResult<()> {
        // Unlike the binary writer, the text writer won't add strings to the symbol table.
        // However, if you ask it to write a symbol ID (e.g. $10) for which its initial symbol
        // table has text, it will convert it to text before writing it.
        let mut buffer = Vec::new();
        let mut text_writer = TextWriterBuilder::new().build(&mut buffer)?;
        // The following symbol IDs are in the system symbol table.
        // https://amazon-ion.github.io/ion-docs/docs/symbols.html#system-symbols
        text_writer.step_in(IonType::Struct)?;
        text_writer.set_field_name(4);
        text_writer.set_annotations(&[1]);
        text_writer.write_symbol(5)?;
        text_writer.step_out()?;
        text_writer.flush()?;
        drop(text_writer);

        let mut reader = ReaderBuilder::new().build(buffer.as_slice())?;
        assert_eq!(Value(IonType::Struct), reader.next()?);
        reader.step_in()?;
        assert_eq!(Value(IonType::Symbol), reader.next()?);
        assert_eq!(1, reader.number_of_annotations());
        // The reader returns text values for the symbol IDs it encountered in the stream
        assert_eq!("$ion", reader.annotations().next().unwrap()?);
        assert_eq!("name", reader.field_name()?);
        assert_eq!("version", reader.read_symbol()?);

        Ok(())
    }
}
