use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{illegal_operation, IonResult};
use crate::text::raw_text_writer::RawTextWriter;
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::writer::Writer;
use crate::IonType;
use crate::SymbolTable;
use delegate::delegate;
use std::io::Write;

/**
 * An application-level text Ion writer. This writer manages a symbol table and so can convert
 * symbol IDs to their corresponding text. However, unlike the BinaryWriter, it is capable of writing
 * text to the output stream without first adding it to the symbol table.
 */
pub struct TextWriter<W: Write> {
    raw_writer: RawTextWriter<W>,
    symbol_table: SymbolTable,
}

impl<W: Write> Writer for TextWriter<W> {
    fn supports_text_symbol_tokens(&self) -> bool {
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
