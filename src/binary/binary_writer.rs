use crate::binary::raw_binary_writer::RawBinaryWriter;
use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{illegal_operation, IonResult};
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::writer::Writer;
use crate::IonType;
use crate::SymbolTable;
use delegate::delegate;
use std::io::Write;

/**
 * An application-level binary Ion writer. This writer manages a symbol table and so can convert
 * symbol IDs to their corresponding text.
 */
pub struct BinaryWriter<W: Write> {
    raw_writer: RawBinaryWriter<W>,
    symbol_table: SymbolTable,
}

impl<W: Write> BinaryWriter<W> {
    pub fn new(raw_writer: RawBinaryWriter<W>) -> Self {
        BinaryWriter {
            raw_writer,
            symbol_table: SymbolTable::new(),
        }
    }

    fn get_or_create_symbol_id(&mut self, text: &str) -> SymbolId {
        if let Some(symbol_id) = self.symbol_table.sid_for(&text) {
            // If the provided text is in the symbol table, use the associated symbol ID...
            symbol_id
        } else {
            // ...otherwise, add it to the symbol table and return the new symbol ID.
            self.symbol_table.intern(text.to_owned())
        }
    }
}

impl<W: Write> Writer for BinaryWriter<W> {
    fn supports_text_symbol_tokens(&self) -> bool {
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
                        panic!(
                            "Cannot set symbol ID ${} as annotation. It is undefined.",
                            symbol_id
                        );
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
                    return illegal_operation(format!(
                        "Cannot set symbol ID ${} as annotation. It is undefined.",
                        symbol_id
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
                    return panic!(
                        "Cannot set symbol ID ${} as field name. It is undefined.",
                        symbol_id
                    );
                }
            }
            RawSymbolTokenRef::Text(text) => self.get_or_create_symbol_id(text),
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
