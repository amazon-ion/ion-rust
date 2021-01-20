use std::boxed::Box;
use std::io;
use std::ops::Range;

use bigdecimal::BigDecimal;
use chrono::{DateTime, FixedOffset};
use delegate::delegate;

use crate::{BinaryIonCursor, Cursor, IonType};
use crate::constants::v1_0::system_symbol_ids;
use crate::cursor::StreamItem::*;
use crate::result::IonResult;
use crate::symbol_table::SymbolTable;
use crate::system_event_handler::SystemEventHandler;
use crate::types::SymbolId;

/// A streaming Ion reader that resolves symbol IDs into the appropriate text.
///
/// Reader itself is format-agnostic; all format-specific logic is handled by the
/// wrapped Cursor implementation.
pub struct Reader<C: Cursor> {
    cursor: C,
    symbol_table: SymbolTable,
    system_event_handler: Option<Box<dyn SystemEventHandler>>,
}

impl<C: Cursor> Reader<C> {
    pub fn new(cursor: C) -> Reader<C> {
        Reader {
            cursor,
            symbol_table: SymbolTable::new(),
            system_event_handler: None,
        }
    }

    /// Allows the user to specify an implementation of SymbolTableEventHandler to respond
    /// to otherwise internal events like symbol table imports and appends.
    // TODO: Boxing this type means that it is impossible to retrieve from the Reader later.
    //       This complicates checking the internal state of the handler. We should make
    //       Reader generic over the handler type and set the Boxed trait object as the default.
    pub fn set_symtab_event_handler<H>(&mut self, handler: H)
    where
        H: 'static + SystemEventHandler,
    {
        self.system_event_handler = Some(Box::new(handler));
    }

    /// Advances the cursor to the next user-level Ion value, processing any system-level directives
    /// encountered along the way.
    pub fn next(&mut self) -> IonResult<Option<(IonType, bool)>> {
        loop {
            match self.cursor.next()? {
                Some(VersionMarker(major, minor)) => {
                    self.symbol_table.reset();
                    self.invoke_on_ivm_handler((major, minor));
                    self.invoke_on_symbol_table_reset_handler();
                }
                Some(Value(IonType::Struct, false)) => {
                    if let [system_symbol_ids::ION_SYMBOL_TABLE, ..] = self.cursor.annotation_ids()
                    {
                        self.read_symbol_table()?;
                    } else {
                        return Ok(Some((IonType::Struct, false)));
                    }
                }
                Some(Value(ion_type, is_null)) => return Ok(Some((ion_type, is_null))),
                None => return Ok(None),
            }
        }
    }

    fn read_symbol_table(&mut self) -> IonResult<()> {
        self.cursor.step_in()?;

        let mut is_append = false;
        let mut new_symbols = vec![];

        while let Some(Value(ion_type, is_null)) = self.cursor.next()? {
            let field_id = self
                .cursor
                .field_id()
                .expect("No field ID found inside $ion_symbol_table struct.");
            match (field_id, ion_type, is_null) {
                // TODO: This implementation only supports local symbol table imports and appends.
                (system_symbol_ids::IMPORTS, IonType::Symbol, false) => {
                    if self.cursor.read_symbol_id()?.unwrap() != 3 {
                        unimplemented!("Can't handle non-$ion_symbol_table imports value.");
                    }
                    is_append = true;
                }
                (system_symbol_ids::SYMBOLS, IonType::List, false) => {
                    self.cursor.step_in()?;
                    while let Some(Value(IonType::String, false)) = self.cursor.next()? {
                        let text = self.cursor.read_string()?.unwrap();
                        new_symbols.push(text);
                    }
                    self.cursor.step_out()?;
                }
                something_else => {
                    unimplemented!("No support for {:?}", something_else);
                }
            }
        }

        if is_append {
            // We're adding new symbols to the end of the symbol table.
            let new_ids_start = self.symbol_table.len();
            for new_symbol in new_symbols.drain(..) {
                let _id = self.symbol_table.intern(new_symbol);
            }
            // If a symtab event handler is defined, pass it an immutable reference to the symbol
            // table and the ID of the first new symbol that was added.
            self.invoke_on_append_handler(new_ids_start);
        } else {
            // The symbol table has been set by defining new symbols without importing the current
            // symbol table.
            self.symbol_table.reset();
            for new_symbol in new_symbols.drain(..) {
                let _id = self.symbol_table.intern(new_symbol);
            }
            // If a symtab event handler is defined, pass it an immutable reference to the symbol
            // table so it can be inspected.
            self.invoke_on_symbol_table_reset_handler();
        }

        self.cursor.step_out()?;
        Ok(())
    }

    fn invoke_on_ivm_handler(&mut self, ion_version: (u8, u8)) {
        self.system_event_handler
            .as_mut()
            .map(|h| h.on_ivm(ion_version));
    }

    fn invoke_on_symbol_table_reset_handler(&mut self) {
        // Temporarily break apart 'self' to get simultaneous references to the symbol table
        // and the system event handler.
        let Reader {
            system_event_handler: symtab_event_handler,
            symbol_table,
            ..
        } = self;
        symtab_event_handler
            .as_mut()
            .map(|h| h.on_symbol_table_reset(symbol_table));
    }

    fn invoke_on_append_handler(&mut self, new_ids_start: usize) {
        // Temporarily break apart 'self' to get simultaneous references to the symbol table
        // and the system event handler.
        let Reader {
            system_event_handler: symtab_event_handler,
            symbol_table,
            ..
        } = self;
        symtab_event_handler
            .as_mut()
            .map(|h| h.on_symbol_table_append(symbol_table, new_ids_start));
    }

    pub fn field_name(&self) -> Option<&str> {
        if let Some(id) = self.cursor.field_id() {
            return self.symbol_table.text_for(id);
        }
        None
    }

    pub fn annotations(&self) -> impl Iterator<Item = &str> {
        self.cursor
            .annotation_ids()
            .iter()
            .map(move |sid| self.symbol_table.text_for(sid.clone()).unwrap())
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }

    // The Reader needs to expose many of the same functions as the Cursor, but only some of those
    // need to be re-defined to allow for system value processing. Any method listed here will be
    // delegated to self.cursor directly.
    delegate! {
        to self.cursor {
            pub fn is_null(&self) -> bool;
            pub fn ion_version(&self) -> (u8, u8);
            pub fn ion_type(&self) -> Option<IonType>;
            pub fn annotation_ids(&self) -> &[SymbolId];
            pub fn field_id(&self) -> Option<SymbolId>;
            pub fn read_null(&mut self) -> IonResult<Option<IonType>>;
            pub fn read_bool(&mut self) -> IonResult<Option<bool>>;
            pub fn read_i64(&mut self) -> IonResult<Option<i64>>;
            pub fn read_f32(&mut self) -> IonResult<Option<f32>>;
            pub fn read_f64(&mut self) -> IonResult<Option<f64>>;
            pub fn read_big_decimal(&mut self) -> IonResult<Option<BigDecimal>>;
            pub fn read_string(&mut self) -> IonResult<Option<String>>;
            pub fn read_symbol_id(&mut self) -> IonResult<Option<SymbolId>>;
            pub fn read_blob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;
            pub fn read_clob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;
            pub fn read_datetime(&mut self) -> IonResult<Option<DateTime<FixedOffset>>>;
            pub fn step_in(&mut self) -> IonResult<()>;
            pub fn step_out(&mut self) -> IonResult<()>;
            pub fn depth(&self) -> usize;

            pub fn string_ref_map<F, U>(&mut self, f: F) -> IonResult<Option<U>> where F: FnOnce(&str) -> U;
            pub fn string_bytes_map<F, U>(&mut self, f: F) -> IonResult<Option<U>> where F: FnOnce(&[u8]) -> U;

            pub fn clob_ref_map<F, U>(&mut self, f: F) -> IonResult<Option<U>> where F: FnOnce(&[u8]) -> U;
            pub fn blob_ref_map<F, U>(&mut self, f: F) -> IonResult<Option<U>> where F: FnOnce(&[u8]) -> U;
        }
    }
}

/// Functionality that is only available if the data source we're reading from is in-memory, like
/// a Vec<u8> or &[u8].
impl<T: AsRef<[u8]>> Reader<BinaryIonCursor<io::Cursor<T>>> {
    delegate! {
        to self.cursor {
            pub fn raw_bytes(&self) -> Option<&[u8]>;
            pub fn raw_field_id_bytes(&self) -> Option<&[u8]>;
            pub fn raw_header_bytes(&self) -> Option<&[u8]>;
            pub fn raw_value_bytes(&self) -> Option<&[u8]>;
            pub fn raw_annotations_bytes(&self) -> Option<&[u8]>;

            pub fn field_id_length(&self) -> Option<usize>;
            pub fn field_id_offset(&self) -> Option<usize>;
            pub fn field_id_range(&self) -> Option<Range<usize>>;

            pub fn annotations_length(&self) -> Option<usize>;
            pub fn annotations_offset(&self) -> Option<usize>;
            pub fn annotations_range(&self) -> Option<Range<usize>>;

            pub fn header_length(&self) -> usize;
            pub fn header_offset(&self) -> usize;
            pub fn header_range(&self) -> Range<usize>;

            pub fn value_length(&self) -> usize;
            pub fn value_offset(&self) -> usize;
            pub fn value_range(&self) -> Range<usize>;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io;

    use crate::{Reader, SymbolTable};
    use crate::binary::constants::v1_0::IVM;
    use crate::binary::cursor::BinaryIonCursor;
    use crate::cursor::{Cursor, StreamItem::*};
    use crate::result::IonResult;
    use crate::system_event_handler::SystemEventHandler;
    use crate::types::IonType;

    type TestDataSource = io::Cursor<Vec<u8>>;

    // Create a growable byte vector that starts with the Ion 1.0 version marker
    fn ion_data(bytes: &[u8]) -> Vec<u8> {
        let mut data = Vec::new();
        data.extend_from_slice(&IVM);
        data.extend_from_slice(bytes);
        data
    }

    // Creates an io::Cursor over the provided data
    fn data_source_for(bytes: &[u8]) -> TestDataSource {
        let data = ion_data(bytes);
        io::Cursor::new(data)
    }

    // Prepends an Ion 1.0 IVM to the provided data and then creates a BinaryIonCursor over it
    fn ion_cursor_for(bytes: &[u8]) -> BinaryIonCursor<TestDataSource> {
        let mut binary_cursor = BinaryIonCursor::new(data_source_for(bytes));
        assert_eq!(binary_cursor.ion_type(), None);
        assert_eq!(binary_cursor.next(), Ok(Some(VersionMarker(1, 0))));
        assert_eq!(binary_cursor.ion_version(), (1u8, 0u8));
        binary_cursor
    }

    fn ion_reader_for(bytes: &[u8]) -> Reader<BinaryIonCursor<TestDataSource>> {
        Reader::new(ion_cursor_for(bytes))
    }

    const EXAMPLE_STREAM: &[u8] = &[
        // $ion_symbol_table::{imports: $ion_symbol_table, symbols: ["foo", "bar", "baz"]}
        0xEE, // Var len annotations
        0x94, // Annotations + Value length: 20 bytes
        0x81, // Annotations length: 1
        0x83, // Annotation 3 ('$ion_symbol_table')
        0xDE, // Var len struct
        0x91, // Length: 17 bytes
        0x86, // Field ID 6 ('imports')
        0x71, 0x03, // Symbol 3 ('$ion_symbol_table')
        0x87, // Field ID 7 ('symbols')
        0xBC, // 12-byte List
        0x83, 0x66, 0x6f, 0x6f, // "foo"
        0x83, 0x62, 0x61, 0x72, // "bar"
        0x83, 0x62, 0x61, 0x7a, // "baz"
        // System: {$10: 1, $11: 2, $12: 3}
        // User: {foo: 1, bar: 1, baz: 1}
        0xD9, // 9-byte struct
        0x8A, // Field ID 10
        0x21, 0x01, // Integer 1
        0x8B, // Field ID 11
        0x21, 0x02, // Integer 2
        0x8C, // Field ID 12
        0x21, 0x03, // Integer 3
    ];

    struct Handler;
    impl SystemEventHandler for Handler {
        fn on_symbol_table_append<'a>(&'a mut self, symbol_table: &'a SymbolTable, starting_id: usize) {
            let new_symbols = symbol_table.symbols_tail(starting_id);
            assert_eq!(3, new_symbols.len());
            assert_eq!("foo", new_symbols[0].as_str());
            assert_eq!("bar", new_symbols[1].as_str());
            assert_eq!("baz", new_symbols[2].as_str());
        }
    }

    #[test]
    fn test_read_struct() -> IonResult<()> {
        let mut reader = ion_reader_for(EXAMPLE_STREAM);
        let handler = Handler;
        reader.set_symtab_event_handler(handler);

        assert_eq!(Some((IonType::Struct, false)), reader.next()?);
        reader.step_in()?;

        assert_eq!(reader.next()?, Some((IonType::Integer, false)));
        assert_eq!(reader.field_name(), Some("foo"));

        assert_eq!(reader.next()?, Some((IonType::Integer, false)));
        assert_eq!(reader.field_name(), Some("bar"));

        assert_eq!(reader.next()?, Some((IonType::Integer, false)));
        assert_eq!(reader.field_name(), Some("baz"));

        Ok(())
    }
}
