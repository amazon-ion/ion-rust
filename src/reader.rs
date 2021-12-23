use std::io;
use std::ops::Range;

use bigdecimal::BigDecimal;
use chrono::{DateTime, FixedOffset};
use delegate::delegate;

use crate::constants::v1_0::system_symbol_ids;
use crate::raw_reader::RawStreamItem::*;
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{decoding_error, IonResult};
use crate::symbol_table::SymbolTable;
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::{IonType, RawBinaryReader, RawReader};

/// A streaming Ion reader that resolves symbol IDs into the appropriate text.
///
/// Reader itself is format-agnostic; all format-specific logic is handled by the
/// wrapped Cursor implementation.
pub struct Reader<R: RawReader> {
    raw_reader: R,
    symbol_table: SymbolTable,
}

// FIXME: The `read_datetime` method is deprecated. However, this function body is generated by a
// macro, making it impossible to apply this #[allow(deprecated)] more narrowly. When `read_datetime`
// is removed, this annotation should be removed too.
#[allow(deprecated)]
impl<C: RawReader> Reader<C> {
    pub fn new(raw_reader: C) -> Reader<C> {
        Reader {
            raw_reader,
            symbol_table: SymbolTable::new(),
        }
    }

    /// Advances the raw reader to the next user-level Ion value, processing any system-level directives
    /// encountered along the way.
    pub fn next(&mut self) -> IonResult<Option<(IonType, bool)>> {
        loop {
            match self.raw_reader.next()? {
                Some(VersionMarker(1, 0)) => {
                    self.symbol_table.reset();
                }
                Some(VersionMarker(major, minor)) => {
                    return decoding_error(format!(
                        "Encountered a version marker for v{}.{}, but only v1.0 is supported.",
                        major, minor
                    ));
                }
                Some(Value(IonType::Struct, false)) => {
                    // If we're at the top level and the first annotation is $ion_symbol_table...
                    match (self.raw_reader.depth(), self.raw_reader.annotations()) {
                        (0, [symbol, ..])
                            if symbol.matches(
                                system_symbol_ids::ION_SYMBOL_TABLE,
                                "$ion_symbol_table",
                            ) =>
                        {
                            self.read_symbol_table()?;
                        }
                        _ => return Ok(Some((IonType::Struct, false))),
                    }
                }
                Some(Value(ion_type, is_null)) => return Ok(Some((ion_type, is_null))),
                None => return Ok(None),
            }
        }
    }

    fn read_symbol_table(&mut self) -> IonResult<()> {
        self.raw_reader.step_in()?;

        let mut is_append = false;
        let mut new_symbols = vec![];

        while let Some(Value(ion_type, is_null)) = self.raw_reader.next()? {
            let field_id = self
                .raw_reader
                .field_name()
                .expect("No field ID found inside $ion_symbol_table struct.");
            match (field_id, ion_type, is_null) {
                // The field name is either SID 6 or the text 'imports' and the
                // field value is a non-null symbol
                (symbol, IonType::Symbol, false)
                    if symbol.matches(system_symbol_ids::IMPORTS, "imports") =>
                {
                    // TODO: SST imports. This implementation only supports local symbol
                    //       table imports and appends.
                    let import_symbol = self.raw_reader.read_symbol()?.unwrap();
                    if !import_symbol.matches(3, "$ion_symbol_table") {
                        unimplemented!("Can't handle non-$ion_symbol_table imports value.");
                    }
                    is_append = true;
                }
                // The field name is either SID 7 or the text 'imports' and the
                // field value is a non-null list
                (symbol, IonType::List, false)
                    if symbol.matches(system_symbol_ids::SYMBOLS, "symbols") =>
                {
                    self.raw_reader.step_in()?;
                    while let Some(Value(IonType::String, false)) = self.raw_reader.next()? {
                        let text = self.raw_reader.read_string()?.unwrap();
                        new_symbols.push(text);
                    }
                    self.raw_reader.step_out()?;
                }
                something_else => {
                    unimplemented!("No support for {:?}", something_else);
                }
            }
        }

        if is_append {
            // We're adding new symbols to the end of the symbol table.
            for new_symbol in new_symbols.drain(..) {
                let _id = self.symbol_table.intern(new_symbol);
            }
        } else {
            // The symbol table has been set by defining new symbols without importing the current
            // symbol table.
            self.symbol_table.reset();
            for new_symbol in new_symbols.drain(..) {
                let _id = self.symbol_table.intern(new_symbol);
            }
        }

        self.raw_reader.step_out()?;
        Ok(())
    }

    pub fn field_name(&self) -> Option<&str> {
        match self.raw_reader.field_name() {
            Some(RawSymbolToken::SymbolId(sid)) => self.symbol_table.text_for(*sid),
            Some(RawSymbolToken::Text(text)) => Some(text.as_str()),
            None => None,
        }
    }

    pub fn raw_annotations(&mut self) -> impl Iterator<Item = &RawSymbolToken> {
        self.raw_reader.annotations().iter()
    }

    // TODO: The iterator should return a resolved symbol (OwnedSymbolToken?) that has
    //       the symbol's ID, text, and import source (if available).
    pub fn annotations(&self) -> impl Iterator<Item = Option<&str>> {
        self.raw_reader
            .annotations()
            .iter()
            .map(move |raw_token| match raw_token {
                RawSymbolToken::SymbolId(sid) => self.symbol_table.text_for(*sid),
                RawSymbolToken::Text(text) => Some(text.as_str()),
            })
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }

    // TODO: Offer other flavors of this method, including:
    //       * a version that returns a resolved token (OwnedSymbolToken?) that can provide both
    //         text and a SID if available
    //       * a version that returns just the symbol's text, since that's what most users will want
    pub fn read_raw_symbol(&mut self) -> IonResult<Option<RawSymbolToken>> {
        self.raw_reader.read_symbol()
    }

    pub fn raw_field_name_token(&mut self) -> Option<&RawSymbolToken> {
        self.raw_reader.field_name()
    }

    // The Reader needs to expose many of the same functions as the Cursor, but only some of those
    // need to be re-defined to allow for system value processing. Any method listed here will be
    // delegated to self.raw_reader directly.
    delegate! {
        to self.raw_reader {
            pub fn is_null(&self) -> bool;
            pub fn ion_version(&self) -> (u8, u8);
            pub fn ion_type(&self) -> Option<IonType>;
            pub fn read_null(&mut self) -> IonResult<Option<IonType>>;
            pub fn read_bool(&mut self) -> IonResult<Option<bool>>;
            pub fn read_i64(&mut self) -> IonResult<Option<i64>>;
            pub fn read_f32(&mut self) -> IonResult<Option<f32>>;
            pub fn read_f64(&mut self) -> IonResult<Option<f64>>;
            pub fn read_decimal(&mut self) -> IonResult<Option<Decimal>>;
            pub fn read_big_decimal(&mut self) -> IonResult<Option<BigDecimal>>;
            pub fn read_string(&mut self) -> IonResult<Option<String>>;
            pub fn read_blob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;
            pub fn read_clob_bytes(&mut self) -> IonResult<Option<Vec<u8>>>;
            pub fn read_datetime(&mut self) -> IonResult<Option<DateTime<FixedOffset>>>;
            pub fn read_timestamp(&mut self) -> IonResult<Option<Timestamp>>;
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
impl<T: AsRef<[u8]>> Reader<RawBinaryReader<io::Cursor<T>>> {
    delegate! {
        to self.raw_reader {
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

    use crate::binary::constants::v1_0::IVM;
    use crate::binary::raw_binary_reader::RawBinaryReader;
    use crate::raw_reader::{RawReader, RawStreamItem::*};
    use crate::result::IonResult;
    use crate::types::IonType;
    use crate::Reader;

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
    fn raw_binary_reader_for(bytes: &[u8]) -> RawBinaryReader<TestDataSource> {
        let mut raw_reader = RawBinaryReader::new(data_source_for(bytes));
        assert_eq!(raw_reader.ion_type(), None);
        assert_eq!(raw_reader.next(), Ok(Some(VersionMarker(1, 0))));
        assert_eq!(raw_reader.ion_version(), (1u8, 0u8));
        raw_reader
    }

    fn ion_reader_for(bytes: &[u8]) -> Reader<RawBinaryReader<TestDataSource>> {
        Reader::new(raw_binary_reader_for(bytes))
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

    #[test]
    fn test_read_struct() -> IonResult<()> {
        let mut reader = ion_reader_for(EXAMPLE_STREAM);

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
