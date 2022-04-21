use std::io;
use std::ops::Range;

use delegate::delegate;

use crate::constants::v1_0::system_symbol_ids;
use crate::raw_reader::{RawReader, RawStreamItem};
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{decoding_error, decoding_error_raw, IonResult};
use crate::stream_reader::StreamReader;
use crate::symbol_table::{Symbol, SymbolTable};
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::{IonType, RawBinaryReader};

/// A streaming Ion reader that resolves symbol IDs into their corresponding text.
///
/// Reader itself is format-agnostic; all format-specific logic is handled by the
/// wrapped [RawReader] implementation.
pub struct Reader<R: RawReader> {
    raw_reader: R,
    symbol_table: SymbolTable,
}

/// Stream components that an application-level [Reader] implementation may encounter.
#[derive(Eq, PartialEq, Debug)]
pub enum StreamItem {
    /// An Ion value (e.g. an integer, timestamp, or struct).
    /// Includes the value's IonType and whether it is null.
    /// Stream values that represent system constructs (e.g. a struct marked with a
    /// $ion_symbol_table annotation) are still considered values at the raw level.
    Value(IonType, bool),
    /// Indicates that the reader is not positioned over anything. This can happen:
    /// * before the reader has begun processing the stream.
    /// * after the reader has stepped into a container, but before the reader has called next()
    /// * after the reader has stepped out of a container, but before the reader has called next()
    /// * after the reader has read the last item in a container
    Nothing,
}

impl<R: RawReader> Reader<R> {
    pub fn new(raw_reader: R) -> Reader<R> {
        Reader {
            raw_reader,
            symbol_table: SymbolTable::new(),
        }
    }

    pub fn read_raw_symbol(&mut self) -> IonResult<RawSymbolToken> {
        self.raw_reader.read_symbol()
    }

    pub fn raw_field_name_token(&mut self) -> IonResult<RawSymbolToken> {
        self.raw_reader.field_name()
    }

    fn read_symbol_table(&mut self) -> IonResult<()> {
        self.raw_reader.step_in()?;

        let mut is_append = false;
        let mut new_symbols = vec![];

        while let RawStreamItem::Value(ion_type, is_null) = self.raw_reader.next()? {
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
                    let import_symbol = self.raw_reader.read_symbol()?;
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
                    while let RawStreamItem::Value(IonType::String, false) =
                        self.raw_reader.next()?
                    {
                        let text = self.raw_reader.read_string()?;
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

    fn raw_annotations(&mut self) -> impl Iterator<Item = RawSymbolToken> + '_ {
        // RawReader implementations do not attempt to resolve each annotation into text.
        // Additionally, they perform all I/O related to annotations in their implementations
        // of Reader::next. As such, it's safe to call `unwrap()` on each raw annotation.
        self.raw_reader.annotations().map(|a| a.unwrap())
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }
}

impl<R: RawReader> StreamReader for Reader<R> {
    type Item = StreamItem;
    type Symbol = Symbol;

    fn current(&self) -> Self::Item {
        if let Some(ion_type) = self.ion_type() {
            return StreamItem::Value(ion_type, self.is_null());
        }
        StreamItem::Nothing
    }

    /// Advances the raw reader to the next user-level Ion value, processing any system-level directives
    /// encountered along the way.
    // v-- Clippy complains that `next` resembles `Iterator::next()`
    #[allow(clippy::should_implement_trait)]
    fn next(&mut self) -> IonResult<Self::Item> {
        use RawStreamItem::*;
        loop {
            match self.raw_reader.next()? {
                VersionMarker(1, 0) => {
                    self.symbol_table.reset();
                }
                VersionMarker(major, minor) => {
                    return decoding_error(format!(
                        "Encountered a version marker for v{}.{}, but only v1.0 is supported.",
                        major, minor
                    ));
                }
                Value(IonType::Struct, false) => {
                    // Top-level structs whose _first_ annotation is $ion_symbol_table are
                    // interpreted as local symbol tables. Other trailing annotations (if any) are
                    // ignored. If the first annotation is something other than `$ion_symbol_table`,
                    // the struct is considered user data even if one of the trailing annotations
                    // is `$ion_symbol_table`. For more information, see this section of the spec:
                    // https://amzn.github.io/ion-docs/docs/symbols.html#local-symbol-tables
                    if self.raw_reader.depth() == 0 {
                        let is_symtab = match self.raw_reader.annotations().next() {
                            Some(Err(error)) => return Err(error),
                            Some(Ok(symbol))
                                if symbol.matches(
                                    system_symbol_ids::ION_SYMBOL_TABLE,
                                    "$ion_symbol_table",
                                ) =>
                            {
                                true
                            }
                            _ => false,
                        };
                        // This logic cannot be merged into the `match` statement above because
                        // `self.read_symbol_table()` requires a mutable borrow which is not
                        // possible while iterating over the reader's annotations.
                        if is_symtab {
                            self.read_symbol_table()?;
                            continue;
                        }
                    }
                    return Ok(StreamItem::Value(IonType::Struct, false));
                }
                Value(ion_type, is_null) => return Ok(StreamItem::Value(ion_type, is_null)),
                Nothing => return Ok(StreamItem::Nothing),
            }
        }
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match self.raw_reader.field_name()? {
            RawSymbolToken::SymbolId(sid) => {
                self.symbol_table.symbol_for(sid).cloned().ok_or_else(|| {
                    decoding_error_raw(format!("encountered field ID with unknown text: ${}", sid))
                })
            }
            RawSymbolToken::Text(text) => Ok(Symbol::owned(text)),
        }
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        let iterator = self
            .raw_reader
            .annotations()
            .map(move |raw_token| match raw_token? {
                RawSymbolToken::SymbolId(sid) => {
                    self.symbol_table.symbol_for(sid).cloned().ok_or_else(|| {
                        decoding_error_raw(format!(
                            "found annotation ID with unknown text: ${}",
                            sid
                        ))
                    })
                }
                RawSymbolToken::Text(text) => Ok(Symbol::owned(text)),
            });
        Box::new(iterator)
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        match self.raw_reader.read_symbol()? {
            RawSymbolToken::SymbolId(symbol_id) => {
                if let Some(symbol) = self.symbol_table.symbol_for(symbol_id) {
                    Ok(symbol.clone())
                } else {
                    return decoding_error(format!(
                        "Found symbol ID ${}, which is not defined.",
                        symbol_id
                    ));
                }
            }
            RawSymbolToken::Text(text) => Ok(Symbol::owned(text)),
        }
    }

    // The Reader needs to expose many of the same functions as the Cursor, but only some of those
    // need to be re-defined to allow for system value processing. Any method listed here will be
    // delegated to self.raw_reader directly.
    delegate! {
        to self.raw_reader {
            fn is_null(&self) -> bool;
            fn ion_version(&self) -> (u8, u8);
            fn ion_type(&self) -> Option<IonType>;
            fn read_null(&mut self) -> IonResult<IonType>;
            fn read_bool(&mut self) -> IonResult<bool>;
            fn read_i64(&mut self) -> IonResult<i64>;
            fn read_f32(&mut self) -> IonResult<f32>;
            fn read_f64(&mut self) -> IonResult<f64>;
            fn read_decimal(&mut self) -> IonResult<Decimal>;
            fn read_string(&mut self) -> IonResult<String>;
            fn map_string<F, U>(&mut self, f: F) -> IonResult<U> where F: FnOnce(&str) -> U;
            fn map_string_bytes<F, U>(&mut self, f: F) -> IonResult<U> where F: FnOnce(&[u8]) -> U;
            fn read_blob(&mut self) -> IonResult<Vec<u8>>;
            fn map_blob<F, U>(&mut self, f: F) -> IonResult<U> where F: FnOnce(&[u8]) -> U;
            fn read_clob(&mut self) -> IonResult<Vec<u8>>;
            fn map_clob<F, U>(&mut self, f: F) -> IonResult<U> where F: FnOnce(&[u8]) -> U;
            fn read_timestamp(&mut self) -> IonResult<Timestamp>;
            fn step_in(&mut self) -> IonResult<()>;
            fn step_out(&mut self) -> IonResult<()>;
            fn parent_type(&self) -> Option<IonType>;
            fn depth(&self) -> usize;
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

    use super::*;
    use crate::binary::constants::v1_0::IVM;
    use crate::binary::raw_binary_reader::RawBinaryReader;

    use crate::result::IonResult;
    use crate::types::IonType;
    use crate::Reader;
    use crate::StreamItem::Value;

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
        use RawStreamItem::*;
        let mut raw_reader = RawBinaryReader::new(data_source_for(bytes));
        assert_eq!(raw_reader.ion_type(), None);
        assert_eq!(raw_reader.next(), Ok(VersionMarker(1, 0)));
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

        assert_eq!(Value(IonType::Struct, false), reader.next()?);
        reader.step_in()?;

        assert_eq!(reader.next()?, Value(IonType::Integer, false));
        assert_eq!(reader.field_name()?, "foo");

        assert_eq!(reader.next()?, Value(IonType::Integer, false));
        assert_eq!(reader.field_name()?, "bar");

        assert_eq!(reader.next()?, Value(IonType::Integer, false));
        assert_eq!(reader.field_name()?, "baz");

        Ok(())
    }
}
