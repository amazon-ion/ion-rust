use std::io;
use std::io::Read;
use std::ops::Range;

use delegate::delegate;

use crate::binary::constants::v1_0::IVM;
use crate::constants::v1_0::system_symbol_ids;
use crate::data_source::ToIonDataSource;
use crate::element::{Blob, Clob};
use crate::raw_reader::{RawReader, RawStreamItem};
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{decoding_error, decoding_error_raw, IonResult};
use crate::stream_reader::IonReader;
use crate::symbol_table::SymbolTable;
use crate::types::{Decimal, Int, Symbol, Timestamp};
use crate::{BlockingRawBinaryReader, BlockingRawTextReader, IonType};
use std::fmt::{Display, Formatter};

use crate::types::Str;
/// Configures and constructs new instances of [Reader].
pub struct ReaderBuilder {}

impl ReaderBuilder {
    /// Constructs a [ReaderBuilder] pre-populated with common default settings.
    pub fn new() -> ReaderBuilder {
        ReaderBuilder {
            // Eventually, this will contain settings like a `Catalog` implementation.
        }
    }

    /// Applies the specified settings to a new instance of `Reader`. This process involves
    /// reading some data from the beginning of `input` to detect whether its content is
    /// text or binary Ion. If this read operation fails, `build` will return an `Err`
    /// describing the problem it encountered.
    pub fn build<'a, I: 'a + ToIonDataSource>(self, input: I) -> IonResult<Reader<'a>> {
        // Convert the provided input into an implementation of `BufRead`
        let mut input = input.to_ion_data_source();
        // Stack-allocated buffer to hold the first four bytes from input
        let mut header: [u8; 4] = [0u8; 4];

        // Read up to four bytes of input. This has to be done somewhat manually. Convenience
        // functions like `read_exact` will return an error if the input doesn't contain the
        // correct number of bytes, and there are legal Ion streams that have fewer than four
        // bytes in them. (For example, the stream `1 `.)
        let mut total_bytes_read = 0usize;
        while total_bytes_read < IVM.len() {
            let bytes_read = input.read(&mut header[total_bytes_read..])?;
            // If `bytes_read` is zero, we reached the end of the file before we could get
            // all four bytes. That means this isn't a (valid) binary stream. We'll assume
            // it's text.
            if bytes_read == 0 {
                // `header` is a stack-allocated buffer that won't outlive this function call.
                // If it were full, we could move the whole `[u8; 4]` into the reader. However,
                // only some of it is populated and we can't use a slice of it because the array
                // is short-lived. Instead we'll make a statically owned copy of the bytes that
                // we can move into the reader.
                let owned_header = Vec::from(&header[..total_bytes_read]);
                // The file was too short to be binary Ion. Construct a text Reader.
                return Self::make_text_reader(owned_header);
            }
            total_bytes_read += bytes_read;
        }

        // If we've reached this point, we successfully read 4 bytes from the file into `header`.
        // Match against `header` to see if it contains the Ion 1.0 version marker.
        match header {
            [0xe0, 0x01, 0x00, 0xea] => {
                // Binary Ion v1.0
                let full_input = io::Cursor::new(header).chain(input);
                Ok(Self::make_binary_reader(full_input)?)
            }
            [0xe0, major, minor, 0xea] => {
                // Binary Ion v{major}.{minor}
                decoding_error(format!(
                    "cannot read Ion v{major}.{minor}; only v1.0 is supported"
                ))
            }
            _ => {
                // It's not binary, assume it's text
                let full_input = io::Cursor::new(header).chain(input);
                Ok(Self::make_text_reader(full_input)?)
            }
        }
    }

    fn make_text_reader<'a, I: 'a + ToIonDataSource>(data: I) -> IonResult<Reader<'a>> {
        let raw_reader = Box::new(BlockingRawTextReader::new(data)?);
        Ok(Reader {
            raw_reader,
            symbol_table: SymbolTable::new(),
        })
    }

    fn make_binary_reader<'a, I: 'a + ToIonDataSource>(data: I) -> IonResult<Reader<'a>> {
        let raw_reader = Box::new(BlockingRawBinaryReader::new(data)?);
        Ok(Reader {
            raw_reader,
            symbol_table: SymbolTable::new(),
        })
    }
}

impl Default for ReaderBuilder {
    fn default() -> Self {
        ReaderBuilder::new()
    }
}

/// A Reader that uses dynamic dispatch to abstract over the format (text or binary) being
/// read by an underlying [RawReader].
pub type Reader<'a> = UserReader<Box<dyn RawReader + 'a>>;

/// A streaming Ion reader that resolves symbol IDs into their corresponding text.
///
/// Reader itself is format-agnostic; all format-specific logic is handled by the
/// wrapped [RawReader] implementation.
pub struct UserReader<R: RawReader> {
    raw_reader: R,
    symbol_table: SymbolTable,
}

impl<R: RawReader> UserReader<R> {
    pub fn new(raw_reader: R) -> UserReader<R> {
        UserReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
        }
    }
}

// This module exists to allow our integration tests to directly construct a `UserReader`
// with not-yet-supported settings. We want users to use `ReaderBuilder` instead; eventually,
// `ReaderBuilder` will also work for the integration tests and we can remove this.
// See: https://github.com/amazon-ion/ion-rust/issues/484
#[doc(hidden)]
pub mod integration_testing {
    use crate::{RawReader, Reader, UserReader};

    pub fn new_reader<'a, R: 'a + RawReader>(raw_reader: R) -> Reader<'a> {
        UserReader::new(Box::new(raw_reader))
    }
}

/// Stream components that an application-level [Reader] implementation may encounter.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum StreamItem {
    /// A non-null Ion value and its corresponding Ion data type.
    Value(IonType),
    /// A null Ion value and its corresponding Ion data type.
    Null(IonType),
    /// Indicates that the reader is not positioned over anything. This can happen:
    /// * before the reader has begun processing the stream.
    /// * after the reader has stepped into a container, but before the reader has called next()
    /// * after the reader has stepped out of a container, but before the reader has called next()
    /// * after the reader has read the last item in a container
    Nothing,
}

impl StreamItem {
    /// If `is_null` is `true`, returns `StreamItem::Value(ion_type)`. Otherwise,
    /// returns `StreamItem::Null(ion_type)`.
    pub fn nullable_value(ion_type: IonType, is_null: bool) -> StreamItem {
        if is_null {
            StreamItem::Null(ion_type)
        } else {
            StreamItem::Value(ion_type)
        }
    }
}

impl Display for StreamItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use StreamItem::*;
        match self {
            Value(ion_type) => write!(f, "{ion_type}"),
            Null(ion_type) => write!(f, "null.{ion_type}"),
            Nothing => Ok(()),
        }
    }
}

impl<R: RawReader> UserReader<R> {
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

        // It's illegal for a symbol table to have multiple `symbols` or `imports` fields.
        // Keep track of whether we've already encountered them.
        let mut has_found_symbols_field = false;
        let mut has_found_imports_field = false;

        loop {
            let ion_type = match self.raw_reader.next()? {
                RawStreamItem::Value(ion_type) => ion_type,
                RawStreamItem::Null(_) => continue,
                RawStreamItem::Nothing => break,
                RawStreamItem::VersionMarker(major, minor) => {
                    return decoding_error(format!(
                        "encountered Ion version marker for v{major}.{minor} in symbol table"
                    ))
                }
            };

            let field_id = self
                .raw_reader
                .field_name()
                .expect("No field ID found inside $ion_symbol_table struct.");
            match (field_id, ion_type) {
                // The field name is either SID 6 or the text 'imports' and the
                // field value is a non-null List
                (symbol, IonType::List)
                    if symbol.matches(system_symbol_ids::IMPORTS, "imports") =>
                {
                    // TODO: SST imports. This implementation only supports local symbol
                    //       table imports and appends.
                    return decoding_error("importing shared symbol tables is not yet supported");
                }
                // The field name is either SID 6 or the text 'imports' and the
                // field value is a non-null symbol
                (symbol, IonType::Symbol)
                    if symbol.matches(system_symbol_ids::IMPORTS, "imports") =>
                {
                    if has_found_imports_field {
                        return decoding_error("symbol table had multiple 'imports' fields");
                    }
                    has_found_imports_field = true;
                    let import_symbol = self.raw_reader.read_symbol()?;
                    if !import_symbol.matches(3, "$ion_symbol_table") {
                        // Field name `imports` with a symbol other than $ion_symbol_table is ignored
                        continue;
                    }
                    is_append = true;
                }
                // The field name is either SID 7 or the text 'imports' and the
                // field value is a non-null list
                (symbol, IonType::List)
                    if symbol.matches(system_symbol_ids::SYMBOLS, "symbols") =>
                {
                    if has_found_symbols_field {
                        return decoding_error("symbol table had multiple 'symbols' fields");
                    }
                    has_found_symbols_field = true;
                    self.raw_reader.step_in()?;
                    loop {
                        use RawStreamItem::*;
                        match self.raw_reader.next()? {
                            Value(IonType::String) => {
                                new_symbols.push(Some(self.raw_reader.read_string()?));
                            }
                            Value(_) | Null(_) => {
                                // If we encounter a non-string or null, add a placeholder
                                new_symbols.push(None);
                            }
                            VersionMarker(_, _) => {
                                return decoding_error("Found IVM in symbol table.")
                            }
                            Nothing => break,
                        }
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
            for maybe_text in new_symbols.drain(..) {
                let _sid = self.symbol_table.intern_or_add_placeholder(maybe_text);
            }
        } else {
            // The symbol table has been set by defining new symbols without importing the current
            // symbol table.
            self.symbol_table.reset();
            for maybe_text in new_symbols.drain(..) {
                let _sid = self.symbol_table.intern_or_add_placeholder(maybe_text);
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

impl<R: RawReader> IonReader for UserReader<R> {
    type Item = StreamItem;
    type Symbol = Symbol;

    fn current(&self) -> Self::Item {
        if let Some(ion_type) = self.ion_type() {
            return if self.is_null() {
                StreamItem::Null(ion_type)
            } else {
                StreamItem::Value(ion_type)
            };
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
                        "Encountered a version marker for v{major}.{minor}, but only v1.0 is supported."
                    ));
                }
                Value(IonType::Struct) => {
                    // Top-level structs whose _first_ annotation is $ion_symbol_table are
                    // interpreted as local symbol tables. Other trailing annotations (if any) are
                    // ignored. If the first annotation is something other than `$ion_symbol_table`,
                    // the struct is considered user data even if one of the trailing annotations
                    // is `$ion_symbol_table`. For more information, see this section of the spec:
                    // https://amazon-ion.github.io/ion-docs/docs/symbols.html#local-symbol-tables
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
                    return Ok(StreamItem::Value(IonType::Struct));
                }
                Value(ion_type) => return Ok(StreamItem::Value(ion_type)),
                Null(ion_type) => return Ok(StreamItem::Null(ion_type)),
                Nothing => return Ok(StreamItem::Nothing),
            }
        }
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match self.raw_reader.field_name()? {
            RawSymbolToken::SymbolId(sid) => {
                self.symbol_table.symbol_for(sid).cloned().ok_or_else(|| {
                    decoding_error_raw(format!("encountered field ID with unknown text: ${sid}"))
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
                        decoding_error_raw(format!("found annotation ID with unknown text: ${sid}"))
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
                    decoding_error(format!(
                        "Found symbol ID ${symbol_id}, which is not defined."
                    ))
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
            fn read_int(&mut self) -> IonResult<Int>;
            fn read_i64(&mut self) -> IonResult<i64>;
            fn read_f32(&mut self) -> IonResult<f32>;
            fn read_f64(&mut self) -> IonResult<f64>;
            fn read_decimal(&mut self) -> IonResult<Decimal>;
            fn read_string(&mut self) -> IonResult<Str>;
            fn read_str(&mut self) -> IonResult<&str>;
            fn read_blob(&mut self) -> IonResult<Blob>;
            fn read_clob(&mut self) -> IonResult<Clob>;
            fn read_timestamp(&mut self) -> IonResult<Timestamp>;
            fn step_in(&mut self) -> IonResult<()>;
            fn step_out(&mut self) -> IonResult<()>;
            fn parent_type(&self) -> Option<IonType>;
            fn depth(&self) -> usize;
        }
    }
}

/// Functionality that is only available if the data source we're reading from is in-memory, like
/// a `Vec<u8>` or `&[u8]`.
impl<T: AsRef<[u8]>> UserReader<BlockingRawBinaryReader<io::Cursor<T>>> {
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
    use crate::BlockingRawBinaryReader;

    use crate::result::IonResult;
    use crate::types::IonType;
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
    fn raw_binary_reader_for(bytes: &[u8]) -> BlockingRawBinaryReader<TestDataSource> {
        use RawStreamItem::*;
        let mut raw_reader =
            BlockingRawBinaryReader::new(data_source_for(bytes)).expect("unable to create reader");
        assert_eq!(raw_reader.ion_type(), None);
        assert_eq!(raw_reader.next(), Ok(VersionMarker(1, 0)));
        assert_eq!(raw_reader.ion_version(), (1u8, 0u8));
        raw_reader
    }

    fn ion_reader_for(bytes: &[u8]) -> Reader {
        ReaderBuilder::new().build(ion_data(bytes)).unwrap()
    }

    const EXAMPLE_STREAM: &[u8] = &[
        // $ion_symbol_table::{imports: $ion_symbol_table, symbols: ["foo", "bar", "baz"]}
        0xEE, // Var len annotations
        0x92, // Annotations + Value length: 21 bytes
        0x81, // Annotations length: 1
        0x83, // Annotation 3 ('$ion_symbol_table')
        0xDE, // Var len struct
        0x8E, // Length: 14 bytes
        0x87, // Field ID 7 ('symbols')
        0xBC, // 12-byte List
        0x83, 0x66, 0x6f, 0x6f, // "foo"
        0x83, 0x62, 0x61, 0x72, // "bar"
        0x83, 0x62, 0x61, 0x7a, // "baz"
        // System: {$10: 1, $11: 2, $12: 3}
        // User: {foo: 1, bar: 2, baz: 3}
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

        assert_eq!(Value(IonType::Struct), reader.next()?);
        reader.step_in()?;

        assert_eq!(reader.next()?, Value(IonType::Int));
        assert_eq!(reader.field_name()?, "foo");

        assert_eq!(reader.next()?, Value(IonType::Int));
        assert_eq!(reader.field_name()?, "bar");

        assert_eq!(reader.next()?, Value(IonType::Int));
        assert_eq!(reader.field_name()?, "baz");

        Ok(())
    }
}
