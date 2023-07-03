use std::io;
use std::io::Read;
use std::ops::Range;

use delegate::delegate;

use crate::binary::constants::v1_0::IVM;
use crate::binary::non_blocking::raw_binary_reader::RawBinaryReader;
use crate::blocking_reader::{BlockingRawBinaryReader, BlockingRawTextReader};
use crate::data_source::IonDataSource;
use crate::element::{Blob, Clob};
use crate::ion_reader::IonReader;
use crate::raw_reader::{Expandable, RawReader};
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::{IonFailure, IonResult};
use crate::symbol_table::SymbolTable;
use crate::system_reader::SystemReader;
use crate::types::{Decimal, Int, Symbol, Timestamp};
use crate::IonType;
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
    pub fn build<'a, I: 'a + IonDataSource>(self, input: I) -> IonResult<Reader<'a>> {
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
                IonResult::decoding_error(format!(
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

    fn make_text_reader<'a, I: 'a + IonDataSource>(data: I) -> IonResult<Reader<'a>> {
        let raw_reader = Box::new(BlockingRawTextReader::new(data)?);
        Ok(Reader::new(raw_reader))
    }

    fn make_binary_reader<'a, I: 'a + IonDataSource>(data: I) -> IonResult<Reader<'a>> {
        let raw_reader = Box::new(BlockingRawBinaryReader::new(data)?);
        Ok(Reader::new(raw_reader))
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
    system_reader: SystemReader<R>,
}

impl<R: RawReader> UserReader<R> {
    pub fn new(raw_reader: R) -> UserReader<R> {
        UserReader {
            system_reader: SystemReader::new(raw_reader),
        }
    }
}

// This module exists to allow our integration tests to directly construct a `UserReader`
// with not-yet-supported settings. We want users to use `ReaderBuilder` instead; eventually,
// `ReaderBuilder` will also work for the integration tests and we can remove this.
// See: https://github.com/amazon-ion/ion-rust/issues/484
#[doc(hidden)]
pub mod integration_testing {
    use crate::raw_reader::RawReader;
    use crate::reader::{Reader, UserReader};

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
        self.system_reader.read_raw_symbol()
    }

    pub fn raw_field_name_token(&mut self) -> IonResult<RawSymbolToken> {
        self.system_reader.raw_field_name_token()
    }

    fn raw_annotations(&mut self) -> impl Iterator<Item = IonResult<RawSymbolToken>> + '_ {
        self.system_reader.raw_annotations()
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        self.system_reader.symbol_table()
    }
}

impl<R: RawReader> IonReader for UserReader<R> {
    type Item = StreamItem;
    type Symbol = Symbol;

    /// Advances the raw reader to the next user-level Ion value, processing any system-level directives
    /// encountered along the way.
    // v-- Clippy complains that `next` resembles `Iterator::next()`
    #[allow(clippy::should_implement_trait)]
    fn next(&mut self) -> IonResult<Self::Item> {
        use crate::system_reader::SystemStreamItem::*;
        loop {
            // If the system reader encounters an encoding artifact like a symbol table or IVM,
            // keep going until we find a value or exhaust the stream.
            let item = match self.system_reader.next()? {
                VersionMarker(_, _) | SymbolTableValue(_) | SymbolTableNull(_) => continue,
                Value(ion_type) => StreamItem::Value(ion_type),
                Null(ion_type) => StreamItem::Null(ion_type),
                Nothing => StreamItem::Nothing,
            };
            return Ok(item);
        }
    }

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

    delegate! {
        to self.system_reader {
            fn is_null(&self) -> bool;
            fn ion_version(&self) -> (u8, u8);
            fn ion_type(&self) -> Option<IonType>;
            fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Symbol>> + 'a>;
            fn read_null(&mut self) -> IonResult<IonType>;
            fn read_bool(&mut self) -> IonResult<bool>;
            fn read_int(&mut self) -> IonResult<Int>;
            fn read_i64(&mut self) -> IonResult<i64>;
            fn read_f32(&mut self) -> IonResult<f32>;
            fn read_f64(&mut self) -> IonResult<f64>;
            fn read_decimal(&mut self) -> IonResult<Decimal>;
            fn read_symbol(&mut self) -> IonResult<Self::Symbol>;
            fn read_string(&mut self) -> IonResult<Str>;
            fn read_str(&mut self) -> IonResult<&str>;
            fn read_blob(&mut self) -> IonResult<Blob>;
            fn read_clob(&mut self) -> IonResult<Clob>;
            fn read_timestamp(&mut self) -> IonResult<Timestamp>;
            fn step_in(&mut self) -> IonResult<()>;
            fn field_name(&self) -> IonResult<Symbol>;
            fn step_out(&mut self) -> IonResult<()>;
            fn parent_type(&self) -> Option<IonType>;
            fn depth(&self) -> usize;
        }
    }
}

/// Functionality that is only available if the data source we're reading from is in-memory, like
/// a `Vec<u8>` or `&[u8]`.
impl<T: AsRef<[u8]> + Expandable> UserReader<RawBinaryReader<T>> {
    delegate! {
        to self.system_reader {
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
    use crate::reader::{BlockingRawBinaryReader, StreamItem::Value};

    use crate::result::IonResult;
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
    fn raw_binary_reader_for(bytes: &[u8]) -> BlockingRawBinaryReader<TestDataSource> {
        use crate::raw_reader::RawStreamItem::*;
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
