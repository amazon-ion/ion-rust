use delegate::delegate;
use std::ops::Range;

use crate::binary::non_blocking::raw_binary_reader::RawBinaryReader;
use crate::data_source::ToIonDataSource;
use crate::element::{Blob, Clob};
use crate::raw_reader::BufferedRawReader;
use crate::result::IonResult;
use crate::stream_reader::IonReader;
use crate::text::non_blocking::raw_text_reader::RawTextReader;
use crate::types::Timestamp;
use crate::{Decimal, Int, IonError, IonType, Str};

pub type BlockingRawTextReader<T> = BlockingRawReader<RawTextReader<Vec<u8>>, T>;
pub type BlockingRawBinaryReader<T> = BlockingRawReader<RawBinaryReader<Vec<u8>>, T>;

/// The BlockingRawReader wraps a non-blocking RawReader that implements the BufferedReader trait,
/// providing a blocking RawReader.
pub struct BlockingRawReader<R: BufferedRawReader, T: ToIonDataSource> {
    source: T::DataSource,
    reader: R,
    expected_read_size: usize,
}

const READER_DEFAULT_BUFFER_CAPACITY: usize = 1024 * 4;

impl<R: BufferedRawReader, T: ToIonDataSource> BlockingRawReader<R, T> {
    pub fn read_source(&mut self, length: usize) -> IonResult<usize> {
        let mut bytes_read = 0;
        loop {
            let n = self.reader.read_from(&mut self.source, length)?;
            bytes_read += n;
            if n == 0 || bytes_read + n >= length {
                break;
            }
        }
        Ok(bytes_read)
    }

    pub fn new(input: T) -> IonResult<Self> {
        Self::new_with_size(input, READER_DEFAULT_BUFFER_CAPACITY)
    }

    pub fn new_with_size(input: T, size: usize) -> IonResult<Self> {
        let buffer = Vec::with_capacity(size);
        let mut reader = Self {
            source: input.to_ion_data_source(),
            reader: buffer.into(),
            expected_read_size: size,
        };
        reader.read_source(size)?;
        Ok(reader)
    }
}

impl<R: BufferedRawReader, T: ToIonDataSource> IonReader for BlockingRawReader<R, T> {
    type Item = R::Item;
    type Symbol = R::Symbol;

    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn next(&mut self) -> IonResult<Self::Item> {
        let mut read_size = self.expected_read_size;

        loop {
            let result = self.reader.next();
            if let Err(IonError::Incomplete { .. }) = result {
                let bytes_read = self.read_source(read_size)?;
                // if we have no bytes, and our stream has been marked as fully loaded, then we
                // need to bubble up the error. Otherwise, if our stream has not been marked as
                // loaded, then we need to mark it as loaded and retry.
                if 0 == bytes_read {
                    if self.reader.is_stream_complete() {
                        return result;
                    } else {
                        self.reader.stream_complete();
                    }
                }
                // The assumption here is that most buffer sizes will start at a magnitude the user
                // is comfortable with in terms of memory usage. So if we're reading more in order
                // to reach a parsable point we do not want to start consuming more than an order of
                // magnitude more memory just to get there.
                read_size = std::cmp::min(read_size * 2, self.expected_read_size * 10);
            } else {
                return result;
            }
        }
    }

    fn current(&self) -> Self::Item {
        self.reader.current()
    }

    fn ion_type(&self) -> Option<IonType> {
        self.reader.ion_type()
    }

    fn is_null(&self) -> bool {
        self.reader.is_null()
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        self.reader.annotations()
    }

    fn has_annotations(&self) -> bool {
        self.reader.has_annotations()
    }

    fn number_of_annotations(&self) -> usize {
        self.reader.number_of_annotations()
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        self.reader.field_name()
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        self.reader.read_null()
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        self.reader.read_bool()
    }

    fn read_int(&mut self) -> IonResult<Int> {
        self.reader.read_int()
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        self.reader.read_i64()
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        self.reader.read_f32()
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        self.reader.read_f64()
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        self.reader.read_decimal()
    }

    fn read_string(&mut self) -> IonResult<Str> {
        self.reader.read_string()
    }

    fn read_str(&mut self) -> IonResult<&str> {
        self.reader.read_str()
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        self.reader.read_symbol()
    }

    fn read_blob(&mut self) -> IonResult<Blob> {
        self.reader.read_blob()
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        self.reader.read_clob()
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        self.reader.read_timestamp()
    }

    fn step_in(&mut self) -> IonResult<()> {
        self.reader.step_in()
    }

    fn step_out(&mut self) -> IonResult<()> {
        let mut read_size = self.expected_read_size;
        loop {
            let result = self.reader.step_out();
            if let Err(IonError::Incomplete { .. }) = result {
                if 0 == self.read_source(read_size)? {
                    return result;
                }
            } else {
                return result;
            }
            read_size = std::cmp::min(read_size * 2, self.expected_read_size * 10);
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        self.reader.parent_type()
    }

    fn depth(&self) -> usize {
        self.reader.depth()
    }
}

impl<T: ToIonDataSource> BlockingRawReader<RawBinaryReader<Vec<u8>>, T> {
    delegate! {
        to self.reader {
            pub fn raw_bytes(&self) ->  Option<&[u8]>;

            pub fn field_id_length(&self) -> Option<usize>;
            pub fn field_id_offset(&self) -> Option<usize>;
            pub fn field_id_range(&self) -> Option<Range<usize>>;
            pub fn raw_field_id_bytes(&self) -> Option<&[u8]>;

            pub fn annotations_length(&self) -> Option<usize>;
            pub fn annotations_offset(&self) -> Option<usize>;
            pub fn annotations_range(&self) -> Option<Range<usize>>;
            pub fn raw_annotations_bytes(&self) -> Option<&[u8]>;

            pub fn header_length(&self) -> usize;
            pub fn header_offset(&self) -> usize;
            pub fn header_range(&self) -> Range<usize>;
            pub fn raw_header_bytes(&self) -> Option<&[u8]>;

            pub fn value_length(&self) -> usize;
            pub fn value_offset(&self) -> usize;
            pub fn value_range(&self) -> Range<usize>;
            pub fn raw_value_bytes(&self) -> Option<&[u8]>;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::non_blocking::raw_binary_reader::RawBinaryReader as NBRawBinaryReader;
    use crate::raw_reader::RawStreamItem;
    use crate::result::IonResult;
    use crate::text::non_blocking::raw_text_reader::RawTextReader;

    fn bin_reader(source: &[u8]) -> BlockingRawBinaryReader<Vec<u8>> {
        let reader = BlockingRawReader::<NBRawBinaryReader<Vec<u8>>, Vec<u8>>::new(source.to_vec());
        reader.unwrap()
    }

    fn text_reader(source: &[u8]) -> BlockingRawTextReader<Vec<u8>> {
        let reader = BlockingRawReader::<RawTextReader<Vec<u8>>, Vec<u8>>::new(source.to_vec());
        reader.unwrap()
    }

    mod data {
        pub mod binary_reader {
            // Binary reader data has been converted from the text data. In the cases where symbol
            // tables were added to the binary output, an empty struct was added to the text
            // version in order to keep the sequence of tests the same.
            pub const BASIC_INCOMPLETE: &[u8] = &[
                0xe0, 0x01, 0x00, 0xea, 0xb6, 0x21, 0x01, 0x21, 0x02, 0x21, // 0x03,
            ];

            pub const STRING_BASIC: &[u8] = &[
                0xe0, 0x01, 0x00, 0xea, 0x8b, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72,
                0x6c, 0x64,
            ];

            pub const STRUCT_NESTED: &[u8] = &[
                0xe0, 0x01, 0x00, 0xea, 0xee, 0x95, 0x81, 0x83, 0xde, 0x91, 0x86, 0x71, 0x03, 0x87,
                0xbc, 0x83, 0x66, 0x6f, 0x6f, 0x83, 0x62, 0x61, 0x72, 0x81, 0x61, 0x81, 0x62, 0xde,
                0x95, 0x8a, 0xb9, 0x21, 0x01, 0xb4, 0x21, 0x02, 0x21, 0x03, 0x21, 0x04, 0x8b, 0xd8,
                0x8c, 0x21, 0x05, 0x8d, 0xc3, 0x11, 0x11, 0x11, 0x21, 0x0b,
            ];

            pub const BASIC_SYMBOL_TABLE: &[u8] = &[
                /* 0x00 */ 0xe0, 0x01, 0x00, 0xea, 0xee, 0x95, 0x81, 0x83, 0xde, 0x91, 0x86,
                0x71, 0x03, 0x87, 0xbc, 0x83, 0x66, /* 0x10 */ 0x6f, 0x6f, 0x83, 0x62, 0x61,
                0x72, 0x83, 0x62, 0x61, 0x7a, 0x71, 0x0a, 0x71, 0x0b, 0x71, 0x0c,
            ];
        }
        pub mod text_reader {
            pub const BASIC_INCOMPLETE: &[u8] = r#"
              $ion_1_0
              [1, 2, 3
              "#
            .as_bytes();
            pub const STRING_BASIC: &[u8] = r#"
            $ion_1_0
            "Hello World"
            "#
            .as_bytes();

            pub const STRUCT_NESTED: &[u8] = r#"
                $ion_1_0
                $ion_symbol_table::{}
                {
                    foo: [
                        1,
                        [2, 3],
                        4
                    ],
                    bar: {
                        a: 5,
                        b: (true true true)
                    }
                }
                11
            "#
            .as_bytes();

            pub const BASIC_SYMBOL_TABLE: &[u8] = r#"
               $ion_1_0
               $ion_symbol_table::{
                  imports: $ion_symbol_table,
                  symbols: ["foo", "bar", "baz"],
               }
               $10
               $11
               $12
            "#
            .as_bytes();
        }
    }

    macro_rules! raw_reader_tests {
        ($($name:ident: $type:ty,)*) => {
        $(
            mod $name {
                use super::*;
                use super::data::$name::*;
                use crate::raw_symbol_token::RawSymbolToken;

                fn next_type(reader: &mut BlockingRawReader<$type, Vec<u8>>, ion_type: IonType, is_null: bool) {
                    assert_eq!(
                        reader.next().unwrap(),
                        RawStreamItem::nullable_value(ion_type, is_null)
                    );
                }

                // Creates a reader for the specified reader type, with a small (24 byte) read
                // initial size.
                fn new_reader(source: &[u8]) -> BlockingRawReader<$type, Vec<u8>> {
                    let reader = BlockingRawReader::<$type, Vec<u8>>::new_with_size(source.to_vec(), 24);
                    reader.unwrap()
                }

                #[test]
                fn basic_incomplete() -> IonResult<()> {
                    let reader = &mut new_reader(BASIC_INCOMPLETE);
                    assert_eq!(reader.next().unwrap(), RawStreamItem::VersionMarker(1, 0));
                    next_type(reader, IonType::List, false);
                    reader.step_in()?;

                    next_type(reader, IonType::Int, false);
                    assert_eq!(reader.read_i64()?, 1);
                    let result = reader.step_out();
                    match result {
                        Err(IonError::Incomplete { .. }) => (),
                        r => panic!("Unexpected result: {:?}", r),
                    }
                    assert!(result.is_err());

                    Ok(())
                }

                #[test]
                fn incomplete_string() -> IonResult<()> {
                    let reader = &mut new_reader(STRING_BASIC);
                    assert_eq!(reader.next().unwrap(), RawStreamItem::VersionMarker(1, 0));
                    next_type(reader, IonType::String, false);
                    assert_eq!(reader.read_string()?, "Hello World");
                    Ok(())
                }

                #[test]
                fn nested_struct() -> IonResult<()> {
                    let reader = &mut new_reader(STRUCT_NESTED);
                    assert_eq!(reader.next().unwrap(), RawStreamItem::VersionMarker(1, 0));

                    next_type(reader, IonType::Struct, false); // Version Table

                    next_type(reader, IonType::Struct, false);
                    reader.step_in()?;
                    next_type(reader, IonType::List, false);
                    assert!(reader.field_name().is_ok());

                    reader.step_in()?;
                    next_type(reader, IonType::Int, false);
                    assert_eq!(reader.read_i64()?, 1);
                    next_type(reader, IonType::List, false);
                    reader.step_in()?;
                    next_type(reader, IonType::Int, false);
                    assert_eq!(reader.read_i64()?, 2);
                    // next_type(reader, IonType::Integer, false);
                    // assert_eq!(reader.read_i64()?, 3);
                    reader.step_out()?; // Step out of foo[1]
                    reader.step_out()?; // Step out of foo

                    next_type(reader, IonType::Struct, false);
                    assert!(reader.field_name().is_ok());

                    reader.step_in()?;
                    next_type(reader, IonType::Int, false);
                    assert_eq!(reader.read_i64()?, 5);
                    next_type(reader, IonType::SExp, false);
                    reader.step_in()?;
                    next_type(reader, IonType::Bool, false);
                    assert_eq!(reader.read_bool()?, true);
                    next_type(reader, IonType::Bool, false);
                    assert_eq!(reader.read_bool()?, true);
                    next_type(reader, IonType::Bool, false);
                    assert_eq!(reader.read_bool()?, true);
                    // The reader is now at the second 'true' in the s-expression nested in 'bar'/'b'
                    reader.step_out()?; // Step out of bar.b
                    reader.step_out()?; // Step out of bar
                    reader.step_out()?; // Step out of our top-levelstruct

                    next_type(reader, IonType::Int, false);
                    assert_eq!(reader.read_i64()?, 11);
                    Ok(())
                }

                #[test]
                fn basic_symbol_table() -> IonResult<()> {
                    let reader = &mut new_reader(BASIC_SYMBOL_TABLE);
                    assert_eq!(reader.next().unwrap(), RawStreamItem::VersionMarker(1, 0));

                    next_type(reader, IonType::Struct, false);
                    reader.step_in()?;

                    next_type(reader, IonType::Symbol, false);

                    next_type(reader, IonType::List, false);
                    reader.step_in()?;

                    next_type(reader, IonType::String, false);
                    assert_eq!(reader.read_string()?, "foo");
                    next_type(reader, IonType::String, false);
                    assert_eq!(reader.read_string()?, "bar");
                    next_type(reader, IonType::String, false);
                    assert_eq!(reader.read_string()?, "baz");

                    reader.step_out()?; // List
                    reader.step_out()?; // Symbol table
                    next_type(reader, IonType::Symbol, false);
                    assert_eq!(reader.read_symbol()?, RawSymbolToken::SymbolId(10));

                    next_type(reader, IonType::Symbol, false);
                    assert_eq!(reader.read_symbol()?, RawSymbolToken::SymbolId(11));

                    next_type(reader, IonType::Symbol, false);
                    assert_eq!(reader.read_symbol()?, RawSymbolToken::SymbolId(12));

                    Ok(())
                }
            }


        )*
        }
    }

    raw_reader_tests! {
        binary_reader: RawBinaryReader<Vec<u8>>,
        text_reader: RawTextReader<Vec<u8>>,
    }

    #[test]
    fn test_raw_bytes() -> IonResult<()> {
        // Note: technically invalid Ion because the symbol IDs referenced are never added to the
        // symbol table.

        // {$11: [1, 2, 3], $10: 1}
        let ion_data: &[u8] = &[
            // First top-level value in the stream
            0xDB, // 11-byte struct
            0x8B, // Field ID 11
            0xB6, // 6-byte List
            0x21, 0x01, // Integer 1
            0x21, 0x02, // Integer 2
            0x21, 0x03, // Integer 3
            0x8A, // Field ID 10
            0x21, 0x01, // Integer 1
            // Second top-level value in the stream
            0xE3, // 3-byte annotations envelope
            0x81, // * Annotations themselves take 1 byte
            0x8C, // * Annotation w/SID $12
            0x10, // Boolean false
        ];
        let mut cursor = BlockingRawBinaryReader::new(ion_data.to_owned())?;
        assert_eq!(RawStreamItem::Value(IonType::Struct), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[0..1])); // No value bytes for containers.
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[0..=0]));
        assert_eq!(cursor.raw_value_bytes(), None);
        cursor.step_in()?;
        assert_eq!(RawStreamItem::Value(IonType::List), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[1..3]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[1..=1]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[2..=2]));
        assert_eq!(cursor.raw_value_bytes(), None);
        cursor.step_in()?;
        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[3..=4]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[3..=3]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[4..=4]));
        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[5..=6]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[5..=5]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[6..=6]));
        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[7..=8]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[7..=7]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[8..=8]));

        cursor.step_out()?; // Step out of list

        assert_eq!(RawStreamItem::Value(IonType::Int), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[9..=11]));
        assert_eq!(cursor.raw_field_id_bytes(), Some(&ion_data[9..=9]));
        assert_eq!(cursor.raw_annotations_bytes(), None);
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[10..=10]));
        assert_eq!(cursor.raw_value_bytes(), Some(&ion_data[11..=11]));

        cursor.step_out()?; // Step out of struct

        // Second top-level value
        assert_eq!(RawStreamItem::Value(IonType::Bool), cursor.next()?);
        assert_eq!(cursor.raw_bytes(), Some(&ion_data[12..16]));
        assert_eq!(cursor.raw_field_id_bytes(), None);
        assert_eq!(cursor.raw_annotations_bytes(), Some(&ion_data[12..=14]));
        assert_eq!(cursor.raw_header_bytes(), Some(&ion_data[15..=15]));
        assert_eq!(
            cursor.raw_value_bytes(),
            Some(&ion_data[15..15] /* That is, zero bytes */)
        );
        Ok(())
    }
}
