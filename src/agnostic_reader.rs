use crate::binary::non_blocking::raw_binary_reader::RawBinaryBufferReader as NBRawBinaryReader;
use crate::data_source::ToIonDataSource;
use crate::raw_reader::RawReader;
use crate::result::IonResult;
use crate::stream_reader::IonReader;
use crate::text::non_blocking::raw_text_reader::RawTextReader as NBRawTextReader;
use crate::types::timestamp::Timestamp;
use crate::{Decimal, Int, IonError, IonType};

use std::io::Read;

pub type RawTextReader<T> = AgnosticRawReader<NBRawTextReader<Vec<u8>>, T>;
pub type RawBinaryReader<T> = AgnosticRawReader<NBRawBinaryReader<Vec<u8>>, T>;

/// BufferedRawReader is a RawReader which can be created from a Vec<u8> and implements the needed
/// functionality to provide non-blocking reader support. This includes the ability to add more
/// data as needed, as well as marking when the stream is complete.
pub trait BufferedRawReader: RawReader + From<Vec<u8>> {
    fn append_bytes(&mut self, bytes: &[u8]) -> IonResult<()>;
    fn read_from<R: Read>(&mut self, source: R, length: usize) -> IonResult<usize>;
    // Mark the stream as complete. This allows the reader to understand when partial parses on
    // data boundaries are not possible.
    fn stream_complete(&mut self);
    fn is_stream_complete(&self) -> bool;
}

/// The AgnosticRawReader wraps a non-blocking RawReader that implements the BufferedReader trait,
/// providing a blocking RawReader.
pub struct AgnosticRawReader<R: BufferedRawReader, T: ToIonDataSource> {
    source: T::DataSource,
    reader: R,
    expected_read_size: usize,
}

const READER_DEFAULT_BUFFER_CAPACITY: usize = 1024 * 4;

impl<R: BufferedRawReader, T: ToIonDataSource> AgnosticRawReader<R, T> {
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

impl<R: BufferedRawReader, T: ToIonDataSource> IonReader for AgnosticRawReader<R, T> {
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

    fn read_string(&mut self) -> IonResult<String> {
        self.reader.read_string()
    }

    fn map_string<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&str) -> U,
    {
        self.reader.map_string(f)
    }

    fn map_string_bytes<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        self.reader.map_string_bytes(f)
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        self.reader.read_symbol()
    }

    fn read_blob(&mut self) -> IonResult<Vec<u8>> {
        self.map_blob(|b| Vec::from(b))
    }

    fn map_blob<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        self.reader.map_blob(f)
    }

    fn read_clob(&mut self) -> IonResult<Vec<u8>> {
        self.map_clob(|c| Vec::from(c))
    }

    fn map_clob<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        self.reader.map_clob(f)
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

impl<T: ToIonDataSource> RawBinaryReader<T> {
    pub fn raw_bytes(&self) -> Option<&[u8]> {
        unimplemented!()
    }

    pub fn raw_field_id_bytes(&self) -> Option<&[u8]> {
        unimplemented!()
    }

    pub fn raw_header_bytes(&self) -> Option<&[u8]> {
        unimplemented!()
    }

    pub fn raw_value_bytes(&self) -> Option<&[u8]> {
        unimplemented!()
    }

    pub fn raw_annotations_bytes(&self) -> Option<&[u8]> {
        unimplemented!()
    }

    pub fn field_id_length(&self) -> Option<usize> {
        unimplemented!()
    }

    pub fn field_id_offset(&self) -> Option<usize> {
        unimplemented!()
    }

    pub fn field_id_range(&self) -> Option<std::ops::Range<usize>> {
        unimplemented!()
    }

    pub fn annotations_length(&self) -> Option<usize> {
        unimplemented!()
    }

    pub fn annotations_offset(&self) -> Option<usize> {
        unimplemented!()
    }

    pub fn annotations_range(&self) -> Option<std::ops::Range<usize>> {
        unimplemented!()
    }

    pub fn header_length(&self) -> usize {
        self.reader.header_length()
    }

    pub fn header_offset(&self) -> usize {
        unimplemented!()
    }

    pub fn header_range(&self) -> std::ops::Range<usize> {
        unimplemented!()
    }

    pub fn value_length(&self) -> usize {
        unimplemented!()
    }

    pub fn value_offset(&self) -> usize {
        unimplemented!()
    }

    pub fn value_range(&self) -> std::ops::Range<usize> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::non_blocking::raw_binary_reader::RawBinaryBufferReader;
    use crate::raw_reader::RawStreamItem;
    use crate::result::IonResult;
    use crate::text::non_blocking::raw_text_reader::RawTextReader;

    fn bin_reader(source: &[u8]) -> AgnosticRawReader<RawBinaryBufferReader<Vec<u8>>, Vec<u8>> {
        let reader =
            AgnosticRawReader::<RawBinaryBufferReader<Vec<u8>>, Vec<u8>>::new(source.to_vec());
        reader.unwrap()
    }

    fn text_reader(source: &[u8]) -> AgnosticRawReader<RawTextReader<Vec<u8>>, Vec<u8>> {
        let reader = AgnosticRawReader::<RawTextReader<Vec<u8>>, Vec<u8>>::new(source.to_vec());
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

                fn next_type(reader: &mut AgnosticRawReader<$type, Vec<u8>>, ion_type: IonType, is_null: bool) {
                    assert_eq!(
                        reader.next().unwrap(),
                        RawStreamItem::nullable_value(ion_type, is_null)
                    );
                }

                // Creates a reader for the specified reader type, with a small (24 byte) read
                // initial size.
                fn new_reader(source: &[u8]) -> AgnosticRawReader<$type, Vec<u8>> {
                    let reader = AgnosticRawReader::<$type, Vec<u8>>::new_with_size(source.to_vec(), 24);
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
        binary_reader: RawBinaryBufferReader<Vec<u8>>,
        text_reader: RawTextReader<Vec<u8>>,
    }
}
