use crate::data_source::ToIonDataSource;
use crate::element::{Blob, Clob};
use crate::raw_reader::RawStreamItem;
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::IonResult;
use crate::stream_reader::IonReader;
use crate::types::string::Str;
use crate::types::timestamp::Timestamp;
use crate::{Decimal, Int, IonError, IonType};

use crate::text::non_blocking::raw_text_reader::RawTextReader as NonBlockingReader;

const INITIAL_PARENTS_CAPACITY: usize = 16;
const READER_DEFAULT_BUFFER_CAPACITY: usize = 1024 * 4;

pub struct RawTextReader<T: ToIonDataSource> {
    source: T::DataSource,
    // The inner non-blocking reader.
    reader: NonBlockingReader<Vec<u8>>,
    // The expected read size. The reader will read larger amounts when incomplete errors are
    // reached back-to-back, but this represents the read size that will occur first.
    expected_read_size: usize,
}

impl<T: ToIonDataSource> RawTextReader<T> {
    pub fn new(input: T) -> IonResult<RawTextReader<T>> {
        Self::new_with_size(input, READER_DEFAULT_BUFFER_CAPACITY)
    }

    pub fn new_with_size(input: T, size: usize) -> IonResult<RawTextReader<T>> {
        let buffer = Vec::with_capacity(size);
        let mut reader = RawTextReader {
            source: input.to_ion_data_source(),
            reader: NonBlockingReader::new(buffer),
            expected_read_size: size,
        };
        reader.read_source(size)?;
        Ok(reader)
    }

    // Read up to `length` bytes from the source, into the underlying non-blocking reader.
    fn read_source(&mut self, length: usize) -> IonResult<usize> {
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
}

impl<T: ToIonDataSource> IonReader for RawTextReader<T> {
    type Item = RawStreamItem;
    type Symbol = RawSymbolToken;

    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn next(&mut self) -> IonResult<RawStreamItem> {
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

    fn current(&self) -> RawStreamItem {
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

    fn read_blob(&mut self) -> IonResult<Blob> {
        self.map_blob(|b| Vec::from(b)).map(Blob::from)
    }

    fn map_blob<F, U>(&mut self, f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        self.reader.map_blob(f)
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        self.map_clob(|c| Vec::from(c)).map(Clob::from)
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
                let bytes_read = self.read_source(read_size)?;
                if 0 == bytes_read {
                    if self.reader.is_stream_complete() {
                        return result;
                    } else {
                        self.reader.stream_complete();
                    }
                }
                read_size = std::cmp::min(read_size * 2, self.expected_read_size * 10);
            } else {
                return result;
            }
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        self.reader.parent_type()
    }

    fn depth(&self) -> usize {
        self.reader.depth()
    }
}

#[cfg(test)]
mod reader_tests {
    use crate::data_source::ToIonDataSource;
    use crate::raw_reader::RawStreamItem;
    use crate::raw_symbol_token::{local_sid_token, text_token, RawSymbolToken};
    use crate::result::IonResult;
    use crate::stream_reader::IonReader;
    use crate::text::raw_text_reader::RawTextReader;
    use crate::text::text_value::IntoRawAnnotations;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::IonType;
    use crate::RawStreamItem::Nothing;

    fn next_type<T: ToIonDataSource>(
        reader: &mut RawTextReader<T>,
        ion_type: IonType,
        is_null: bool,
    ) {
        assert_eq!(
            reader.next().unwrap(),
            RawStreamItem::nullable_value(ion_type, is_null)
        );
    }

    fn annotations_eq<I: IntoRawAnnotations>(reader: &mut RawTextReader<&str>, expected: I) {
        let expected: Vec<RawSymbolToken> = expected.into_annotations();
        let actual: Vec<RawSymbolToken> = reader
            .annotations()
            .map(|a| a.expect("annotation with unknown text"))
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_skipping_containers() -> IonResult<()> {
        let ion_data = r#"
            0 [1, 2, 3] (4 5) 6
        "#;
        let reader = &mut RawTextReader::new(ion_data)?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 0);

        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 1);
        reader.step_out()?;
        // This should have skipped over the `2, 3` at the end of the list.
        next_type(reader, IonType::SExp, false);
        // Don't step into the s-expression. Instead, skip over it.
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 6);
        Ok(())
    }

    #[test]
    fn test_read_nested_containers() -> IonResult<()> {
        let ion_data = r#"
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
        "#;
        let reader = &mut RawTextReader::new(ion_data)?;
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        // The reader is now at the '2' nested inside of 'foo'
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        next_type(reader, IonType::SExp, false);
        reader.step_in()?;
        next_type(reader, IonType::Bool, false);
        next_type(reader, IonType::Bool, false);
        // The reader is now at the second 'true' in the s-expression nested in 'bar'/'b'
        reader.step_out()?;
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 11);
        Ok(())
    }

    #[test]
    fn test_read_container_with_mixed_scalars_and_containers() -> IonResult<()> {
        let ion_data = r#"
            {
                foo: 4,
                bar: {
                    a: 5,
                    b: (true true true)
                }
            }
            42
        "#;

        let reader = &mut RawTextReader::new(ion_data)?;
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.field_name()?, text_token("foo"));
        next_type(reader, IonType::Struct, false);
        assert_eq!(reader.field_name()?, text_token("bar"));
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);
        reader.step_out()?;
        assert_eq!(reader.next()?, RawStreamItem::Nothing);
        reader.step_out()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 42);
        Ok(())
    }

    #[test]
    fn test_text_read_multiple_top_level_values() -> IonResult<()> {
        let ion_data = r#"
            null
            true
            5
            5e0
            5.5
            2021-09-25T
            '$ion_1_0' // A quoted symbol, not an IVM
            $ion_1_0   // An IVM, not a symbol
            foo
            "hello"
            {foo: bar}
            ["foo", "bar"]
            ('''foo''')
        "#;

        let reader = &mut RawTextReader::new(ion_data)?;
        next_type(reader, IonType::Null, true);

        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);

        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);

        next_type(reader, IonType::Float, false);
        assert_eq!(reader.read_f64()?, 5.0f64);

        next_type(reader, IonType::Decimal, false);
        assert_eq!(reader.read_decimal()?, Decimal::new(55i32, -1i64));

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2021, 9, 25).build().unwrap()
        );

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("$ion_1_0"));

        // A mid-stream Ion Version Marker
        assert_eq!(reader.next()?, RawStreamItem::VersionMarker(1, 0));

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("foo"));

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, "hello".to_string());

        // ===== CONTAINERS =====

        // Reading a struct: {foo: bar}
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("bar"));
        assert_eq!(reader.field_name()?, text_token("foo"));

        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading a list: ["foo", "bar"]
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("foo"));
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("bar"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading an s-expression: ('''foo''')
        next_type(reader, IonType::SExp, false);
        reader.step_in()?;
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("foo"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // There are no more top level values.snow
        assert_eq!(reader.next()?, Nothing);

        // Asking for more still results in `None`
        assert_eq!(reader.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn test_read_multiple_top_level_values_with_comments() -> IonResult<()> {
        let ion_data = r#"
            /*
                Arrokoth is a trans-Neptunian object in the Kuiper belt.
                It is a contact binary composed of two plenetesimals joined
                along their major axes.
            */
            "(486958) 2014 MU69" // Original designation
            2014-06-26T // Date of discovery
            km::36 // width
        "#;

        let reader = &mut RawTextReader::new(ion_data)?;

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("(486958) 2014 MU69"));

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2014, 6, 26).build()?
        );
        // TODO: Check for 'km' annotation after change to OwnedSymbolToken
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 36);
        Ok(())
    }

    #[test]
    fn test_text_read_multiple_annotated_top_level_values() -> IonResult<()> {
        let ion_data = r#"
            mercury::null
            venus::'earth'::true
            $17::mars::5
            jupiter::5e0
            'saturn'::5.5
            $100::$200::$300::2021-09-25T
            'uranus'::foo
            neptune::"hello"
            $55::{foo: $21::bar}
            pluto::[1, $77::2, 3]
            haumea::makemake::eris::ceres::(++ -- &&&&&)
        "#;
        // TODO: Check for annotations after OwnedSymbolToken

        let reader = &mut RawTextReader::new(ion_data)?;
        next_type(reader, IonType::Null, true);
        annotations_eq(reader, ["mercury"]);

        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);
        annotations_eq(reader, ["venus", "earth"]);

        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);
        annotations_eq(reader, &[local_sid_token(17), text_token("mars")]);

        next_type(reader, IonType::Float, false);
        assert_eq!(reader.read_f64()?, 5.0f64);
        annotations_eq(reader, ["jupiter"]);

        next_type(reader, IonType::Decimal, false);
        assert_eq!(reader.read_decimal()?, Decimal::new(55i32, -1i64));
        annotations_eq(reader, ["saturn"]);

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2021, 9, 25).build().unwrap()
        );
        annotations_eq(reader, [100, 200, 300]);

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("foo"));
        annotations_eq(reader, ["uranus"]);

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, "hello".to_string());
        annotations_eq(reader, ["neptune"]);

        // ===== CONTAINERS =====

        // Reading a struct: $55::{foo: $21::bar}
        next_type(reader, IonType::Struct, false);
        annotations_eq(reader, 55);
        reader.step_in()?;
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.field_name()?, text_token("foo"));
        annotations_eq(reader, 21);
        assert_eq!(reader.read_symbol()?, text_token("bar"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading a list: pluto::[1, $77::2, 3]
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.number_of_annotations(), 0);
        assert_eq!(reader.read_i64()?, 1);
        next_type(reader, IonType::Int, false);
        annotations_eq(reader, [77]);
        assert_eq!(reader.read_i64()?, 2);
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.number_of_annotations(), 0);
        assert_eq!(reader.read_i64()?, 3);
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading an s-expression: haumea::makemake::eris::ceres::(++ -- &&&&&)
        next_type(reader, IonType::SExp, false);
        annotations_eq(reader, ["haumea", "makemake", "eris", "ceres"]);
        reader.step_in()?;
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("++"));
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("--"));
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("&&&&&"));
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // There are no more top level values.
        assert_eq!(reader.next()?, Nothing);

        // Asking for more still results in `None`
        assert_eq!(reader.next()?, Nothing);

        Ok(())
    }

    #[test]
    fn structs_trailing_comma() -> IonResult<()> {
        let pretty_ion = br#"
            // Structs with last field with/without trailing comma
            (
                {a:1, b:2,}     // with trailing comma
                {a:1, b:2 }     // without trailing comma
            )
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..])?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::SExp));
        reader.step_in()?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Struct));

        reader.step_in()?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?, RawSymbolToken::Text("a".to_string()));
        assert_eq!(reader.read_i64()?, 1);
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?, RawSymbolToken::Text("b".to_string()));
        assert_eq!(reader.read_i64()?, 2);
        reader.step_out()?;

        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Struct));
        reader.step_out()?;
        Ok(())
    }

    #[test]
    fn annotation_false() -> IonResult<()> {
        // The reader will reject the unquoted boolean keyword 'false' when used as an annotation
        let pretty_ion = br#"
            false::23
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..])?;
        let result = reader.next();
        println!("{result:?}");
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn annotation_nan() -> IonResult<()> {
        // The reader will reject the unquoted float keyword 'nan' when used as an annotation
        let pretty_ion = br#"
            nan::23
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..])?;
        let result = reader.next();
        println!("{result:?}");
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    // This test generates a large blob of over 4kb, which exceeds the default buffer size when
    // reading, which will cause an Incomplete error and trigger the RawTextReader to read more
    // data from the source.
    fn incomplete_blob_read() -> IonResult<()> {
        let mut source = String::from("{{");
        // Adding a large base64 blob.. the reader defaults to having a 4k buffer,
        // so we need the blob to be larger than 4K in order to trigger a read in response to an
        // incomplete.
        (0..4200).for_each(|_| source.push('A'));
        source.push_str(" }}");

        let mut reader = RawTextReader::new(&source[..])?;
        let result = reader.next();
        assert!(result.is_ok());
        Ok(())
    }

    #[test]
    // This test generates a large, but incomplete, blob of over 4kb, which exceeds the default buffer
    // size when reading, which will cause an Incomplete error and trigger the RawTextReader to read
    // more data from the source. Parsing should fail since the blob's closing delimeter is
    // missing.
    fn incomplete_blob_error() -> IonResult<()> {
        let mut source = String::from("{{");
        // Adding a large base64 blob.. the reader defaults to having a 4k buffer,
        // so we need the blob to be larger than 4K in order to trigger a read in response to an
        // incomplete. We then want to form an improper blob in order to generate an error after a
        // buffer read boundary.
        (0..4200).for_each(|_| source.push('A'));

        let mut reader = RawTextReader::new(&source[..])?;
        let result = reader.next();
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn buffered_struct_read() -> IonResult<()> {
        let mut source = String::from("{{");
        (0..4083).for_each(|_| source.push('A'));
        source.push_str("}}{foo:null.float");
        (0..4096).for_each(|_| source.push(' '));
        source.push('}');

        let mut reader = RawTextReader::new(&source[..])?;
        reader.next()?;
        // Blob..
        assert_eq!(IonType::Blob, reader.ion_type().unwrap());

        // Struct start..
        let result = reader.next();
        assert!(result.is_ok());
        assert_eq!(IonType::Struct, reader.ion_type().unwrap());
        assert!(reader.step_in().is_ok());

        let result = reader.next();
        assert!(result.is_ok());
        assert_eq!(IonType::Float, reader.ion_type().unwrap());
        assert_eq!(IonType::Float, reader.read_null()?);

        let result = reader.step_out();
        assert!(result.is_ok());

        Ok(())
    }

    #[test]
    fn buffered_struct_error() -> IonResult<()> {
        let mut source = String::from("{{");
        (0..4084).for_each(|_| source.push('A'));
        source.push_str("}}{foo: 0e0,");
        (0..4096).for_each(|_| source.push(' '));

        let mut reader = RawTextReader::new(&source[..])?;

        let result = reader.next();
        // Blob..
        assert!(result.is_ok());
        // Struct start..
        let result = reader.next();
        assert!(result.is_ok());
        assert!(reader.step_in().is_ok());

        let result = reader.next();
        assert!(result.is_ok());
        assert!(!reader.has_annotations());
        assert_eq!(0.0, reader.read_f32()?);
        assert_eq!(IonType::Struct, reader.parent_type().unwrap());

        let result = reader.step_out();
        assert!(result.is_err());

        Ok(())
    }

    use std::cell::RefCell;
    use std::rc::Rc;

    // Simple struct to track metrics around reading.
    struct ReaderMetrics {
        bytes_read: usize,
    }

    // An ion data source for use in testing when and how much data is read during parsing.
    struct TestIonSource {
        data: &'static str,
        current: usize,
        metrics: Rc<RefCell<ReaderMetrics>>,
    }

    impl TestIonSource {
        fn new(data: &'static str) -> (TestIonSource, Rc<RefCell<ReaderMetrics>>) {
            let metrics = Rc::new(RefCell::new(ReaderMetrics { bytes_read: 0 }));

            (
                TestIonSource {
                    data,
                    metrics: metrics.clone(),
                    current: 0,
                },
                metrics,
            )
        }
    }

    impl crate::data_source::ToIonDataSource for TestIonSource {
        type DataSource = Self;

        fn to_ion_data_source(self) -> Self::DataSource {
            self
        }
    }

    impl std::io::BufRead for TestIonSource {
        fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
            Ok(self.data[self.current..].as_bytes())
        }

        fn consume(&mut self, amt: usize) {
            self.current += amt;
        }
    }

    impl std::io::Read for TestIonSource {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            let size = std::cmp::min(self.data.len() - self.current, buf.len());
            buf[..size].copy_from_slice(&self.data.as_bytes()[self.current..self.current + size]);
            self.metrics.borrow_mut().bytes_read += size;
            self.current += size;
            Ok(size)
        }
    }

    #[test]
    // This test validates that the last value in the text buffer is not consumed unless the user
    // has flagged the stream as being completely loaded.
    fn verify_end_of_stream() -> IonResult<()> {
        let (source, metrics) = TestIonSource::new("2002-10-15");

        // create our reader with a starting buffer size of 4. This verifies that the reader will
        // return an incomplete if the token read completely consumes the buffer, since 4
        // characters would allow the reader to parse an integer from the year.
        let mut reader = RawTextReader::new_with_size(source, 4)?;
        assert_eq!(4, metrics.borrow().bytes_read); // Verify we read the buffer size specified.

        let result = reader.next();
        assert!(result.is_ok());
        assert_eq!(10, metrics.borrow().bytes_read);

        Ok(())
    }

    #[test]
    fn incomplete_string() -> IonResult<()> {
        const BUF_SIZE: usize = 12;
        const SOURCE: &str = "\"hello world\"";

        // We create a reader that will read the first 12 bytes of the string. When the reader
        // parses this value it should result in an incomplete error from the non-blocking reader,
        // which will cause the blocking reader to read more data, and retry.
        let (source, metrics) = TestIonSource::new(SOURCE);
        let mut reader = RawTextReader::new_with_size(source, BUF_SIZE)?;
        assert_eq!(BUF_SIZE, metrics.borrow().bytes_read);

        // Since the buffer will contain a fully delimited value we will be able to read the string
        // without marking the stream as complete.
        let result = reader.next();
        assert!(result.is_ok());
        assert_eq!(SOURCE.len(), metrics.borrow().bytes_read);
        assert_eq!(IonType::String, reader.ion_type().unwrap());

        let result = reader.next();
        assert!(result.is_ok());
        assert_eq!(None, reader.ion_type());

        Ok(())
    }

    #[test]
    fn incomplete_symbol() -> IonResult<()> {
        const BUF_SIZE: usize = 3;
        const SOURCE: &str = "foo ";

        // We create a reader that will read the first 3 bytes of the string. When the reader
        // parses this value it should result in an incomplete error from the non-blocking reader,
        // which will cause the blocking reader to read more data, and retry.
        let (source, metrics) = TestIonSource::new(SOURCE);
        let mut reader = RawTextReader::new_with_size(source, BUF_SIZE)?;
        assert_eq!(BUF_SIZE, metrics.borrow().bytes_read);

        let result = reader.next();
        assert_eq!(SOURCE.len(), metrics.borrow().bytes_read);
        assert!(result.is_ok());
        assert_eq!(IonType::Symbol, reader.ion_type().unwrap());

        Ok(())
    }

    #[test]
    fn nested_struct() -> IonResult<()> {
        let (source, _metrics) = TestIonSource::new(
            r#"
                $ion_1_0
                {}
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
            "#,
        );
        let reader = &mut RawTextReader::new_with_size(source, 24)?;

        assert_eq!(reader.next().unwrap(), RawStreamItem::VersionMarker(1, 0));

        next_type(reader, IonType::Struct, false);

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
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 3);
        reader.step_out()?; // Step out of .[1].foo[1]
        reader.step_out()?; // Step out of .[1].foo

        next_type(reader, IonType::Struct, false);
        assert!(reader.field_name().is_ok());

        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);
        next_type(reader, IonType::SExp, false);
        reader.step_in()?;
        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);
        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);
        next_type(reader, IonType::Bool, false);
        assert!(reader.read_bool()?);
        // The reader is now at the second 'true' in the s-expression nested in 'bar'/'b'
        reader.step_out()?; // Step out of .[1].bar.b
        reader.step_out()?; // Step out of .[1].bar
        reader.step_out()?; // Step out of .[1]

        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 11);
        Ok(())
    }
}
