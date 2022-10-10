use std::io::BufRead;

use crate::data_source::ToIonDataSource;
use crate::raw_reader::RawStreamItem;
use crate::raw_symbol_token::RawSymbolToken;
use crate::result::IonResult;
use crate::stream_reader::IonReader;
use crate::types::timestamp::Timestamp;
use crate::{Decimal, Integer, IonError, IonType};

use crate::text::non_blocking::raw_text_reader::RawTextReader as NonBlockingReader;

const INITIAL_PARENTS_CAPACITY: usize = 16;
const READER_BUFFER_CAPACITY: usize = 1024 * 4;

pub struct RawTextReader<T: ToIonDataSource> {
    source: T::DataSource,
    // The inner non-blocking reader.
    reader: NonBlockingReader<Vec<u8>>,
    // The number of bytes fed to the inner reader.
    bytes_fed: usize,
}

/// Represents the final outcome of a [RawTextReader]'s attempt to parse the next value in the stream.
///
/// `IonParseResult<'a>` is not suitable for this purpose; its lifetime, `'a`, causes
/// the result to hold a reference to the [RawTextReader]'s buffer even after parsing has finished,
/// making it difficult to perform the necessary bookkeeping that follows finding the next value.
///
/// This type is intentionally limited in what it stores to avoid having a lifetime.
#[derive(Eq, PartialEq, Debug)]
pub(crate) enum RootParseResult<O> {
    Ok(O),
    Eof,
    NoMatch,
    Failure(String),
}

impl<T: ToIonDataSource> RawTextReader<T> {
    pub fn new(input: T) -> RawTextReader<T> {
        let buffer = Vec::with_capacity(READER_BUFFER_CAPACITY);
        RawTextReader {
            source: input.to_ion_data_source(),
            reader: NonBlockingReader::new(buffer),
            bytes_fed: 0,
        }
    }

    pub fn bytes_read(&self) -> usize {
        self.reader.bytes_read()
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
        self.bytes_fed += bytes_read;
        Ok(bytes_read)
    }

    // Returns the number of bytes unconsumed in the underlying reader.
    fn reader_remaining(&self) -> usize {
        self.bytes_fed - self.reader.bytes_read()
    }

    // Read data into the underlying non-blocking reader if we have more data in our source,
    // and the non-blocking reader has less than 1/4 of a full buffer.
    //
    // The 1/4 full buffer is fairly arbitrary, but provides some headroom so we're not constantly
    // reading, while at the same time ensuring we have enough data that we don't land on a false
    // type boundary.
    fn feed_if_needed(&mut self) -> IonResult<()> {
        let more_source = self.source.fill_buf().map(|b| !b.is_empty())?;
        let add_source = more_source && self.reader_remaining() < self.reader.buffer_size() / 4;
        if self.bytes_fed == 0 || add_source {
            let size = if self.bytes_fed == 0 {
                READER_BUFFER_CAPACITY
            } else {
                self.reader.buffer_size() - self.reader_remaining()
            };
            self.read_source(size)?;
        }
        Ok(())
    }
}

impl<T: ToIonDataSource> IonReader for RawTextReader<T> {
    type Item = RawStreamItem;
    type Symbol = RawSymbolToken;

    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn next(&mut self) -> IonResult<RawStreamItem> {
        self.feed_if_needed()?;

        match self.reader.next() {
            Err(err @ IonError::IncompleteText { .. }) => {
                // We received an incomplete.. and need more data..
                loop {
                    // If there is no more data to read, we need to bubble the incomplete up to the
                    // caller.
                    if 0 == self.read_source(1024)? {
                        return Err(err);
                    }

                    match self.reader.next() {
                        Err(IonError::IncompleteText { .. }) => (),
                        other => return other,
                    }
                }
            }
            other => other,
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

    fn read_integer(&mut self) -> IonResult<Integer> {
        self.reader.read_integer()
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
        self.feed_if_needed()?;
        match self.reader.step_in() {
            Err(err @ IonError::IncompleteText { .. }) => {
                // We received an incomplete.. and need more data..
                loop {
                    // If there is no more data to read, we need to bubble the incomplete up to the
                    // caller.
                    if 0 == self.read_source(1024)? {
                        return Err(err);
                    }

                    match self.reader.step_in() {
                        Err(IonError::IncompleteText { .. }) => (),
                        other => return other,
                    }
                }
            }
            other => other,
        }
    }

    fn step_out(&mut self) -> IonResult<()> {
        self.feed_if_needed()?;
        match self.reader.step_out() {
            Err(err @ IonError::IncompleteText { .. }) => {
                // We received an incomplete.. and need more data..
                loop {
                    // If there is no more data to read, we need to bubble the incomplete up to the
                    // caller.
                    if 0 == self.read_source(1024)? {
                        return Err(err);
                    }

                    match self.reader.step_out() {
                        Err(IonError::IncompleteText { .. }) => (),
                        other => return other,
                    }
                }
            }
            other => other,
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
    use crate::raw_reader::RawStreamItem;
    use crate::raw_symbol_token::{local_sid_token, text_token, RawSymbolToken};
    use crate::result::IonResult;
    use crate::stream_reader::IonReader;
    use crate::text::raw_text_reader::RawTextReader;
    use crate::text::text_value::IntoAnnotations;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::IonType;
    use crate::RawStreamItem::Nothing;

    fn next_type(reader: &mut RawTextReader<&str>, ion_type: IonType, is_null: bool) {
        assert_eq!(
            reader.next().unwrap(),
            RawStreamItem::nullable_value(ion_type, is_null)
        );
    }

    fn annotations_eq<I: IntoAnnotations>(reader: &mut RawTextReader<&str>, expected: I) {
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
        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.read_i64()?, 0);

        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.read_i64()?, 1);
        reader.step_out()?;
        // This should have skipped over the `2, 3` at the end of the list.
        next_type(reader, IonType::SExpression, false);
        // Don't step into the s-expression. Instead, skip over it.
        next_type(reader, IonType::Integer, false);
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
        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Integer, false);
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Integer, false);
        // The reader is now at the '2' nested inside of 'foo'
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Integer, false);
        next_type(reader, IonType::SExpression, false);
        reader.step_in()?;
        next_type(reader, IonType::Boolean, false);
        next_type(reader, IonType::Boolean, false);
        // The reader is now at the second 'true' in the s-expression nested in 'bar'/'b'
        reader.step_out()?;
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Integer, false);
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

        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.field_name()?, text_token("foo"));
        next_type(reader, IonType::Struct, false);
        assert_eq!(reader.field_name()?, text_token("bar"));
        reader.step_in()?;
        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.read_i64()?, 5);
        reader.step_out()?;
        assert_eq!(reader.next()?, RawStreamItem::Nothing);
        reader.step_out()?;
        next_type(reader, IonType::Integer, false);
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

        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Null, true);

        next_type(reader, IonType::Boolean, false);
        assert_eq!(reader.read_bool()?, true);

        next_type(reader, IonType::Integer, false);
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
        next_type(reader, IonType::SExpression, false);
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

        let reader = &mut RawTextReader::new(ion_data);

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, String::from("(486958) 2014 MU69"));

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2014, 6, 26).build()?
        );
        // TODO: Check for 'km' annotation after change to OwnedSymbolToken
        next_type(reader, IonType::Integer, false);
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

        let reader = &mut RawTextReader::new(ion_data);
        next_type(reader, IonType::Null, true);
        annotations_eq(reader, &["mercury"]);

        next_type(reader, IonType::Boolean, false);
        assert_eq!(reader.read_bool()?, true);
        annotations_eq(reader, &["venus", "earth"]);

        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.read_i64()?, 5);
        annotations_eq(reader, &[local_sid_token(17), text_token("mars")]);

        next_type(reader, IonType::Float, false);
        assert_eq!(reader.read_f64()?, 5.0f64);
        annotations_eq(reader, &["jupiter"]);

        next_type(reader, IonType::Decimal, false);
        assert_eq!(reader.read_decimal()?, Decimal::new(55i32, -1i64));
        annotations_eq(reader, &["saturn"]);

        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2021, 9, 25).build().unwrap()
        );
        annotations_eq(reader, &[100, 200, 300]);

        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, text_token("foo"));
        annotations_eq(reader, &["uranus"]);

        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, "hello".to_string());
        annotations_eq(reader, &["neptune"]);

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
        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.number_of_annotations(), 0);
        assert_eq!(reader.read_i64()?, 1);
        next_type(reader, IonType::Integer, false);
        annotations_eq(reader, &[77]);
        assert_eq!(reader.read_i64()?, 2);
        next_type(reader, IonType::Integer, false);
        assert_eq!(reader.number_of_annotations(), 0);
        assert_eq!(reader.read_i64()?, 3);
        assert_eq!(reader.next()?, Nothing);
        reader.step_out()?;

        // Reading an s-expression: haumea::makemake::eris::ceres::(++ -- &&&&&)
        next_type(reader, IonType::SExpression, false);
        annotations_eq(reader, &["haumea", "makemake", "eris", "ceres"]);
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
        let mut reader = RawTextReader::new(&pretty_ion[..]);
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::SExpression));
        reader.step_in()?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Struct));

        reader.step_in()?;
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Integer));
        assert_eq!(reader.field_name()?, RawSymbolToken::Text("a".to_string()));
        assert_eq!(reader.read_i64()?, 1);
        assert_eq!(reader.next()?, RawStreamItem::Value(IonType::Integer));
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
        let mut reader = RawTextReader::new(&pretty_ion[..]);
        let result = reader.next();
        println!("{:?}", result);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn annotation_nan() -> IonResult<()> {
        // The reader will reject the unquoted float keyword 'nan' when used as an annotation
        let pretty_ion = br#"
            nan::23
        "#;
        let mut reader = RawTextReader::new(&pretty_ion[..]);
        let result = reader.next();
        println!("{:?}", result);
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
        (0..4200).for_each(|_| source.push_str("A"));
        source.push_str(" }}");

        let mut reader = RawTextReader::new(&source[..]);
        let result = reader.next();
        println!("{:?}", result);
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
        (0..4200).for_each(|_| source.push_str("A"));

        let mut reader = RawTextReader::new(&source[..]);
        let result = reader.next();
        assert!(result.is_err());
        Ok(())
    }
}
