use nom::branch::alt;
use nom::combinator::opt;
use nom::Err::Incomplete;
use nom::IResult;
use nom::sequence::preceded;

use crate::result::IonResult;
use crate::text::parsers::blob::parse_blob;
use crate::text::parsers::boolean::parse_boolean;
use crate::text::parsers::decimal::parse_decimal;
use crate::text::parsers::float::parse_float;
use crate::text::parsers::integer::parse_integer;
use crate::text::parsers::null::parse_null;
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::parse_symbol;
use crate::text::parsers::timestamp::parse_timestamp;
use crate::text::parsers::whitespace;
use crate::text::TextStreamItem;

// TODO: Implement a full text reader.
//       This implementation is a placeholder. It currently capable of reading a single top-level scalar
//       of any type. It cannot iterate, step in/out, or handle annotations.
//       It currently operates an an input of [String]. A full implementation will instead have
//       an input source implementing [io::BufRead] and pull in several lines of text at a time,
//       appending more to the working String when an attempt at parsing a value returns
//       `nom::error::Incomplete(_)`.
//       For other String streaming alternatives, see:
//       See: https://crates.io/crates/encoding_rs_io

pub struct TextReader {
    input: String,
    current_item: Option<TextStreamItem>,
    bytes_read: usize,
}

impl TextReader {
    fn new(input: String) -> TextReader {
        TextReader {
            input,
            current_item: None,
            bytes_read: 0,
        }
    }

    fn stream_item(input: &str) -> IResult<&str, TextStreamItem> {
        alt((
            parse_null,
            parse_boolean,
            parse_integer,
            parse_float,
            parse_decimal,
            parse_timestamp,
            parse_string,
            parse_symbol,
            parse_blob,
        ))(input)
    }

    fn top_level_value(input: &str) -> IResult<&str, TextStreamItem> {
        preceded(
            opt(whitespace),
            Self::stream_item,
        )(input)
    }

    pub fn bytes_read(&self) -> usize {
        self.bytes_read
    }

    //TODO: TextStreamItem is an internal data type and should not be part of the public API.
    //      This method is currently private and only usable in this module's unit tests.
    fn next(&mut self) -> IonResult<TextStreamItem> {
        let input = &self.input[self.bytes_read..];
        let length_before_parse = input.len();
        let (remaining_text, item) = match Self::top_level_value(input) {
             Err(Incomplete(needed)) => {
                 panic!("Incomplete data: {:?}", needed);
                 // TODO: 'Incomplete' indicates that the current input string ends with a partial
                 //       value. In most cases, this just means we need to read more text from input
                 //       and append it to the end of the input string before trying again.
            },
            Ok((remaining_text, item)) => {
                (remaining_text, item)
            },
            Err(_) => {
                panic!("Could not parse provided input.");
            }
        };
        self.bytes_read += length_before_parse - remaining_text.len();
        Ok(item)
    }
}

#[cfg(test)]
mod reader_tests {
    use crate::IonType;
    use crate::result::IonResult;
    use crate::text::parsers::unit_test_support::parse_unwrap;
    use crate::text::reader::TextReader;
    use crate::text::TextStreamItem;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;

    fn top_level_value_test(ion_text: &str, expected: TextStreamItem) {
        let mut reader = TextReader::new(ion_text.to_owned());
        let item = reader.next().unwrap();
        assert_eq!(item, expected);
    }

    #[test]
    fn test_read_single_top_level_values() -> IonResult<()>{
        let tlv = top_level_value_test;
        tlv(" null ", TextStreamItem::Null(IonType::Null));
        tlv(" null.string ", TextStreamItem::Null(IonType::String));
        tlv(" true ", TextStreamItem::Boolean(true));
        tlv(" false ", TextStreamItem::Boolean(false));
        tlv(" 738 ", TextStreamItem::Integer(738));
        tlv(" 2.5e0 ", TextStreamItem::Float(2.5));
        tlv(" 2.5 ", TextStreamItem::Decimal(Decimal::new(25, -1)));
        tlv(" 2007-07-12T ", TextStreamItem::Timestamp(Timestamp::with_ymd(2007, 7, 12).build()?));
        tlv(" foo ", TextStreamItem::Symbol("foo".to_owned()));
        tlv(" \"hi!\" ", TextStreamItem::String("hi!".to_owned()));
        tlv(" {{ZW5jb2RlZA==}} ", TextStreamItem::Blob(Vec::from("encoded".as_bytes())));
        Ok(())
    }

    #[test]
    fn test_detect_stream_item_types() {
        let expect_type = |text: &str, expected_ion_type: IonType| {
            let value = parse_unwrap(TextReader::stream_item, text);
            assert_eq!(expected_ion_type, value.ion_type().unwrap());
        };

        expect_type("null ", IonType::Null);
        expect_type("null.timestamp ", IonType::Timestamp);
        expect_type("null.list ", IonType::List);
        expect_type("true ", IonType::Boolean);
        expect_type("false ", IonType::Boolean);
        expect_type("5 ", IonType::Integer);
        expect_type("-5 ", IonType::Integer);
        expect_type("5.0 ", IonType::Decimal);
        expect_type("-5.0 ", IonType::Decimal);
        expect_type("5.0d0 ", IonType::Decimal);
        expect_type("-5.0d0 ", IonType::Decimal);
        expect_type("5.0e0 ", IonType::Float);
        expect_type("-5.0e1_024 ", IonType::Float);
        expect_type("\"foo\"", IonType::String);
        expect_type("'''foo''' 1", IonType::String);
        expect_type("foo ", IonType::Symbol);
        expect_type("'foo bar baz' ", IonType::Symbol);
        expect_type("2021T ", IonType::Timestamp);
        expect_type("2021-02T ", IonType::Timestamp);
        expect_type("2021-02-08T ", IonType::Timestamp);
        expect_type("2021-02-08T12:30Z ", IonType::Timestamp);
        expect_type("2021-02-08T12:30:02-00:00 ", IonType::Timestamp);
        expect_type("2021-02-08T12:30:02.111-00:00 ", IonType::Timestamp);
    }
}
