use crate::text::parsers::timestamp::parse_timestamp;
use crate::text::parsers::integer::parse_integer;
use crate::text::parsers::boolean::parse_boolean;
use crate::text::parsers::float::parse_float;
use crate::text::parsers::null::parse_null;
use crate::text::parsers::decimal::parse_decimal;
use crate::text::parsers::symbol::parse_symbol;
use crate::text::parsers::string::parse_string;
use crate::text::TextStreamItem;
use crate::text::parsers::blob::parse_blob;
use nom::branch::alt;
use nom::IResult;
// TODO: Modify impl to match this description.
//       See: https://crates.io/crates/encoding_rs_io
// We have a String buffer that we fill periodically by reading from input.
// We read the string N lines-at-a-time.
// If a read comes back as incomplete, we clear the buffer of any already-processed text
// and then append the next N lines from input. Then we try the same read again.

pub struct TextReader {
    input: String,
}

//TODO: Explanatory note about how `recognize` works and how to combine it with many0_count and many1_count.

impl TextReader {
    fn buffer(&self) -> &str {
        self.input.as_str()
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
}

#[cfg(test)]
mod reader_tests {
    use crate::IonType;
    use crate::text::parsers::unit_test_support::parse_unwrap;
    use crate::text::reader::TextReader;

    #[test]
    fn test_detect_stream_item_types() {
        let expect_type = |text: &str, expected_ion_type: IonType| {
            let value = parse_unwrap(TextReader::stream_item, text);
            assert_eq!(expected_ion_type, value.ion_type());
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
        expect_type("5.0e ", IonType::Float);
        expect_type("-5.0e ", IonType::Float);
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
