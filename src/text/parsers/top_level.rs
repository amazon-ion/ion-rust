use crate::text::parsers::annotations::parse_annotations;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::complete::multispace0;
use nom::combinator::map_opt;
use nom::multi::many1;
use nom::sequence::{delimited, pair, preceded};
use nom::{IResult, Parser};

use crate::text::parsers::blob::parse_blob;
use crate::text::parsers::boolean::parse_boolean;
use crate::text::parsers::clob::parse_clob;
use crate::text::parsers::comments::parse_comment;
use crate::text::parsers::containers::{parse_container_end, parse_container_start};
use crate::text::parsers::decimal::parse_decimal;
use crate::text::parsers::float::parse_float;
use crate::text::parsers::integer::parse_integer;
use crate::text::parsers::null::parse_null;
use crate::text::parsers::stream_item::{annotated_stream_item, stream_item};
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::parse_symbol;
use crate::text::parsers::timestamp::parse_timestamp;
use crate::text::TextStreamItem;
use crate::value::owned::OwnedSymbolToken;

/// Matches an optional series of annotations and a TextStreamItem at the beginning of the given
/// string. If there are no annotations (or the TextStreamItem found cannot have annotations), the
/// annotations [Vec] will be empty.
pub(crate) fn top_level_stream_item(
    input: &str,
) -> IResult<&str, (Vec<OwnedSymbolToken>, TextStreamItem)> {
    preceded(
        // Allow any amount of whitespace followed by...
        multispace0,
        // either...
        alt((
            // An annotated value or...
            annotated_stream_item,
            // An empty Vec paired with an unannotated value.
            // `Vec::new()` does not allocate, so calling this for each item is cheap.
            stream_item.map(|x| (Vec::new(), x)),
        )),
    )(input)
}

#[cfg(test)]
mod parse_stream_item_tests {
    use super::*;
    use crate::text::parsers::unit_test_support::parse_unwrap;
    use crate::types::SymbolId;
    use crate::value::owned::{local_sid_token, text_token};
    use crate::IonType;
    use rstest::*;

    // Unit test helper; converts strings into OwnedSymbolTokens
    fn text_tokens(strs: &[&str]) -> Vec<OwnedSymbolToken> {
        return strs.iter().map(|s| text_token(*s)).collect();
    }

    #[test]
    fn test_detect_stream_item_types() {
        let expect_option_type = |text: &str, expected: Option<IonType>| {
            let value = parse_unwrap(stream_item, text);
            assert_eq!(expected, value.ion_type());
        };

        let expect_type = |text: &str, expected_ion_type: IonType| {
            expect_option_type(text, Some(expected_ion_type))
        };

        let expect_no_type = |text: &str| expect_option_type(text, None);

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
        expect_type("{{\"hello\"}}", IonType::Clob);

        // End of...
        expect_no_type("} "); // struct
        expect_no_type("] "); // list
        expect_no_type(") "); // s-expression
    }

    #[rstest]
    // For these tests, the input text must end in an unrelated value so the parser knows that
    // the first value is complete. For example, it's not possible to know whether this Ion data:
    //     foo::bar::baz
    // is the symbol 'baz' with the annotations 'foo' and 'bar', or if it's actually
    // _three annotations_ on a value that we're still waiting to read from the stream.
    // On the other hand, a parser looking at the same data with a trailing value like this:
    //     foo::bar::baz END
    // can easily tell that 'foo' and 'bar' are annotations and 'baz' is the value.
    // Here, 'END' is simply an unrelated symbol value that the parser knows to ignore.
    #[case("foo::bar::baz END", &["foo", "bar"], TextStreamItem::Symbol(text_token("baz")))]
    #[case("foo::bar::baz END", &["foo", "bar"], TextStreamItem::Symbol(text_token("baz")))]
    #[case("foo::'bar'::7 END", &["foo", "bar"], TextStreamItem::Integer(7))]
    #[case("'foo'::'bar'::{ END", &["foo", "bar"], TextStreamItem::StructStart)]
    #[case("'foo bar'::false END", &["foo bar"], TextStreamItem::Boolean(false))]
    fn test_parse_annotated_stream_item(
        #[case] text: &str,
        #[case] expected_annotations: &[&str],
        #[case] expected_item: TextStreamItem,
    ) {
        assert_eq!(
            annotated_stream_item(text).unwrap().1,
            (text_tokens(expected_annotations), expected_item)
        );
    }
}
