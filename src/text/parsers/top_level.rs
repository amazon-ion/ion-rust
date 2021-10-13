use nom::branch::alt;
use nom::sequence::preceded;
use nom::{IResult, Parser};

use crate::text::parsers::comments::whitespace_or_comments;
use crate::text::parsers::value::{annotated_value, value};
use crate::text::text_value::AnnotatedTextValue;

/// Matches an optional series of annotations and a TextValue at the beginning of the given
/// string. If there are no annotations (or the TextValue found cannot have annotations), the
/// annotations [Vec] will be empty.
pub(crate) fn top_level_value(input: &str) -> IResult<&str, AnnotatedTextValue> {
    preceded(
        // Allow any amount of whitespace followed by...
        whitespace_or_comments,
        // either...
        alt((
            // An annotated value or...
            annotated_value,
            // An empty Vec paired with an unannotated value.
            // `Vec::new()` does not allocate, so calling this for each value is cheap.
            value.map(|x| x.without_annotations()),
        )),
    )(input)
}

#[cfg(test)]
mod parse_top_level_values_tests {
    use rstest::*;

    use crate::text::parsers::unit_test_support::parse_unwrap;
    use crate::text::text_value::TextValue;
    use crate::value::owned::{text_token, OwnedSymbolToken};
    use crate::IonType;

    use super::*;

    // Unit test helper; converts strings into OwnedSymbolTokens
    fn text_tokens(strs: &[&str]) -> Vec<OwnedSymbolToken> {
        return strs.iter().map(|s| text_token(*s)).collect();
    }

    #[test]
    fn test_detect_value_types() {
        let expect_type = |text: &str, expected_ion_type: IonType| {
            let value = parse_unwrap(value, text);
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
    #[case("foo::bar::baz END", &["foo", "bar"], TextValue::Symbol(text_token("baz")))]
    #[case("foo::bar::baz END", &["foo", "bar"], TextValue::Symbol(text_token("baz")))]
    #[case("foo::'bar'::7 END", &["foo", "bar"], TextValue::Integer(7))]
    #[case("'foo'::'bar'::{ END", &["foo", "bar"], TextValue::StructStart)]
    #[case("'foo bar'::false END", &["foo bar"], TextValue::Boolean(false))]
    fn test_parse_annotated_value(
        #[case] text: &str,
        #[case] expected_annotations: &[&str],
        #[case] expected_value: TextValue,
    ) {
        assert_eq!(
            annotated_value(text).unwrap().1,
            expected_value.with_annotations(expected_annotations)
        );
    }
}
