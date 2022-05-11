use std::str::FromStr;
use nom::bytes::streaming::tag;
use nom::sequence::{pair, preceded, tuple};
use nom::{alt, Err, IResult, many1_count};
use nom::branch::alt;
use nom::character::streaming::{digit0, digit1, one_of};
use nom::combinator::recognize;
use nom::error::{ErrorKind, make_error};
use nom::multi::many1_count;

use crate::text::parsers::comments::whitespace_or_comments;
use crate::text::parsers::digit;
use crate::text::parsers::numeric_support::base_10_integer_digits;
use crate::text::parsers::value::annotated_value;
use crate::text::text_value::AnnotatedTextValue;

/// Matches an optional series of annotations and a TextValue at the beginning of the given
/// string. If there are no annotations (or the TextValue found cannot have annotations), the
/// annotations [Vec] will be empty.
pub(crate) fn top_level_value(input: &str) -> IResult<&str, AnnotatedTextValue> {
    preceded(
        // Allow any amount of whitespace followed by...
        whitespace_or_comments,
        // ...an optionally annotated value
        annotated_value,
    )(input)
}

pub(crate) fn version_int(input: &str) -> IResult<&str, &str> {
    recognize(
        pair(
            alt((tag("0"), recognize(one_of("123456789")))),
            digit0 // One or more digits 0-9
        )
    )(input)
}

/// Matches any amount of whitespace/comments followed by an identifier in the format
/// `$ion_MAJOR_MINOR`, in which `MAJOR` and `MINOR` are each decimal digit sequences representing
/// the major and minor version of the Ion stream to follow, respectively. See [version_int].
/// Note that this MUST be an identifier (i.e. an unquoted symbol) and not any other encoding of the
/// same symbol value. For more information see:
/// https://amzn.github.io/ion-docs/docs/symbols.html#ion-version-markers
pub(crate) fn ion_version_marker(input: &str) -> IResult<&str, (u32, u32)> {
    // See if the input text matches an IVM. If not, return a non-fatal error.
    let (remaining_input, (_, major_text, _, minor_text)) = preceded(
        whitespace_or_comments,
        tuple((tag("$ion_"), version_int, tag("_"), version_int))
    )(input)?;

    // If the text matched but parsing that into a major and minor version fails, it's a fatal
    // error.

    // XXX: We cannot signal a fatal error by returning `nom::Err::Failure` here as we would in any
    // other case. Due to API limitations, it is currently not possible for the RawTextReader to
    // distinguish between a fatal error and a run-of-the-mill mismatch. For now, in the unlikely
    // event that the reader encounters an IVM with a major or minor version so large that they
    // cannot fit in a u32, we simply panic.
    // TODO: Create a custom parsing error type that allows us to bubble up more information.

    let major_version = u32::from_str(major_text)
        .unwrap_or_else(|e| panic!("IVM major version '{}' could not fit in a u32", major_text));

    let minor_version = u32::from_str(minor_text)
        .unwrap_or_else(|e| panic!("IVM minor version '{}' could not fit in a u32", minor_text));

    Ok((remaining_input, (major_version, minor_version)))
}

#[cfg(test)]
mod parse_top_level_values_tests {
    use rstest::*;

    use crate::raw_symbol_token::{text_token, RawSymbolToken};
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok, parse_unwrap};
    use crate::text::parsers::value::value;
    use crate::text::text_value::TextValue;
    use crate::types::integer::Integer;
    use crate::IonType;

    use super::*;

    // Unit test helper; converts strings into OwnedSymbolTokens
    fn text_tokens(strs: &[&str]) -> Vec<RawSymbolToken> {
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
    #[case("foo::'bar'::7 END", &["foo", "bar"], TextValue::Integer(Integer::I64(7)))]
    #[case("'foo'::'bar'::{ END", &["foo", "bar"], TextValue::StructStart)]
    #[case("'foo bar'::false END", &["foo bar"], TextValue::Boolean(false))]
    fn test_parse_annotated_value(
        #[case] text: &str,
        #[case] expected_annotations: &[&str],
        #[case] expected_value: TextValue,
    ) {
        parse_test_ok(
            annotated_value,
            text,
            expected_value.with_annotations(expected_annotations),
        );
    }

    #[rstest]
    #[case("$ion_1_0 ")]
    #[case("   \r  \t \n $ion_1_0 ")]
    #[case(" /*comment 1*/\n//comment 2\n   $ion_1_0 ")]
    fn test_parse_ion_1_0_ivm(#[case] text: &str) {
        parse_test_ok(ion_version_marker, text, (1, 0));
    }

    #[rstest]
    #[case("$ion_1_1 ", (1, 1))]
    #[case("/*hello!*/ $ion_1_1 ", (1, 1))]
    #[case("$ion_2_0 ", (2, 0))]
    #[case("\n \n $ion_2_0 ", (2, 0))]
    #[case("$ion_5_8 ", (5, 8))]
    #[case("$ion_21_99 ", (21, 99))]
    fn test_parse_ivm_for_other_versions(#[case] text: &str, #[case] expected: (u32, u32)) {
        parse_test_ok(ion_version_marker, text, expected);
    }

    #[rstest]
    // Quoted, therefore a symbol
    #[case("'$ion_1_0' ")]
    // Not a literal, therefore a symbol
    #[case("$2 ")]
    // Int
    #[case("5 ")]
    fn test_parse_bad_ivm(#[case] text: &str) {
        parse_test_err(ion_version_marker, text);
    }
}
