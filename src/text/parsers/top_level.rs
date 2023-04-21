use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::{digit0, one_of};
use nom::combinator::{map, not, recognize};

use crate::text::parse_result::{IonParseResult, OrFatalParseError, UpgradeIResult};
use crate::text::parsers::annotations::annotation_delimiter;
use nom::sequence::{delimited, pair, preceded, tuple};

use std::str::FromStr;

use crate::text::parsers::comments::whitespace_or_comments;

use crate::text::parsers::value::annotated_value;
use crate::text::text_value::AnnotatedTextValue;

/// Represents a single item that can appear at the top level of a text stream.
#[derive(PartialEq, Debug)]
pub(crate) enum RawTextStreamItem {
    /// An marker indicating that the stream's version is (major, minor).
    IonVersionMarker(u32, u32),
    /// A (possibly annotated) Ion value.
    AnnotatedTextValue(AnnotatedTextValue),
}

/// Matches an Ion version marker or a (possibly annotated) value.
pub(crate) fn stream_item(input: &str) -> IonParseResult<RawTextStreamItem> {
    alt((
        map(ion_version_marker, |(major, minor)| {
            RawTextStreamItem::IonVersionMarker(major, minor)
        }),
        map(top_level_value, |value| {
            RawTextStreamItem::AnnotatedTextValue(value)
        }),
    ))(input)
}

/// Matches an optional series of annotations and a TextValue at the beginning of the given
/// string. If there are no annotations (or the TextValue found cannot have annotations), the
/// annotations [Vec] will be empty.
pub(crate) fn top_level_value(input: &str) -> IonParseResult<AnnotatedTextValue> {
    preceded(
        // Allow any amount of whitespace followed by...
        whitespace_or_comments,
        // ...an optionally annotated value
        annotated_value,
    )(input)
}

pub(crate) fn version_int(input: &str) -> IonParseResult<&str> {
    recognize(pair(
        alt((tag("0"), recognize(one_of("123456789")))),
        digit0, // One or more digits 0-9
    ))(input)
    .upgrade()
}

/// Matches any amount of whitespace/comments followed by an identifier in the format
/// `$ion_MAJOR_MINOR`, in which `MAJOR` and `MINOR` are each decimal digit sequences representing
/// the major and minor version of the Ion stream to follow, respectively. See [version_int].
/// Note that this MUST be an identifier (i.e. an unquoted symbol) and not any other encoding of the
/// same symbol value. For more information see:
/// <https://amazon-ion.github.io/ion-docs/docs/symbols.html#ion-version-markers>
pub(crate) fn ion_version_marker(input: &str) -> IonParseResult<(u32, u32)> {
    // See if the input text matches an IVM. If not, return a non-fatal error.
    let (remaining_input, (_, major_text, _, minor_text)) = delimited(
        whitespace_or_comments,
        tuple((tag("$ion_"), version_int, tag("_"), version_int)),
        not(annotation_delimiter),
    )(input)?;

    // If the text matched but parsing that into a major and minor version fails, it's a fatal
    // error.

    let major_version = u32::from_str(major_text)
        .or_fatal_parse_error(major_text, "major version could not fit in a u32")?
        .1;
    let minor_version = u32::from_str(minor_text)
        .or_fatal_parse_error(minor_text, "minor version could not fit in a u32")?
        .1;

    Ok((remaining_input, (major_version, minor_version)))
}

#[cfg(test)]
mod parse_top_level_values_tests {
    use rstest::*;

    use crate::raw_symbol_token::{text_token, RawSymbolToken};
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok, parse_unwrap};
    use crate::text::parsers::value::value;
    use crate::text::text_value::TextValue;
    use crate::types::integer::Int;
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
        expect_type("true ", IonType::Bool);
        expect_type("false ", IonType::Bool);
        expect_type("5 ", IonType::Int);
        expect_type("-5 ", IonType::Int);
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
    #[case("foo::'bar'::7 END", &["foo", "bar"], TextValue::Int(Int::I64(7)))]
    #[case("'foo'::'bar'::{ END", &["foo", "bar"], TextValue::StructStart)]
    #[case("'foo bar'::false END", &["foo bar"], TextValue::Bool(false))]
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

    // Each of these input strings is followed by a ` 1` so the parser can definitively say the
    // IVM is not followed by a `::`, which would make it an annotation instead.
    #[rstest]
    #[case("$ion_1_0 1")]
    #[case("   \r  \t \n $ion_1_0 1")]
    #[case(" /*comment 1*/\n//comment 2\n   $ion_1_0 1")]
    fn test_parse_ion_1_0_ivm(#[case] text: &str) {
        parse_test_ok(ion_version_marker, text, (1, 0));
    }

    // Each of these input strings is followed by a ` 1` so the parser can definitively say the
    // IVM is not followed by a `::`, which would make it an annotation instead.
    #[rstest]
    #[case("$ion_1_1 1", (1, 1))]
    #[case("/*hello!*/ $ion_1_1 1", (1, 1))]
    #[case("$ion_2_0 1", (2, 0))]
    #[case("\n \n $ion_2_0 1", (2, 0))]
    #[case("$ion_5_8 1", (5, 8))]
    #[case("$ion_21_99 1", (21, 99))]
    fn test_parse_ivm_for_other_versions(#[case] text: &str, #[case] expected: (u32, u32)) {
        parse_test_ok(ion_version_marker, text, expected);
    }

    #[rstest]
    // An annotation, not an IVM
    #[case("$ion_1_0::foo")]
    // An annotation, not an IVM
    #[case("$ion_1_0      ::foo")]
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
