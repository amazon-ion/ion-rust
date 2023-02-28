use crate::text::parse_result::{IonParseResult, UpgradeIResult};
use crate::text::parsers::whitespace;

use nom::branch::alt;
use nom::bytes::streaming::{is_not, tag, take_until};
use nom::character::streaming::one_of;
use nom::combinator::{peek, recognize, value};
use nom::multi::many0_count;
use nom::sequence::{delimited, preceded};

/// Matches any number of consecutive `/* multiline */` or `// rest-of-line` comments with any
/// amount of leading or trailing whitespace.
pub(crate) fn whitespace_or_comments(input: &str) -> IonParseResult<&str> {
    recognize(many0_count(alt((
        // At least one character of whitespace...
        whitespace, // ...or a comment of any format.
        comment,
    ))))(input)
}

/// Matches a `/* multiline */` or `// rest-of-line` comment.
pub(crate) fn comment(input: &str) -> IonParseResult<&str> {
    alt((rest_of_line_comment, multiline_comment))(input)
}

/// Matches a rest-of-line comment. Returns the text of the comment without the leading "//".
/// If no closing newline is found, this will return `Incomplete`.
fn rest_of_line_comment(input: &str) -> IonParseResult<&str> {
    preceded(
        // Matches a leading "//"...
        tag("//"),
        // ...followed by either...
        alt((
            // ...one or more non-EOL characters...
            is_not("\r\n"),
            // ...or any EOL character.
            value("", peek(recognize(one_of("\r\n")))),
            // In either case, the line ending will not be consumed.
        )),
    )(input)
    .upgrade()
}

/// Matches a multiline comment. Returns the text of the comment without the
/// delimiting "/*" and "*/". If no closing "*/" is found, this will return `Incomplete`.
fn multiline_comment(input: &str) -> IonParseResult<&str> {
    delimited(
        // Matches a leading "/*"
        tag("/*"),
        // Any number of non-"*/" characters
        take_until("*/"),
        // and then a closing "*/"
        tag("*/"),
    )(input)
}

#[cfg(test)]
pub(crate) mod comment_parser_tests {
    use super::*;
    use rstest::*;

    #[rstest]
    #[case("//hello!\n", "hello!")]
    #[case("//😎 😎 😎\n", "😎 😎 😎")]
    #[case("//\n ", "")] // Empty comments are allowed
    #[case("//\t   \n ", "\t   ")] // Whitespace is allowed
    #[should_panic]
    #[case("// no newline ", "<should panic>")]
    fn test_parse_rest_of_line_comment(#[case] text: &str, #[case] expected: &str) {
        assert_eq!(rest_of_line_comment(text).unwrap().1, expected);
    }

    #[rstest]
    #[case("/*hello!*/", "hello!")]
    #[case("/*foo\nbar\nbaz*/", "foo\nbar\nbaz")]
    #[should_panic]
    #[case("/* no closing tag", "<should panic>")]
    fn test_parse_multiline_comment(#[case] text: &str, #[case] expected: &str) {
        assert_eq!(multiline_comment(text).unwrap().1, expected);
    }

    #[rstest]
    #[case("//hello!\n", "hello!")]
    #[case("//😎 😎 😎\n", "😎 😎 😎")]
    #[case("/*hello!*/", "hello!")]
    #[case("/*foo\nbar\nbaz*/", "foo\nbar\nbaz")]
    fn test_parse_comment(#[case] text: &str, #[case] expected: &str) {
        assert_eq!(comment(text).unwrap().1, expected);
    }

    #[rstest]
    #[case(" //hello!\n0", "0")]
    #[case(" //foo\n//bar\nbaz\n", "baz\n")]
    #[case(" /*hello!*/5", "5")]
    #[case(" /*foo\nbar\nbaz*/\n//foo\ntrue", "true")]
    fn test_parse_whitespace_or_comments(#[case] text: &str, #[case] remaining: &str) {
        // The unwrap() requires the parser to succeed. We're comparing the remaining unmatched
        // part of the input because it's shorter.
        assert_eq!(whitespace_or_comments(text).unwrap().0, remaining);
    }
}
