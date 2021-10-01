use crate::text::TextStreamItem;
use nom::branch::alt;
use nom::bytes::streaming::{is_not, tag, take_until};
use nom::combinator::map;
use nom::sequence::{delimited, preceded};
use nom::IResult;

/// Matches a `/* multiline */` or `// rest-of-line` comment.
pub(crate) fn parse_comment(input: &str) -> IResult<&str, TextStreamItem> {
    map(alt((rest_of_line_comment, multiline_comment)), |_text| {
        TextStreamItem::Comment
    })(input)
}

/// Matches a rest-of-line comment. Returns the text of the comment without the leading "//".
/// If no closing newline is found, this will return `Incomplete`.
fn rest_of_line_comment(input: &str) -> IResult<&str, &str> {
    preceded(
        // Matches a leading "//"...
        tag("//"),
        // ...followed by any characters that are not a '\r' or '\n'.
        is_not("\r\n"), // Note that this will not consume the newline.
    )(input)
}

/// Matches a multiline comment. Returns the text of the comment without the
/// delimiting "/*" and "*/". If no closing "*/" is found, this will return `Incomplete`.
fn multiline_comment(input: &str) -> IResult<&str, &str> {
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
    use crate::text::TextStreamItem;
    use rstest::*;

    #[rstest]
    #[case("//hello!\n", "hello!")]
    #[case("//😎 😎 😎\n", "😎 😎 😎")]
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
    #[case("//hello!\n")]
    #[case("//😎 😎 😎\n")]
    #[case("/*hello!*/")]
    #[case("/*foo\nbar\nbaz*/")]
    fn test_parse_comment(#[case] text: &str) {
        assert_eq!(parse_comment(text).unwrap().1, TextStreamItem::Comment);
    }
}
