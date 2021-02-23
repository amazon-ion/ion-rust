use crate::text::parsers::text_support::{escaped_char, escaped_newline, StringFragment};
use crate::text::parsers::whitespace;
use crate::text::TextStreamItem;
use nom::branch::alt;
use nom::bytes::streaming::{is_not, tag, take_until};
use nom::character::streaming::char;
use nom::combinator::{map, not, opt, peek, verify};
use nom::multi::{fold_many0, many1};
use nom::sequence::{delimited, terminated};
use nom::IResult;

/// Matches the text representation of a string value and returns the resulting [String]
/// as a [TextStreamItem::String].
pub(crate) fn parse_string(input: &str) -> IResult<&str, TextStreamItem> {
    alt((short_string, long_string))(input)
}

/// Matches a short string (e.g. `"Hello"`) and returns the resulting [String]
/// as a [TextStreamItem::String].
fn short_string(input: &str) -> IResult<&str, TextStreamItem> {
    map(delimited(char('"'), short_string_body, char('"')), |text| {
        TextStreamItem::String(text)
    })(input)
}

/// Matches a long string (e.g. `'''Hello, '''\n'''World!'''`) and returns the resulting [String]
/// as a [TextStreamItem::String].
fn long_string(input: &str) -> IResult<&str, TextStreamItem> {
    // TODO: This parser allocates a Vec to hold each intermediate '''...''' string
    //       and then again to merge them into a finished product. These allocations
    //       could be removed with some refactoring.
    map(
        terminated(
            many1(terminated(
                delimited(tag("'''"), long_string_body, tag("'''")),
                opt(whitespace),
            )),
            peek(not(tag("'''"))),
        ),
        |text| {
            println!("Long string parts: {:?}", &text);
            TextStreamItem::String(text.join(""))
        },
    )(input)
}

/// Matches the body of a long string fragment. (The `hello` in `'''hello'''`.)
fn long_string_body(input: &str) -> IResult<&str, String> {
    fold_many0(
        long_string_fragment,
        String::new(),
        |mut string, fragment| {
            match fragment {
                StringFragment::EscapedNewline => {} // Discard escaped newlines
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::Substring(s) => string.push_str(s),
            }
            string
        },
    )(input)
}

/// Matches an escaped character or a substring without any escapes in a long string.
fn long_string_fragment(input: &str) -> IResult<&str, StringFragment> {
    alt((
        escaped_newline,
        escaped_char,
        long_string_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next string fragment while respecting the long string delimiter (`'''`).
fn long_string_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
    map(verify(take_until("'''"), |s: &str| !s.is_empty()), |text| {
        StringFragment::Substring(text)
    })(input)
}

/// Matches the body of a short string. (The `hello` in `"hello"`.)
fn short_string_body(input: &str) -> IResult<&str, String> {
    fold_many0(
        short_string_fragment,
        String::new(), // TODO: Reusable buffer
        |mut string, fragment| {
            match fragment {
                StringFragment::EscapedNewline => {} // Discard escaped newlines
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::Substring(s) => string.push_str(s),
            }
            string
        },
    )(input)
}

/// Matches an escaped character or a substring without any escapes in a short string.
fn short_string_fragment(input: &str) -> IResult<&str, StringFragment> {
    alt((
        escaped_newline,
        escaped_char,
        short_string_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next string fragment while respecting the short string delimiter (`"`).
fn short_string_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
    map(verify(is_not("\"\\\""), |s: &str| !s.is_empty()), |text| {
        StringFragment::Substring(text)
    })(input)
}

#[cfg(test)]
mod string_parsing_tests {
    use crate::text::parsers::string::parse_string;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::TextStreamItem;

    fn parse_equals(text: &str, expected: &str) {
        parse_test_ok(
            parse_string,
            text,
            TextStreamItem::String(expected.to_owned()),
        )
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_string, text)
    }

    #[test]
    fn test_parse_short_strings() {
        parse_equals("\"\" ", "");
        parse_equals("\"Hello, world!\" ", "Hello, world!");
        // Escape literals
        parse_equals("\"Hello\nworld!\" ", "Hello\nworld!");
        parse_equals("\"Hello\tworld!\" ", "Hello\tworld!");
        parse_equals("\"\\\"Hello, world!\\\"\" ", "\"Hello, world!\"");
        // 2-digit Unicode hex escape sequences
        parse_equals("\"\\x48ello, \\x77orld!\" ", "Hello, world!");
        // 4-digit Unicode hex escape sequences
        parse_equals("\"\\u0048ello, \\u0077orld!\" ", "Hello, world!");
        // 8-digit Unicode hex escape sequences
        parse_equals("\"\\U00000048ello, \\U00000077orld!\" ", "Hello, world!");
        // Escaped newlines are discarded
        parse_equals("\"Hello,\\\n world!\" ", "Hello, world!");

        // Missing quotes
        parse_fails("Hello, world ");
        // Missing closing quote
        parse_fails("\"Hello, world ");
        // Leading whitespace not accepted
        parse_fails(" \"Hello, world\" ");
    }

    #[test]
    fn test_parse_long_strings() {
        // Long strings can have any number of segments separated by whitespace.
        // These test strings end in an integer so the parser knows the long string is done.
        parse_equals("'''foo''' 1", "foo");
        parse_equals("'''foo bar baz''' 1", "foo bar baz");
        parse_equals("'''foo''' '''bar''' '''baz''' 1", "foobarbaz");
        parse_equals("'''foo'''\n\n\n'''bar'''\n\n\n'''baz''' 1", "foobarbaz");
        parse_equals(
            "'''\\x66oo''' '''\\u0062\\U00000061r''' '''\\x62\\U00000061z''' 1",
            "foobarbaz",
        );
    }
}
