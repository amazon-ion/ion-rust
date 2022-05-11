use crate::text::parse_result::{IonParseResult, UpgradeIResult};
use crate::text::parsers::string::long_string_fragment_without_escaped_text;
use crate::text::parsers::text_support::{
    escaped_char_no_unicode, escaped_newline, StringFragment,
};
use crate::text::parsers::whitespace;
use crate::text::text_value::TextValue;
use nom::branch::alt;
use nom::bytes::streaming::{is_not, tag};
use nom::character::streaming::char;
use nom::combinator::{map, not, opt, peek, verify};
use nom::multi::{fold_many0, many1};
use nom::sequence::{delimited, terminated};
use std::str;

/// Matches the text representation of a clob value and returns the resulting [Clob]
/// as a [TextValue::Clob].
pub(crate) fn parse_clob(input: &str) -> IonParseResult<TextValue> {
    map(
        delimited(
            tag("{{").upgrade(),
            delimited(opt(whitespace), parse_clob_body, opt(whitespace)),
            tag("}}").upgrade(),
        ),
        |text| text,
    )(input)
}

/// Matches the body of a clob value (e.g. "Hello" in {{"Hello"}})
fn parse_clob_body(input: &str) -> IonParseResult<TextValue> {
    alt((short_clob, long_clob))(input)
}

/// Matches a short clob (e.g. `"Hello"`) and returns the resulting [Clob]
/// as a [TextValue::Clob].
fn short_clob(input: &str) -> IonParseResult<TextValue> {
    map(delimited(char('"'), short_clob_body, char('"')), |text| {
        TextValue::Clob(text)
    })(input)
}

use crate::text::parse_result::UpgradeParser;

fn long_clob(input: &str) -> IonParseResult<TextValue> {
    // TODO: This parser allocates a Vec to hold each intermediate '''...''' string
    //       and then again to merge them into a finished product. These allocations
    //       could be removed with some refactoring.
    map(
        terminated(
            many1(terminated(
                delimited(tag("'''"), long_clob_body, tag("'''")),
                opt(whitespace),
            )),
            peek(not(tag("'''"))),
        ),
        |text| {
            let mut text_vec = Vec::new();
            for value in text {
                text_vec.extend(value);
            }
            TextValue::Clob(text_vec)
        },
    )(input)
}

/// Matches the body of a long clob fragment. (The `hello` in `'''hello'''`.)
fn long_clob_body(input: &str) -> IonParseResult<Vec<u8>> {
    fold_many0(long_clob_fragment, Vec::new, |mut string, fragment| {
        match fragment {
            StringFragment::EscapedNewline => {} // Discard escaped newlines
            StringFragment::EscapedChar(c) => string.push(c as u8),
            StringFragment::Substring(s) => string.extend(s.as_bytes()),
        }
        string
    })(input)
}

/// Matches an escaped character or a substring without any escapes in a long clob.
fn long_clob_fragment(input: &str) -> IonParseResult<StringFragment> {
    alt((
        escaped_newline,
        escaped_char_no_unicode,
        long_clob_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next string fragment while respecting the long clob delimiter (`'''`).
fn long_clob_fragment_without_escaped_text(input: &str) -> IonParseResult<StringFragment> {
    // Matches the head of the string up to the next `'''` or `\`.
    // Will not match if the `'''` or `\` is at the very beginning of the string.
    long_string_fragment_without_escaped_text(input)
}

/// Matches the body of a short clob. (The `hello` in `"hello"`.)
fn short_clob_body(input: &str) -> IonParseResult<Vec<u8>> {
    fold_many0(short_clob_fragment, Vec::new, |mut string, fragment| {
        match fragment {
            StringFragment::EscapedNewline => {} // Discard escaped newlines
            StringFragment::EscapedChar(c) => string.push(c as u8),
            StringFragment::Substring(s) => string.extend_from_slice(s.as_bytes()),
        }
        string
    })(input)
}

/// Matches an escaped character or a substring without any escapes in a short clob.
fn short_clob_fragment(input: &str) -> IonParseResult<StringFragment> {
    alt((
        escaped_newline,
        escaped_char_no_unicode,
        short_clob_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next string fragment while respecting the short clob delimiter (`"`).
fn short_clob_fragment_without_escaped_text(input: &str) -> IonParseResult<StringFragment> {
    map(verify(is_not("\"\\\""), |s: &str| !s.is_empty()), |text| {
        StringFragment::Substring(text)
    })(input)
    .upgrade()
}

#[cfg(test)]
mod clob_parsing_tests {
    use std::iter::FromIterator;

    use crate::text::parsers::clob::parse_clob;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;

    fn parse_equals<A: AsRef<[u8]>>(text: &str, expected: A) {
        let data = Vec::from_iter(expected.as_ref().iter().copied());
        parse_test_ok(parse_clob, text, TextValue::Clob(data))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_clob, text)
    }

    #[test]
    fn test_parse_clobs() {
        // parse tests for short clob
        parse_equals("{{\"hello\"}}\n", "hello");
        parse_equals("{{\"a\\\"'\\n\"}}\n", "a\"\'\n");
        parse_equals("{{\"\\xe2\\x9d\\xa4\\xef\\xb8\\x8f\"}}\n", "❤️");

        // parse tests for long clob
        parse_equals("{{'''Hello''' '''world'''}}", "Helloworld");
        parse_equals("{{'''Hello world'''}}", "Hello world");
        parse_equals("{{'''\\xe2\\x9d\\xa4\\xef\\xb8\\x8f\'''}}", "❤️");

        // Clobs represent text of some encoding, but it may or may not be a flavor of Unicode.
        // As such, clob syntax does not support Unicode escape sequences like `\u` or `\U`.
        // Byte literals may be written using `\x`, however.
        parse_fails(r#"{{ "\u3000" }}"#);
    }
}
