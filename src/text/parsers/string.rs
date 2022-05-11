use crate::text::parse_result::{fatal_parse_error, IonParseResult};
use crate::text::parsers::comments::whitespace_or_comments;
use crate::text::parsers::text_support::{
    escaped_char, escaped_newline, normalized_newline, string_fragment_or_mismatch, StringFragment,
};
use crate::text::parsers::WHITESPACE_CHARACTERS;
use crate::text::text_value::TextValue;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::char;
use nom::combinator::{map, not, opt, peek};
use nom::multi::{fold_many0, many1};
use nom::sequence::{delimited, terminated};
use nom::Err::Incomplete;
use nom::Needed;

/// Matches the text representation of a string value and returns the resulting [String]
/// as a [TextValue::String].
pub(crate) fn parse_string(input: &str) -> IonParseResult<TextValue> {
    alt((short_string, long_string))(input)
}

/// Matches a short string (e.g. `"Hello"`) and returns the resulting [String]
/// as a [TextValue::String].
fn short_string(input: &str) -> IonParseResult<TextValue> {
    map(delimited(char('"'), short_string_body, char('"')), |text| {
        TextValue::String(text)
    })(input)
}

/// Matches a long string (e.g. `'''Hello, '''\n'''World!'''`) and returns the resulting [String]
/// as a [TextValue::String].
fn long_string(input: &str) -> IonParseResult<TextValue> {
    // TODO: This parser allocates a Vec to hold each intermediate '''...''' string
    //       and then again to merge them into a finished product. These allocations
    //       could be removed with some refactoring.

    map(
        terminated(
            many1(terminated(
                delimited(tag("'''"), long_string_body, tag("'''")),
                opt(whitespace_or_comments),
            )),
            peek(not(tag("'''"))),
        ),
        |text| TextValue::String(text.join("")),
    )(input)
}

/// Matches the body of a long string fragment. (The `hello` in `'''hello'''`.)
fn long_string_body(input: &str) -> IonParseResult<String> {
    fold_many0(long_string_fragment, String::new, |mut string, fragment| {
        match fragment {
            StringFragment::EscapedNewline => {} // Discard escaped newlines
            StringFragment::EscapedChar(c) => string.push(c),
            StringFragment::Substring(s) => string.push_str(s),
        }
        string
    })(input)
}

/// Matches an escaped character or a substring without any escapes in a long string.
fn long_string_fragment(input: &str) -> IonParseResult<StringFragment> {
    alt((
        normalized_newline,
        escaped_newline,
        escaped_char,
        long_string_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next string fragment without escape sequences while also respecting the long
/// string delimiter (`'''`).
pub(in crate::text::parsers) fn long_string_fragment_without_escaped_text(
    input: &str,
) -> IonParseResult<StringFragment> {
    for (byte_index, character) in input.char_indices() {
        match character {
            '\\' | '\r' => {
                // Escapes and carriage returns are handled by other clob fragment parsers.
                // Return a match for everything leading up to this.
                return string_fragment_or_mismatch(input, byte_index);
            }
            '\'' => {
                // This might be the terminating `'''`. Look ahead to see if it's followed by two
                // more `'`s. If so, return a match for everything leading up to it.
                let remaining = &input[byte_index..];
                if remaining.starts_with("'''") {
                    return string_fragment_or_mismatch(input, byte_index);
                }
            }
            c if u32::from(c) < 0x20 && !WHITESPACE_CHARACTERS.contains(&c) => {
                return fatal_parse_error(
                    input,
                    "strings cannot contain unescaped control characters",
                );
            }
            _ => {
                // Any other character is allowed
            }
        };
    }
    // We never found an end-of-fragment; we need more input to tell if this is a valid string.
    Err(Incomplete(Needed::Unknown))
}

/// Matches the body of a short string. (The `hello` in `"hello"`.)
fn short_string_body(input: &str) -> IonParseResult<String> {
    fold_many0(
        short_string_fragment,
        String::new,
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
fn short_string_fragment(input: &str) -> IonParseResult<StringFragment> {
    alt((
        escaped_newline,
        escaped_char,
        short_string_fragment_without_escaped_text,
    ))(input)
}

/// Matches the next string fragment while respecting the short string delimiter (`"`).
pub(in crate::text::parsers) fn short_string_fragment_without_escaped_text(
    input: &str,
) -> IonParseResult<StringFragment> {
    for (byte_index, character) in input.char_indices() {
        match character {
            '\\' | '\r' | '\"' => {
                // Escapes and carriage returns are handled by other clob fragment parsers, while
                // a double quote (`"`) marks the end of this string fragment.
                // Return a match for everything leading up to this character.
                return string_fragment_or_mismatch(input, byte_index);
            }
            '\n' => {
                return fatal_parse_error(input, "short strings cannot contain unescaped newlines");
            }
            c if u32::from(c) < 0x20 && !WHITESPACE_CHARACTERS.contains(&c) => {
                return fatal_parse_error(
                    input,
                    "strings cannot contain unescaped control characters",
                );
            }
            _ => {
                // Any other character is allowed
            }
        };
    }
    // We never found an end-of-fragment; we need more input to tell if this is a valid string.
    Err(Incomplete(Needed::Unknown))
}

#[cfg(test)]
mod string_parsing_tests {
    use crate::text::parsers::string::parse_string;

    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;

    fn parse_equals(text: &str, expected: &str) {
        parse_test_ok(parse_string, text, TextValue::String(expected.to_owned()))
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
        // Unicode escape producing invalid surrogate
        parse_fails(r#"'''\ud800'''\n"#);
    }

    #[test]
    fn test_parse_long_strings() {
        // Long strings can have any number of segments separated by whitespace.
        // These test strings end in an integer so the parser knows the long string is done.
        parse_equals("'''''' 1", "");
        parse_equals("'''foo''' 1", "foo");
        parse_equals("'''foo bar baz''' 1", "foo bar baz");
        parse_equals("'''foo''' '''bar''' '''baz''' 1", "foobarbaz");
        parse_equals("'''foo'''\n\n\n'''bar'''\n\n\n'''baz''' 1", "foobarbaz");
        parse_equals(
            "'''\\x66oo''' '''\\u0062\\U00000061r''' '''\\x62\\U00000061z''' 1",
            "foobarbaz",
        );
    }

    #[test]
    fn long_string_escapes() {
        parse_equals(r#"'''foo\nbar''' '''\nbaz\n''' 1"#, "foo\nbar\nbaz\n");
        parse_equals("'''foo\\\r\nbar''' 1", "foobar"); // Escaped newline
    }
}
