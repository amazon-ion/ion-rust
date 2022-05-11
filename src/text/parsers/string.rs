use crate::text::parsers::text_support::{escaped_char, escaped_newline, StringFragment};
use crate::text::parsers::whitespace;
use crate::text::text_value::TextValue;
use nom::branch::alt;
use nom::bytes::streaming::{is_not, tag};
use nom::character::streaming::char;
use nom::combinator::{map, not, opt, peek, verify};
use nom::error::{make_error, ErrorKind};
use nom::multi::{fold_many0, many1};
use nom::sequence::{delimited, terminated};
use nom::Err::Incomplete;
use nom::{IResult, Needed};

/// Matches the text representation of a string value and returns the resulting [String]
/// as a [TextValue::String].
pub(crate) fn parse_string(input: &str) -> IResult<&str, TextValue> {
    alt((short_string, long_string))(input)
}

/// Matches a short string (e.g. `"Hello"`) and returns the resulting [String]
/// as a [TextValue::String].
fn short_string(input: &str) -> IResult<&str, TextValue> {
    map(delimited(char('"'), short_string_body, char('"')), |text| {
        TextValue::String(text)
    })(input)
}

/// Matches a long string (e.g. `'''Hello, '''\n'''World!'''`) and returns the resulting [String]
/// as a [TextValue::String].
fn long_string(input: &str) -> IResult<&str, TextValue> {
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
        |text| TextValue::String(text.join("")),
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

/// Matches the next string fragment without escape sequences while also respecting the long
/// string delimiter (`'''`).
fn long_string_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
    // In contrast with the `short_string_fragment_without_escaped_text` function, this parser is
    // hand-written because has two possible 'end' sequences to detect:
    //   1. A slash (`\`), indicating the beginning of an escape sequence.
    //   2. A triple-single-quote (`'''`), indicating the end of the string fragment.
    // `nom` provides parser combinators that can detect multiple single-character 'end' markers
    // or a single multiple-charracter 'end' marker. However, it does not provide one to detect
    // multiple 'end' markers that may be more than one character. If that functionality is added
    // in a future release, we can replace this implementation.

    // Detecting a `'''` requires keeping track of some state as we traverse the input.
    // We'll record the first byte offset at which we encountered a quote...
    let mut first_single_quote_index = 0usize;
    // ..as well as how many quotes in a row we've found.
    let mut quote_count = 0usize;
    // We'll iterate across each 'char' (Unicode codepoint) in the input string. Each char can
    // take multiple input bytes to represent, so we'll use `char_indices()` to get both the char
    // itself and the byte index at which it started.
    for (index, char) in input.char_indices() {
        if char == '\\' {
            if index == 0 {
                // The input starts with a `\`; the parser doesn't match.
                return Err(nom::Err::Error(make_error(input, ErrorKind::Escaped)));
            }
            // We found a `\`; return a match for all of the text up to `index`, exclusive.
            return Ok((&input[index..], StringFragment::Substring(&input[0..index])));
        } else if char == '\'' {
            // We found a single quote. Increment the count.
            quote_count += 1;
            match quote_count {
                1 => {
                    // If this is the first quote we've found, keep track of its byte offset.
                    // When we're ready to return a matching substring, we'll need it to end at
                    // that index.
                    first_single_quote_index = index;
                }
                2 => {}
                3 => {
                    // We've found a third single quote in a row.
                    if first_single_quote_index == 0 {
                        // The `'''` was at the beginning of the input; the parser doesn't match.
                        // We'll return an Err so the `long_string_fragment` parser will know
                        // there weren't any more string fragments in the input. The `'''` we just
                        // ran into will be consumed later by `long_string`.
                        return Err(nom::Err::Error(make_error(input, ErrorKind::Escaped)));
                    }
                    // This `'''` indicates the end of the string fragment. Return a match for all
                    // of the text leading up to the offset of the first single quote, exclusive.
                    return Ok((
                        &input[first_single_quote_index..],
                        StringFragment::Substring(&input[0..first_single_quote_index]),
                    ));
                }
                _ => unreachable!("quote_count was greater than 3"),
            }
        } else {
            quote_count = 0;
        }
    }
    // We got to the end of the input without encountering either a `\` or a `'''`. We can't
    // say for sure whether this would've matched successfully given more input, so we return
    // `Incomplete`, indicating that the reader should load more data and try parsing it again.
    Err(Incomplete(Needed::Unknown))
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
