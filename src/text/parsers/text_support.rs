// Parsing functions that are common to textual types

use nom::combinator::{value, map, map_res, recognize};
use nom::{IResult, AsChar};
use nom::sequence::{preceded, tuple};
use nom::branch::alt;
use crate::result::{IonError, decoding_error_raw};
use nom::character::streaming::{char, satisfy};
use nom::bytes::streaming::tag;

/// The text Ion types each need to be able to read strings that contain escaped characters.
/// This type represents the possible types of substring that make up any given piece of text from
/// the parser's perspective. escaped characters that need to be replaced, escaped characters that
/// need to be discarded, and unescaped substrings that are valid as-is.
#[derive(Debug, Clone)]
pub(crate) enum StringFragment<'a> {
    /// A substring that contains no escaped characters and which is valid as-is.
    Substring(&'a str),
    /// An escaped character (like '\n' or '\xFF') that maps to a substitute character.
    EscapedChar(char),
    /// An escaped newline, which can be ignored altogether.
    EscapedNewline,
}

/// Matches an escaped newline, returning [StringFragment::EscapedNewline].
pub(crate) fn escaped_newline(input: &str) -> IResult<&str, StringFragment> {
    value(StringFragment::EscapedNewline, tag("\\\n"))(input)
}

/// Matches an escaped literal (like '\n') or a Unicode escape (starting with '\x', '\u', or '\U'),
/// returning the appropriate substitute character as a [StringFragment::EscapedChar].
pub(crate) fn escaped_char(input: &str) -> IResult<&str, StringFragment> {
    map(
        preceded(
            char('\\'),
            alt((
                escaped_char_unicode,
                escaped_char_literal,
            ))
        ),
        |c| StringFragment::EscapedChar(c)
    )(input)
}

/// Matches an escaped literal and returns the appropriate substitute character.
/// See: https://amzn.github.io/ion-docs/docs/spec.html#escapes
pub(crate) fn escaped_char_literal(input: &str) -> IResult<&str, char> {
    alt((
        value('\n', char('n')),
        value('\r', char('r')),
        value('\t', char('t')),
        value('\\', char('\\')),
        value('/', char('/')),
        value('"', char('"')),
        value('\'', char('\'')),
        value('?', char('?')),
        value('\u{00}', char('0')), // NUL
        value('\u{07}', char('a')), // alert BEL
        value('\u{08}', char('b')), // backspace
        value('\u{0B}', char('v')), // vertical tab
        value('\u{0C}', char('f')), // form feed
    ))(input)
}

/// Matches a Unicode escape (starting with '\x', '\u', or '\U'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode(input: &str) -> IResult<&str, char> {
    map_res::<_, _, _, _, IonError, _, _>(
        alt((
            escaped_char_unicode_2_digit_hex,
            escaped_char_unicode_4_digit_hex,
            escaped_char_unicode_8_digit_hex,
        )),
        |hex_digits| {
            let number_value = u32::from_str_radix(hex_digits, 16)
                .or_else(|e| Err(decoding_error_raw(
                    format!("Couldn't parse unicode escape '{}': {:?}", hex_digits, e)
                )))?;
            let char_value = std::char::from_u32(number_value)
                .ok_or_else(|| decoding_error_raw(
                    format!(
                        "Couldn't parse unicode escape '{}': {} is not a valid codepoint.",
                        hex_digits,
                        number_value
                    )
                ))?;
            Ok(char_value)
        }
    )(input)
}

/// Matches a 2-digit Unicode escape (starting with '\x'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode_2_digit_hex(input: &str) -> IResult<&str, &str> {
    let hex_digit = single_hex_digit;
    preceded(
        char('x'),
        recognize(
            tuple(
                (hex_digit, hex_digit)
            )
        )
    )(input)
}

/// Matches a 4-digit Unicode escape (starting with '\u'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode_4_digit_hex(input: &str) -> IResult<&str, &str> {
    let hex_digit = single_hex_digit;
    preceded(
        char('u'),
        recognize(
            tuple(
                (hex_digit, hex_digit, hex_digit, hex_digit)
            )
        )
    )(input)
}


/// Matches an 8-digit Unicode escape (starting with '\U'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode_8_digit_hex(input: &str) -> IResult<&str, &str> {
    let hex_digit = single_hex_digit;
    preceded(
        char('U'),
        recognize(
            tuple(
                (hex_digit, hex_digit, hex_digit, hex_digit,
                 hex_digit, hex_digit, hex_digit, hex_digit)
            )
        )
    )(input)
}

/// Matches and returns a single base-16 digit.
pub(crate) fn single_hex_digit(input: &str) -> IResult<&str, char> {
    satisfy(|c| <char as AsChar>::is_hex_digit(c))(input)
}
