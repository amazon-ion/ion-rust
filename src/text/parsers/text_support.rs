// Parsing functions that are common to textual types

use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::{char, satisfy};
use nom::combinator::{map, recognize, value};
use nom::error::{Error, ErrorKind, ParseError};
use nom::sequence::{preceded, tuple};
use nom::{AsChar, Err, IResult};

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
    value(
        StringFragment::EscapedNewline,
        alt((tag("\\\n"), tag("\\\r\n"), tag("\\\r"))),
    )(input)
}

/// Matches an escaped literal (like '\n') or a Unicode escape (starting with '\x', '\u', or '\U'),
/// returning the appropriate substitute character as a [StringFragment::EscapedChar].
pub(crate) fn escaped_char(input: &str) -> IResult<&str, StringFragment> {
    map(
        preceded(
            char('\\'),
            alt((escaped_char_unicode, escaped_char_literal)),
        ),
        StringFragment::EscapedChar,
    )(input)
}

/// Matches an escaped literal (like '\n') or a hex escape (like `\x`), returning the appropriate
/// substitute character as a [StringFragment::EscapedChar]. Does NOT match Unicode escapes
/// ('\u' or '\U').
pub(crate) fn escaped_char_no_unicode(input: &str) -> IResult<&str, StringFragment> {
    map(
        preceded(char('\\'), alt((escaped_hex_char, escaped_char_literal))),
        StringFragment::EscapedChar,
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

pub(crate) fn escaped_hex_char(input: &str) -> IResult<&str, char> {
    // First, try to match the input to a hex escape sequence. If successful, extract the hex
    // digits that were included in the sequence. If matching fails, this isn't a hex escape sequence.
    // Return early with a non-fatal error.
    let (remaining_input, hex_digits) = escaped_char_2_digit_hex(input)?;

    // Now that we have our hex digits, we'll try to convert them to a char.
    // If this fails, it will return a fatal error.
    decode_hex_digits_to_char(remaining_input, hex_digits)
}

/// Matches a Unicode escape (starting with '\x', '\u', or '\U'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode(input: &str) -> IResult<&str, char> {
    // First, try to match the input to a Unicode escape sequence. If successful, extract the hex
    // digits that were included in the sequence. If matching fails, this isn't an escape sequence.
    // Return early with a non-fatal error.
    let (remaining_input, hex_digits) = alt((
        escaped_char_2_digit_hex,
        escaped_char_unicode_4_digit_hex,
        escaped_char_unicode_8_digit_hex,
    ))(input)?;

    // Now that we have our hex digits, we'll try to convert them to Unicode code points.
    // If this fails, it will return a fatal error.
    decode_hex_digits_to_char(remaining_input, hex_digits)
}

/// Treats a given string as the hex-encoded byte representation of a char
pub(crate) fn decode_hex_digits_to_char<'a>(
    remaining_input: &'a str,
    hex_digits: &'a str,
) -> IResult<&'a str, char> {
    // If this step fails, the Ion data stream is malformed and we need to bail out completely.
    // We can't simply return an error as we did above; if we did that, the parser would go on to
    // treat the input as a String literal without escapes, which is the incorrect behavior.
    // Instead, we need to return a nom `Err::Failure`, indicating that we cannot proceed.
    let number_value = match u32::from_str_radix(hex_digits, 16) {
        Ok(number_value) => number_value,
        Err(_parse_int_error) => {
            // TODO: A custom error type would be required to bubble up specific information
            //       about the failure.
            return Err(Err::Failure(Error::from_error_kind(
                hex_digits,
                ErrorKind::Escaped,
            )));
        }
    };
    let char_value = match std::char::from_u32(number_value) {
        Some(char_value) => char_value,
        None => {
            // TODO: A custom error type would be required to bubble up specific information
            //       about the failure.
            return Err(Err::Failure(Error::from_error_kind(
                hex_digits,
                ErrorKind::Escaped,
            )));
        }
    };
    Ok((remaining_input, char_value))
}

/// Matches a 2-digit hex escape (starting with '\x'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_2_digit_hex(input: &str) -> IResult<&str, &str> {
    let hex_digit = single_hex_digit;
    preceded(char('x'), recognize(tuple((hex_digit, hex_digit))))(input)
}

/// Matches a 4-digit Unicode escape (starting with '\u'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode_4_digit_hex(input: &str) -> IResult<&str, &str> {
    let hex_digit = single_hex_digit;
    preceded(
        char('u'),
        recognize(tuple((hex_digit, hex_digit, hex_digit, hex_digit))),
    )(input)
}

/// Matches an 8-digit Unicode escape (starting with '\U'), returning the appropriate
/// substitute character.
pub(crate) fn escaped_char_unicode_8_digit_hex(input: &str) -> IResult<&str, &str> {
    let hex_digit = single_hex_digit;
    preceded(
        char('U'),
        recognize(tuple((
            hex_digit, hex_digit, hex_digit, hex_digit, hex_digit, hex_digit, hex_digit, hex_digit,
        ))),
    )(input)
}

/// Matches and returns a single base-16 digit.
pub(crate) fn single_hex_digit(input: &str) -> IResult<&str, char> {
    satisfy(<char as AsChar>::is_hex_digit)(input)
}
