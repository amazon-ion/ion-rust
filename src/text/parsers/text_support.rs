// Parsing functions that are common to textual types

use crate::text::parse_result::{
    fatal_parse_error, IonParseError, IonParseResult, OrFatalParseError, UpgradeIResult,
};
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::{char, satisfy};
use nom::combinator::{map, recognize, value};
use nom::sequence::{preceded, tuple};
use nom::{AsChar, IResult, Parser};
use std::str;

/// The text Ion types each need to be able to read strings that contain escaped characters.
/// This type represents the possible types of substring that make up any given piece of text from
/// the parser's perspective. escaped characters that need to be replaced, escaped characters that
/// need to be discarded, and unescaped substrings that are valid as-is.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum StringFragment<'a> {
    /// A substring that contains no escaped characters and which is valid as-is.
    Substring(&'a str),
    /// An escaped character (like '\n' or '\xFF') that maps to a substitute character.
    EscapedChar(char),
    /// An escaped newline, which can be ignored altogether.
    EscapedNewline,
}

/// Checks the given input for a leading slash (`\`); if it finds one, it applies the provided
/// `parser` to the text that follows. If the parser doesn't match, returns a fatal error.
pub(crate) fn escape_and_then<'a, 'b, P>(
    input: &'a str,
    label: &'b str,
    mut parser: P,
) -> IonParseResult<'a, StringFragment<'a>>
where
    P: Parser<&'a str, StringFragment<'a>, IonParseError<'a>>,
{
    // If it doesn't start with a slash, it's not a match. Return a non-fatal error.
    let (remaining, _slash) = char('\\')(input).upgrade()?;
    // If the provided parser doesn't match what comes next, it's not a valid escape.
    // Return a fatal error.
    match parser.parse(remaining) {
        Ok((remaining, string_fragment)) => Ok((remaining, string_fragment)),
        Err(e @ nom::Err::Incomplete(_)) => Err(e),
        Err(e) => fatal_parse_error(remaining, format!("could not parse {label}: {e}")),
    }
}

/// Matches an escaped newline, returning [StringFragment::EscapedNewline].
pub(crate) fn escaped_newline(input: &str) -> IonParseResult<StringFragment> {
    value(
        StringFragment::EscapedNewline,
        alt((tag("\\\n"), tag("\\\r\n"), tag("\\\r"))),
    )(input)
    .upgrade()
}

/// Matches an escaped literal (like '\n') or a Unicode escape (starting with '\x', '\u', or '\U'),
/// returning the appropriate substitute character as a [StringFragment::EscapedChar].
pub(crate) fn escaped_char(input: &str) -> IonParseResult<StringFragment> {
    let parser = map(
        alt((escaped_char_unicode, escaped_char_literal)),
        StringFragment::EscapedChar,
    );

    escape_and_then(
        input,
        "an escaped character (Unicode, hex, or literal)",
        parser,
    )
}

/// Matches an escaped literal (like '\n') or a hex escape (like `\x`), returning the appropriate
/// substitute character as a [StringFragment::EscapedChar]. Does NOT match Unicode escapes
/// ('\u' or '\U').
pub(crate) fn escaped_char_no_unicode(input: &str) -> IonParseResult<StringFragment> {
    let parser = map(
        alt((escaped_hex_char, escaped_char_literal)),
        StringFragment::EscapedChar,
    );

    escape_and_then(input, "an escaped character (hex or literal)", parser)
}

/// Matches an escaped literal and returns the appropriate substitute character.
/// See: <https://amazon-ion.github.io/ion-docs/docs/spec.html#escapes>
pub(crate) fn escaped_char_literal(input: &str) -> IonParseResult<char> {
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
    .upgrade()
}

pub(crate) fn escaped_hex_char(input: &str) -> IonParseResult<char> {
    // First, try to match the input to a hex escape sequence. If successful, extract the hex
    // digits that were included in the sequence. If matching fails, this isn't a hex escape sequence.
    // Return early with a non-fatal error.
    let (remaining_input, hex_digits) = escaped_char_2_digit_hex(input).upgrade()?;

    // Now that we have our hex digits, we'll try to convert them to a char.
    // If this fails, it will return a fatal error.
    decode_hex_digits_to_char(remaining_input, hex_digits)
}

/// Returns `true` if the provided code point is a utf-16 high surrogate.
///
/// Terse primer: Unicode text is made up of a stream of unsigned integers called 'code points'.
/// What a person might think of as a 'character' (for example: 'a', '本', or '🥸') can be made up
/// of one or more code points.
///
/// A single code point can require up to 21 bits. Depending on which Unicode encoding you're using,
/// these 21 bits can come with different amounts of additional overhead bits:
/// * In utf-8, a code point can be 1, 2, 3, or 4 bytes, with some bits in each byte being used
///   for the code point and others being used to indicate whether more bytes are coming.
/// * In utf-16, a code point can be 2 bytes or 4 bytes. If it's four bytes, the first two bytes will
///   be a 'high surrogate' (a value between 0xD800 and 0xDFFF) to communicate that another two
///   bytes are coming to complete the code point.
/// * In utf-32, a code point is always 32 bits. This is a bit wasteful, but makes for simple
///   processing.
///
/// This helper function detects high surrogates (which are only used in utf-16) so the parser
/// can know to require a second one immediately following.
///
/// Further reading:
/// * <https://doc.rust-lang.org/std/primitive.char.html>
/// * <https://www.unicode.org/glossary/#surrogate_code_point>
fn code_point_is_a_high_surrogate(value: u32) -> bool {
    (0xD800..=0xDFFF).contains(&value)
}

/// Matches a Unicode escape (starting with '\x', '\u', or '\U'), returning the appropriate
/// substitute character. If the value represented by the escape is a utf-16 high surrogate,
/// another Unicode escape will be matched from input to produce a Unicode scalar.
pub(crate) fn escaped_char_unicode(input: &str) -> IonParseResult<char> {
    // First, try to match the input to a Unicode escape sequence. If successful, extract the hex
    // digits that were included in the sequence. If matching fails, this isn't an escape sequence.
    // Return early with a non-fatal error.
    let (remaining_input, hex_digits) = alt((
        escaped_char_2_digit_hex,
        escaped_char_unicode_4_digit_hex,
        escaped_char_unicode_8_digit_hex,
    ))(input)
    .upgrade()?;

    // We matched on a sequence of hex digits of some length; convert it to a `u32`.
    let (_, number_value) = u32::from_str_radix(hex_digits, 16)
        .or_fatal_parse_error(hex_digits, "could not parse escape hex sequence")?;

    // Check to see if this is a high surrogate; if it is, our code point isn't complete. Another
    // unicode escape representing the low surrogate has to be next in the input to complete it.
    // See the docs for this helper function for details. (Note: this will only ever be true for
    // 4- and 8-digit escape sequences. `\x` escapes don't have enough digits to represent a
    // high surrogate.)
    if code_point_is_a_high_surrogate(number_value) {
        // It's a high surrogate. It needs to be followed by a low surrogate to complete the
        // codepoint.
        return complete_surrogate_pair(input, remaining_input, hex_digits, number_value);
    }

    // A Rust `char` can represent any Unicode scalar value--a code point that is not part of a
    // surrogate pair. If the value we found isn't a high surrogate, then it's a complete scalar
    // value. We can safely convert it to a `char`.
    let character = char::from_u32(number_value).unwrap();

    Ok((remaining_input, character))
}

/// Rust's [`char`](prim@char) type represents any Unicode code point EXCEPT a surrogate. If we
/// encounter a high surrogate in the stream, we cannot convert it to a `char` yet. We must find the
/// (mandatory) low surrogate that follows it in the stream; then we can combine the high and low
/// surrogates into a complete code point. This code point can then be returned as a Rust
/// [`char`](prim@char).
fn complete_surrogate_pair<'a>(
    input: &'a str,
    input_after_high_surrogate: &'a str,
    high_surrogate_hex_digits: &'a str,
    high_surrogate_number_value: u32,
) -> IonParseResult<'a, char> {
    let (_, (input_after_low_surrogate, low_surrogate_hex_digits)) =
        // Look for a `\` followed by a \uXXXX or \UXXXXXXXX escape
        preceded(
            char('\\'),
            alt((
                escaped_char_unicode_4_digit_hex,
                escaped_char_unicode_8_digit_hex,
            )),
        )(input_after_high_surrogate)
        .or_fatal_parse_error(
            input_after_high_surrogate,
            "encountered an incomplete surrogate pair",
        )?;

    // Convert the second set of hex digits to a `u32`.
    let low_surrogate_number_value = u32::from_str_radix(low_surrogate_hex_digits, 16)
        .or_fatal_parse_error(
            high_surrogate_hex_digits,
            "could not parse escape hex sequence for trailing surrogate",
        )?
        .1;

    // Convert our pair of surrogate number values into u16s so we can feed them into the utf-16
    // decoder. We know the first surrogate number value will fit in a u16 because we checked
    // its range above, so we can safely unwrap it.
    let high_surrogate: u16 = u16::try_from(high_surrogate_number_value).unwrap();
    let low_surrogate: u16 = u16::try_from(low_surrogate_number_value)
        .or_fatal_parse_error(
            low_surrogate_hex_digits,
            "trailing surrogate number value did not fit in a u16",
        )?
        .1;

    let character = char::decode_utf16([high_surrogate, low_surrogate])
        .next()
        .unwrap() // We provided enough data to produce either a char or an Err
        .or_fatal_parse_error(input, "encountered invalid surrogate pair")?
        .1;

    Ok((input_after_low_surrogate, character))
}

/// Treats a given string as the hex-encoded byte representation of a char
pub(crate) fn decode_hex_digits_to_char<'a>(
    remaining_input: &'a str,
    hex_digits: &'a str,
) -> IonParseResult<'a, char> {
    // If this step fails, the Ion data stream is malformed and we need to bail out completely.
    // We can't simply return an error as we did above; if we did that, the parser would go on to
    // treat the input as a String literal without escapes, which is the incorrect behavior.
    // Instead, we need to return a nom `Err::Failure`, indicating that we cannot proceed.
    let number_value = match u32::from_str_radix(hex_digits, 16) {
        Ok(number_value) => number_value,
        Err(parse_int_error) => {
            return fatal_parse_error(
                hex_digits,
                format!("could not parse escaped code unit: {parse_int_error}"),
            )
        }
    };
    let char_value = match std::char::from_u32(number_value) {
        Some(char_value) => char_value,
        None => {
            return fatal_parse_error(
                hex_digits,
                format!("escape value (decimal:'{number_value}') is not a valid character"),
            );
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

/// Matches a `\r` or `\r\n` and returns a StringFragment::EscapedChar('\n').
pub(crate) fn normalized_newline(input: &str) -> IonParseResult<StringFragment> {
    // In a long string, \r and \r\n are both normalized to `\n`
    value(
        // Return a newline...
        StringFragment::EscapedChar('\n'),
        // ...if the input is one of the following:
        alt((tag("\r\n"), tag("\r"))),
    )(input)
    .upgrade()
}

/// If `byte_index` is zero, returns an `Err` signaling that the input was not matched. Otherwise,
/// splits the text at `byte_index` and returns a match on the head with the tail as remaining
/// input.
///
/// This is used by the string and clob parsers to detect non-empty long-string-formatted text
/// fragments. (e.g. '''hello''' ''' world!''')
pub(crate) fn string_fragment_or_mismatch(
    input: &str,
    byte_index: usize,
) -> IonParseResult<StringFragment> {
    if byte_index == 0 {
        return Err(nom::Err::Error(IonParseError::new(input)));
    }
    Ok((
        &input[byte_index..],
        StringFragment::Substring(&input[0..byte_index]),
    ))
}
