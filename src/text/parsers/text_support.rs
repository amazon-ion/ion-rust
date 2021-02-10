// Parsing functions that are common to textual types

use nom::combinator::{value, map, map_res, recognize};
use nom::{IResult, AsChar};
use nom::sequence::{preceded, tuple};
use nom::branch::alt;
use crate::result::{IonError, decoding_error_raw};
use nom::character::streaming::{char, satisfy};
use nom::bytes::streaming::tag;


#[derive(Debug, Clone)]
pub(crate) enum StringFragment<'a> {
    Substring(&'a str),
    EscapedChar(char),
    EscapedNewline,
}

// Discards escaped newlines
pub(crate) fn escaped_newline(input: &str) -> IResult<&str, StringFragment> {
    value(StringFragment::EscapedNewline, tag("\\\n"))(input)
}

// Some escape sequences discard the associated character (like escaped newlines),
// so this returns Option<char> to accommodate that.
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

// See: https://amzn.github.io/ion-docs/docs/spec.html#escapes
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

pub(crate) fn single_hex_digit(input: &str) -> IResult<&str, char> {
    satisfy(|c| <char as AsChar>::is_hex_digit(c))(input)
}
