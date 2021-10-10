use crate::text::parsers::numeric_support::base_10_integer_digits;
use crate::text::parsers::stop_character;
use crate::text::text_value::TextValue;
use nom::branch::alt;
use nom::bytes::streaming::{is_a, tag, take_while1};
use nom::character::streaming::char;
use nom::combinator::{map_res, opt, recognize};
use nom::multi::many0_count;
use nom::sequence::{pair, preceded, separated_pair, terminated};
use nom::IResult;
use std::num::ParseIntError;

// This module uses the phrase "base 10" to avoid potentially confusing references to "decimal",
// a phrase which is heavily overloaded in the context of parsing Ion. It may refer to the Ion type
// decimal, the base-10 notation, or the fractional delimiter of a floating-point number.

/// Matches the text representation of an integer in any supported notation (base-2, base-10, or
/// base-16) and returns the resulting [i64] as a [TextValue::Integer].
pub(crate) fn parse_integer(input: &str) -> IResult<&str, TextValue> {
    terminated(
        alt((base_16_integer, base_2_integer, base_10_integer)),
        stop_character,
    )(input)
}

/// Matches a base-16 notation integer (e.g. `0xCAFE`, `0Xcafe`, or `-0xCa_Fe`) and returns the
/// resulting [i64] as a [TextValue::Integer].
fn base_16_integer(input: &str) -> IResult<&str, TextValue> {
    map_res(
        separated_pair(
            opt(char('-')),
            alt((tag("0x"), tag("0X"))),
            base_16_integer_digits,
        ),
        |(maybe_sign, text_digits)| {
            parse_i64_with_radix(text_digits, 16)
                .map(|i| if maybe_sign.is_some() { -i } else { i })
                .map(|i| TextValue::Integer(i))
        },
    )(input)
}

/// Recognizes the digits that follow the '0x' or '0X' in a base-16 integer.
fn base_16_integer_digits(input: &str) -> IResult<&str, &str> {
    recognize(terminated(
        // Zero or more digits-followed-by-underscores
        many0_count(pair(take_base_16_digits1, char('_'))),
        // One or more digits
        take_base_16_digits1,
    ))(input)
}

/// Recognizes 1 or more consecutive base-16 digits.
// This function's "1" suffix is a style borrowed from `nom`.
fn take_base_16_digits1(input: &str) -> IResult<&str, &str> {
    take_while1(|c: char| c.is_digit(16))(input)
}

/// Matches a base-2 notation integer (e.g. `0b0`, `0B1`, or `-0b10_10`) and returns the resulting
/// [i64] as a [TextValue::Integer].
fn base_2_integer(input: &str) -> IResult<&str, TextValue> {
    map_res(
        separated_pair(
            opt(char('-')),
            alt((tag("0b"), tag("0B"))),
            base_2_integer_digits,
        ),
        |(maybe_sign, text_digits)| {
            parse_i64_with_radix(text_digits, 2)
                .map(|i| if maybe_sign.is_some() { -i } else { i })
                .map(|i| TextValue::Integer(i))
        },
    )(input)
}

/// Recognizes the digits that follow the '0b' or 'B' in a base-2 integer.
fn base_2_integer_digits(input: &str) -> IResult<&str, &str> {
    recognize(terminated(
        // Zero or more digits-followed-by-underscores
        many0_count(pair(is_a("01"), char('_'))),
        // One or more digits
        is_a("01"),
    ))(input)
}

/// Matches a base-10 notation integer (e.g. `0`, `255`, or `-1_024`) and returns the resulting
/// [i64] as a [TextValue::Integer].
fn base_10_integer(input: &str) -> IResult<&str, TextValue> {
    map_res(
        recognize(preceded(opt(char('-')), base_10_integer_digits)),
        |text| parse_i64_with_radix(text, 10).map(|i| TextValue::Integer(i)),
    )(input)
}

/// Strips any underscores out of the provided text and then parses it according to the specified
/// radix.
fn parse_i64_with_radix(text: &str, radix: u32) -> Result<i64, ParseIntError> {
    if text.contains('_') {
        let sanitized = text.replace("_", "");
        return i64::from_str_radix(&sanitized, radix);
    }
    i64::from_str_radix(text, radix)
}

#[cfg(test)]
mod integer_parsing_tests {
    use crate::text::parsers::integer::parse_integer;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;

    fn parse_equals(text: &str, expected: i64) {
        parse_test_ok(parse_integer, text, TextValue::Integer(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_integer, text)
    }

    #[test]
    fn test_parse_base_10_integers() {
        parse_equals("1 ", 1);
        parse_equals("305 ", 305);
        parse_equals("-279 ", -279);

        // Doesn't consume leading whitespace
        parse_fails(" 305 ");
        // Doesn't accept leading plus sign
        parse_fails("+305 ");
        // Doesn't accept multiple negative signs
        parse_fails("--305 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        parse_fails("305");
    }

    #[test]
    fn test_parse_base_10_integers_with_underscores() {
        parse_equals("111_111_222 ", 111_111_222);
        parse_equals("-999_999 ", -999_999);
        parse_equals("1_2_3_4_5_6 ", 123456);

        // Doesn't accept leading underscores
        parse_fails("_111_111_222 ");
        // Doesn't accept trailing underscores
        parse_fails("111_111_222_ ");
        // Doesn't accept multiple contiguous underscores
        parse_fails("111__111_222 ");
    }

    #[test]
    fn test_parse_base_2_integers() {
        parse_equals("0b1 ", 1);
        parse_equals("0b101 ", 5);
        parse_equals("0B101 ", 5);
        parse_equals("0b11110000 ", 240);
        parse_equals("-0b11110000 ", -240);
        parse_equals("0B11111111 ", 255);
        parse_equals("-0B11111111 ", -255);

        // Doesn't consume leading whitespace
        parse_fails(" 0b0011_0001 ");
        // Doesn't accept leading plus sign
        parse_fails("+0b0011_0001 ");
        // Doesn't accept multiple negative signs
        parse_fails("--0b0011_0001 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        parse_fails("0b0011_0001");
    }

    #[test]
    fn test_parse_base_2_integers_with_underscores() {
        parse_equals("0b1_0_1 ", 5);
        parse_equals("-0b111 ", -7);

        parse_equals("-0b1111_0000 ", -240);

        // Doesn't accept leading underscores
        parse_fails("0b_0011_0001 ");
        parse_fails("_0b_0011_0001 ");
        // Doesn't accept trailing underscores
        parse_fails("0b0011_0001_ ");
        // Doesn't accept multiple consecutive underscores
        parse_fails("0b0011__0001 ");
    }

    #[test]
    fn test_parse_base_16_integers() {
        parse_equals("0x1 ", 1);
        parse_equals("0xA ", 10);
        parse_equals("0xFF ", 255);
        parse_equals("0xff ", 255);
        parse_equals("0XfF ", 255);
        parse_equals("-0xDECAF ", -912559);

        // Doesn't consume leading whitespace
        parse_fails(" 0xCAFE ");
        // Doesn't accept leading plus sign
        parse_fails("+0xCAFE ");
        // Doesn't accept multiple negative signs
        parse_fails("--0xCAFE ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        parse_fails("0xCAFE");
    }

    #[test]
    fn test_parse_base_16_integers_with_underscores() {
        parse_equals("0xFA_CE ", 64_206);
        parse_equals("0xF_A_C_E ", 64_206);

        // Doesn't accept leading underscores
        parse_fails("0x_CAFE ");
        parse_fails("_0xCAFE ");
        // Doesn't accept trailing underscores
        parse_fails("0xCAFE_ ");
        // Doesn't accept multiple consecutive underscores
        parse_fails("0xCA__FE ");
    }
}
