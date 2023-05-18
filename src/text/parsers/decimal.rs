use std::str::FromStr;

use crate::text::parse_result::{IonParseResult, OrFatalParseError, UpgradeParser};
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::one_of;
use nom::combinator::{map, opt};
use nom::sequence::{pair, preceded, terminated};
use num_bigint::BigUint;

use crate::text::parsers::numeric_support::{
    digits_before_dot, exponent_digits, floating_point_number_components,
};
use crate::text::parsers::stop_character;
use crate::text::text_value::TextValue;
use crate::types::{Coefficient, Decimal, Sign, UInt};

/// Matches the text representation of a decimal value and returns the resulting [Decimal]
/// as a [TextValue::Decimal].
pub(crate) fn parse_decimal(input: &str) -> IonParseResult<TextValue> {
    terminated(
        alt((decimal_with_exponent, decimal_without_exponent)),
        stop_character,
    )(input)
}

/// Matches decimal values that have an exponent. (For example, `7d0`, `71d-1`, and `-71d-1`.)
fn decimal_with_exponent(input: &str) -> IonParseResult<TextValue> {
    let (remaining, ((sign, digits_before, digits_after), exponent)) = pair(
        alt((
            // Returns a tuple of (sign, digits before '.', and digits after '.')
            floating_point_number_components,
            // Needs to return the same fields as above, so we tack on a 'None'
            map(
                pair(opt(tag("-")).upgrade(), digits_before_dot),
                |(sign, leading_digits)| (sign, leading_digits, None),
            ),
        )),
        decimal_exponent_marker_followed_by_digits,
    )(input)?;

    let decimal =
        decimal_from_text_components(input, sign, digits_before, digits_after, exponent)?.1;
    Ok((remaining, TextValue::Decimal(decimal)))
}

/// Matches decimal values that do not have an exponent. (For example, `7.`, `7.1`, and `-7.1`.)
fn decimal_without_exponent(input: &str) -> IonParseResult<TextValue> {
    let (remaining, (sign, digits_before_dot, digits_after_dot)) =
        floating_point_number_components(input)?;
    let decimal = decimal_from_text_components(
        input,
        sign,
        digits_before_dot,
        digits_after_dot,
        "0", // If no exponent is specified, we always start from 0
    )?
    .1;
    Ok((remaining, TextValue::Decimal(decimal)))
}

/// Given the four text components of a decimal value (the sign, the digits before the decimal point,
/// the digits after the decimal point, and the exponent), constructs a [Decimal] value.
fn decimal_from_text_components<'a>(
    input: &'a str,
    sign_text: Option<&'a str>,
    digits_before_dot: &'a str,
    digits_after_dot: Option<&'a str>,
    exponent_text: &'a str,
) -> IonParseResult<'a, Decimal> {
    // The longest number that can fit into a u64 without finer-grained bounds checks.
    const MAX_U64_DIGITS: usize = 19;
    // u64::MAX is a 20-digit number starting with `1`. For simplicity, we'll turn any number
    // with 19 or fewer digits into a u64 and anything else into a BigUint.

    let digits_after_dot = digits_after_dot.unwrap_or("");
    let sign = if sign_text.is_some() {
        Sign::Negative
    } else {
        Sign::Positive
    };

    // TODO: Reusable buffer for formatting/sanitization
    let mut magnitude_text = format!("{digits_before_dot}{digits_after_dot}");
    magnitude_text.retain(|c| c != '_');
    // Ion's parsing rules should only let through strings of digits and underscores. Since
    // we've just removed the underscores above, the `from_str` methods below should always
    // succeed.
    let magnitude: UInt = if magnitude_text.len() < MAX_U64_DIGITS {
        let value = u64::from_str(&magnitude_text)
            .or_fatal_parse_error(input, "parsing coefficient magnitude as u64 failed")?
            .1;
        UInt::U64(value)
    } else {
        let value = BigUint::from_str(&magnitude_text)
            .or_fatal_parse_error(input, "parsing coefficient magnitude as u64 failed")?
            .1;
        UInt::BigUInt(value)
    };

    let coefficient = Coefficient::new(sign, magnitude);

    // TODO: Reusable buffer for sanitization
    let sanitized = exponent_text.trim_start_matches('+').replace('_', "");
    let mut exponent = i64::from_str(&sanitized).expect("parsing exponent as i64 failed");
    // Reduce the exponent by the number of digits that follow the decimal point
    exponent -= digits_after_dot
        .chars()
        .filter(|c| c.is_ascii_digit())
        .count() as i64;
    Ok(("", Decimal::new(coefficient, exponent)))
}

/// Matches the decimal exponent marker ('d' or 'D') followed by a signed integer. (e.g. 'd-16')
fn decimal_exponent_marker_followed_by_digits(input: &str) -> IonParseResult<&str> {
    preceded(one_of("dD"), exponent_digits)(input)
}

#[cfg(test)]
mod reader_tests {
    use crate::text::parsers::decimal::parse_decimal;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;
    use crate::types::Decimal;

    fn parse_equals(text: &str, expected: Decimal) {
        parse_test_ok(parse_decimal, text, TextValue::Decimal(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_decimal, text)
    }

    #[test]
    fn test_parse_decimals_with_exponents() {
        parse_equals("0d0 ", Decimal::new(0, 0));
        parse_equals("0D0 ", Decimal::new(0, 0));
        parse_equals("-0d0 ", Decimal::negative_zero());
        parse_equals("-0D0 ", Decimal::negative_zero());
        parse_equals("-0d5 ", Decimal::negative_zero_with_exponent(5));
        parse_equals("-0d-5 ", Decimal::negative_zero_with_exponent(-5));
        parse_equals("305d1 ", Decimal::new(305, 1));
        parse_equals("305d-1 ", Decimal::new(305, -1));
        parse_equals("111_111d222 ", Decimal::new(111_111, 222));
        parse_equals("111_111d-222 ", Decimal::new(111_111, -222));
        parse_equals("111_111d222_222 ", Decimal::new(111_111, 222_222));
        parse_equals("-279d0 ", Decimal::new(-279, 0));
        parse_equals("-999_9d9_9 ", Decimal::new(-9_999, 99));
        parse_equals("-999_9d-9_9 ", Decimal::new(-9_999, -99));

        // Missing exponent, would be parsed as an integer)
        parse_fails("305 ");
        // Fractional exponent
        parse_fails("305d0.5");
        // Negative fractional exponent
        parse_fails("305d-0.5");
        // Doesn't consume leading whitespace
        parse_fails(" 305d1 ");
        // Doesn't accept leading underscores
        parse_fails("_305d1 ");
        // Doesn't accept leading zeros
        parse_fails("0305d1 ");
        // Doesn't accept trailing underscores
        parse_fails("305d1_ ");
        // Doesn't accept multiple consecutive underscores
        parse_fails("30__5d1 ");
        // Doesn't accept leading plus sign
        parse_fails("+305d1 ");
        // Doesn't accept multiple negative signs
        parse_fails("--305d1 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        parse_fails("305d1");
    }

    #[test]
    fn test_parse_decimals_without_exponents() {
        parse_equals("0. ", Decimal::new(0, 0));
        parse_equals("-0. ", Decimal::negative_zero());
        parse_equals("0.0 ", Decimal::new(0, -1));
        parse_equals("0.5 ", Decimal::new(5, -1));
        parse_equals("3050. ", Decimal::new(3050, 0));
        parse_equals("3050.667 ", Decimal::new(3050667, -3));
        parse_equals("111_111.000 ", Decimal::new(111111000, -3));
        parse_equals("111_111.0_0_0 ", Decimal::new(111111000, -3));
        parse_equals("-279. ", Decimal::new(-279, 0));
        parse_equals("-279.0 ", Decimal::new(-2790, -1));
        parse_equals("-279.701 ", Decimal::new(-279701, -3));
        parse_equals("-999_9.0_0 ", Decimal::new(-999900, -2));

        // Missing decimal point, would be parsed as an integer
        parse_fails("305 ");
        // Doesn't consume leading whitespace
        parse_fails(" 3050.0 ");
        // Doesn't accept leading underscores
        parse_fails("_3050.0 ");
        // Doesn't accept leading zeros
        parse_fails("03050.0 ");
        // Doesn't accept trailing underscores
        parse_fails("3050.0_ ");
        // Doesn't accept multiple consecutive underscores
        parse_fails("30__50.0 ");
        // Doesn't accept leading plus sign
        parse_fails("+3050.0 ");
        // Doesn't accept multiple negative signs
        parse_fails("--3050.0 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        parse_fails("3050.0");
    }
}
