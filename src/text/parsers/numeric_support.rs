//! This module contains parsing functions that are useful in parsing multiple numeric Ion types.

use crate::text::parse_result::{IonParseResult, UpgradeIResult, UpgradeParser};
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::{char, digit1, one_of};
use nom::combinator::{map, opt, recognize};
use nom::multi::many0_count;
use nom::sequence::{pair, preceded, terminated};
use nom::Parser;

/// Recognizes the digits of a base-10 integer. (i.e. An integer without a sign.)
pub(crate) fn base_10_integer_digits(input: &str) -> IonParseResult<&str> {
    alt((
        // The number is either a zero...
        recognize(char('0')).upgrade(),
        // Or it's a non-zero followed by some number of '_'-separated digits
        digits_before_dot,
    ))(input)
}

/// Recognizes either:
/// * a zero
/// * a non-zero followed by some number of digits with optional underscores
pub(crate) fn digits_before_dot(input: &str) -> IonParseResult<&str> {
    alt((tag("0"), recognize(pair(leading_digit, trailing_digits))))(input)
}

/// Recognizes the first digit of a multi-digit base-10 integer. (i.e. Any digit but zero.)
pub(crate) fn leading_digit(input: &str) -> IonParseResult<&str> {
    recognize(one_of("123456789"))(input).upgrade()
}

/// Recognizes any number of digits with underscores optionally appearing in the middle.
/// This parser accepts leading zeros, which is why it cannot be used for the beginning
/// of a number.
pub(crate) fn trailing_digits(input: &str) -> IonParseResult<&str> {
    recognize(many0_count(pair(opt(char('_')), digit1)))(input).upgrade()
}

/// Match an optional sign (if present), digits before the decimal point, then digits after the
/// decimal point (if present).
pub(crate) fn floating_point_number_components(
    input: &str,
) -> IonParseResult<(Option<&str>, &str, Option<&str>)> {
    map(
        opt(tag("-"))
            .and(digits_before_dot)
            .and(dot_followed_by_digits),
        |parts| {
            // Flatten out the unwieldy tuple structure created by chaining and()s
            let ((sign, leading_digits), trailing_digits) = parts;
            (sign, leading_digits, trailing_digits)
        },
    )(input)
}

/// Returns the complete text that was matched by `floating_point_number_components`, ignoring
/// structure.
pub(crate) fn floating_point_number(input: &str) -> IonParseResult<&str> {
    recognize(floating_point_number_components)(input)
}

/// Recognizes the exponent portion of a decimal (everything after the 'd') or float
/// (everything after the 'e'). This includes:
/// * an optional '+' OR '-'
/// * any number of decimal digits, which may:
///    * have underscores in between them: `1_000_000`
///    * have one or more leading zeros: `0005`
pub(crate) fn exponent_digits(input: &str) -> IonParseResult<&str> {
    recognize(pair(opt(alt((char('+'), char('-')))), digits_after_dot))(input)
}

/// Recognizes a decimal point followed by some number of base-10 digits.
pub(crate) fn dot_followed_by_digits(input: &str) -> IonParseResult<Option<&str>> {
    preceded(tag("."), opt(digits_after_dot))(input)
}

/// Recognizes the digits that follow a decimal point. (e.g. `5`, `25`, or `0001`)
fn digits_after_dot(input: &str) -> IonParseResult<&str> {
    recognize(terminated(
        // Zero or more digits-followed-by-underscores
        many0_count(pair(digit1, char('_'))),
        // One or more digits
        digit1,
    ))(input)
    .upgrade()
}
