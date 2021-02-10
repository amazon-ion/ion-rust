// This file contains parsing functions that are useful in parsing multiple numeric Ion types.

use nom::{IResult, Parser};
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::combinator::{recognize, opt, map};
use nom::sequence::{pair, terminated, preceded};
use nom::character::streaming::{char, one_of, digit1};
use nom::multi::many0_count;

// Recognizes either:
// * a zero
// * a non-zero followed by some number of digits with optional underscores
pub(crate) fn digits_before_dot(input: &str) -> IResult<&str, &str> {
    alt((
        tag("0"),
        recognize(
            pair(leading_digit, trailing_digits)
        )
    ))(input)
}

pub(crate) fn leading_digit(input: &str) -> IResult<&str, &str> {
    recognize(one_of("123456789"))(input)
}

// Any number of digits with underscores optionally appearing in the middle.
// This parser accepts leading zeros, which is why it cannot be used for the beginning
// of a number.
pub(crate) fn trailing_digits(input: &str) -> IResult<&str, &str> {
    recognize(
        many0_count(
            pair(
                opt(char('_')),
                digit1
            )
        )
    )(input)
}

// Match an optional sign, leading digits, dot, then trailing digits
pub(crate) fn floating_point_number_components(input: &str) -> IResult<&str, (Option<&str>, &str, Option<&str>)> {
    map(
        opt(tag("-"))
            .and(digits_before_dot)
            .and(dot_followed_by_digits),
        |parts| {
            // Flatten out the unweildy tuple structure created by chaining and()s
            let ((sign, leading_digits), trailing_digits) = parts;
            (sign, leading_digits, trailing_digits)
        }
    )(input)
}

// Returns the complete text that was matched by `floating_point_number_components`, ignoring
// structure.
pub(crate) fn floating_point_number(input: &str) -> IResult<&str, &str> {
    recognize(floating_point_number_components)(input)
}

pub(crate) fn exponent_digits(input: &str) -> IResult<&str, &str> {
    recognize(pair(opt(char('-')), digits_after_exponent_delimiter))(input)
}

pub(crate) fn dot_followed_by_digits(input: &str) -> IResult<&str, Option<&str>> {
    preceded(
        tag("."),
        opt(digits_after_exponent_delimiter)
    )(input)
}

// Unlike before the 'e' or 'd' delimiter, the digits that follow the delimiter can start with one
// or more zeros.
fn digits_after_exponent_delimiter(input: &str) -> IResult<&str, &str> {
    recognize(
        terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(digit1, char('_'))),
            // One or more digits
            digit1
        )
    )(input)
}