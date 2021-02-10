use std::str::FromStr;

use nom::IResult;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::one_of;
use nom::combinator::{map, opt};
use nom::sequence::{pair, preceded, terminated};
use num_bigint::BigUint;

use crate::text::parsers::numeric_support::{digits_before_dot, exponent_digits, floating_point_number_components};
use crate::text::parsers::stop_character;
use crate::text::TextStreamItem;
use crate::types::decimal::{Coefficient, Decimal, Sign};

pub(crate) fn parse_decimal(input: &str) -> IResult<&str, TextStreamItem> {
    terminated(
        alt((decimal_with_exponent, decimal_without_exponent)),
        stop_character
    )(input)
}

fn decimal_with_exponent(input: &str) -> IResult<&str, TextStreamItem> {
    map(
        pair(
            alt((
                // Returns a tuple of (sign, digits before '.', and digits after '.')
                floating_point_number_components,
                // Needs to return the same fields as above, so we tack on a 'None'
                map(
                    pair(opt(tag("-")), digits_before_dot),
                    |(sign, leading_digits)| (sign, leading_digits, None)
                )
            )),
            decimal_exponent_marker_followed_by_digits,
        ),
        |((sign, digits_before, digits_after), exponent)| {
            let decimal = decimal_from_text_components(
                sign,
                digits_before,
                digits_after,
                exponent,
            );
            TextStreamItem::Decimal(decimal)
        }
    )(input)
}

fn decimal_without_exponent(input: &str) -> IResult<&str, TextStreamItem> {
    map(
        floating_point_number_components,
        |(sign, digits_before_dot, digits_after_dot)| {
            let decimal = decimal_from_text_components(
                sign,
                digits_before_dot,
                digits_after_dot,
                "0", // If no exponent is specified, we always start from 0
            );
            TextStreamItem::Decimal(decimal)
        }
    )(input)
}

fn decimal_from_text_components(
    sign_text: Option<&str>,
    digits_before_dot: &str,
    digits_after_dot: Option<&str>,
    exponent_text: &str
) -> Decimal {
    let digits_after_dot = digits_after_dot.unwrap_or("");

    let sign = if sign_text.is_some() {Sign::Negative} else {Sign::Positive};

    let mut coefficient_text = format!("{}{}", digits_before_dot, digits_after_dot);
    coefficient_text.retain(|c| c != '_');
    // u64::MAX is a 20-digit number starting with `1`. For simplicity, we'll turn any number
    // with 19 or fewer digits into a u64 and anything else into a BigUint. This leaves a small
    // amount of performance on the table.
    // TODO: Constant for `20`, store any value that will fit in a u64 in a u64.
    // Ion's parsing rules should only let through strings of digits and underscores. Since
    // we've just removed the underscores above, the `from_str` methods below should always
    // succeed.
    let coefficient: Coefficient = if coefficient_text.len() < 20 {
        let value = u64::from_str(&coefficient_text)
            .expect("parsing coefficient as u64 failed");
        Coefficient::U64(value)
    } else {
        let value = BigUint::from_str(&coefficient_text)
            .expect("parsing coefficient as BigUint failed");
        Coefficient::BigUInt(value)
    };

    let sanitized = exponent_text.replace('_', "");
    let mut exponent = i64::from_str(&sanitized)
        .expect("parsing exponent as i64 failed");
    // Reduce the exponent by the number of digits that follow the decimal point
    exponent -= digits_after_dot.chars().filter(|c| c.is_digit(10)).count() as i64;
    Decimal::new(sign, coefficient, exponent)
}

fn decimal_exponent_marker_followed_by_digits(input: &str) -> IResult<&str, &str> {
    preceded(
        one_of("dD"),
        exponent_digits
    )(input)
}

#[cfg(test)]
mod reader_tests {
    use crate::text::parsers::decimal::parse_decimal;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::TextStreamItem;
    use crate::types::decimal::{Decimal, Sign};

    fn parse_equals(text: &str, expected: Decimal) {
        parse_test_ok(parse_decimal, text, TextStreamItem::Decimal(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_decimal, text)
    }

    #[test]
    fn test_parse_decimals_with_exponents() {
        use Sign::{Positive, Negative};

        parse_equals("0d0 ", Decimal::new(Positive, 0, 0));
        parse_equals("0D0 ", Decimal::new(Positive, 0, 0));
        parse_equals("-0d0 ", Decimal::new(Negative, 0, 0));
        parse_equals("-0D0 ", Decimal::new(Negative, 0, 0));
        parse_equals("305d1 ", Decimal::new(Positive, 305, 1));
        parse_equals("305d-1 ", Decimal::new(Positive, 305, -1));
        parse_equals("111_111d222 ", Decimal::new(Positive, 111_111, 222));
        parse_equals("111_111d-222 ", Decimal::new(Positive, 111_111, -222));
        parse_equals("111_111d222_222 ", Decimal::new(Positive, 111_111, 222_222));
        parse_equals("-279d0 ", Decimal::new(Negative, 279, 0));
        parse_equals("-999_9d9_9 ", Decimal::new(Negative, 9_999, 99));
        parse_equals("-999_9d-9_9 ", Decimal::new(Negative, 9_999, -99));

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
        use Sign::{Positive, Negative};

        parse_equals("0. ", Decimal::new(Positive, 0, 0));
        parse_equals("-0. ", Decimal::new(Negative, 0, 0));
        parse_equals("0.0 ",  Decimal::new(Positive, 0, -1));
        parse_equals("0.5 ", Decimal::new(Positive, 5, -1));
        parse_equals("3050. ", Decimal::new(Positive, 3050, 0));
        parse_equals("3050.667 ", Decimal::new(Positive, 3050667, -3));
        parse_equals("111_111.000 ", Decimal::new(Positive, 111111000, -3));
        parse_equals("111_111.0_0_0 ", Decimal::new(Positive, 111111000, -3));
        parse_equals("-279. ", Decimal::new(Negative, 279, 0));
        parse_equals("-279.0 ", Decimal::new(Negative, 2790, -1));
        parse_equals("-279.701 ", Decimal::new(Negative, 279701, -3));
        parse_equals("-999_9.0_0 ", Decimal::new(Negative, 999900, -2));

        // // Missing decimal point, would be parsed as an integer
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