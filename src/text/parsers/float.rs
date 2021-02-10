use nom::{IResult, Parser};
use crate::text::TextStreamItem;
use nom::sequence::{terminated, preceded, tuple};
use nom::branch::alt;
use crate::text::parsers::stop_character;
use nom::combinator::{map_res, opt, recognize, map};
use nom::bytes::streaming::{tag};
use nom::character::streaming::one_of;
use crate::text::parsers::numeric_support::{digits_before_dot, floating_point_number, exponent_digits};
use std::num::ParseFloatError;
use std::str::FromStr;

pub(crate) fn parse_float(input: &str) -> IResult<&str, TextStreamItem> {
    terminated(
        alt((float_special_value, float_numeric_value)),
        stop_character
    )(input)
}

fn float_special_value(input: &str) -> IResult<&str, TextStreamItem> {
    map(tag("nan"), |_| TextStreamItem::Float(f64::NAN))
        .or(map(tag("+inf"), |_| TextStreamItem::Float(f64::INFINITY)))
        .or(map(tag("-inf"), |_| TextStreamItem::Float(f64::NEG_INFINITY)))
        .parse(input)
}

fn float_numeric_value(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, ParseFloatError, _, _>(
        recognize(
            tuple((
                opt(tag("-")),
                alt((floating_point_number, digits_before_dot)),
                recognize(float_exponent_marker_followed_by_digits),
            ))),
        |text| {
            println!("Numeric float: {:?}", text);
            // TODO: Reusable buffer for sanitization
            let mut sanitized = text.replace("_", "");
            if sanitized.ends_with('e') || sanitized.ends_with('E') {
                sanitized.push_str("0");
            }
            println!("Sanitized: {:?}", &sanitized);
            Ok(TextStreamItem::Float(f64::from_str(&sanitized)?))
        }
    )(input)
}

fn float_exponent_marker_followed_by_digits(input: &str) -> IResult<&str, Option<&str>> {
    preceded(
        one_of("eE"),
        opt(exponent_digits)
    )(input)
}

#[cfg(test)]
mod float_parsing_tests {
    use crate::text::parsers::unit_test_support::{parse_test_ok, parse_test_err, parse_unwrap};
    use crate::text::TextStreamItem;
    use crate::text::parsers::float::parse_float;
    use std::str::FromStr;

    fn parse_equals(text: &str, expected: f64) {
        parse_test_ok(parse_float, text, TextStreamItem::Float(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_float, text)
    }

    #[test]
    fn test_parse_float_special_values() {
        parse_equals("+inf ", f64::INFINITY);
        parse_equals("-inf ", f64::NEG_INFINITY);

        // Can't test two NaNs for equality with assert_eq
        let item = parse_unwrap(parse_float, "nan ");
        if let TextStreamItem::Float(f) = item {
            assert!(f.is_nan());
        } else {
            panic!("Expected NaN, but got: {:?}", item);
        }
    }

    #[test]
    fn test_parse_float_numeric_values() {
        parse_equals("0.0e ", 0.0);
        parse_equals("0E ", 0.0);
        parse_equals("0e0 ", 0e0);
        parse_equals("305e1 ", 3050.0);
        parse_equals("305.0e1 ", 3050.0);
        parse_equals("-279e ", -279.0);
        parse_equals("-279e0 ", -279.0);
        parse_equals("-279.5e ", -279.5);

        // // Missing exponent (would be parsed as an integer)
        parse_fails("305 ");
        // Fractional exponent
        parse_fails("305e0.5");
        // Negative fractional exponent
        parse_fails("305e-0.5");
        // Doesn't consume leading whitespace
        parse_fails(" 305e1 ");
        // Doesn't accept leading zeros
        parse_fails("0305e1 ");
        // Doesn't accept leading plus sign
        parse_fails("+305e1 ");
        // Doesn't accept multiple negative signs
        parse_fails("--305e1 ");
        // Doesn't accept a number if it's the last thing in the input (might be incomplete stream)
        parse_fails("305e1");
    }

    #[test]
    fn test_parse_float_numeric_values_with_underscores() {
        parse_equals("111_111e222 ", 111111.0 * 10f64.powf(222f64));
        parse_equals("111_111.667e222 ", 111111.667 * 10f64.powf(222f64));
        parse_equals("111_111e222_222 ", 111111.0 * 10f64.powf(222222f64));
        parse_equals("-999_9e9_9 ", f64::from_str("-9999e99").unwrap());

        // Doesn't accept leading underscores
        parse_fails("_305e1 ");
        // Doesn't accept trailing underscores
        parse_fails("305e1_ ");
        // Doesn't accept multiple consecutive underscores
        parse_fails("30__5e1 ");
    }
}