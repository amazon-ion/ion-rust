use crate::text::parse_result::{IonParseResult, OrFatalParseError, UpgradeIResult};
use crate::text::parsers::numeric_support::{
    digits_before_dot, exponent_digits, floating_point_number,
};
use crate::text::parsers::stop_character;
use crate::text::text_value::TextValue;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::one_of;
use nom::combinator::{map, opt, recognize};
use nom::sequence::{pair, preceded, terminated, tuple};
use nom::Parser;
use std::str::FromStr;

/// Matches the text representation of a float value and returns the resulting [f64]
/// as a [TextValue::Float].
pub(crate) fn parse_float(input: &str) -> IonParseResult<TextValue> {
    terminated(
        alt((float_special_value, float_numeric_value)),
        stop_character,
    )(input)
}

/// Matches special IEEE-754 floating point values, including +/- infinity and NaN.
fn float_special_value(input: &str) -> IonParseResult<TextValue> {
    map(tag("nan"), |_| TextValue::Float(f64::NAN))
        .or(map(tag("+inf"), |_| TextValue::Float(f64::INFINITY)))
        .or(map(tag("-inf"), |_| TextValue::Float(f64::NEG_INFINITY)))
        .parse(input)
        .upgrade()
}

/// Matches numeric floating point values. (e.g. `7e0`, `7.1e0` or `71e-1`)
fn float_numeric_value(input: &str) -> IonParseResult<TextValue> {
    let (remaining, text) = recognize(tuple((
        alt((
            floating_point_number,
            recognize(pair(opt(tag("-")), digits_before_dot)),
        )),
        recognize(float_exponent_marker_followed_by_digits),
    )))(input)?;
    // TODO: Reusable buffer for sanitization
    let mut sanitized = text.replace('_', "");
    if sanitized.ends_with('e') || sanitized.ends_with('E') {
        sanitized.push('0');
    }
    let float = f64::from_str(&sanitized)
        .or_fatal_parse_error(input, "could not parse float as f64")?
        .1;
    Ok((remaining, TextValue::Float(float)))
}

fn float_exponent_marker_followed_by_digits(input: &str) -> IonParseResult<&str> {
    preceded(one_of("eE"), exponent_digits)(input)
}

#[cfg(test)]
mod float_parsing_tests {
    use crate::text::parsers::float::parse_float;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok, parse_unwrap};
    use crate::text::text_value::TextValue;
    use std::str::FromStr;

    fn parse_equals(text: &str, expected: f64) {
        parse_test_ok(parse_float, text, TextValue::Float(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_float, text)
    }

    #[test]
    fn test_parse_float_special_values() {
        parse_equals("+inf ", f64::INFINITY);
        parse_equals("-inf ", f64::NEG_INFINITY);

        // Can't test two NaNs for equality with assert_eq
        let value = parse_unwrap(parse_float, "nan ");
        if let TextValue::Float(f) = value {
            assert!(f.is_nan());
        } else {
            panic!("Expected NaN, but got: {:?}", value);
        }

        // -0 keeps its negative sign
        let value = parse_unwrap(parse_float, "-0e0 ");
        if let TextValue::Float(f) = value {
            assert!(f == 0.0f64);
            assert!(f.is_sign_negative())
        } else {
            panic!("Expected -0e0, but got: {:?}", value);
        }
    }

    #[test]
    fn test_parse_float_numeric_values() {
        parse_equals("0.0e0 ", 0.0);
        parse_equals("0E0 ", 0.0);
        parse_equals("0e0 ", 0e0);
        parse_equals("305e1 ", 3050.0);
        parse_equals("305.0e1 ", 3050.0);
        parse_equals("-0.279e3 ", -279.0);
        parse_equals("-279e0 ", -279.0);
        parse_equals("-279.5e0 ", -279.5);

        // Missing exponent (would be parsed as an integer)
        parse_fails("305 ");
        // Has exponent delimiter but missing exponent
        parse_fails("305e ");
        // No digits before the decimal point
        parse_fails(".305e ");
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
