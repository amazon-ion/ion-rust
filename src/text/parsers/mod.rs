// This module contains logic to parse the the text representation of each Ion type.
// See: https://amzn.github.io/ion-docs/docs/spec.html

use std::str::FromStr;

use nom::bytes::streaming::is_a;
use nom::character::streaming::{one_of, satisfy};
use nom::combinator::peek;
use nom::IResult;

pub(crate) mod annotations;
pub(crate) mod blob;
pub(crate) mod boolean;
pub(crate) mod clob;
mod comments;
pub(crate) mod containers;
pub(crate) mod decimal;
pub(crate) mod float;
pub(crate) mod integer;
pub(crate) mod null;
pub(crate) mod numeric_support;
pub(crate) mod string;
pub(crate) mod symbol;
pub(crate) mod text_support;
pub(crate) mod timestamp;
pub(crate) mod top_level;
pub(crate) mod value;

// ===== The functions below are used by several modules and live here for common access. =====

/// Matches (but does not consume) the next character in the input stream if it is one of the Ion
/// stop characters. These characters must follow several different Ion text encodings, including
/// integers, floats, decimals, and timestamps.
pub(crate) fn stop_character(input: &str) -> IResult<&str, char> {
    peek(one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}"))(input)
}

/// Takes a numeric string and removes all leading zeros. If the string is entirely zeros
/// (for example, "0" or "000"), it will be reduced to a single zero ("0").
pub(crate) fn trim_leading_zeros(input: &str) -> &str {
    // Remove all leading zeros. If the last character is a zero, leave it alone.
    let trimmed = input.trim_start_matches('0');
    if trimmed.is_empty() {
        return "0";
    }
    trimmed
}

/// Takes a numeric string and removes all leading zeros before attempting to parse it as a u32.
/// Callers are expected to validate the numeric text being passed before calling this method.
/// If parsing fails, `trim_zeros_expect_u32` will panic and produce an error message containing
/// the text in `label`.
pub(crate) fn trim_zeros_expect_u32(input: &str, label: &str) -> u32 {
    u32::from_str(trim_leading_zeros(input)).expect(&format!("parsing {} as a u32 failed", label))
}

/// Takes a numeric string and removes all leading zeros before attempting to parse it as an i32.
/// Callers are expected to validate the numeric text being passed before calling this method.
/// If parsing fails, `trim_zeros_expect_i32` will panic and produce an error message containing
/// the text in `label`.
pub(crate) fn trim_zeros_expect_i32(input: &str, label: &str) -> i32 {
    i32::from_str(trim_leading_zeros(input)).expect(&format!("parsing {} as an i32 failed", label))
}

/// Matches the next input character if it is a base-10 digit. This wraps [char::is_digit] in the
/// nom parsing function signature.
pub(crate) fn digit(input: &str) -> IResult<&str, char> {
    satisfy(|c| c.is_digit(10))(input)
}

/// Matches one or more whitespace characters.
pub(crate) fn whitespace(input: &str) -> IResult<&str, &str> {
    is_a(" \r\n\t")(input)
}

/// Helper functions used in the unit tests for each parsing module.
#[cfg(test)]
pub(crate) mod unit_test_support {
    use nom::{Finish, IResult};
    use std::fmt::Debug;

    /// Uses `parser` to parse the provided `text` and then asserts that the output is equal
    /// to `expected`.
    pub(crate) fn parse_test_ok<'a, T, P>(parser: P, text: &'a str, expected: T)
    where
        T: Debug + PartialEq,
        P: Fn(&'a str) -> IResult<&'a str, T>,
    {
        let actual = parse_unwrap(parser, text);
        assert_eq!(actual, expected);
    }

    /// Uses `parser` to parse the provided `text` expecting it to fail. If it succeeds, this
    /// method will panic and display the value that was read.
    pub(crate) fn parse_test_err<'a, T, P>(parser: P, text: &'a str)
    where
        T: Debug,
        P: Fn(&'a str) -> IResult<&'a str, T>,
    {
        let parsed = parser(text);
        if parsed.is_ok() {
            panic!(
                "parse unexpectedly succeeded: {:?} -> {:?}",
                text,
                parsed.unwrap().1
            );
        }
    }

    /// Uses `parser` to parse the provided `text` and then unwraps the resulting value.
    /// If parsing fails, this method will panic.
    pub(crate) fn parse_unwrap<'a, T, P>(parser: P, text: &'a str) -> T
    where
        T: Debug + PartialEq,
        P: Fn(&'a str) -> IResult<&'a str, T>,
    {
        let parsed = parser(text);
        if parsed.is_err() {
            panic!(
                "{:?}: parse unexpectedly failed on input: {:?}",
                parsed.finish(),
                text
            );
        }
        parsed.unwrap().1
    }
}
