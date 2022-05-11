//! This module contains logic to parse the the text representation of each Ion type.
//! See: <https://amzn.github.io/ion-docs/docs/spec.html>

use std::str::FromStr;

use crate::text::parse_result::{fatal_parse_error, IonParseResult, UpgradeIResult};
use nom::bytes::streaming::is_a;
use nom::character::streaming::one_of;
use nom::combinator::peek;

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

const WHITESPACE_CHARACTERS: &[char] = &[
    ' ',    // Space
    '\t',   // Tab
    '\r',   // Carriage return
    '\n',   // Newline
    '\x09', // Horizontal tab
    '\x0B', // Vertical tab
    '\x0C', // Form feed
];

/// Same as [WHITESPACE_CHARACTERS], but formatted as a string for use in some `nom` APIs
const WHITESPACE_CHARACTERS_AS_STR: &str = " \t\r\n\x09\x0B\x0C";

// ===== The functions below are used by several modules and live here for common access. =====

/// Matches (but does not consume) the next character in the input stream if it is one of the Ion
/// stop characters. These characters must follow several different Ion text encodings, including
/// integers, floats, decimals, and timestamps.
pub(crate) fn stop_character(input: &str) -> IonParseResult<char> {
    peek(one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}"))(input).upgrade()
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
pub(crate) fn trim_zeros_and_parse_u32<'a>(input: &'a str, label: &str) -> IonParseResult<'a, u32> {
    match u32::from_str(trim_leading_zeros(input)) {
        Ok(value) => Ok(("", value)), // The entire input was consumed, leaving the empty string
        Err(e) => fatal_parse_error(input, format!("parsing {} as a u32 failed: {}", label, e)),
    }
}

/// Takes a numeric string and removes all leading zeros before attempting to parse it as an i32.
/// Callers are expected to validate the numeric text being passed before calling this method.
/// If parsing fails, `trim_zeros_expect_i32` will panic and produce an error message containing
/// the text in `label`.
pub(crate) fn trim_zeros_and_parse_i32<'a>(input: &'a str, label: &str) -> IonParseResult<'a, i32> {
    match i32::from_str(trim_leading_zeros(input)) {
        Ok(value) => Ok(("", value)), // The entire input was consumed, leaving the empty string
        Err(e) => fatal_parse_error(input, format!("parsing {} as an i32 failed: {}", label, e)),
    }
}

/// Matches one or more whitespace characters.
pub(crate) fn whitespace(input: &str) -> IonParseResult<&str> {
    is_a(WHITESPACE_CHARACTERS_AS_STR)(input).upgrade()
}

/// Helper functions used in the unit tests for each parsing module.
#[cfg(test)]
pub(crate) mod unit_test_support {
    use crate::text::parse_result::IonParseResult;
    use nom::Finish;
    use std::fmt::Debug;

    /// Uses `parser` to parse the provided `text` and then asserts that the output is equal
    /// to `expected`.
    pub(crate) fn parse_test_ok<'a, T, P>(parser: P, text: &'a str, expected: T)
    where
        T: Debug + PartialEq,
        P: Fn(&'a str) -> IonParseResult<'a, T>,
    {
        let actual = parse_unwrap(parser, text);
        assert_eq!(actual, expected);
    }

    /// Uses `parser` to parse the provided `text` expecting it to fail. If it succeeds, this
    /// method will panic and display the value that was read.
    pub(crate) fn parse_test_err<'a, T, P>(parser: P, text: &'a str)
    where
        T: Debug,
        P: Fn(&'a str) -> IonParseResult<'a, T>,
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
        P: Fn(&'a str) -> IonParseResult<'a, T>,
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
