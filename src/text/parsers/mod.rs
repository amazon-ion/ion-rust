use std::str::FromStr;
use nom::IResult;
use nom::character::streaming::{satisfy, one_of};
use nom::bytes::streaming::is_a;
use nom::combinator::peek;

pub(crate) mod boolean;
pub(crate) mod blob;
pub(crate) mod decimal;
pub(crate) mod float;
pub(crate) mod integer;
pub(crate) mod null;
pub(crate) mod numeric_support;
pub(crate) mod string;
pub(crate) mod symbol;
pub(crate) mod text_support;
pub(crate) mod timestamp;

// TODO: Are these only stop characters for numeric values? See the ANTLR grammar:
// https://amzn.github.io/ion-docs/grammar/IonText.g4.txt
pub(crate) fn stop_character(input: &str) -> IResult<&str, char> {
    peek(one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}"))(input)
}

pub(crate) fn trim_leading_zeros(input: &str) -> &str {
    // Remove all leading zeros. If the last character is a zero, leave it alone.
    let trimmed = input.trim_start_matches('0');
    if trimmed.is_empty() {
        return "0";
    }
    trimmed
}

pub(crate) fn trim_zeros_expect_u32(input: &str, label: &str) -> u32 {
    u32::from_str(trim_leading_zeros(input))
        .expect(&format!("parsing {} as a u32 failed", label))
}

pub(crate) fn trim_zeros_expect_i32(input: &str, label: &str) -> i32 {
    i32::from_str(trim_leading_zeros(input))
        .expect(&format!("parsing {} as an i32 failed", label))
}

pub(crate) fn digit(input: &str) -> IResult<&str, char> {
    satisfy(|c| c.is_digit(10))(input)
}

pub(crate) fn whitespace(input: &str) -> IResult<&str, &str> {
    //TODO Comments
    is_a(" \r\n\t")(input)
}

#[cfg(test)]
pub(crate) mod unit_test_support {
    use crate::text::TextStreamItem;
    use nom::{IResult, Finish};

    pub(crate) type TestParser = fn(&str) -> IResult<&str, TextStreamItem>;

    pub(crate) fn parse_test_ok(parser: TestParser, text: &str, expected: TextStreamItem) {
        let actual = parse_unwrap(parser, text);
        assert_eq!(expected, actual);
    }

    pub(crate) fn parse_test_err(parser: TestParser, text: &str) {
        let parsed = parser(text);
        if parsed.is_ok() {
            panic!("Parse unexpectedly succeeded: {:?} -> {:?}", text, parsed.unwrap().1);
        }
    }

    pub(crate) fn parse_unwrap(parser: TestParser, text: &str) -> TextStreamItem {
        let parsed = parser(text);
        if parsed.is_err() {
            panic!("{:?}: Parse unexpectedly failed on input: {:?}", parsed.finish(), text);
        }
        parsed.unwrap().1
    }
}