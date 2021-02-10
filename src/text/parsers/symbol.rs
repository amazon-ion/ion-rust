use nom::combinator::{map, recognize, verify};
use nom::{IResult};
use nom::sequence::{delimited, terminated, pair};
use nom::branch::alt;
use nom::character::streaming::{char, satisfy, one_of};
use nom::bytes::streaming::is_not;
use crate::text::TextStreamItem;
use nom::multi::{fold_many0, many0_count};
use crate::text::parsers::stop_character;
use crate::text::parsers::text_support::{StringFragment, escaped_newline, escaped_char};

pub(crate) fn parse_symbol(input: &str) -> IResult<&str, TextStreamItem> {
    alt((identifier, quoted_symbol))(input)
}

fn quoted_symbol(input: &str) -> IResult<&str, TextStreamItem> {
    map(
        delimited(char('\''), quoted_symbol_body, char('\'')),
        |text| {
            println!("Symbol text: {:?}", &text);
            TextStreamItem::Symbol(text)
        }
    )(input)
}

fn quoted_symbol_body(input: &str) -> IResult<&str, String> {
    fold_many0(
        quoted_symbol_string_fragment,
        String::new(),
        |mut string, fragment| {
            match fragment {
                StringFragment::EscapedNewline => {} // Discard escaped newlines
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::Substring(s) => string.push_str(s),
            }
            string
        },
    )(input)
}

fn quoted_symbol_string_fragment(input: &str) -> IResult<&str, StringFragment> {
    alt((
        escaped_newline,
        escaped_char,
        quoted_symbol_fragment_without_escaped_text,
    ))(input)
}

fn quoted_symbol_fragment_without_escaped_text(input: &str) -> IResult<&str, StringFragment> {
    map(
        verify(is_not("'\\'"), |s: &str| !s.is_empty()),
        |text| StringFragment::Substring(text)
    )(input)
}

fn identifier(input: &str) -> IResult<&str, TextStreamItem> {
    map(
        recognize(
            terminated(
                pair(
                    identifier_initial_character,
                    identifier_trailing_characters
                ),
                stop_character
            )
        ),
        |text| {
            TextStreamItem::Symbol(text.to_owned())
        }
    )(input)
}

fn identifier_initial_character(input: &str) -> IResult<&str, char> {
    alt((one_of("$_"), satisfy(|c| c.is_ascii_alphabetic())))(input)
}

fn identifier_trailing_characters(input: &str) -> IResult<&str, &str> {
    recognize(
        many0_count(
            alt((
                one_of("$_"),
                satisfy(|c| c.is_ascii_alphanumeric())
            ))
        )
    )(input)
}

#[cfg(test)]
mod symbol_parsing_tests {
    use crate::text::parsers::unit_test_support::{parse_test_ok, parse_test_err};
    use crate::text::TextStreamItem;
    use crate::text::parsers::symbol::parse_symbol;

    fn parse_equals(text: &str, expected: &str) {
        parse_test_ok(parse_symbol, text, TextStreamItem::Symbol(expected.to_owned()))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_symbol, text)
    }

    #[test]
    fn test_parse_quoted_symbols() {
        parse_equals("'foo' ", "foo");
        parse_equals("'$foo' ", "$foo");
        parse_equals("'_foo' ", "_foo");
        parse_equals("'11foo' ", "11foo");
        parse_equals("'$_' ", "$_");
        parse_equals("'$ion_1_0' ", "$ion_1_0");
        parse_equals("'__foo__' ", "__foo__");
        parse_equals("'foo12345' ", "foo12345");
        parse_equals("'foo bar baz' ", "foo bar baz");
        parse_equals("'foo \"bar\" baz' ", "foo \"bar\" baz");
        parse_equals("'7@#$%^&*()!' ", "7@#$%^&*()!");

        // Leading whitespace not accepted
        parse_fails(" 'foo' ");
    }

    #[test]
    fn test_parse_symbol_identifiers() {
        parse_equals("foo ", "foo");
        parse_equals("$foo ", "$foo");
        parse_equals("_foo ", "_foo");
        parse_equals("$_ ", "$_");
        parse_equals("$ion_1_0 ", "$ion_1_0");
        parse_equals("__foo__ ", "__foo__");
        parse_equals("foo12345 ", "foo12345");

        // Starts with a digit
        parse_fails("1foo ");
        // Leading whitespace not accepted
        parse_fails(" foo ");
        // Cannot be the last thing in input (stream might be incomplete
        parse_fails("foo");
    }
}