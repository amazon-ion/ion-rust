//! Parsing logic for the text representation of boolean values.

use nom::bytes::streaming::tag;
use nom::combinator::{map, recognize};
use nom::sequence::terminated;
use nom::{IResult, Parser};

use crate::text::parsers::stop_character;
use crate::text::text_value::TextValue;

/// Matches the text representation of a boolean value and returns the resulting `true` or `false`
/// as a [TextValue::Boolean].
pub(crate) fn parse_boolean(input: &str) -> IResult<&str, TextValue> {
    map(
        recognize(terminated(tag("true").or(tag("false")), stop_character)),
        |bool_text: &str| match bool_text {
            "true" => TextValue::Boolean(true),
            "false" => TextValue::Boolean(false),
            _ => unreachable!("text had to match 'true' or 'false' before reaching this point"),
        },
    )(input)
}

#[cfg(test)]
mod boolean_parsing_tests {
    use crate::text::parsers::boolean::parse_boolean;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;

    fn parse_equals(text: &str, expected: bool) {
        parse_test_ok(parse_boolean, text, TextValue::Boolean(expected))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_boolean, text)
    }

    #[test]
    fn test_parse_booleans() {
        parse_equals("true ", true);
        parse_equals("false ", false);

        // Misspelled boolean name
        parse_fails("ture ");
        parse_fails("fasle ");
        // Capitalized
        parse_fails("True ");
        parse_fails("TRUE ");
        // Leading whitespace
        parse_fails(" true");
        // Boolean is end of current input; might be an incomplete stream
        parse_fails("true");
    }
}
