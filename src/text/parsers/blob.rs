//! Parsing logic for the text representation of blob values.

use crate::text::parse_result::{fatal_parse_error, IonParseResult, UpgradeIResult};
use nom::branch::alt;
use nom::bytes::streaming::{is_a, tag};
use nom::character::streaming::alphanumeric1;
use nom::combinator::{opt, recognize};
use nom::multi::{many0_count, many1_count};
use nom::sequence::{delimited, pair, terminated};

use crate::text::parsers::{whitespace, WHITESPACE_CHARACTERS};
use crate::text::text_value::TextValue;

/// Matches the text representation of a blob value, decodes it, and returns the resulting bytes
/// as a [TextValue::Blob].
pub(crate) fn parse_blob(input: &str) -> IonParseResult<TextValue> {
    let (remaining_input, base64_text) = delimited(
        pair(tag("{{"), opt(whitespace)),
        // Whitespace can appear in between chunks of the base64 data. Here we match on any
        // number of (base64_data, optional_whitespace) chunks and return the &str that contained them.
        recognize(many0_count(terminated(
            recognize_base64_data,
            opt(whitespace),
        ))),
        pair(opt(whitespace), tag("}}")),
    )(input)?;

    let decode_result = if base64_text.contains(WHITESPACE_CHARACTERS) {
        let sanitized = base64_text.replace(WHITESPACE_CHARACTERS, "");
        base64::decode(sanitized)
    } else {
        base64::decode(base64_text)
    };

    // If the parser matched the input text ("{{ ... }}"), it's definitely supposed to be
    // a blob. If we can't decode that text as base64, the stream is malformed.
    match decode_result {
        Ok(data) => Ok((remaining_input, TextValue::Blob(data))),
        Err(e) => fatal_parse_error(base64_text, format!("could not decode base64 data: {}", e)),
    }
}

/// Matches a series of valid base64-encoded characters. This function does not attempt to decode
/// the matched value; it is possible for it to match a string that cannot be decoded successfully.
fn recognize_base64_data(input: &str) -> IonParseResult<&str> {
    recognize(many1_count(alt((alphanumeric1, is_a("+/=")))))(input).upgrade()
}

#[cfg(test)]
mod blob_parsing_tests {
    use std::iter::FromIterator;

    use crate::text::parsers::blob::parse_blob;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;

    fn parse_equals<A: AsRef<[u8]>>(text: &str, expected: A) {
        let data = Vec::from_iter(expected.as_ref().iter().copied());
        parse_test_ok(parse_blob, text, TextValue::Blob(data))
    }

    fn parse_fails(text: &str) {
        parse_test_err(parse_blob, text)
    }

    #[test]
    fn test_parse_blobs() {
        // In each test below, the expected strings (on the right) are being coerced into byte
        // arrays before being compared to the results of the parsed text.

        // No padding characters ('=') required
        parse_equals("{{aGVsbG8h}} ", "hello!");
        // 1 padding character required
        parse_equals(
            "{{YnJldml0eSBpcyB0aGUgc291bCBvZiB3aXQ=}} ",
            "brevity is the soul of wit",
        );
        // 2 padding characters required
        parse_equals("{{Zm9vLCBiYXIsIGJheiwgcXV1eA==}} ", "foo, bar, baz, quux");
        // Various legal whitespace arrangements
        parse_equals("{{   aGVsbG8h}} ", "hello!");
        parse_equals("{{aGVsbG8h   }} ", "hello!");
        parse_equals("{{   aGVsbG8h   }} ", "hello!");

        // Delimiting {{ has spaces in it
        parse_fails("{ {Zm9vLCBiYXIsIGJheiwgcXV1eA==}} ");
        // Delimiting }} has spaces in it
        parse_fails("{{Zm9vLCBiYXIsIGJheiwgcXV1eA==} } ");
        // Too many padding characters
        parse_fails("{{Zm9vLCBiYXIsIGJheiwgcXV1eA===}} ");
        // Padding characters somewhere other than at the end
        parse_fails("{{Zm9vLC=BiYXIsIGJheiwgcXV1eA==}} ");
        // Non-base64 character in the value
        parse_fails("{{Zm9vLCBiYXIsI_GJheiwgcXV1eA==}} ");
    }
}
