//! Parsing logic for the text representation of blob values.

use base64::DecodeError;
use nom::IResult;
use nom::branch::alt;
use nom::bytes::streaming::{is_a, tag};
use nom::character::streaming::{alphanumeric1, char};
use nom::combinator::{map_res, opt, recognize};
use nom::multi::many0_count;
use nom::sequence::{delimited, pair};

use crate::text::parsers::whitespace;
use crate::text::TextStreamItem;

/// Matches the text representation of a blob value, decodes it, and returns the resulting bytes
/// as a [TextStreamItem::Blob].
pub(crate) fn parse_blob(input: &str) -> IResult<&str, TextStreamItem> {
    map_res::<_, _, _, _, DecodeError, _, _>(
        delimited(
            pair(tag("{{"), opt(whitespace)),
            recognize_base64_data,
            pair(opt(whitespace), tag("}}")),
        ),
        |base64_text| {
            Ok(TextStreamItem::Blob(base64::decode(base64_text)?))
        }
    )(input)
}

/// Matches a series of valid base64-encoded characters. (This function does not attempt to decode
/// the matched value.)
fn recognize_base64_data(input: &str) -> IResult<&str, &str> {
    recognize(
        pair(
            many0_count(
                alt((alphanumeric1, is_a("+/")))
            ),
        pair(opt(char('=')), opt(char('=')))
        )
    )(input)
}

#[cfg(test)]
mod blob_parsing_tests {
    use std::iter::FromIterator;

    use crate::text::parsers::blob::parse_blob;
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::TextStreamItem;

    fn parse_equals<A: AsRef<[u8]>>(text: &str, expected: A) {
        let data = Vec::from_iter(expected.as_ref().iter().copied());
        parse_test_ok(parse_blob, text, TextStreamItem::Blob(data))
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
        parse_equals("{{YnJldml0eSBpcyB0aGUgc291bCBvZiB3aXQ=}} ", "brevity is the soul of wit");
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