use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::complete::multispace0;
use nom::combinator::map_opt;
use nom::multi::many1;
use nom::sequence::{delimited, pair, preceded};
use nom::{IResult, Parser};

use crate::text::parsers::blob::parse_blob;
use crate::text::parsers::boolean::parse_boolean;
use crate::text::parsers::clob::parse_clob;
use crate::text::parsers::comments::parse_comment;
use crate::text::parsers::containers::{parse_container_end, parse_container_start};
use crate::text::parsers::decimal::parse_decimal;
use crate::text::parsers::float::parse_float;
use crate::text::parsers::integer::parse_integer;
use crate::text::parsers::null::parse_null;
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::parse_symbol;
use crate::text::parsers::timestamp::parse_timestamp;
use crate::text::TextStreamItem;
use crate::value::owned::OwnedSymbolToken;

/// Matches a TextStreamItem at the beginning of the given string.
pub(crate) fn stream_item(input: &str) -> IResult<&str, TextStreamItem> {
    alt((
        parse_null,
        parse_boolean,
        parse_integer,
        parse_float,
        parse_decimal,
        parse_timestamp,
        parse_string,
        parse_symbol,
        parse_blob,
        parse_clob,
        parse_container_start,
        parse_container_end,
        parse_comment,
    ))(input)
}

/// Matches a series of annotations and their associated TextStreamItem.
pub(crate) fn annotated_stream_item(
    input: &str,
) -> IResult<&str, (Vec<OwnedSymbolToken>, TextStreamItem)> {
    pair(parse_annotations, stream_item)(input)
}

/// Matches an optional series of annotations and a TextStreamItem at the beginning of the given
/// string. If there are no annotations (or the TextStreamItem found cannot have annotations), the
/// annotations [Vec] will be empty.
pub(crate) fn top_level_stream_item(
    input: &str,
) -> IResult<&str, (Vec<OwnedSymbolToken>, TextStreamItem)> {
    preceded(
        // Allow any amount of whitespace followed by...
        multispace0,
        // either...
        alt((
            // An annotated value or...
            annotated_stream_item,
            // An empty Vec paired with an unannotated value.
            // `Vec::new()` does not allocate, so calling this for each item is cheap.
            stream_item.map(|x| (Vec::new(), x)),
        )),
    )(input)
}

/// Matches a series of '::'-delimited symbols used to annotate a value.
pub(crate) fn parse_annotations(input: &str) -> IResult<&str, Vec<OwnedSymbolToken>> {
    many1(parse_annotation)(input)
}

/// Matches a single symbol of any format (foo, 'foo', or $10) followed by a '::' delimiter.
/// The delimiter can be preceded or trailed by any amount of whitespace.
pub(crate) fn parse_annotation(input: &str) -> IResult<&str, OwnedSymbolToken> {
    map_opt(
        // 0+ spaces, a symbol ('quoted', identifier, or $id), 0+ spaces, '::'
        delimited(multispace0, parse_symbol, annotation_delimiter),
        |text_stream_item| {
            // This should always be true because `parse_symbol` would not have matched an
            // item if it were not a symbol.
            if let TextStreamItem::Symbol(symbol) = text_stream_item {
                return Some(symbol);
            }
            None
        },
    )(input)
}

fn annotation_delimiter(input: &str) -> IResult<&str, &str> {
    preceded(multispace0, tag("::"))(input)
}

#[cfg(test)]
// TODO: Move relevant tests from reader.rs to this module
mod parse_top_level_value_tests {
    use super::*;
    use crate::types::SymbolId;
    use crate::value::owned::{local_sid_token, text_token};
    use rstest::*;

    // Unit test helper; converts strings into OwnedSymbolTokens
    fn text_tokens(strs: &[&str]) -> Vec<OwnedSymbolToken> {
        return strs.iter().map(|s| text_token(*s)).collect();
    }

    #[rstest]
    #[case::identifier_no_spaces("foo::", "foo")]
    #[case::identifier_leading_spaces("   foo::", "foo")]
    #[case::identifier_trailing_spaces("foo::   ", "foo")]
    #[case::identifier_interstitial_spaces("foo   ::", "foo")]
    #[case::identifier_all_spaces("   foo   ::   ", "foo")]
    #[case::quoted_no_spaces("'foo'::", "foo")]
    #[case::quoted_leading_spaces("   'foo'::", "foo")]
    #[case::quoted_trailing_spaces("'foo'::   ", "foo")]
    #[case::quoted_interstitial_spaces("'foo'   ::", "foo")]
    #[case::quoted_all_spaces("   'foo'   ::   ", "foo")]
    fn test_parse_annotation(#[case] text: &str, #[case] expected: &str) {
        assert_eq!(parse_annotation(text).unwrap().1, text_token(expected));
    }

    #[rstest]
    #[case::symbol_id_no_spaces("$10::", 10)]
    #[case::symbol_id_leading_spaces("   $10::", 10)]
    #[case::symbol_id_trailing_spaces("$10::   ", 10)]
    #[case::symbol_id_interstitial_spaces("$10   ::", 10)]
    #[case::symbol_id_all_spaces("   $10   ::   ", 10)]
    fn test_parse_symbol_id_annotation(#[case] text: &str, #[case] expected: SymbolId) {
        assert_eq!(parse_annotation(text).unwrap().1, local_sid_token(expected));
    }

    #[rstest]
    // For these tests, the input text must end in an unrelated value so the parser knows that
    // the first value is complete. For example, it's not possible to know whether this Ion data:
    //     foo::bar::baz
    // is the symbol 'baz' with the annotations 'foo' and 'bar', or if it's actually
    // _three annotations_ on a value that we're still waiting to read from the stream.
    // On the other hand, a parser looking at the same data with a trailing value like this:
    //     foo::bar::baz END
    // can easily tell that 'foo' and 'bar' are annotations and 'baz' is the value.
    // Here, 'END' is simply an unrelated symbol value that the parser knows to ignore.
    #[case("foo::bar::baz END", &["foo", "bar"], TextStreamItem::Symbol(text_token("baz")))]
    #[case("foo::bar::baz END", &["foo", "bar"], TextStreamItem::Symbol(text_token("baz")))]
    #[case("foo::'bar'::7 END", &["foo", "bar"], TextStreamItem::Integer(7))]
    #[case("'foo'::'bar'::{ END", &["foo", "bar"], TextStreamItem::StructStart)]
    #[case("'foo bar'::false END", &["foo bar"], TextStreamItem::Boolean(false))]
    fn test_parse_annotated_value(
        #[case] text: &str,
        #[case] expected_annotations: &[&str],
        #[case] expected_item: TextStreamItem,
    ) {
        assert_eq!(
            annotated_stream_item(text).unwrap().1,
            (text_tokens(expected_annotations), expected_item)
        );
    }
}
