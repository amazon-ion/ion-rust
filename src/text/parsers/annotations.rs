use crate::text::parsers::comments::whitespace_or_comments;
use nom::bytes::streaming::tag;
use nom::character::streaming::multispace0;
use nom::combinator::map_opt;
use nom::multi::many1;
use nom::sequence::{delimited, pair, preceded};
use nom::IResult;
use crate::raw_symbol_token::RawSymbolToken;

use crate::text::parsers::symbol::parse_symbol;
use crate::text::text_value::TextValue;

/// Matches a series of '::'-delimited symbols used to annotate a value.
pub(crate) fn parse_annotations(input: &str) -> IResult<&str, Vec<RawSymbolToken>> {
    many1(parse_annotation)(input)
}

/// Matches a single symbol of any format (foo, 'foo', or $10) followed by a '::' delimiter.
/// The delimiter can be preceded or trailed by any amount of whitespace.
pub(crate) fn parse_annotation(input: &str) -> IResult<&str, RawSymbolToken> {
    map_opt(
        // 0+ spaces, a symbol ('quoted', identifier, or $id), 0+ spaces, '::'
        delimited(
            whitespace_or_comments,
            parse_symbol,
            pair(whitespace_or_comments, annotation_delimiter),
        ),
        |text_value| {
            // This should always be true because `parse_symbol` would not have matched a
            // value if it were not a symbol.
            if let TextValue::Symbol(symbol) = text_value {
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
mod parse_annotations_tests {
    use rstest::*;

    use crate::types::SymbolId;
    use crate::raw_symbol_token::{local_sid_token, text_token};

    use super::*;

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
}
