use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::one_of;
use nom::combinator::{map, peek, recognize};
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::{IResult, Parser};

use crate::text::parsers::annotations::parse_annotations;
use crate::text::parsers::comments::whitespace_or_comments;
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::{parse_operator, parse_symbol};
use crate::text::parsers::top_level::top_level_stream_item;
use crate::text::TextStreamItem;
use crate::value::owned::{text_token, OwnedSymbolToken};

/// Matches the beginning of a container and returns a [TextStreamItem] indicating its type.
pub(crate) fn parse_container_start(input: &str) -> IResult<&str, TextStreamItem> {
    alt((
        recognize_struct_start,
        recognize_list_start,
        recognize_s_expression_start,
    ))(input)
}

/// Matches the beginning of a struct and returns a [TextStreamItem::StructStart].
pub(crate) fn recognize_struct_start(input: &str) -> IResult<&str, TextStreamItem> {
    map(recognize(tag("{")), |_matched_text| {
        TextStreamItem::StructStart
    })(input)
}

/// Matches the beginning of a list and returns a [TextStreamItem::ListStart].
pub(crate) fn recognize_list_start(input: &str) -> IResult<&str, TextStreamItem> {
    map(recognize(tag("[")), |_matched_text| {
        TextStreamItem::ListStart
    })(input)
}

/// Matches the beginning of an s-expression and returns a [TextStreamItem::SExpressionStart].
pub(crate) fn recognize_s_expression_start(input: &str) -> IResult<&str, TextStreamItem> {
    map(recognize(tag("(")), |_matched_text| {
        TextStreamItem::SExpressionStart
    })(input)
}

/// Matches the end of a container and returns a [TextStreamItem] indicating its type.
pub(crate) fn parse_container_end(input: &str) -> IResult<&str, TextStreamItem> {
    alt((
        recognize_struct_end,
        recognize_list_end,
        recognize_s_expression_end,
    ))(input)
}

/// Matches the end of a struct and returns a [TextStreamItem::StructEnd].
pub(crate) fn recognize_struct_end(input: &str) -> IResult<&str, TextStreamItem> {
    map(recognize(tag("}")), |_matched_text| {
        TextStreamItem::StructEnd
    })(input)
}

/// Matches the end of a list and returns a [TextStreamItem::StructEnd].
pub(crate) fn recognize_list_end(input: &str) -> IResult<&str, TextStreamItem> {
    map(recognize(tag("]")), |_matched_text| TextStreamItem::ListEnd)(input)
}

/// Matches the end of a list and returns a [TextStreamItem::StructEnd].
pub(crate) fn recognize_s_expression_end(input: &str) -> IResult<&str, TextStreamItem> {
    map(recognize(tag(")")), |_matched_text| {
        TextStreamItem::SExpressionEnd
    })(input)
}

/// Matches an optional series of annotations, a TextStreamItem, and a delimiting comma if present.
/// If no comma is present, the end-of-list marker must come next. This marker will not be consumed.
/// If there are no annotations (or the TextStreamItem found cannot have annotations), the
/// annotations [Vec] will be empty. Whitespace and comments can appear throughout; they will be
/// discarded.
pub(crate) fn list_stream_item(
    input: &str,
) -> IResult<&str, (Vec<OwnedSymbolToken>, TextStreamItem)> {
    // A list stream item is the same as a top level value but must be followed by either
    // a comma or the end-of-list delimiter (`]`).
    terminated(
        // Match the value itself (may be preceded by whitespace/comments)
        top_level_stream_item,
        // Check for any amount of whitespace followed by a comma or end-of-list delimiter.
        preceded(
            whitespace_or_comments,
            alt((tag(","), peek(recognize(recognize_list_end)))),
        ),
    )(input)
}

/// Matches a single item in an s-expression. S-expression items are the same as top-level items
/// with one exception: they can include operators, sequences of one or more ASCII special
/// characters. S-expression items are terminated by either whitespace or the end of the
/// s-expression (that is: with a `)`). The item being parsed can be prefixed by comments and
/// whitespace.
pub(crate) fn s_expression_stream_item(
    input: &str,
) -> IResult<&str, (Vec<OwnedSymbolToken>, TextStreamItem)> {
    delimited(
        whitespace_or_comments,
        // An s-expression item can be either...
        alt((
            // ...an annotated operator (`foo::++`)...
            pair(parse_annotations, parse_operator),
            // ...an un-annotated operator (`++`) paired with an empty annotations Vec...
            parse_operator.map(|op| (Vec::new(), op)),
            // ...or some other kind of value (`5`, `"hello"`, etc).
            top_level_stream_item,
        )),
        // Check for a whitespace character or an end-of-s-expression delimiter.
        alt((
            recognize(one_of(" \t\r\n")),
            peek(recognize(recognize_s_expression_end)),
        )),
    )(input)
}

/// Matches a struct field name and returns it as an [OwnedSymbolToken].
/// This function should be called before [struct_stream_item].
pub(crate) fn struct_field_name(input: &str) -> IResult<&str, OwnedSymbolToken> {
    delimited(
        whitespace_or_comments,
        parse_symbol.or(parse_string),
        pair(whitespace_or_comments, tag(":")),
    )
    .map(|item| match item {
        TextStreamItem::String(text) => text_token(text),
        TextStreamItem::Symbol(token) => token,
        other => unreachable!(
            "Struct field names can only be strings or symbols. Found a {:?}",
            other
        ),
    })
    .parse(input)
}

/// Matches an optional series of annotations, a TextStreamItem, and a delimiting comma if present.
/// If no comma is present, the end-of-struct marker must come next. This marker will not be consumed.
/// If there are no annotations (or the TextStreamItem found cannot have annotations), the
/// annotations [Vec] will be empty. Whitespace and comments can appear throughout; they will be
/// discarded.
pub(crate) fn struct_stream_item(
    input: &str,
) -> IResult<&str, (Vec<OwnedSymbolToken>, TextStreamItem)> {
    terminated(
        // Match the value itself (may be preceded by whitespace/comments)
        top_level_stream_item,
        // Check for any amount of whitespace followed by a comma or end-of-struct delimiter.
        preceded(
            whitespace_or_comments,
            alt((tag(","), peek(recognize(recognize_struct_end)))),
        ),
    )(input)
}

#[cfg(test)]
mod container_parsing_tests {
    use rstest::*;

    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::TextStreamItem;
    use crate::types::decimal::Decimal;
    use crate::value::owned::text_token;

    use super::*;

    #[rstest]
    #[case::start_of_struct("{", TextStreamItem::StructStart)]
    #[case::start_of_list("[", TextStreamItem::ListStart)]
    #[case::start_of_s_expression("(", TextStreamItem::SExpressionStart)]
    fn test_parse_container_start_ok(#[case] text: &str, #[case] expected: TextStreamItem) {
        parse_test_ok(parse_container_start, text, expected)
    }

    #[rstest]
    #[case("5")]
    #[case("true")]
    #[case("foo")]
    #[case("foo::{")]
    #[case("\"hello\"")]
    #[case("<")]
    fn test_parse_container_start_err(#[case] text: &str) {
        parse_test_err(parse_container_start, text)
    }

    #[rstest]
    #[case::end_of_struct("}", TextStreamItem::StructEnd)]
    #[case::end_of_list("]", TextStreamItem::ListEnd)]
    #[case::end_of_s_expression(")", TextStreamItem::SExpressionEnd)]
    fn test_parse_container_end_ok(#[case] text: &str, #[case] expected: TextStreamItem) {
        parse_test_ok(parse_container_end, text, expected)
    }

    #[rstest]
    #[case("5")]
    #[case("true")]
    #[case("foo")]
    #[case("foo::{")]
    #[case("\"hello\"")]
    #[case("<")]
    fn test_parse_container_end_err(#[case] text: &str) {
        parse_test_err(parse_container_end, text)
    }

    #[rstest]
    #[case("5,", (vec![], TextStreamItem::Integer(5)))]
    #[case("foo::bar::5,", (vec![text_token("foo"), text_token("bar")], TextStreamItem::Integer(5)))]
    #[case("foo::bar,", (vec![text_token("foo")], TextStreamItem::Symbol(text_token("bar"))))]
    #[case("bar]", (vec![], TextStreamItem::Symbol(text_token("bar"))))]
    #[case("7.]", (vec![], TextStreamItem::Decimal(Decimal::new(7, 0))))]
    #[should_panic]
    //       v---- Missing trailing , or ]
    #[case("5 ", (vec![], TextStreamItem::String(String::from("<should panic>"))))]
    #[should_panic]
    //      v--- No value, just a comma
    #[case(", ", (vec![], TextStreamItem::String(String::from("<should panic>"))))]
    fn test_parse_list_items(
        #[case] text: &str,
        #[case] expected: (Vec<OwnedSymbolToken>, TextStreamItem),
    ) {
        assert_eq!(list_stream_item(text).unwrap().1, expected);
    }

    #[rstest]
    #[case("++ ", (vec![], TextStreamItem::Symbol(text_token("++"))))]
    #[case("foo::++ ", (vec![text_token("foo")], TextStreamItem::Symbol(text_token("++"))))]
    #[case("5 ", (vec![], TextStreamItem::Integer(5)))]
    #[case("5)", (vec![], TextStreamItem::Integer(5)))]
    #[case("foo::bar::5 ", (vec![text_token("foo"), text_token("bar")], TextStreamItem::Integer(5)))]
    //               v--- This zero allows the parser to tell that the previous value is complete.
    #[case("foo::bar 0", (vec![text_token("foo")], TextStreamItem::Symbol(text_token("bar"))))]
    #[case("bar)", (vec![], TextStreamItem::Symbol(text_token("bar"))))]
    #[case("7.)", (vec![], TextStreamItem::Decimal(Decimal::new(7, 0))))]
    #[should_panic]
    //       v---- Comma instead of whitespace
    #[case("5, ", (vec![], TextStreamItem::String(String::from("<should panic>"))))]
    #[should_panic]
    //      v--- Wrong closing delimiter
    #[case("5]", (vec![], TextStreamItem::String(String::from("<should panic>"))))]
    fn test_parse_s_expression_items(
        #[case] text: &str,
        #[case] expected: (Vec<OwnedSymbolToken>, TextStreamItem),
    ) {
        assert_eq!(s_expression_stream_item(text).unwrap().1, expected);
    }

    #[rstest]
    #[case("5,", (vec![], TextStreamItem::Integer(5)))]
    #[case("5  ,", (vec![], TextStreamItem::Integer(5)))]
    #[case("foo::bar::5,", (vec![text_token("foo"), text_token("bar")], TextStreamItem::Integer(5)))]
    #[case("foo::bar,", (vec![text_token("foo")], TextStreamItem::Symbol(text_token("bar"))))]
    #[case("bar}", (vec![], TextStreamItem::Symbol(text_token("bar"))))]
    #[case("7.}", (vec![], TextStreamItem::Decimal(Decimal::new(7, 0))))]
    #[should_panic]
    //       v---- Missing trailing , or }
    #[case("5 ", (vec![], TextStreamItem::String(String::from("<should panic>"))))]
    #[should_panic]
    //      v--- No value, just a comma
    #[case(", ", (vec![], TextStreamItem::String(String::from("<should panic>"))))]
    fn test_parse_struct_items(
        #[case] text: &str,
        #[case] expected: (Vec<OwnedSymbolToken>, TextStreamItem),
    ) {
        assert_eq!(struct_stream_item(text).unwrap().1, expected);
    }

    #[rstest]
    #[case("foo:")]
    #[case("  foo  :")]
    #[case("/* Here's a field name */  foo // And here's a delimiter\n:")]
    #[case("'foo':")]
    #[case("  'foo'  :")]
    #[case("$10:")]
    #[case("  $10  :")]
    #[case("\"foo\":")]
    #[case("  \"foo\"  :")]
    fn test_parse_struct_field_name(#[case] text: &str) {
        parse_test_err(parse_container_end, text)
    }
}
