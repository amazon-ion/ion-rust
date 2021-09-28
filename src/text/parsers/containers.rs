use crate::text::TextStreamItem;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::combinator::{map, recognize};
use nom::IResult;

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

#[cfg(test)]
mod container_parsing_tests {
    use crate::text::parsers::containers::{parse_container_end, parse_container_start};
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::TextStreamItem;
    use rstest::*;

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
}
