use crate::raw_symbol_token::RawSymbolToken;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::streaming::one_of;
use nom::combinator::{map, peek, recognize, value};
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::{IResult, Parser};

use crate::text::parsers::annotations::parse_annotations;
use crate::text::parsers::comments::whitespace_or_comments;
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::{parse_operator, parse_symbol};
use crate::text::parsers::top_level::top_level_value;
use crate::text::parsers::value::{annotated_container_start, annotated_scalar};
use crate::text::text_value::{AnnotatedTextValue, TextValue};

/// Matches the beginning of a container and returns a [TextValue] indicating its type.
pub(crate) fn container_start(input: &str) -> IResult<&str, TextValue> {
    alt((struct_start, list_start, s_expression_start))(input)
}

/// Matches the beginning of a struct and returns a [TextValue::StructStart].
pub(crate) fn struct_start(input: &str) -> IResult<&str, TextValue> {
    value(TextValue::StructStart, tag("{"))(input)
}

/// Matches the beginning of a list and returns a [TextValue::ListStart].
pub(crate) fn list_start(input: &str) -> IResult<&str, TextValue> {
    value(TextValue::ListStart, tag("["))(input)
}

/// Matches the beginning of an s-expression and returns a [TextValue::SExpressionStart].
pub(crate) fn s_expression_start(input: &str) -> IResult<&str, TextValue> {
    value(TextValue::SExpressionStart, tag("("))(input)
}

/// Matches the end of a struct and returns a `&str` containing the delimiter.
pub(crate) fn struct_end(input: &str) -> IResult<&str, &str> {
    preceded(whitespace_or_comments, tag("}"))(input)
}

/// Matches the end of a list and returns a `&str` containing the delimiter.
pub(crate) fn list_end(input: &str) -> IResult<&str, &str> {
    preceded(whitespace_or_comments, tag("]"))(input)
}

/// Matches the end of an s-expression and returns a `&str` containing the delimiter.
pub(crate) fn s_expression_end(input: &str) -> IResult<&str, &str> {
    preceded(whitespace_or_comments, tag(")"))(input)
}

/// Matches an optional series of annotations and a TextValue. If the TextValue is not a container,
/// this parser will also match a trailing delimiting comma (that will be consumed) or end-of-list
/// marker (that will not be consumed). Whitespace and comments can appear throughout; they will be
/// discarded.
pub(crate) fn list_value(input: &str) -> IResult<&str, AnnotatedTextValue> {
    alt((
        // Matches a scalar value and either a delimiter or end-of-container.
        list_scalar,
        // If the next value in the list is a container, we only need to match the start.
        // We'll look for the trailing delimiter or end-of-container when the reader steps out.
        preceded(whitespace_or_comments, annotated_container_start),
    ))(input)
}

/// Matches a (possibly annotated) non-container value in a list followed by a delimiter
/// or end-of-container.
pub(crate) fn list_scalar(input: &str) -> IResult<&str, AnnotatedTextValue> {
    // A list scalar must be followed by either a comma or the end-of-list delimiter (`]`).
    delimited(
        // Any amount of whitespace or comments
        whitespace_or_comments,
        // Match the value itself (may be preceded by whitespace/comments)
        annotated_scalar,
        // Check for any amount of whitespace followed by a comma or end-of-list delimiter.
        list_delimiter,
    )(input)
}

/// Matches any amount of whitespace/comments followed by either a delimiter (which is consumed)
/// or an end-of-container (which is not consumed).
pub(crate) fn list_delimiter(input: &str) -> IResult<&str, ()> {
    preceded(whitespace_or_comments, alt((tag(","), peek(list_end))))
        // TODO: This parser discards the matched &str as a workaround to a limitation in RawTextReader.
        //       See: https://github.com/amzn/ion-rust/issues/337
        .map(|_| ())
        .parse(input)
}

/// Returns [None] if the next token in input is an end-of-list delimiter (`]`).
/// Otherwise, matches and returns the next value in the list using [list_value].
pub(crate) fn list_value_or_end(input: &str) -> IResult<&str, Option<AnnotatedTextValue>> {
    map(list_end, |_end_marker| None)
        .or(map(list_value, Some))
        .parse(input)
}

/// Matches an optional series of annotations and a TextValue (including operators). If the TextValue
/// is not a container, this parser will also match a trailing delimiting whitespace character
/// (that will be consumed) or end-of-s-expression marker (that will not be consumed).
pub(crate) fn s_expression_value(input: &str) -> IResult<&str, AnnotatedTextValue> {
    alt((
        // Matches a scalar value followed by either a delimiter or end-of-container.
        s_expression_scalar,
        // If the next value in the s-expression is a container, we only need to match the start.
        // We'll look for the trailing delimiter or end-of-container when the reader steps out.
        preceded(whitespace_or_comments, annotated_container_start),
    ))(input)
}

/// Matches a (possibly annotated) non-container value in an s-expression followed by a delimiter
/// or end-of-container.
pub(crate) fn s_expression_scalar(input: &str) -> IResult<&str, AnnotatedTextValue> {
    delimited(
        whitespace_or_comments,
        // An s-expression value can be either...
        alt((
            // ...an annotated operator (`foo::++`)...
            pair(parse_annotations, parse_operator)
                .map(|(annotations, value)| AnnotatedTextValue::new(annotations, value)),
            // ...an un-annotated operator (`++`) paired with an empty annotations Vec...
            parse_operator.map(|op| op.without_annotations()),
            // ...or some other kind of value (`5`, `"hello"`, etc).
            top_level_value,
        )),
        // Check for a whitespace character or an end-of-s-expression delimiter.
        alt((
            recognize(one_of(" \t\r\n")),
            peek(recognize(s_expression_end)),
        )),
    )(input)
}

/// Returns [None] if the next token in input is an end-of-s-expression delimiter (`)`).
/// Otherwise, matches and returns the next value in the s-expression using [s_expression_stream_value].
pub(crate) fn s_expression_value_or_end(input: &str) -> IResult<&str, Option<AnnotatedTextValue>> {
    map(s_expression_end, |_end_marker| None)
        .or(map(s_expression_value, Some))
        .parse(input)
}

/// Matches a whitespace character (which is consumed) or an end-of-container (which is not consumed).
pub(crate) fn s_expression_delimiter(input: &str) -> IResult<&str, ()> {
    alt((recognize(one_of(" \t\r\n")), peek(list_end)))
        // TODO: This parser discards the matched &str as a workaround to a limitation in RawTextReader.
        //       See: https://github.com/amzn/ion-rust/issues/337
        .map(|_| ())
        .parse(input)
}

/// Matches a struct field name and returns it as an [OwnedSymbolToken].
/// This function should be called before [struct_stream_value].
pub(crate) fn struct_field_name(input: &str) -> IResult<&str, RawSymbolToken> {
    delimited(
        whitespace_or_comments,
        parse_symbol.or(parse_string),
        pair(whitespace_or_comments, tag(":")),
    )
    .map(|value| match value {
        TextValue::String(text) => RawSymbolToken::Text(text),
        TextValue::Symbol(token) => token,
        other => unreachable!(
            "Struct field names can only be strings or symbols. Found a {:?}",
            other
        ),
    })
    .parse(input)
}

/// Matches an optional series of annotations and a TextValue. If the TextValue is not a container,
/// this parser will also match a trailing delimiting comma (that will be consumed) or end-of-struct
/// marker (that will not be consumed). Whitespace and comments can appear throughout; they will be
/// discarded.
pub(crate) fn struct_field_value(input: &str) -> IResult<&str, AnnotatedTextValue> {
    alt((
        // Matches a scalar value and either a delimiter or end-of-container.
        struct_field_scalar,
        // If the next value in the list is a container, we only need to match the start.
        // We'll look for the trailing delimiter or end-of-container when the reader steps out.
        preceded(whitespace_or_comments, annotated_container_start),
    ))(input)
}

/// Matches a (possibly annotated) non-container value in an struct followed by a delimiter
/// or end-of-container.
pub(crate) fn struct_field_scalar(input: &str) -> IResult<&str, AnnotatedTextValue> {
    terminated(
        // Match the value itself (may be preceded by whitespace/comments)
        top_level_value,
        // Check for any amount of whitespace followed by a comma or end-of-struct delimiter.
        struct_delimiter,
    )(input)
}

/// Returns [None] if the next token in input is an end-of-struct delimiter (`}`).
/// Otherwise, matches and returns the next field name in the struct using [struct_field_name].
pub(crate) fn struct_field_name_or_end(input: &str) -> IResult<&str, Option<RawSymbolToken>> {
    map(struct_end, |_end_marker| None)
        .or(map(struct_field_name, Some))
        .parse(input)
}

/// Matches any amount of whitespace/comments followed by either a delimiter (which is consumed)
/// or an end-of-container (which is not consumed).
pub(crate) fn struct_delimiter(input: &str) -> IResult<&str, ()> {
    preceded(whitespace_or_comments, alt((tag(","), peek(struct_end))))
        // TODO: This parser discards the matched &str as a workaround to a limitation in RawTextReader.
        //       See: https://github.com/amzn/ion-rust/issues/337
        .map(|_| ())
        .parse(input)
}

#[cfg(test)]
mod container_parsing_tests {
    use rstest::*;

    use crate::raw_symbol_token::{local_sid_token, text_token};
    use crate::text::parsers::unit_test_support::{parse_test_err, parse_test_ok};
    use crate::text::text_value::TextValue;
    use crate::types::decimal::Decimal;

    use super::*;

    #[rstest]
    #[case::start_of_struct("{", TextValue::StructStart)]
    #[case::start_of_list("[", TextValue::ListStart)]
    #[case::start_of_s_expression("(", TextValue::SExpressionStart)]
    fn test_parse_container_start_ok(#[case] text: &str, #[case] expected: TextValue) {
        parse_test_ok(container_start, text, expected)
    }

    #[rstest]
    #[case("5")]
    #[case("true")]
    #[case("foo")]
    #[case("foo::{")]
    #[case("\"hello\"")]
    #[case("<")]
    fn test_parse_container_start_err(#[case] text: &str) {
        parse_test_err(container_start, text)
    }

    #[rstest]
    #[case("5,", TextValue::Integer(5).without_annotations())]
    #[case("foo::bar::5,", TextValue::Integer(5).with_annotations(&["foo", "bar"]))]
    #[case("foo::bar,", TextValue::Symbol(text_token("bar")).with_annotations("foo"))]
    #[case("bar]", TextValue::Symbol(text_token("bar")).without_annotations())]
    #[case("7.]", TextValue::Decimal(Decimal::new(7, 0)).without_annotations())]
    #[should_panic]
    //       v---- Missing trailing , or ]
    #[case("5 ", TextValue::String(String::from("<should panic>")).without_annotations())]
    #[should_panic]
    //      v--- No value, just a comma
    #[case(", ", TextValue::String(String::from("<should panic>")).without_annotations())]
    fn test_parse_list_values(#[case] text: &str, #[case] expected: AnnotatedTextValue) {
        parse_test_ok(list_value, text, expected);
    }

    #[rstest]
    #[case("'++',", Some(TextValue::Symbol(text_token("++")).without_annotations()))]
    #[case("foo::'++',", Some(TextValue::Symbol(text_token("++")).with_annotations("foo")))]
    #[case("5    ,", Some(TextValue::Integer(5).without_annotations()))]
    #[case("5]", Some(TextValue::Integer(5).without_annotations()))]
    #[case("]", None)]
    #[case("  ]", None)]
    #[case(" /*comment*/  ]", None)]
    fn test_parse_list_value_or_end(
        #[case] text: &str,
        #[case] expected: Option<AnnotatedTextValue>,
    ) {
        parse_test_ok(list_value_or_end, text, expected);
    }

    #[rstest]
    #[case("++ ", TextValue::Symbol(text_token("++")).without_annotations())]
    #[case("foo::++ ", TextValue::Symbol(text_token("++")).with_annotations("foo"))]
    #[case("5 ", TextValue::Integer(5).without_annotations())]
    #[case("5)", TextValue::Integer(5).without_annotations())]
    #[case("foo::bar::5 ", TextValue::Integer(5).with_annotations(&["foo", "bar"]))]
    //               v--- This zero allows the parser to tell that the previous value is complete.
    #[case("foo::bar 0", TextValue::Symbol(text_token("bar")).with_annotations("foo"))]
    #[case("bar)", TextValue::Symbol(text_token("bar")).without_annotations())]
    #[case("7.)", TextValue::Decimal(Decimal::new(7, 0)).without_annotations())]
    #[should_panic]
    //       v---- Comma instead of whitespace
    #[case("5, ", TextValue::String(String::from("<should panic>")).without_annotations())]
    #[should_panic]
    //      v--- Wrong closing delimiter
    #[case("5]", TextValue::String(String::from("<should panic>")).without_annotations())]
    fn test_parse_s_expression_values(#[case] text: &str, #[case] expected: AnnotatedTextValue) {
        parse_test_ok(s_expression_value, text, expected);
    }

    #[rstest]
    #[case("++ ", Some(TextValue::Symbol(text_token("++")).without_annotations()))]
    #[case("foo::++ ", Some(TextValue::Symbol(text_token("++")).with_annotations("foo")))]
    #[case("5 ", Some(TextValue::Integer(5).without_annotations()))]
    #[case(")", None)]
    #[case("  )", None)]
    #[case(" /*comment*/  )", None)]
    fn test_parse_s_expression_value_or_end(
        #[case] text: &str,
        #[case] expected: Option<AnnotatedTextValue>,
    ) {
        parse_test_ok(s_expression_value_or_end, text, expected);
    }

    #[rstest]
    #[case("5,", TextValue::Integer(5).without_annotations())]
    #[case("5  ,", TextValue::Integer(5).without_annotations())]
    #[case("foo::bar::5,", TextValue::Integer(5).with_annotations(&["foo", "bar"]))]
    #[case("foo::bar,", TextValue::Symbol(text_token("bar")).with_annotations("foo"))]
    #[case("bar}", TextValue::Symbol(text_token("bar")).without_annotations())]
    #[case("7.}", TextValue::Decimal(Decimal::new(7, 0)).without_annotations())]
    #[should_panic]
    //       v---- Missing trailing , or }
    #[case("5 ", TextValue::String(String::from("<should panic>")).without_annotations())]
    #[should_panic]
    //      v--- No value, just a comma
    #[case(", ", TextValue::String(String::from("<should panic>")).without_annotations())]
    fn test_parse_struct_field_values(#[case] text: &str, #[case] expected: AnnotatedTextValue) {
        parse_test_ok(struct_field_value, text, expected);
    }

    #[rstest]
    #[case("foo:", text_token("foo"))]
    #[case("  foo  :", text_token("foo"))]
    #[case(
        "/* Here's a field name */  foo // And here's a delimiter\n:",
        text_token("foo")
    )]
    #[case("'foo':", text_token("foo"))]
    #[case("  'foo'  :", text_token("foo"))]
    #[case("$10:", local_sid_token(10))]
    #[case("  $10  :", local_sid_token(10))]
    #[case("\"foo\":", text_token("foo"))]
    #[case("  \"foo\"  :", text_token("foo"))]
    fn test_parse_struct_field_name(#[case] text: &str, #[case] expected: RawSymbolToken) {
        parse_test_ok(struct_field_name, text, expected);
    }

    #[rstest]
    #[case("foo:", Some(text_token("foo")))]
    #[case("  foo  :", Some(text_token("foo")))]
    #[case("'foo':", Some(text_token("foo")))]
    #[case("}", None)]
    #[case("   }", None)]
    #[case("/*comment*/}", None)]
    fn test_parse_struct_field_name_or_end(
        #[case] text: &str,
        #[case] expected: Option<RawSymbolToken>,
    ) {
        parse_test_ok(struct_field_name_or_end, text, expected);
    }
}
