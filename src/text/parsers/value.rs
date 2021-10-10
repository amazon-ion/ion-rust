use nom::branch::alt;
use nom::sequence::pair;
use nom::{IResult, Parser};

use crate::text::parsers::annotations::parse_annotations;
use crate::text::parsers::blob::parse_blob;
use crate::text::parsers::boolean::parse_boolean;
use crate::text::parsers::clob::parse_clob;
use crate::text::parsers::containers::container_start;
use crate::text::parsers::decimal::parse_decimal;
use crate::text::parsers::float::parse_float;
use crate::text::parsers::integer::parse_integer;
use crate::text::parsers::null::parse_null;
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::parse_symbol;
use crate::text::parsers::timestamp::parse_timestamp;
use crate::text::text_value::{AnnotatedTextValue, TextValue};

/// Matches a TextValue at the beginning of the given string.
pub(crate) fn value(input: &str) -> IResult<&str, TextValue> {
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
        container_start,
    ))(input)
}

/// Matches a series of annotations and their associated TextValue.
pub(crate) fn annotated_value(input: &str) -> IResult<&str, AnnotatedTextValue> {
    pair(parse_annotations, value)
        .map(|(annotations, value)| value.with_annotations(annotations))
        .parse(input)
}
