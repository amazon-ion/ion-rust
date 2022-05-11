use crate::text::parse_result::IonParseResult;
use nom::branch::alt;
use nom::sequence::pair;
use nom::Parser;

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
pub(crate) fn value(input: &str) -> IonParseResult<TextValue> {
    alt((scalar, container_start))(input)
}

/// Matches a scalar (non-container) Ion value at the beginning of the given string and
/// returns it as a [TextValue].
pub(crate) fn scalar(input: &str) -> IonParseResult<TextValue> {
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
    ))(input)
}

// TODO: The following method definitions are very similar and could be rewritten with
//       generics. However, `nom`'s extensive use of generics makes this harder than
//       it sounds.

/// Matches an optional series of annotations and their associated TextValue.
pub(crate) fn annotated_value(input: &str) -> IonParseResult<AnnotatedTextValue> {
    alt((
        pair(parse_annotations, value).map(|(a, v)| v.with_annotations(a)),
        value.map(|v| v.without_annotations()),
    ))(input)
}

/// Matches an optional series of annotations and their associated scalar TextValue.
pub(crate) fn annotated_scalar(input: &str) -> IonParseResult<AnnotatedTextValue> {
    alt((
        pair(parse_annotations, scalar).map(|(a, v)| v.with_annotations(a)),
        scalar.map(|v| v.without_annotations()),
    ))(input)
}

/// Matches an optional series of annotations and their associated scalar TextValue.
pub(crate) fn annotated_container_start(input: &str) -> IonParseResult<AnnotatedTextValue> {
    alt((
        pair(parse_annotations, container_start).map(|(a, v)| v.with_annotations(a)),
        container_start.map(|v| v.without_annotations()),
    ))(input)
}
