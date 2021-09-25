use nom::branch::alt;
use nom::combinator::opt;
use nom::IResult;
use nom::sequence::preceded;

use crate::text::parsers::blob::parse_blob;
use crate::text::parsers::boolean::parse_boolean;
use crate::text::parsers::clob::parse_clob;
use crate::text::parsers::containers::{parse_container_end, parse_container_start};
use crate::text::parsers::decimal::parse_decimal;
use crate::text::parsers::float::parse_float;
use crate::text::parsers::integer::parse_integer;
use crate::text::parsers::null::parse_null;
use crate::text::parsers::string::parse_string;
use crate::text::parsers::symbol::parse_symbol;
use crate::text::parsers::timestamp::parse_timestamp;
use crate::text::parsers::whitespace;
use crate::text::TextStreamItem;

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
        parse_container_end
    ))(input)
}

/// Matches a TextStreamItem at the beginning of the given string. The TextStreamItem may be
/// prefixed by whitespace.
pub(crate) fn top_level_value(input: &str) -> IResult<&str, TextStreamItem> {
    preceded(opt(whitespace), stream_item)(input)
}
