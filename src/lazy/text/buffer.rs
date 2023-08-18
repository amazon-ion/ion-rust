use std::fmt::{Debug, Formatter};
use std::iter::{Copied, Enumerate};
use std::ops::{Range, RangeFrom, RangeTo};
use std::slice::Iter;
use std::str::FromStr;

use nom::branch::alt;
use nom::bytes::streaming::{is_a, is_not, tag, take_until, take_while1, take_while_m_n};
use nom::character::streaming::{char, digit1, one_of, satisfy};
use nom::combinator::{fail, map, not, opt, peek, recognize, success, value};
use nom::error::{ErrorKind, ParseError};
use nom::multi::{many0_count, many1_count};
use nom::sequence::{delimited, pair, preceded, separated_pair, terminated, tuple};
use nom::{CompareResult, IResult, InputLength, InputTake, Needed, Parser};

use crate::lazy::encoding::TextEncoding;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::{
    MatchedFloat, MatchedHoursAndMinutes, MatchedInt, MatchedString, MatchedSymbol,
    MatchedTimestamp, MatchedTimestampOffset, MatchedValue,
};
use crate::lazy::text::parse_result::{InvalidInputError, IonParseError};
use crate::lazy::text::parse_result::{IonMatchResult, IonParseResult};
use crate::lazy::text::raw::r#struct::{LazyRawTextField, RawTextStructIterator};
use crate::lazy::text::raw::sequence::{RawTextListIterator, RawTextSExpIterator};
use crate::lazy::text::value::LazyRawTextValue;
use crate::result::DecodingError;
use crate::{IonError, IonResult, IonType, TimestampPrecision};

impl<'a> Debug for TextBufferView<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "TextBufferView {{")?;
        // Try to read the next several bytes from the buffer as UTF-8...
        let text_result = std::str::from_utf8(self.data);
        // ...if it works, print the first 32 unicode scalars...
        if let Ok(text) = text_result {
            write!(f, "\"{}...\"", text.chars().take(32).collect::<String>())?;
        } else {
            // ...if it doesn't, print the first 32 bytes in hex.
            write!(f, "Invalid UTF-8")?;
            for byte in self.bytes().iter().take(32) {
                write!(f, "{:x?} ", *byte)?;
            }
            if self.bytes().len() > 32 {
                write!(f, "...{} more bytes", self.bytes().len() - 32)?;
            }
        }
        write!(f, "}}")
    }
}

/// The Ion specification's enumeration of whitespace characters.
const WHITESPACE_CHARACTERS: &[char] = &[
    ' ',    // Space
    '\t',   // Tab
    '\r',   // Carriage return
    '\n',   // Newline
    '\x09', // Horizontal tab
    '\x0B', // Vertical tab
    '\x0C', // Form feed
];

/// Same as [WHITESPACE_CHARACTERS], but formatted as a string for use in some `nom` APIs
const WHITESPACE_CHARACTERS_AS_STR: &str = " \t\r\n\x09\x0B\x0C";

/// A slice of unsigned bytes that can be cheaply copied and which defines methods for parsing
/// the various encoding elements of a text Ion stream.
///
/// Parsing methods have names that begin with `match_` and each return a `(match, remaining_input)`
/// pair. The `match` may be either the slice of the input that was matched (represented as another
/// `TextBufferView`) or a `MatchedValue` that retains information discovered during parsing that
/// will be useful if the match is later fully materialized into a value.
#[derive(PartialEq, Clone, Copy)]
pub(crate) struct TextBufferView<'a> {
    // `data` is a slice of remaining data in the larger input stream.
    // `offset` is the absolute position in the overall input stream where that slice begins.
    //
    // input: 00 01 02 03 04 05 06 07 08 09
    //                          └────┬────┘
    //                          data: &[u8]
    //                          offset: 6
    data: &'a [u8],
    offset: usize,
}

pub(crate) type ParseResult<'a, T> = IonResult<(T, TextBufferView<'a>)>;

impl<'data> TextBufferView<'data> {
    /// Constructs a new `TextBufferView` that wraps `data`, setting the view's `offset` to zero.
    #[inline]
    pub fn new(data: &[u8]) -> TextBufferView {
        Self::new_with_offset(data, 0)
    }

    /// Constructs a new `TextBufferView` that wraps `data`, setting the view's `offset` to the
    /// specified value. This is useful when `data` is a slice from the middle of a larger stream.
    /// Note that `offset` is the index of the larger stream at which `data` begins and not an
    /// offset _into_ `data`.
    pub fn new_with_offset(data: &[u8], offset: usize) -> TextBufferView {
        TextBufferView { data, offset }
    }

    /// Returns a subslice of the [`TextBufferView`] that starts at `offset` and continues for
    /// `length` bytes.
    ///
    /// Note that `offset` is relative to the beginning of the buffer, not the beginning of the
    /// larger stream of which the buffer is a piece.
    pub fn slice(&self, offset: usize, length: usize) -> TextBufferView<'data> {
        TextBufferView {
            data: &self.data[offset..offset + length],
            offset: self.offset + offset,
        }
    }

    /// Returns a subslice of the [`TextBufferView`] that starts at `offset` and continues
    /// to the end.
    ///
    /// Note that `offset` is relative to the beginning of the buffer, not the beginning of the
    /// larger stream of which the buffer is a piece.
    pub fn slice_to_end(&self, offset: usize) -> TextBufferView<'data> {
        TextBufferView {
            data: &self.data[offset..],
            offset: self.offset + offset,
        }
    }

    /// Returns a slice containing all of the buffer's bytes.
    pub fn bytes(&self) -> &[u8] {
        self.data
    }

    /// Returns the number of bytes between the start of the original input byte array and the
    /// subslice of that byte array that this `TextBufferView` represents.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the number of bytes in the buffer.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if there are no bytes in the buffer. Otherwise, returns `false`.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Attempts to view the contents of the buffer as a UTF-8 `&str`.
    pub fn as_text<'a>(&'a self) -> IonResult<&'data str> {
        // On its surface, this method very closely resembles the `AsUtf8` trait's method.
        // However, this one returns a `&'data str` instead of a `&'a str`, which is to say
        // that the string that's returned lives as long as the data itself, not just the duration
        // of the lifetime introduced by this method call.
        std::str::from_utf8(self.data).map_err(move |_| {
            let decoding_error =
                DecodingError::new("encountered invalid UTF-8").with_position(self.offset());
            IonError::Decoding(decoding_error)
        })
    }

    pub fn match_whitespace(self) -> IonMatchResult<'data> {
        is_a(WHITESPACE_CHARACTERS_AS_STR)(self)
    }

    /// Always succeeds and consumes none of the input. Returns an empty slice of the buffer.
    // This method is useful for parsers that need to match an optional construct but don't want
    // to return an Option<_>. For an example, see its use in `match_optional_whitespace`.
    fn match_nothing(self) -> IonMatchResult<'data> {
        // Use nom's `success` parser to return an empty slice from the head position
        success(self.slice(0, 0))(self)
    }

    /// Matches zero or more whitespace characters.
    pub fn match_optional_whitespace(self) -> IonMatchResult<'data> {
        // Either match whitespace and return what follows or just return the input as-is.
        // This will always return `Ok`, but it is packaged as an IonMatchResult for compatability
        // with other parsers.
        alt((Self::match_whitespace, Self::match_nothing))(self)
    }

    /// Matches any amount of contiguous comments and whitespace, including none.
    pub fn match_optional_comments_and_whitespace(self) -> IonMatchResult<'data> {
        recognize(many0_count(alt((
            Self::match_whitespace,
            Self::match_comment,
        ))))(self)
    }

    /// Matches a single
    ///     // Rest-of-the-line
    /// or
    ///     /* multi
    ///        line */
    /// comment
    pub fn match_comment(self) -> IonMatchResult<'data> {
        alt((
            Self::match_rest_of_line_comment,
            Self::match_multiline_comment,
        ))(self)
    }

    /// Matches a single rest-of-the-line comment.
    fn match_rest_of_line_comment(self) -> IonMatchResult<'data> {
        preceded(
            // Matches a leading "//"...
            tag("//"),
            // ...followed by either...
            alt((
                // ...one or more non-EOL characters...
                is_not("\r\n"),
                // ...or any EOL character.
                peek(recognize(one_of("\r\n"))),
                // In either case, the line ending will not be consumed.
            )),
        )(self)
    }

    /// Matches a single multiline comment.
    fn match_multiline_comment(self) -> IonMatchResult<'data> {
        recognize(delimited(
            // Matches a leading "/*"...
            tag("/*"),
            // ...any number of non-"*/" characters...
            take_until("*/"),
            // ...and then a closing "*/"
            tag("*/"),
        ))(self)
    }

    /// Matches an Ion version marker (e.g. `$ion_1_0` or `$ion_1_1`.)
    pub fn match_ivm(self) -> IonParseResult<'data, RawStreamItem<'data, TextEncoding>> {
        let (remaining, (major, minor)) =
            preceded(tag("$ion_"), separated_pair(digit1, tag("_"), digit1))(self)?;
        // `major` and `minor` are base 10 digits. Turning them into `&str`s is guaranteed to succeed.
        let major_version = u8::from_str(major.as_text().unwrap()).map_err(|_| {
            let error = InvalidInputError::new(major)
                .with_label("parsing an IVM major version")
                .with_description("value did not fit in an unsigned byte");
            nom::Err::Failure(IonParseError::Invalid(error))
        })?;
        let minor_version = u8::from_str(minor.as_text().unwrap()).map_err(|_| {
            let error = InvalidInputError::new(minor)
                .with_label("parsing an IVM minor version")
                .with_description("value did not fit in an unsigned byte");
            nom::Err::Failure(IonParseError::Invalid(error))
        })?;

        Ok((
            remaining,
            RawStreamItem::VersionMarker(major_version, minor_version),
        ))
    }

    /// Matches one or more annotations.
    pub fn match_annotations(self) -> IonMatchResult<'data> {
        recognize(many1_count(Self::match_annotation))(self)
    }

    /// Matches an annotation (symbol token) and a terminating '::'.
    pub fn match_annotation(self) -> IonParseResult<'data, (MatchedSymbol, Range<usize>)> {
        terminated(
            whitespace_and_then(match_and_span(Self::match_symbol)),
            whitespace_and_then(tag("::")),
        )(self)
    }

    pub fn match_sexp_value(self) -> IonParseResult<'data, Option<LazyRawTextValue<'data>>> {
        whitespace_and_then(alt((
            value(None, tag(")")),
            pair(
                opt(Self::match_annotations),
                alt((Self::match_value, Self::match_operator)),
            )
            .map(|(maybe_annotations, mut value)| {
                if let Some(annotations) = maybe_annotations {
                    value.encoded_value = value
                        .encoded_value
                        .with_annotations_sequence(annotations.offset(), annotations.len());
                    // Rewind the value's input to include the annotations sequence.
                    value.input = self.slice_to_end(annotations.offset() - self.offset());
                }
                Some(value)
            }),
        )))
        .parse(self)
    }

    /// Matches a single value in a list OR the end of the list, allowing for leading whitespace
    /// and comments in either case.
    ///
    /// If a value is found, returns `Ok(Some(value))`. If the end of the list is found, returns
    /// `Ok(None)`.
    pub fn match_list_value(self) -> IonParseResult<'data, Option<LazyRawTextValue<'data>>> {
        preceded(
            // Some amount of whitespace/comments...
            Self::match_optional_comments_and_whitespace,
            // ...followed by either the end of the list...
            alt((
                value(None, tag("]")),
                // ...or a value...
                terminated(
                    Self::match_annotated_value.map(Some),
                    // ...followed by a comma or end-of-list
                    Self::match_delimiter_after_list_value,
                ),
            )),
        )(self)
    }

    /// Matches a struct field name/value pair.
    ///
    /// If a pair is found, returns `Some(field)` and consumes the following comma if present.
    /// If no pair is found (that is: the end of the struct is next), returns `None`.
    pub fn match_struct_field(self) -> IonParseResult<'data, Option<LazyRawTextField<'data>>> {
        // A struct field can have leading whitespace, but we want the buffer slice that we match
        // to begin with the field name. Here we skip any whitespace so we have another named
        // slice (`input_including_field_name`) with that property.
        let (input_including_field_name, _ws) = self.match_optional_comments_and_whitespace()?;
        alt((
            // If the next thing in the input is a `}`, return `None`.
            value(None, Self::match_struct_end),
            // Otherwise, match a name/value pair and turn it into a `LazyRawTextField`.
            Self::match_struct_field_name_and_value.map(
                move |((name_syntax, name_span), mut value)| {
                    // Add the field name offsets to the `EncodedTextValue`
                    value.encoded_value = value.encoded_value.with_field_name(
                        name_syntax,
                        name_span.start,
                        name_span.len(),
                    );
                    // Replace the value's buffer slice (which starts with the value itself) with the
                    // buffer slice we created that begins with the field name.
                    value.input = input_including_field_name;
                    Some(LazyRawTextField { value })
                },
            ),
        ))(input_including_field_name)
    }

    /// Matches any amount of whitespace followed by a closing `}`.
    fn match_struct_end(self) -> IonMatchResult<'data> {
        whitespace_and_then(peek(tag("}"))).parse(self)
    }

    /// Matches a field name/value pair. Returns the syntax used for the field name, the range of
    /// input bytes where the field name is found, and the value.
    pub fn match_struct_field_name_and_value(
        self,
    ) -> IonParseResult<'data, ((MatchedSymbol, Range<usize>), LazyRawTextValue<'data>)> {
        terminated(
            separated_pair(
                whitespace_and_then(match_and_span(Self::match_struct_field_name)),
                whitespace_and_then(tag(":")),
                whitespace_and_then(Self::match_annotated_value),
            ),
            whitespace_and_then(alt((tag(","), peek(tag("}"))))),
        )(self)
    }

    /// Matches an optional annotation sequence and a trailing value.
    pub fn match_annotated_value(self) -> IonParseResult<'data, LazyRawTextValue<'data>> {
        pair(
            opt(Self::match_annotations),
            whitespace_and_then(Self::match_value),
        )
        .map(|(maybe_annotations, mut value)| {
            if let Some(annotations) = maybe_annotations {
                value.encoded_value = value
                    .encoded_value
                    .with_annotations_sequence(annotations.offset(), annotations.len());
                // Rewind the value's input to include the annotations sequence.
                value.input = self.slice_to_end(annotations.offset() - self.offset());
            }
            value
        })
        .parse(self)
    }

    /// Matches a struct field name. That is:
    /// * A quoted symbol
    /// * An identifier
    /// * A symbol ID
    /// * A short-form string
    pub fn match_struct_field_name(self) -> IonParseResult<'data, MatchedSymbol> {
        alt((
            Self::match_symbol,
            Self::match_short_string.map(|s| {
                // NOTE: We're "casting" the matched short string to a matched symbol here.
                //       This relies on the fact that the MatchedSymbol logic ignores
                //       the first and last matched byte, which are usually single
                //       quotes but in this case are double quotes.
                match s {
                    MatchedString::ShortWithoutEscapes => MatchedSymbol::QuotedWithoutEscapes,
                    MatchedString::ShortWithEscapes => MatchedSymbol::QuotedWithEscapes,
                    _ => unreachable!("field name parser matched long string"),
                }
            }),
        ))(self)
    }

    /// Matches syntax that is expected to follow a value in a list: any amount of whitespace and/or
    /// comments followed by either a comma (consumed) or an end-of-list `]` (not consumed).
    fn match_delimiter_after_list_value(self) -> IonMatchResult<'data> {
        preceded(
            Self::match_optional_comments_and_whitespace,
            alt((tag(","), peek(tag("]")))),
        )(self)
    }

    /// Matches a single top-level value, an IVM, or the end of the stream.
    pub fn match_top_level_item(self) -> IonParseResult<'data, RawStreamItem<'data, TextEncoding>> {
        // If only whitespace/comments remain, we're at the end of the stream.
        let (input_after_ws, _ws) = self.match_optional_comments_and_whitespace()?;
        if input_after_ws.is_empty() {
            return Ok((input_after_ws, RawStreamItem::EndOfStream));
        }
        // Otherwise, the next item must be an IVM or a value.
        // We check for IVMs first because the rules for a symbol identifier will match them.
        alt((Self::match_ivm, Self::match_top_level_value))(input_after_ws)
    }

    /// Matches a single value at the top level. The caller must verify that the input is not an
    /// IVM before calling; otherwise, that IVM will be recognized as an identifier/symbol.
    fn match_top_level_value(self) -> IonParseResult<'data, RawStreamItem<'data, TextEncoding>> {
        self.match_annotated_value()
            .map(|(remaining, value)| (remaining, RawStreamItem::Value(value)))
    }

    /// Matches a single scalar value or the beginning of a container.
    pub fn match_value(self) -> IonParseResult<'data, LazyRawTextValue<'data>> {
        alt((
            // For `null` and `bool`, we use `read_` instead of `match_` because there's no additional
            // parsing to be done.
            map(match_and_length(Self::read_null), |(ion_type, length)| {
                EncodedTextValue::new(MatchedValue::Null(ion_type), self.offset(), length)
            }),
            map(match_and_length(Self::read_bool), |(value, length)| {
                EncodedTextValue::new(MatchedValue::Bool(value), self.offset(), length)
            }),
            // For `int` and the other types, we use `match` and store the partially-processed input in the
            // `matched_value` field of the `EncodedTextValue` we return.
            map(
                match_and_length(Self::match_int),
                |(matched_int, length)| {
                    EncodedTextValue::new(MatchedValue::Int(matched_int), self.offset(), length)
                },
            ),
            map(
                match_and_length(Self::match_float),
                |(matched_float, length)| {
                    EncodedTextValue::new(MatchedValue::Float(matched_float), self.offset(), length)
                },
            ),
            map(
                match_and_length(Self::match_timestamp),
                |(matched_timestamp, length)| {
                    EncodedTextValue::new(
                        MatchedValue::Timestamp(matched_timestamp),
                        self.offset(),
                        length,
                    )
                },
            ),
            map(
                match_and_length(Self::match_string),
                |(matched_string, length)| {
                    EncodedTextValue::new(
                        MatchedValue::String(matched_string),
                        self.offset(),
                        length,
                    )
                },
            ),
            map(
                match_and_length(Self::match_symbol),
                |(matched_symbol, length)| {
                    EncodedTextValue::new(
                        MatchedValue::Symbol(matched_symbol),
                        self.offset(),
                        length,
                    )
                },
            ),
            map(
                match_and_length(Self::match_list),
                |(matched_list, length)| {
                    EncodedTextValue::new(MatchedValue::List, matched_list.offset(), length)
                },
            ),
            map(
                match_and_length(Self::match_sexp),
                |(matched_list, length)| {
                    EncodedTextValue::new(MatchedValue::SExp, matched_list.offset(), length)
                },
            ),
            map(
                match_and_length(Self::match_struct),
                |(matched_struct, length)| {
                    EncodedTextValue::new(MatchedValue::Struct, matched_struct.offset(), length)
                },
            ),
            // TODO: The other Ion types
        ))
        .map(|encoded_value| LazyRawTextValue {
            encoded_value,
            input: self,
        })
        .parse(self)
    }

    /// Matches a list.
    ///
    /// If the input does not contain the entire list, returns `IonError::Incomplete(_)`.
    pub fn match_list(self) -> IonMatchResult<'data> {
        // If it doesn't start with [, it isn't a list.
        if self.bytes().first() != Some(&b'[') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this list.
        let list_body = self.slice_to_end(1);
        let sequence_iter = RawTextListIterator::new(list_body);
        let span = match sequence_iter.find_span() {
            Ok(span) => span,
            // If the complete container isn't available, return an incomplete.
            Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
            // If invalid syntax was encountered, return a failure to prevent nom from trying
            // other parser kinds.
            Err(e) => {
                return {
                    let error = InvalidInputError::new(self)
                        .with_label("matching a list")
                        .with_description(format!("{}", e));
                    Err(nom::Err::Failure(IonParseError::Invalid(error)))
                }
            }
        };

        // For the matched span, we use `self` again to include the opening `[`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        Ok((remaining, matched))
    }

    /// Matches a list.
    ///
    /// If the input does not contain the entire list, returns `IonError::Incomplete(_)`.
    pub fn match_sexp(self) -> IonMatchResult<'data> {
        if self.bytes().first() != Some(&b'(') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this sexp
        let sexp_body = self.slice_to_end(1);
        let sexp_iter = RawTextSExpIterator::new(sexp_body);
        let span = match sexp_iter.find_span() {
            Ok(span) => span,
            // If the complete container isn't available, return an incomplete.
            Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
            // If invalid syntax was encountered, return a failure to prevent nom from trying
            // other parser kinds.
            Err(e) => {
                return {
                    let error = InvalidInputError::new(self)
                        .with_label("matching a sexp")
                        .with_description(format!("{}", e));
                    Err(nom::Err::Failure(IonParseError::Invalid(error)))
                }
            }
        };
        // For the matched span, we use `self` again to include the opening `(`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        Ok((remaining, matched))
    }

    /// Matches a struct.
    ///
    /// If the input does not contain the entire struct, returns `IonError::Incomplete(_)`.
    pub fn match_struct(self) -> IonMatchResult<'data> {
        // If it doesn't start with {, it isn't a struct.
        if self.bytes().first() != Some(&b'{') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this struct.
        let struct_body = self.slice_to_end(1);
        let struct_iter = RawTextStructIterator::new(struct_body);
        let span = match struct_iter.find_span() {
            Ok(span) => span,
            // If the complete container isn't available, return an incomplete.
            Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
            // If invalid syntax was encountered, return a failure to prevent nom from trying
            // other parser kinds.
            Err(e) => {
                return {
                    let error = InvalidInputError::new(self)
                        .with_label("matching a struct")
                        .with_description(format!("{}", e));
                    Err(nom::Err::Failure(IonParseError::Invalid(error)))
                }
            }
        };

        // For the matched span, we use `self` again to include the opening `{`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        Ok((remaining, matched))
    }

    /// Matches a boolean value.
    pub fn match_bool(self) -> IonMatchResult<'data> {
        recognize(Self::read_bool)(self)
    }

    /// Matches and returns a boolean value.
    pub fn read_bool(self) -> IonParseResult<'data, bool> {
        terminated(
            alt((value(true, tag("true")), value(false, tag("false")))),
            Self::peek_stop_character,
        )(self)
    }

    /// Matches any type of null. (`null`, `null.null`, `null.int`, etc)
    pub fn match_null(self) -> IonMatchResult<'data> {
        recognize(Self::read_null)(self)
    }

    /// Matches and returns a null value.
    pub fn read_null(self) -> IonParseResult<'data, IonType> {
        delimited(
            tag("null"),
            opt(preceded(char('.'), Self::read_ion_type)),
            Self::peek_stop_character,
        )
        .map(|explicit_ion_type| explicit_ion_type.unwrap_or(IonType::Null))
        .parse(self)
    }

    /// Matches and returns an Ion type.
    fn read_ion_type(self) -> IonParseResult<'data, IonType> {
        alt((
            value(IonType::Null, tag("null")),
            value(IonType::Bool, tag("bool")),
            value(IonType::Int, tag("int")),
            value(IonType::Float, tag("float")),
            value(IonType::Decimal, tag("decimal")),
            value(IonType::Timestamp, tag("timestamp")),
            value(IonType::Symbol, tag("symbol")),
            value(IonType::String, tag("string")),
            value(IonType::Clob, tag("clob")),
            value(IonType::Blob, tag("blob")),
            value(IonType::List, tag("list")),
            value(IonType::SExp, tag("sexp")),
            value(IonType::Struct, tag("struct")),
        ))(self)
    }

    /// Matches any one of Ion's stop characters.
    fn match_stop_character(self) -> IonMatchResult<'data> {
        recognize(one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}")).parse(self)
    }

    /// Matches--but does not consume--any one of Ion's stop characters.
    fn peek_stop_character(self) -> IonMatchResult<'data> {
        peek(Self::match_stop_character).parse(self)
    }

    /// Matches the three parts of an int--its base, its sign, and its digits--without actually
    /// constructing an Int from them.
    fn match_int(self) -> IonParseResult<'data, MatchedInt> {
        terminated(
            // We test for base 16 and base 2 so the '0x' or '0b' isn't confused for a leading zero
            // in a base 10 number, which would be illegal.
            alt((
                Self::match_base_2_int,
                Self::match_base_16_int,
                Self::match_base_10_int,
            )),
            Self::peek_stop_character,
        )(self)
    }

    /// Matches a base-2 notation integer (e.g. `0b0`, `0B1010`, or `-0b0111`) and returns the
    /// partially parsed value as a [`MatchedInt`].
    fn match_base_2_int(self) -> IonParseResult<'data, MatchedInt> {
        separated_pair(
            opt(char('-')),
            alt((tag("0b"), tag("0B"))),
            Self::match_base_2_int_digits,
        )
        .map(|(maybe_sign, digits)| {
            MatchedInt::new(2, maybe_sign.is_some(), digits.offset() - self.offset())
        })
        .parse(self)
    }

    /// Matches the digits of a base-2 integer.
    fn match_base_2_int_digits(self) -> IonMatchResult<'data> {
        recognize(terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(is_a("01"), char('_'))),
            // One or more digits
            is_a("01"),
        ))(self)
    }

    /// Matches a base-10 notation integer (e.g. `0`, `255`, or `-1_024`) and returns the partially
    /// parsed value as a [`MatchedInt`].
    fn match_base_10_int(self) -> IonParseResult<'data, MatchedInt> {
        pair(opt(char('-')), Self::match_base_10_int_digits)
            .map(|(maybe_sign, digits)| {
                MatchedInt::new(10, maybe_sign.is_some(), digits.offset() - self.offset())
            })
            .parse(self)
    }

    /// Matches the digits of a base-10 integer. (i.e. An integer without a sign.)
    fn match_base_10_int_digits(self) -> IonMatchResult<'data> {
        alt((
            // The number is either a zero...
            recognize(char('0')),
            // Or it's a non-zero followed by some number of '_'-separated digits
            Self::match_base_10_digits_before_dot,
        ))(self)
    }

    /// Matches either:
    /// * a zero
    /// * a non-zero followed by some number of digits with optional underscores
    fn match_base_10_digits_before_dot(self) -> IonMatchResult<'data> {
        alt((
            tag("0"),
            recognize(pair(
                Self::match_base_10_leading_digit,
                Self::match_base_10_trailing_digits,
            )),
        ))(self)
    }

    /// Matches the first digit of a multi-digit base-10 integer. (i.e. Any digit but zero.)
    fn match_base_10_leading_digit(self) -> IonMatchResult<'data> {
        recognize(one_of("123456789"))(self)
    }

    /// Matches any number of digits with underscores optionally appearing in the middle.
    /// This parser accepts leading zeros, which is why it cannot be used for the beginning
    /// of a number.
    fn match_base_10_trailing_digits(self) -> IonMatchResult<'data> {
        recognize(many0_count(pair(opt(char('_')), digit1)))(self)
    }

    /// Matches a base-10 notation integer (e.g. `0x0`, `0X20`, or `-0xCAFE`) and returns the
    /// partially parsed value as a [`MatchedInt`].
    fn match_base_16_int(self) -> IonParseResult<'data, MatchedInt> {
        separated_pair(
            opt(char('-')),
            alt((tag("0x"), tag("0X"))),
            Self::match_base_16_int_trailing_digits,
        )
        .map(|(maybe_sign, digits)| {
            MatchedInt::new(16, maybe_sign.is_some(), digits.offset() - self.offset())
        })
        .parse(self)
    }

    /// Matches the digits that follow the '0x' or '0X' in a base-16 integer
    fn match_base_16_int_trailing_digits(self) -> IonMatchResult<'data> {
        recognize(terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(Self::take_base_16_digits1, char('_'))),
            // One or more digits
            Self::take_base_16_digits1,
        ))(self)
    }

    /// Recognizes 1 or more consecutive base-16 digits.
    // This function's "1" suffix is a style borrowed from `nom`.
    fn take_base_16_digits1(self) -> IonMatchResult<'data> {
        take_while1(|b: u8| b.is_ascii_hexdigit())(self)
    }

    /// Matches an Ion float of any syntax
    fn match_float(self) -> IonParseResult<'data, MatchedFloat> {
        alt((
            Self::match_float_special_value,
            Self::match_float_numeric_value,
        ))(self)
    }

    /// Matches special IEEE-754 floating point values, including +/- infinity and NaN.
    fn match_float_special_value(self) -> IonParseResult<'data, MatchedFloat> {
        alt((
            value(MatchedFloat::NotANumber, tag("nan")),
            value(MatchedFloat::PositiveInfinity, tag("+inf")),
            value(MatchedFloat::NegativeInfinity, tag("-inf")),
        ))(self)
    }

    /// Matches numeric IEEE-754 floating point values.
    fn match_float_numeric_value(self) -> IonParseResult<'data, MatchedFloat> {
        terminated(
            recognize(pair(
                Self::match_number_with_optional_dot_and_digits,
                Self::match_float_exponent_marker_and_digits,
            )),
            Self::peek_stop_character,
        )
        .map(|_matched| MatchedFloat::Numeric)
        .parse(self)
    }

    /// Matches a number that may or may not have a decimal place and trailing fractional digits.
    /// If a decimal place is present, there must also be trailing digits.
    /// For example:
    ///   1000
    ///   1000.559
    ///   -25.2
    fn match_number_with_optional_dot_and_digits(self) -> IonMatchResult<'data> {
        recognize(tuple((
            opt(tag("-")),
            Self::match_base_10_digits_before_dot,
            opt(Self::match_dot_followed_by_base_10_digits),
        )))(self)
    }

    /// In a float or decimal, matches the digits that are permitted before the decimal point.
    /// This includes either a single zero, or a non-zero followed by any sequence of digits.
    fn match_digits_before_dot(self) -> IonMatchResult<'data> {
        alt((
            tag("0"),
            recognize(pair(Self::match_leading_digit, Self::match_trailing_digits)),
        ))(self)
    }

    /// Matches a single non-zero base 10 digit.
    fn match_leading_digit(self) -> IonMatchResult<'data> {
        recognize(one_of("123456789"))(self)
    }

    /// Matches any number of base 10 digits, allowing underscores at any position except the end.
    fn match_trailing_digits(self) -> IonMatchResult<'data> {
        recognize(many0_count(preceded(opt(char('_')), digit1)))(self)
    }

    /// Recognizes a decimal point followed by any number of base-10 digits.
    fn match_dot_followed_by_base_10_digits(self) -> IonMatchResult<'data> {
        recognize(preceded(tag("."), opt(Self::match_digits_after_dot)))(self)
    }

    /// Like `match_digits_before_dot`, but allows leading zeros.
    fn match_digits_after_dot(self) -> IonMatchResult<'data> {
        recognize(terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(digit1, char('_'))),
            // One or more digits
            digit1,
        ))(self)
    }

    /// Matches an `e` or `E` followed by an optional sign (`+` or `-`) followed by one or more
    /// base 10 digits.
    fn match_float_exponent_marker_and_digits(self) -> IonMatchResult<'data> {
        preceded(one_of("eE"), Self::match_exponent_sign_and_digits)(self)
    }

    /// Recognizes the exponent portion of a decimal (everything after the 'd') or float
    /// (everything after the 'e'). This includes:
    /// * an optional '+' OR '-'
    /// * any number of decimal digits, which may:
    ///    * have underscores in between them: `1_000_000`
    ///    * have one or more leading zeros: `0005`
    fn match_exponent_sign_and_digits(self) -> IonMatchResult<'data> {
        recognize(pair(
            // Optional leading sign; if there's no sign, it's not negative.
            opt(Self::match_any_sign),
            Self::match_digits_after_dot,
        ))(self)
    }

    /// Matches `-` OR `+`.
    ///
    /// This is used for matching exponent signs; most places in Ion do not allow `+`.
    pub fn match_any_sign(self) -> IonMatchResult<'data> {
        alt((tag("+"), tag("-")))(self)
    }

    /// Matches short- or long-form string.
    fn match_string(self) -> IonParseResult<'data, MatchedString> {
        alt((Self::match_short_string, Self::match_long_string))(self)
    }

    /// Matches a short string. For example: `"foo"`
    fn match_short_string(self) -> IonParseResult<'data, MatchedString> {
        delimited(char('"'), Self::match_short_string_body, char('"'))
            .map(|(_matched, contains_escaped_chars)| {
                if contains_escaped_chars {
                    MatchedString::ShortWithEscapes
                } else {
                    MatchedString::ShortWithoutEscapes
                }
            })
            .parse(self)
    }

    /// Returns a matched buffer and a boolean indicating whether any escaped characters were
    /// found in the short string.
    fn match_short_string_body(self) -> IonParseResult<'data, (Self, bool)> {
        Self::match_text_until_unescaped(self, b'\"')
    }

    fn match_long_string(self) -> IonParseResult<'data, MatchedString> {
        // TODO: implement long string matching
        //       The `fail` parser is a nom builtin that never matches.
        fail(self)
    }

    /// Matches an operator symbol, which can only legally appear within an s-expression
    fn match_operator(self) -> IonParseResult<'data, LazyRawTextValue<'data>> {
        match_and_length(is_a("!#%&*+-./;<=>?@^`|~"))
            .map(|(text, length): (TextBufferView, usize)| LazyRawTextValue {
                input: self,
                encoded_value: EncodedTextValue::new(
                    MatchedValue::Symbol(MatchedSymbol::Operator),
                    text.offset(),
                    length,
                ),
            })
            .parse(self)
    }

    /// Matches a symbol ID (`$28`), an identifier (`foo`), or a quoted symbol (`'foo'`).
    fn match_symbol(self) -> IonParseResult<'data, MatchedSymbol> {
        alt((
            Self::match_symbol_id,
            Self::match_identifier,
            Self::match_quoted_symbol,
        ))(self)
    }

    /// Matches a symbol ID (`$28`).
    fn match_symbol_id(self) -> IonParseResult<'data, MatchedSymbol> {
        recognize(terminated(
            // Discard a `$` and parse an integer representing the symbol ID.
            // Note that symbol ID integers:
            //   * CANNOT have underscores in them. For example: `$1_0` is considered an identifier.
            //   * CAN have leading zeros. There's precedent for this in ion-java.
            preceded(tag("$"), digit1),
            // Peek at the next character to make sure it's unrelated to the symbol ID.
            // The spec does not offer a formal definition of what ends a symbol ID.
            // This checks for either a stop_character (which performs its own `peek()`)
            // or a colon (":"), which could be a field delimiter (":") or the beginning of
            // an annotation delimiter ('::').
            alt((
                // Each of the parsers passed to `alt` must have the same return type. `stop_character`
                // returns a char instead of a &str, so we use `recognize()` to get a &str instead.
                recognize(Self::peek_stop_character),
                peek(tag(":")), // Field delimiter (":") or annotation delimiter ("::")
            )),
        ))
        .map(|_matched| MatchedSymbol::SymbolId)
        .parse(self)
    }

    /// Matches an identifier (`foo`).
    fn match_identifier(self) -> IonParseResult<'data, MatchedSymbol> {
        let (remaining, identifier_text) = recognize(terminated(
            pair(
                Self::identifier_initial_character,
                Self::identifier_trailing_characters,
            ),
            not(Self::identifier_trailing_character),
        ))(self)?;
        // Ion defines a number of keywords that are syntactically indistinguishable from
        // identifiers. Keywords take precedence; we must ensure that any identifier we find
        // is not actually a keyword.
        const KEYWORDS: &[&str] = &["true", "false", "nan", "null"];
        // In many situations, this check will not be necessary. Another type's parser will
        // recognize the keyword as its own. (For example, `parse_boolean` would match the input
        // text `false`.) However, because symbols can appear in annotations and the check for
        // annotations precedes the parsing for all other types, we need this extra verification.
        if KEYWORDS
            .iter()
            .any(|k| k.as_bytes() == identifier_text.bytes())
        {
            // Finding a keyword is not a fatal error, it just means that this parser doesn't match.
            return Err(nom::Err::Error(IonParseError::Invalid(
                InvalidInputError::new(self),
            )));
        }
        Ok((remaining, MatchedSymbol::Identifier))
    }

    /// Matches any character that can appear at the start of an identifier.
    fn identifier_initial_character(self) -> IonParseResult<'data, Self> {
        recognize(alt((one_of("$_"), satisfy(|c| c.is_ascii_alphabetic()))))(self)
    }

    /// Matches any character that is legal in an identifier, though not necessarily at the beginning.
    fn identifier_trailing_character(self) -> IonParseResult<'data, Self> {
        recognize(alt((one_of("$_"), satisfy(|c| c.is_ascii_alphanumeric()))))(self)
    }

    /// Matches characters that are legal in an identifier, though not necessarily at the beginning.
    fn identifier_trailing_characters(self) -> IonParseResult<'data, Self> {
        recognize(many0_count(Self::identifier_trailing_character))(self)
    }

    /// Matches a quoted symbol (`'foo'`).
    fn match_quoted_symbol(self) -> IonParseResult<'data, MatchedSymbol> {
        delimited(char('\''), Self::match_quoted_symbol_body, char('\''))
            .map(|(_matched, contains_escaped_chars)| {
                if contains_escaped_chars {
                    MatchedSymbol::QuotedWithEscapes
                } else {
                    MatchedSymbol::QuotedWithoutEscapes
                }
            })
            .parse(self)
    }

    /// Returns a matched buffer and a boolean indicating whether any escaped characters were
    /// found in the short string.
    fn match_quoted_symbol_body(self) -> IonParseResult<'data, (Self, bool)> {
        Self::match_text_until_unescaped(self, b'\'')
    }

    /// A helper method for matching bytes until the specified delimiter. Ignores any byte
    /// (including the delimiter) that is prefaced by the escape character `\`.
    fn match_text_until_unescaped(self, delimiter: u8) -> IonParseResult<'data, (Self, bool)> {
        let mut is_escaped = false;
        let mut contains_escaped_chars = false;
        for (index, byte) in self.bytes().iter().enumerate() {
            if is_escaped {
                // If we're escaped, the previous byte was a \ and we ignore this one.
                is_escaped = false;
                continue;
            }
            if *byte == b'\\' {
                is_escaped = true;
                contains_escaped_chars = true;
                continue;
            }
            if *byte == delimiter {
                let matched = self.slice(0, index);
                let remaining = self.slice_to_end(index);
                return Ok((remaining, (matched, contains_escaped_chars)));
            }
        }
        Err(nom::Err::Incomplete(Needed::Unknown))
    }

    /// Matches a single base-10 digit, 0-9.
    fn match_any_digit(self) -> IonParseResult<'data, char> {
        satisfy(|c| c.is_ascii_digit())(self)
    }

    /// Matches a timestamp of any precision.
    pub fn match_timestamp(self) -> IonParseResult<'data, MatchedTimestamp> {
        alt((
            Self::match_timestamp_y,
            Self::match_timestamp_ym,
            Self::match_timestamp_ymd,
            Self::match_timestamp_ymd_hm,
            Self::match_timestamp_ymd_hms,
            Self::match_timestamp_ymd_hms_fractional,
        ))(self)
    }

    /// Matches a timestamp with year precision.
    fn match_timestamp_y(self) -> IonParseResult<'data, MatchedTimestamp> {
        terminated(
            Self::match_timestamp_year,
            pair(tag("T"), Self::peek_stop_character),
        )
        .map(|_year| MatchedTimestamp::new(TimestampPrecision::Year))
        .parse(self)
    }

    /// Matches a timestamp with month precision.
    fn match_timestamp_ym(self) -> IonParseResult<'data, MatchedTimestamp> {
        terminated(
            pair(Self::match_timestamp_year, Self::match_timestamp_month),
            pair(tag("T"), Self::peek_stop_character),
        )
        .map(|(_year, _month)| MatchedTimestamp::new(TimestampPrecision::Month))
        .parse(self)
    }

    /// Matches a timestamp with day precision.
    fn match_timestamp_ymd(self) -> IonParseResult<'data, MatchedTimestamp> {
        terminated(
            tuple((
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
            )),
            pair(opt(tag("T")), Self::peek_stop_character),
        )
        .map(|_| MatchedTimestamp::new(TimestampPrecision::Day))
        .parse(self)
    }

    /// Matches a timestamp with hour-and-minute precision.
    fn match_timestamp_ymd_hm(self) -> IonParseResult<'data, MatchedTimestamp> {
        terminated(
            tuple((
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
                Self::match_timestamp_hour_and_minute,
                Self::match_timestamp_offset,
            )),
            Self::peek_stop_character,
        )
        .map(|(_y, _m, _d, _hm, offset)| {
            MatchedTimestamp::new(TimestampPrecision::HourAndMinute).with_offset(offset)
        })
        .parse(self)
    }

    /// Matches a timestamp with second precision.
    fn match_timestamp_ymd_hms(self) -> IonParseResult<'data, MatchedTimestamp> {
        terminated(
            tuple((
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
                Self::match_timestamp_hour_and_minute,
                Self::match_timestamp_seconds,
                Self::match_timestamp_offset,
            )),
            Self::peek_stop_character,
        )
        .map(|(_y, _m, _d, _hm, _s, offset)| {
            MatchedTimestamp::new(TimestampPrecision::Second).with_offset(offset)
        })
        .parse(self)
    }

    /// Matches a timestamp with second precision, including a fractional seconds component.
    fn match_timestamp_ymd_hms_fractional(self) -> IonParseResult<'data, MatchedTimestamp> {
        terminated(
            tuple((
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
                Self::match_timestamp_hour_and_minute,
                Self::match_timestamp_seconds,
                Self::match_timestamp_fractional_seconds,
                Self::match_timestamp_offset,
            )),
            Self::peek_stop_character,
        )
        .map(|(_y, _m, _d, _hm, _s, _f, offset)| {
            MatchedTimestamp::new(TimestampPrecision::Second).with_offset(offset)
        })
        .parse(self)
    }

    /// Matches the year component of a timestamp.
    fn match_timestamp_year(self) -> IonMatchResult<'data> {
        recognize(take_while_m_n(4, 4, |c: u8| c.is_ascii_digit()))(self)
    }

    /// Matches the month component of a timestamp, including a leading `-`.
    fn match_timestamp_month(self) -> IonMatchResult<'data> {
        preceded(
            tag("-"),
            recognize(alt((
                pair(char('0'), one_of("123456789")),
                pair(char('1'), one_of("012")),
            ))),
        )(self)
    }

    /// Matches the day component of a timestamp, including a leading `-`.
    fn match_timestamp_day(self) -> IonMatchResult<'data> {
        preceded(
            tag("-"),
            recognize(alt((
                pair(char('0'), one_of("123456789")),
                pair(one_of("12"), Self::match_any_digit),
                pair(char('3'), one_of("10")),
            ))),
        )(self)
    }

    /// Matches a leading `T`, a two-digit hour component of a timestamp, a delimiting ':', and a
    /// two-digit minute component.
    fn match_timestamp_hour_and_minute(
        self,
    ) -> IonParseResult<'data, (TextBufferView<'data>, TextBufferView<'data>)> {
        preceded(
            tag("T"),
            // Hour
            separated_pair(
                recognize(alt((
                    pair(one_of("01"), Self::match_any_digit),
                    pair(char('2'), one_of("0123")),
                ))),
                // Delimiter
                tag(":"),
                // Minutes
                recognize(pair(one_of("012345"), Self::match_any_digit)),
            ),
        )(self)
    }

    /// Matches a leading `:`, and any two-digit second component from `00` to `59` inclusive.
    fn match_timestamp_seconds(self) -> IonMatchResult<'data> {
        preceded(
            tag(":"),
            recognize(pair(one_of("012345"), Self::match_any_digit)),
        )(self)
    }

    /// Matches the fractional seconds component of a timestamp, including a leading `.`.
    fn match_timestamp_fractional_seconds(self) -> IonMatchResult<'data> {
        preceded(tag("."), digit1)(self)
    }

    /// Matches a timestamp offset of any format.
    fn match_timestamp_offset(self) -> IonParseResult<'data, MatchedTimestampOffset> {
        alt((
            value(MatchedTimestampOffset::Zulu, tag("Z")),
            value(MatchedTimestampOffset::Unknown, tag("-00:00")),
            map(
                pair(one_of("-+"), Self::match_timestamp_offset_hours_and_minutes),
                |(sign, (hours, _minutes))| {
                    let is_negative = sign == '-';
                    let hours_offset = hours.offset();
                    MatchedTimestampOffset::HoursAndMinutes(MatchedHoursAndMinutes::new(
                        is_negative,
                        hours_offset,
                    ))
                },
            ),
        ))(self)
    }

    /// Matches a timestamp offset encoded as a two-digit hour, a delimiting `:`, and a two-digit
    /// minute.
    fn match_timestamp_offset_hours_and_minutes(self) -> IonParseResult<'data, (Self, Self)> {
        separated_pair(
            // Hour
            recognize(pair(Self::match_any_digit, Self::match_any_digit)),
            // Delimiter
            tag(":"),
            // Minutes
            recognize(pair(Self::match_any_digit, Self::match_any_digit)),
        )(self)
    }
}

// === nom trait implementations ===
// The trait implementations that follow are necessary for `TextBufferView` to be used as an input
// type in `nom` parsers. (`nom` only supports `&str` and `&[u8]` out of the box.) Defining our own
// input type makes it possible for us to carry around additional context during the parsing process,
// which is important for providing helpful error messages. For example: we can include the absolute
// offset of the input slice currently being read in our error messages.
//
// As `TextBufferView` is just a wrapper around a `&[u8]`, these implementations mostly delegate
// to the existing trait impls for `&[u8]`.

impl<'data> nom::InputTake for TextBufferView<'data> {
    fn take(&self, count: usize) -> Self {
        self.slice(0, count)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        let (before, after) = self.data.split_at(count);
        let buffer_before = TextBufferView::new_with_offset(before, self.offset());
        let buffer_after = TextBufferView::new_with_offset(after, self.offset() + count);
        // Nom's convention is to place the remaining portion of the buffer first, which leads to
        // a potentially surprising reversed tuple order.
        (buffer_after, buffer_before)
    }
}

impl<'data> nom::InputLength for TextBufferView<'data> {
    fn input_len(&self) -> usize {
        self.len()
    }
}

impl<'data> nom::InputIter for TextBufferView<'data> {
    type Item = u8;
    type Iter = Enumerate<Self::IterElem>;
    type IterElem = Copied<Iter<'data, u8>>;

    fn iter_indices(&self) -> Self::Iter {
        self.iter_elements().enumerate()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.data.iter().copied()
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.data.iter().position(|b| predicate(*b))
    }

    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        self.data.slice_index(count)
    }
}

impl<'a, 'b> nom::Compare<&'a str> for TextBufferView<'b> {
    fn compare(&self, t: &'a str) -> CompareResult {
        self.data.compare(t.as_bytes())
    }

    fn compare_no_case(&self, t: &'a str) -> CompareResult {
        self.data.compare_no_case(t.as_bytes())
    }
}

impl<'data> nom::Offset for TextBufferView<'data> {
    fn offset(&self, second: &Self) -> usize {
        self.data.offset(second.data)
    }
}

impl<'data> nom::Slice<RangeFrom<usize>> for TextBufferView<'data> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        self.slice_to_end(range.start)
    }
}

impl<'data> nom::Slice<RangeTo<usize>> for TextBufferView<'data> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        self.slice(0, range.end)
    }
}

impl<'data> nom::FindSubstring<&str> for TextBufferView<'data> {
    fn find_substring(&self, substr: &str) -> Option<usize> {
        self.data.find_substring(substr)
    }
}

impl<'data> nom::InputTakeAtPosition for TextBufferView<'data> {
    type Item = u8;

    fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.data.iter().position(|c| predicate(*c)) {
            Some(i) => Ok(self.take_split(i)),
            None => Err(nom::Err::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position1<P, E: ParseError<Self>>(
        &self,
        predicate: P,
        e: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.data.iter().position(|c| predicate(*c)) {
            Some(0) => Err(nom::Err::Error(E::from_error_kind(*self, e))),
            Some(i) => Ok(self.take_split(i)),
            None => Err(nom::Err::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position_complete<P, E: ParseError<Self>>(
        &self,
        predicate: P,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.data.iter().position(|c| predicate(*c)) {
            Some(i) => Ok(self.take_split(i)),
            None => Ok(self.take_split(self.input_len())),
        }
    }

    fn split_at_position1_complete<P, E: ParseError<Self>>(
        &self,
        predicate: P,
        e: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.data.iter().position(|c| predicate(*c)) {
            Some(0) => Err(nom::Err::Error(E::from_error_kind(*self, e))),
            Some(i) => Ok(self.take_split(i)),
            None => {
                if self.is_empty() {
                    Err(nom::Err::Error(E::from_error_kind(*self, e)))
                } else {
                    Ok(self.take_split(self.input_len()))
                }
            }
        }
    }
}

// === end of `nom` trait implementations

/// Takes a given parser and returns a new one that accepts any amount of leading whitespace before
/// calling the original parser.
fn whitespace_and_then<'data, P, O>(
    parser: P,
) -> impl Parser<TextBufferView<'data>, O, IonParseError<'data>>
where
    P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
{
    preceded(
        TextBufferView::match_optional_comments_and_whitespace,
        parser,
    )
}

/// Augments a given parser such that it returns the matched value and the number of input bytes
/// that it matched.
fn match_and_length<'data, P, O>(
    mut parser: P,
) -> impl Parser<TextBufferView<'data>, (O, usize), IonParseError<'data>>
where
    P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
{
    move |input: TextBufferView<'data>| {
        let offset_before = input.offset();
        let (remaining, matched) = match parser.parse(input) {
            Ok((remaining, matched)) => (remaining, matched),
            Err(e) => return Err(e),
        };
        let offset_after = remaining.offset();
        let match_length = offset_after - offset_before;
        Ok((remaining, (matched, match_length)))
    }
}

/// Augments a given parser such that it returns the matched value and the range of input bytes
/// that it matched.
pub(crate) fn match_and_span<'data, P, O>(
    mut parser: P,
) -> impl Parser<TextBufferView<'data>, (O, Range<usize>), IonParseError<'data>>
where
    P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
{
    move |input: TextBufferView<'data>| {
        let offset_before = input.offset();
        let (remaining, matched) = match parser.parse(input) {
            Ok((remaining, matched)) => (remaining, matched),
            Err(e) => return Err(e),
        };
        let offset_after = remaining.offset();
        let span = offset_before..offset_after;
        Ok((remaining, (matched, span)))
    }
}

/// Returns the number of bytes that the provided parser matched.
fn match_length<'data, P, O>(
    parser: P,
) -> impl Parser<TextBufferView<'data>, usize, IonParseError<'data>>
where
    P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
{
    // Call `match_and_length` and discard the output
    match_and_length(parser).map(|(_output, match_length)| match_length)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Stores an input string that can be tested against a given parser.
    struct MatchTest {
        input: String,
    }

    impl MatchTest {
        /// Takes an `input` string and appends a trailing space to it, guaranteeing that the
        /// contents of the input are considered a complete token.
        fn new(input: &str) -> Self {
            MatchTest {
                input: format!("{input} "), // add trailing space
            }
        }

        fn try_match<'data, P, O>(&'data self, parser: P) -> IonParseResult<'data, usize>
        where
            P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
        {
            let buffer = TextBufferView::new(self.input.as_bytes());
            match_length(parser).parse(buffer)
        }

        fn expect_match<'data, P, O>(&'data self, parser: P)
        where
            P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
        {
            let result = self.try_match(parser);
            let (_remaining, match_length) = result.unwrap();
            // Inputs have a trailing space that should _not_ be part of the match
            assert_eq!(
                match_length,
                self.input.len() - 1,
                "\nInput: '{}'\nMatched: '{}'\n",
                self.input,
                &self.input[..match_length]
            );
        }

        fn expect_mismatch<'data, P, O>(&'data self, parser: P)
        where
            P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
        {
            let result = self.try_match(parser);
            // We expect that only part of the input will match or that the entire
            // input will be rejected outright.
            if let Ok((_remaining, match_length)) = result {
                assert_ne!(
                    match_length,
                    self.input.len() - 1,
                    "parser unexpectedly matched the complete input: '{:?}\nResult: {:?}",
                    self.input,
                    result
                );
            }
        }
    }

    #[test]
    fn test_match_stop_char() {
        MatchTest::new(" ").expect_match(match_length(TextBufferView::match_stop_character));
    }

    #[test]
    fn test_match_ivm() {
        fn match_ivm(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_ivm));
        }
        fn mismatch_ivm(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_ivm));
        }

        match_ivm("$ion_1_0");
        match_ivm("$ion_1_1");
        match_ivm("$ion_1_2");
        match_ivm("$ion_124_17");

        mismatch_ivm("ion_1_0");
        mismatch_ivm("$ion__1_0");
        mismatch_ivm("$$ion_1_0");
        mismatch_ivm("$ion_FF_FF");
    }

    #[test]
    fn test_match_bool() {
        fn match_bool(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_bool));
        }
        fn mismatch_bool(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_bool));
        }

        match_bool("true");
        match_bool("false");

        mismatch_bool("True");
        mismatch_bool("TRUE");
        mismatch_bool("False");
        mismatch_bool("FALSE");
        mismatch_bool("potato");
        mismatch_bool("42");
    }

    #[test]
    fn test_match_null() {
        fn match_null(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_null));
        }
        fn mismatch_null(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_null));
        }
        let good_inputs = &[
            "null",
            "null.null",
            "null.bool",
            "null.int",
            "null.float",
            "null.decimal",
            "null.timestamp",
            "null.symbol",
            "null.string",
            "null.clob",
            "null.blob",
            "null.list",
            "null.sexp",
            "null.struct",
        ];
        for input in good_inputs {
            match_null(input);
        }

        let bad_inputs = &[
            "-1",
            "null.hello",
            "nullnull",
            "nullify",
            "null..int",
            "string.null",
        ];
        for input in bad_inputs {
            mismatch_null(input);
        }
    }

    #[test]
    fn test_match_int() {
        fn match_int(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_int));
        }
        fn mismatch_int(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_int));
        }
        let good_inputs = &[
            // Base 2 integers
            "0b0",
            "0B0",
            "0b1",
            "0B1",
            "0b0001",
            "0B1111",
            "0b1111_1111",
            "0B1010_1010",
            // Base 10 integers
            "0",
            "13",
            "942",
            "7_216",
            "1_000_000",
            "9_999_999",
            // Base 16 integers
            "0x0",
            "0x20",
            "0x0A",
            "0xcafe",
            "0xCAFE",
            "0XcaFE",
            "0xC_A_F_E",
            "0Xca_FE",
        ];
        for input in good_inputs {
            match_int(input);
            let negative = format!("-{input}");
            match_int(&negative);
        }

        let bad_inputs = &[
            "00",          // Zero with leading zero
            "0123",        // Non-zero with leading zero
            "--5",         // Double negative
            "+5",          // Explicit positive
            "1__000__000", // More than one underscore at a time
            "_123",        // Leading underscore
            "0x0x5",       // Multiple 0x prefixes
            "0xx5",        // Multiple Xs after 0
            "0x",          // Base 16 prefix w/no number
            "0b",          // Base 2 prefix w/no number
        ];
        for input in bad_inputs {
            mismatch_int(input);
        }
    }

    #[test]
    fn test_match_float() {
        fn match_float(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_float));
        }
        fn mismatch_float(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_float));
        }

        let good_inputs = &[
            "0.0e0", "0E0", "0e0", "305e1", "305e+1", "305e-1", "305e100", "305e-100", "305e+100",
            "305.0e1", "0.279e3", "279e0", "279.5e0", "279.5E0",
        ];
        for input in good_inputs {
            match_float(input);
            let negative = format!("-{input}");
            match_float(&negative);
        }

        let bad_inputs = &[
            "305",      // Integer
            "305e",     // Has exponent delimiter but no exponent
            ".305e",    // No digits before the decimal point
            "305e0.5",  // Fractional exponent
            "305e-0.5", // Negative fractional exponent
            "0305e1",   // Leading zero
            "+305e1",   // Leading plus sign
            "--305e1",  // Multiple negative signs
        ];
        for input in bad_inputs {
            mismatch_float(input);
        }
    }

    #[test]
    fn test_match_timestamp() {
        fn match_timestamp(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_timestamp));
        }
        fn mismatch_timestamp(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_timestamp));
        }

        let good_inputs = &[
            "2023T",
            "2023-08T",
            "2023-08-13", // T is optional for ymd
            "2023-08-13T",
            "2023-08-13T14:18Z",
            "2023-08-13T14:18+05:00",
            "2023-08-13T14:18-05:00",
            "2023-08-13T14:18:35-05:00",
            "2023-08-13T14:18:35.994-05:00",
        ];
        for input in good_inputs {
            match_timestamp(input);
        }

        let bad_inputs = &[
            "2023",                  // No 'T'
            "2023-08",               // No 'T'
            "20233T",                // 5-digit year
            "2023-13T",              // Out of bounds month
            "2023-08-41T",           // Out of bounds day
            "2023-08+18T",           // Wrong delimiter
            "2023-08-18T25:00Z",     // Out of bounds hour
            "2023-08-18T14:00",      // No offset
            "2023-08-18T14:62",      // Out of bounds minute
            "2023-08-18T14:35:61",   // Out of bounds second
            "2023-08-18T14:35:52.Z", // Dot but no fractional
        ];
        for input in bad_inputs {
            mismatch_timestamp(input);
        }
    }

    #[test]
    fn test_match_string() {
        fn match_string(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_string));
        }
        fn mismatch_string(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_string));
        }

        // These inputs have leading/trailing whitespace to make them more readable, but the string
        // matcher doesn't accept whitespace. We'll trim each one before testing it.
        let good_inputs = &[
            r#"
            "hello"
            "#,
            r#"
            "😀😀😀"
            "#,
            r#"
            "this has an escaped quote \" right in the middle"
            "#,
        ];
        for input in good_inputs {
            match_string(input.trim());
        }

        let bad_inputs = &[
            // Missing an opening quote
            r#"
            hello"
            "#,
            // Missing a closing quote
            r#"
            "hello
            "#,
            // Closing quote is escaped
            r#"
            "hello\"
            "#,
        ];
        for input in bad_inputs {
            mismatch_string(input);
        }
    }

    #[test]
    fn test_match_symbol() {
        fn match_symbol(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_symbol));
        }
        fn mismatch_symbol(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_symbol));
        }

        // These inputs have leading/trailing whitespace to make them more readable, but the string
        // matcher doesn't accept whitespace. We'll trim each one before testing it.
        let good_inputs = &[
            "'hello'",
            "'😀😀😀'",
            "'this has an escaped quote \\' right in the middle'",
            "$308",
            "$0",
            "foo",
            "name",
            "$bar",
            "_baz_quux",
        ];
        for input in good_inputs {
            match_symbol(input);
        }

        let bad_inputs = &[
            "'hello",    // No closing quote
            "'hello\\'", // Closing quote is escaped
            "$-8",       // Negative SID
            "nan",       // Identifier that is also a keyword
        ];
        for input in bad_inputs {
            mismatch_symbol(input);
        }
    }

    #[test]
    fn test_match_annotated_value() {
        fn match_annotated_value(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_annotated_value));
        }
        fn mismatch_annotated_value(input: &str) {
            MatchTest::new(input)
                .expect_mismatch(match_length(TextBufferView::match_annotated_value));
        }
        let good_inputs = &[
            "foo::5",
            "foo::bar::5",
            "foo :: 5",
            "foo::bar::baz::5",
            "foo :: /*comment*/ bar /*comment*/    :: baz :: 5",
            "foo::bar::baz::quux::quuz::5",
            "foo::'bar'::baz::$10::5",
        ];
        for input in good_inputs {
            match_annotated_value(input);
        }

        let bad_inputs = &["foo", "foo:bar", "foo:::bar"];
        for input in bad_inputs {
            mismatch_annotated_value(input);
        }
    }

    #[test]
    fn test_match_sexp() {
        fn match_sexp(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_sexp));
        }
        fn mismatch_sexp(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_sexp));
        }
        let good_inputs = &[
            "()",
            "(1)",
            "(1 2)",
            "(a)",
            "(a b)",
            "(a++)",
            "(++a)",
            "(())",
            "((()))",
            "(1 (2 (3 4) 5) 6)",
        ];
        for input in good_inputs {
            match_sexp(input);
        }

        let bad_inputs = &["foo", "1", "(", "(1 2 (3 4 5)"];
        for input in bad_inputs {
            mismatch_sexp(input);
        }
    }
}
