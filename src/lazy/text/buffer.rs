use std::fmt::{Debug, Formatter};
use std::iter::{Copied, Enumerate};
use std::ops::{Range, RangeFrom, RangeTo};
use std::slice::Iter;
use std::str::FromStr;

use bumpalo::Bump as BumpAllocator;
use nom::branch::alt;
use nom::bytes::complete::{
    is_a as complete_is_a, is_not as complete_is_not, tag as complete_tag,
    take_while as complete_take_while, take_while1 as complete_take_while1,
};
use nom::bytes::streaming::{is_a, tag, take_until, take_while_m_n};
use nom::character::complete::{
    char as complete_char, digit1 as complete_digit1, one_of as complete_one_of,
};
use nom::character::streaming::{alphanumeric1, char, digit1, one_of, satisfy};
use nom::combinator::{consumed, eof, map, not, opt, peek, recognize, success, value};
use nom::error::{ErrorKind, ParseError};
use nom::multi::{fold_many1, fold_many_m_n, many0_count, many1_count};
use nom::sequence::{delimited, pair, preceded, separated_pair, terminated, tuple};
use nom::{AsBytes, CompareResult, IResult, InputLength, InputTake, Needed, Parser};

use crate::lazy::decoder::{LazyRawFieldExpr, LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::{
    MatchedBlob, MatchedClob, MatchedDecimal, MatchedFieldName, MatchedFieldNameSyntax,
    MatchedFloat, MatchedInt, MatchedString, MatchedSymbol, MatchedTimestamp,
    MatchedTimestampOffset, MatchedValue,
};
use crate::lazy::text::parse_result::{InvalidInputError, IonParseError};
use crate::lazy::text::parse_result::{IonMatchResult, IonParseResult};
use crate::lazy::text::raw::r#struct::{LazyRawTextFieldName_1_0, RawTextStructIterator_1_0};
use crate::lazy::text::raw::sequence::{RawTextListIterator_1_0, RawTextSExpIterator_1_0};
use crate::lazy::text::raw::v1_1::reader::{
    EncodedTextMacroInvocation, LazyRawTextFieldName_1_1, MacroIdRef, RawTextEExpression_1_1,
    RawTextListIterator_1_1, RawTextSExpIterator_1_1, RawTextStructIterator_1_1,
    TextListSpanFinder_1_1, TextSExpSpanFinder_1_1, TextStructSpanFinder_1_1,
};
use crate::lazy::text::value::{
    LazyRawTextValue, LazyRawTextValue_1_0, LazyRawTextValue_1_1, LazyRawTextVersionMarker,
};
use crate::result::DecodingError;
use crate::{IonError, IonResult, IonType, TimestampPrecision};

impl<'a> Debug for TextBufferView<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        const CHARS_TO_SHOW: usize = 64;
        write!(f, "TextBufferView {{")?;
        // Try to read the next several bytes from the buffer as UTF-8...
        let text_result = std::str::from_utf8(self.data);
        // ...if it works, print the first 32 unicode scalars...
        if let Ok(text) = text_result {
            write!(
                f,
                "\"{}...\"",
                text.chars().take(CHARS_TO_SHOW).collect::<String>()
            )?;
        } else {
            // ...if it doesn't, print the first 32 bytes in hex.
            write!(f, "Invalid UTF-8")?;
            for byte in self.bytes().iter().take(CHARS_TO_SHOW) {
                write!(f, "{:x?} ", *byte)?;
            }
            if self.bytes().len() > CHARS_TO_SHOW {
                write!(f, "...{} more bytes", self.bytes().len() - CHARS_TO_SHOW)?;
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
pub(crate) const WHITESPACE_CHARACTERS_AS_STR: &str = " \t\r\n\x09\x0B\x0C";

/// A slice of unsigned bytes that can be cheaply copied and which defines methods for parsing
/// the various encoding elements of a text Ion stream.
///
/// Parsing methods have names that begin with `match_` and each return a `(match, remaining_input)`
/// pair. The `match` may be either the slice of the input that was matched (represented as another
/// `TextBufferView`) or a `MatchedValue` that retains information discovered during parsing that
/// will be useful if the match is later fully materialized into a value.
#[derive(Clone, Copy)]
pub struct TextBufferView<'top> {
    // `data` is a slice of remaining data in the larger input stream.
    // `offset` is the absolute position in the overall input stream where that slice begins.
    //
    // input: 00 01 02 03 04 05 06 07 08 09
    //                          └────┬────┘
    //                          data: &[u8]
    //                          offset: 6
    data: &'top [u8],
    offset: usize,
    pub(crate) allocator: &'top BumpAllocator,
}

impl<'a> PartialEq for TextBufferView<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.offset == other.offset && self.data == other.data
    }
}

impl<'top> TextBufferView<'top> {
    /// Constructs a new `TextBufferView` that wraps `data`, setting the view's `offset` to zero.
    #[inline]
    pub fn new(allocator: &'top BumpAllocator, data: &'top [u8]) -> TextBufferView<'top> {
        Self::new_with_offset(allocator, data, 0)
    }

    /// Constructs a new `TextBufferView` that wraps `data`, setting the view's `offset` to the
    /// specified value. This is useful when `data` is a slice from the middle of a larger stream.
    /// Note that `offset` is the index of the larger stream at which `data` begins and not an
    /// offset _into_ `data`.
    pub fn new_with_offset(
        allocator: &'top BumpAllocator,
        data: &'top [u8],
        offset: usize,
    ) -> TextBufferView<'top> {
        TextBufferView {
            allocator,
            data,
            offset,
        }
    }

    pub fn local_lifespan<'a>(self) -> TextBufferView<'a>
    where
        'top: 'a,
    {
        self.slice_to_end(0)
    }

    /// Returns a subslice of the [`TextBufferView`] that starts at `offset` and continues for
    /// `length` bytes.
    ///
    /// Note that `offset` is relative to the beginning of the buffer, not the beginning of the
    /// larger stream of which the buffer is a piece.
    pub fn slice(&self, offset: usize, length: usize) -> TextBufferView<'top> {
        TextBufferView {
            data: &self.data[offset..offset + length],
            offset: self.offset + offset,
            allocator: self.allocator,
        }
    }

    /// Returns a subslice of the [`TextBufferView`] that starts at `offset` and continues
    /// to the end.
    ///
    /// Note that `offset` is relative to the beginning of the buffer, not the beginning of the
    /// larger stream of which the buffer is a piece.
    pub fn slice_to_end(&self, offset: usize) -> TextBufferView<'top> {
        TextBufferView {
            data: &self.data[offset..],
            offset: self.offset + offset,
            allocator: self.allocator,
        }
    }

    /// Returns a slice containing all of the buffer's bytes.
    pub fn bytes(&self) -> &'top [u8] {
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

    /// Returns the stream byte offset range that this buffer contains.
    pub fn range(&self) -> Range<usize> {
        self.offset..self.offset + self.len()
    }

    /// Returns `true` if there are no bytes in the buffer. Otherwise, returns `false`.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Attempts to view the contents of the buffer as a UTF-8 `&str`.
    pub fn as_text<'a>(&'a self) -> IonResult<&'top str> {
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

    pub fn match_whitespace(self) -> IonMatchResult<'top> {
        complete_is_a(WHITESPACE_CHARACTERS_AS_STR)(self)
    }

    /// Always succeeds and consumes none of the input. Returns an empty slice of the buffer.
    // This method is useful for parsers that need to match an optional construct but don't want
    // to return an Option<_>. For an example, see its use in `match_optional_whitespace`.
    fn match_nothing(self) -> IonMatchResult<'top> {
        // Use nom's `success` parser to return an empty slice from the head position
        success(self.slice(0, 0))(self)
    }

    /// Matches zero or more whitespace characters.
    pub fn match_optional_whitespace(self) -> IonMatchResult<'top> {
        // Either match whitespace and return what follows or just return the input as-is.
        // This will always return `Ok`, but it is packaged as an IonMatchResult for compatability
        // with other parsers.
        alt((Self::match_whitespace, Self::match_nothing))(self)
    }

    /// Matches any amount of contiguous comments and whitespace, including none.
    pub fn match_optional_comments_and_whitespace(self) -> IonMatchResult<'top> {
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
    pub fn match_comment(self) -> IonMatchResult<'top> {
        alt((
            Self::match_rest_of_line_comment,
            Self::match_multiline_comment,
        ))(self)
    }

    /// Matches a single rest-of-the-line comment.
    fn match_rest_of_line_comment(self) -> IonMatchResult<'top> {
        preceded(
            // Matches a leading "//"...
            complete_tag("//"),
            // ...followed by either...
            alt((
                // ...one or more non-EOL characters...
                complete_is_not("\r\n"),
                // ...or any EOL character.
                peek(recognize(complete_one_of("\r\n"))),
                // In either case, the line ending will not be consumed.
            )),
        )(self)
    }

    /// Matches a single multiline comment.
    fn match_multiline_comment(self) -> IonMatchResult<'top> {
        recognize(delimited(
            // Matches a leading "/*"...
            complete_tag("/*"),
            // ...any number of non-"*/" characters...
            take_until("*/"),
            // ...and then a closing "*/"
            complete_tag("*/"),
        ))(self)
    }

    /// Matches an Ion version marker (e.g. `$ion_1_0` or `$ion_1_1`.)
    pub fn match_ivm<E: TextEncoding<'top>>(
        self,
    ) -> IonParseResult<'top, LazyRawTextVersionMarker<'top, E>> {
        let (remaining, (matched_marker, (matched_major, matched_minor))) = consumed(terminated(
            preceded(
                complete_tag("$ion_"),
                separated_pair(complete_digit1, complete_tag("_"), complete_digit1),
            ),
            // Look ahead to make sure the IVM isn't followed by a '::'. If it is, then it's not
            // an IVM, it's an annotation.
            peek(whitespace_and_then(not(complete_tag("::")))),
        ))(self)?;
        // `major` and `minor` are base 10 digits. Turning them into `&str`s is guaranteed to succeed.
        let major_version = u8::from_str(matched_major.as_text().unwrap()).map_err(|_| {
            let error = InvalidInputError::new(matched_major)
                .with_label("parsing an IVM major version")
                .with_description("value did not fit in an unsigned byte");
            nom::Err::Failure(IonParseError::Invalid(error))
        })?;
        let minor_version = u8::from_str(matched_minor.as_text().unwrap()).map_err(|_| {
            let error = InvalidInputError::new(matched_minor)
                .with_label("parsing an IVM minor version")
                .with_description("value did not fit in an unsigned byte");
            nom::Err::Failure(IonParseError::Invalid(error))
        })?;
        let marker =
            LazyRawTextVersionMarker::<E>::new(matched_marker, major_version, minor_version);

        Ok((remaining, marker))
    }

    /// Matches one or more annotations.
    pub fn match_annotations(self) -> IonMatchResult<'top> {
        let (remaining, matched) = recognize(many1_count(Self::match_annotation))(self)?;
        if matched.len() > u16::MAX as usize {
            let error = InvalidInputError::new(matched)
                .with_description("the maximum supported annotations sequence length is 65KB")
                .with_label("parsing annotations");
            Err(nom::Err::Error(IonParseError::Invalid(error)))
        } else {
            Ok((remaining, matched))
        }
    }

    /// Matches an annotation (symbol token) and a terminating '::'.
    pub fn match_annotation(self) -> IonParseResult<'top, (MatchedSymbol, Range<usize>)> {
        terminated(
            whitespace_and_then(match_and_span(Self::match_symbol)),
            whitespace_and_then(terminated(
                // The complete_tag/tag pair allows the parser to recognize that:
                //
                //     foo::bar::baz:
                //
                // is incomplete while:
                //
                //     foo::bar::baz
                //
                // is a symbol with two annotations.
                pair(complete_tag(":"), tag(":")),
                Self::match_optional_comments_and_whitespace,
            )),
        )(self)
    }

    /// Matches an optional annotations sequence and a value, including operators.
    pub fn match_sexp_value(self) -> IonParseResult<'top, Option<LazyRawTextValue_1_0<'top>>> {
        whitespace_and_then(alt((
            value(None, tag(")")),
            pair(
                opt(Self::match_annotations),
                // We need the s-expression parser to recognize the input `--3` as the operator `--` and the
                // int `3` while recognizing the input `-3` as the int `-3`. If `match_operator` runs before
                // `match_value`, it will consume the sign (`-`) of negative number values, treating
                // `-3` as an operator (`-`) and an int (`3`). Thus, we run `match_value` first.
                whitespace_and_then(alt((Self::match_value, Self::match_operator))),
            )
            .map(|(maybe_annotations, value)| self.apply_annotations(maybe_annotations, value))
            .map(Some),
        )))
        .parse(self)
    }

    /// Matches either:
    /// * A macro invocation
    /// * An optional annotations sequence and a value
    pub fn match_sexp_value_1_1(
        self,
    ) -> IonParseResult<'top, Option<LazyRawValueExpr<'top, TextEncoding_1_1>>> {
        whitespace_and_then(alt((
            Self::match_e_expression.map(|matched| Some(RawValueExpr::MacroInvocation(matched))),
            value(None, tag(")")),
            pair(
                opt(Self::match_annotations),
                // We need the s-expression parser to recognize the input `--3` as the operator `--` and the
                // int `3` while recognizing the input `-3` as the int `-3`. If `match_operator` runs before
                // `match_value`, it will consume the sign (`-`) of negative number values, treating
                // `-3` as an operator (`-`) and an int (`3`). Thus, we run `match_value` first.
                whitespace_and_then(alt((Self::match_value_1_1, Self::match_operator))),
            )
            .map(|(maybe_annotations, value)| self.apply_annotations(maybe_annotations, value))
            .map(RawValueExpr::ValueLiteral)
            .map(Some),
        )))
        .parse(self)
    }

    fn apply_annotations<E: TextEncoding<'top>>(
        self,
        maybe_annotations: Option<TextBufferView<'top>>,
        mut value: LazyRawTextValue<'top, E>,
    ) -> LazyRawTextValue<'top, E> {
        if let Some(annotations) = maybe_annotations {
            let annotations_length =
                u16::try_from(annotations.len()).expect("already length checked");
            // Update the encoded value's record of how many bytes of annotations precede the data.
            value.encoded_value = value
                .encoded_value
                .with_annotations_sequence(annotations_length);
            let unannotated_value_length = value.input.len();
            // Rewind the value's input to include the annotations sequence.
            value.input = self.slice(
                annotations.offset() - self.offset(),
                annotations_length as usize + unannotated_value_length,
            );
        }
        value
    }

    /// Matches a struct field name/value pair.
    ///
    /// If a pair is found, returns `Some(field)` and consumes the following comma if present.
    /// If no pair is found (that is: the end of the struct is next), returns `None`.
    pub fn match_struct_field(
        self,
    ) -> IonParseResult<'top, Option<LazyRawFieldExpr<'top, TextEncoding_1_0>>> {
        // A struct field can have leading whitespace, but we want the buffer slice that we match
        // to begin with the field name. Here we skip any whitespace so we have another named
        // slice (`input_including_field_name`) with that property.
        let (input_including_field_name, _ws) = self.match_optional_comments_and_whitespace()?;
        alt((
            // If the next thing in the input is a `}`, return `None`.
            value(None, Self::match_struct_end),
            // Otherwise, match a name/value pair and turn it into a `LazyRawTextField`.
            Self::match_struct_field_name_and_value.map(move |(matched_field_name, value)| {
                let field_name = LazyRawTextFieldName_1_0::new(matched_field_name);
                Some(LazyRawFieldExpr::<'top, TextEncoding_1_0>::NameValue(
                    field_name, value,
                ))
            }),
        ))(input_including_field_name)
    }

    /// Matches any amount of whitespace followed by a closing `}`.
    fn match_struct_end(self) -> IonMatchResult<'top> {
        whitespace_and_then(peek(tag("}"))).parse(self)
    }

    /// Matches a field name/value pair. Returns the syntax used for the field name, the range of
    /// input bytes where the field name is found, and the value.
    pub fn match_struct_field_name_and_value(
        self,
    ) -> IonParseResult<'top, (MatchedFieldName<'top>, LazyRawTextValue_1_0<'top>)> {
        terminated(
            separated_pair(
                whitespace_and_then(Self::match_struct_field_name),
                whitespace_and_then(tag(":")),
                whitespace_and_then(Self::match_annotated_value),
            ),
            whitespace_and_then(alt((tag(","), peek(tag("}"))))),
        )(self)
    }

    /// Matches a struct field (name, value expression) pair.
    ///
    /// If a pair is found, returns `Some(field)` and consumes the following comma if present.
    /// If no pair is found (that is: the end of the struct is next), returns `None`.
    pub fn match_struct_field_1_1(
        self,
    ) -> IonParseResult<'top, Option<LazyRawFieldExpr<'top, TextEncoding_1_1>>> {
        // A struct field can have leading whitespace, but we want the buffer slice that we match
        // to begin with the field name. Here we skip any whitespace so we have another named
        // slice (`input_including_field_name`) with that property.
        let (input_including_field_name, _ws) = self.match_optional_comments_and_whitespace()?;
        let (input_after_field, field_expr_result) = alt((
            // If the next thing in the input is a `}`, return `None`.
            Self::match_struct_end.map(|_| Ok(None)),
            terminated(
                Self::match_e_expression.map(|eexp| Ok(Some(LazyRawFieldExpr::EExp(eexp)))),
                whitespace_and_then(alt((tag(","), peek(tag("}"))))),
            ),
            Self::match_struct_field_name_and_e_expression_1_1.map(|(field_name, invocation)| {
                Ok(Some(LazyRawFieldExpr::NameEExp(
                    LazyRawTextFieldName_1_1::new(field_name),
                    invocation,
                )))
            }),
            // Otherwise, match a name/value pair and turn it into a `LazyRawTextField`.
            Self::match_struct_field_name_and_value_1_1.map(move |(field_name, value)| {
                let field_name = LazyRawTextFieldName_1_1::new(field_name);
                Ok(Some(LazyRawFieldExpr::NameValue(field_name, value)))
            }),
        ))(input_including_field_name)?;
        Ok((input_after_field, field_expr_result?))
    }

    /// Matches a field (name, value expression) pair, where the value expression may be either
    /// an annotated value or an e-expression. Returns the syntax used for the field name, the
    /// range of input bytes where the field name is found, and the value.
    pub fn match_struct_field_name_and_e_expression_1_1(
        self,
    ) -> IonParseResult<'top, (MatchedFieldName<'top>, RawTextEExpression_1_1<'top>)> {
        terminated(
            separated_pair(
                whitespace_and_then(Self::match_struct_field_name),
                whitespace_and_then(tag(":")),
                whitespace_and_then(Self::match_e_expression),
            ),
            whitespace_and_then(alt((tag(","), peek(tag("}"))))),
        )(self)
    }

    /// Matches a field (name, value expression) pair, where the value expression may be either
    /// an annotated value or an e-expression. Returns the syntax used for the field name, the
    /// range of input bytes where the field name is found, and the value.
    pub fn match_struct_field_name_and_value_1_1(
        self,
    ) -> IonParseResult<'top, (MatchedFieldName<'top>, LazyRawTextValue_1_1<'top>)> {
        terminated(
            separated_pair(
                whitespace_and_then(Self::match_struct_field_name),
                whitespace_and_then(tag(":")),
                whitespace_and_then(Self::match_annotated_value_1_1),
            ),
            whitespace_and_then(alt((tag(","), peek(tag("}"))))),
        )(self)
    }

    /// Matches an optional annotation sequence and a trailing value.
    pub fn match_annotated_value(self) -> IonParseResult<'top, LazyRawTextValue_1_0<'top>> {
        pair(
            opt(Self::match_annotations),
            whitespace_and_then(Self::match_value),
        )
        .map(|(maybe_annotations, value)| self.apply_annotations(maybe_annotations, value))
        .parse(self)
    }

    /// Matches an optional annotation sequence and a trailing v1.1 value.
    pub fn match_annotated_value_1_1(self) -> IonParseResult<'top, LazyRawTextValue_1_1<'top>> {
        pair(
            opt(Self::match_annotations),
            whitespace_and_then(Self::match_value_1_1),
        )
        .map(|(maybe_annotations, value)| self.apply_annotations(maybe_annotations, value))
        .parse(self)
    }

    /// Matches a struct field name. That is:
    /// * A quoted symbol
    /// * An identifier
    /// * A symbol ID
    /// * A short-form string
    pub fn match_struct_field_name(self) -> IonParseResult<'top, MatchedFieldName<'top>> {
        consumed(alt((
            Self::match_string.map(MatchedFieldNameSyntax::String),
            Self::match_symbol.map(MatchedFieldNameSyntax::Symbol),
        )))
        .map(|(matched_inpet, syntax)| MatchedFieldName::new(matched_inpet, syntax))
        .parse(self)
    }

    /// Matches a single top-level value, an IVM, or the end of the stream.
    pub fn match_top_level_item_1_0(
        self,
    ) -> IonParseResult<'top, LazyRawStreamItem<'top, TextEncoding_1_0>> {
        // If only whitespace/comments remain, we're at the end of the stream.
        let (input_after_ws, _ws) = self.match_optional_comments_and_whitespace()?;
        if input_after_ws.is_empty() {
            return Ok((
                input_after_ws,
                RawStreamItem::EndOfStream(EndPosition::new(input_after_ws.offset())),
            ));
        }
        // Otherwise, the next item must be an IVM or a value.
        // We check for IVMs first because the rules for a symbol identifier will match them.
        alt((
            Self::match_ivm::<TextEncoding_1_0>.map(RawStreamItem::VersionMarker),
            Self::match_annotated_value
                .map(LazyRawTextValue_1_0::from)
                .map(RawStreamItem::Value),
        ))(input_after_ws)
    }

    /// Matches a single top-level value, e-expression (macro invocation), IVM, or the end of
    /// the stream.
    pub fn match_top_level_item_1_1(
        self,
    ) -> IonParseResult<'top, LazyRawStreamItem<'top, TextEncoding_1_1>> {
        // If only whitespace/comments remain, we're at the end of the stream.
        let (input_after_ws, _ws) = self.match_optional_comments_and_whitespace()?;
        if input_after_ws.is_empty() {
            return Ok((
                input_after_ws,
                RawStreamItem::EndOfStream(EndPosition::new(input_after_ws.offset())),
            ));
        }
        // Otherwise, the next item must be an IVM or a value.
        // We check for IVMs first because the rules for a symbol identifier will match them.
        alt((
            Self::match_ivm::<TextEncoding_1_1>.map(RawStreamItem::VersionMarker),
            Self::match_e_expression.map(RawStreamItem::EExpression),
            Self::match_annotated_value_1_1
                .map(LazyRawTextValue_1_1::from)
                .map(RawStreamItem::Value),
        ))(input_after_ws)
    }

    /// Matches a single scalar value or the beginning of a container.
    pub fn match_value(self) -> IonParseResult<'top, LazyRawTextValue_1_0<'top>> {
        consumed(alt((
            // For `null` and `bool`, we use `read_` instead of `match_` because there's no additional
            // parsing to be done.
            map(Self::match_null, |ion_type| {
                EncodedTextValue::new(MatchedValue::Null(ion_type))
            }),
            map(Self::match_bool, |value| {
                EncodedTextValue::new(MatchedValue::Bool(value))
            }),
            // For `int` and the other types, we use `match` and store the partially-processed input in the
            // `matched_value` field of the `EncodedTextValue` we return.
            map(Self::match_int, |matched_int| {
                EncodedTextValue::new(MatchedValue::Int(matched_int))
            }),
            map(Self::match_float, |matched_float| {
                EncodedTextValue::new(MatchedValue::Float(matched_float))
            }),
            map(Self::match_decimal, |matched_decimal| {
                EncodedTextValue::new(MatchedValue::Decimal(matched_decimal))
            }),
            map(Self::match_timestamp, |matched_timestamp| {
                EncodedTextValue::new(MatchedValue::Timestamp(matched_timestamp))
            }),
            map(Self::match_string, |matched_string| {
                EncodedTextValue::new(MatchedValue::String(matched_string))
            }),
            map(Self::match_symbol, |matched_symbol| {
                EncodedTextValue::new(MatchedValue::Symbol(matched_symbol))
            }),
            map(Self::match_blob, |matched_blob| {
                EncodedTextValue::new(MatchedValue::Blob(matched_blob))
            }),
            map(Self::match_clob, |matched_clob| {
                EncodedTextValue::new(MatchedValue::Clob(matched_clob))
            }),
            map(Self::match_list, |_matched_list| {
                // TODO: Cache child expressions found in 1.0 list
                let not_yet_used_in_1_0 =
                    bumpalo::collections::Vec::new_in(self.allocator).into_bump_slice();
                EncodedTextValue::new(MatchedValue::List(not_yet_used_in_1_0))
            }),
            map(Self::match_sexp, |_matched_sexp| {
                // TODO: Cache child expressions found in 1.0 sexp
                let not_yet_used_in_1_0 =
                    bumpalo::collections::Vec::new_in(self.allocator).into_bump_slice();
                EncodedTextValue::new(MatchedValue::SExp(not_yet_used_in_1_0))
            }),
            map(Self::match_struct, |_matched_struct| {
                // TODO: Cache child expressions found in 1.0 struct
                let not_yet_used_in_1_0 =
                    bumpalo::collections::Vec::new_in(self.allocator).into_bump_slice();
                EncodedTextValue::new(MatchedValue::Struct(not_yet_used_in_1_0))
            }),
        )))
        .map(|(input, encoded_value)| LazyRawTextValue_1_0 {
            encoded_value,
            input,
        })
        .parse(self)
    }

    pub fn match_value_1_1(self) -> IonParseResult<'top, LazyRawTextValue_1_1<'top>> {
        consumed(alt((
            // For `null` and `bool`, we use `read_` instead of `match_` because there's no additional
            // parsing to be done.
            map(Self::match_null, |ion_type| {
                EncodedTextValue::new(MatchedValue::Null(ion_type))
            }),
            map(Self::match_bool, |value| {
                EncodedTextValue::new(MatchedValue::Bool(value))
            }),
            // For `int` and the other types, we use `match` and store the partially-processed input in the
            // `matched_value` field of the `EncodedTextValue` we return.
            map(Self::match_int, |matched_int| {
                EncodedTextValue::new(MatchedValue::Int(matched_int))
            }),
            map(Self::match_float, |matched_float| {
                EncodedTextValue::new(MatchedValue::Float(matched_float))
            }),
            map(Self::match_decimal, |matched_decimal| {
                EncodedTextValue::new(MatchedValue::Decimal(matched_decimal))
            }),
            map(Self::match_timestamp, |matched_timestamp| {
                EncodedTextValue::new(MatchedValue::Timestamp(matched_timestamp))
            }),
            map(Self::match_string, |matched_string| {
                EncodedTextValue::new(MatchedValue::String(matched_string))
            }),
            map(Self::match_symbol, |matched_symbol| {
                EncodedTextValue::new(MatchedValue::Symbol(matched_symbol))
            }),
            map(Self::match_blob, |matched_blob| {
                EncodedTextValue::new(MatchedValue::Blob(matched_blob))
            }),
            map(Self::match_clob, |matched_clob| {
                EncodedTextValue::new(MatchedValue::Clob(matched_clob))
            }),
            map(Self::match_list_1_1, |(_matched_list, child_expr_cache)| {
                EncodedTextValue::new(MatchedValue::List(child_expr_cache))
            }),
            map(Self::match_sexp_1_1, |(_matched_sexp, child_expr_cache)| {
                EncodedTextValue::new(MatchedValue::SExp(child_expr_cache))
            }),
            map(
                Self::match_struct_1_1,
                |(_matched_struct, field_expr_cache)| {
                    EncodedTextValue::new(MatchedValue::Struct(field_expr_cache))
                },
            ),
        )))
        .map(|(input, encoded_value)| LazyRawTextValue_1_1 {
            encoded_value,
            input,
        })
        .parse(self)
    }

    /// Matches a list.
    ///
    /// If the input does not contain the entire list, returns `IonError::Incomplete(_)`.
    pub fn match_list(self) -> IonMatchResult<'top> {
        // If it doesn't start with [, it isn't a list.
        if self.bytes().first() != Some(&b'[') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this list.
        let list_body = self.slice_to_end(1);
        let sequence_iter = RawTextListIterator_1_0::new(list_body);
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

    /// Matches an Ion v1.1 list, which allows e-expressions (macro invocations) to appear in value
    /// position.
    ///
    /// If the input does not contain the entire list, returns `IonError::Incomplete(_)`.
    // TODO: DRY with `match_list`
    pub fn match_list_1_1(
        self,
    ) -> IonParseResult<
        'top,
        (
            TextBufferView<'top>,
            &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
        ),
    > {
        // If it doesn't start with [, it isn't a list.
        if self.bytes().first() != Some(&b'[') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this list.
        let list_body = self.slice_to_end(1);
        let sequence_iter = RawTextListIterator_1_1::new(list_body);
        let (span, child_exprs) =
            match TextListSpanFinder_1_1::new(self.allocator, sequence_iter).find_span() {
                Ok((span, child_exprs)) => (span, child_exprs),
                // If the complete container isn't available, return an incomplete.
                Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
                // If invalid syntax was encountered, return a failure to prevent nom from trying
                // other parser kinds.
                Err(e) => {
                    return {
                        let error = InvalidInputError::new(self)
                            .with_label("matching a v1.1 list")
                            .with_description(format!("{}", e));
                        Err(nom::Err::Failure(IonParseError::Invalid(error)))
                    }
                }
            };

        // For the matched span, we use `self` again to include the opening `[`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        Ok((remaining, (matched, child_exprs)))
    }

    // TODO: DRY with `match_sexp`
    pub fn match_sexp_1_1(
        self,
    ) -> IonParseResult<
        'top,
        (
            TextBufferView<'top>,
            &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
        ),
    > {
        if self.bytes().first() != Some(&b'(') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this sexp
        let sexp_body = self.slice_to_end(1);
        let sexp_iter = RawTextSExpIterator_1_1::new(sexp_body);
        let (span, child_expr_cache) =
            match TextSExpSpanFinder_1_1::new(self.allocator, sexp_iter).find_span(1) {
                Ok((span, child_expr_cache)) => (span, child_expr_cache),
                // If the complete container isn't available, return an incomplete.
                Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
                // If invalid syntax was encountered, return a failure to prevent nom from trying
                // other parser kinds.
                Err(e) => {
                    return {
                        let error = InvalidInputError::new(self)
                            .with_label("matching a 1.1 sexp")
                            .with_description(format!("{}", e));
                        Err(nom::Err::Failure(IonParseError::Invalid(error)))
                    }
                }
            };
        // For the matched span, we use `self` again to include the opening `(`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        Ok((remaining, (matched, child_expr_cache)))
    }

    /// Matches a single value in a list OR the end of the list, allowing for leading whitespace
    /// and comments in either case.
    ///
    /// If a value is found, returns `Ok(Some(value))`. If the end of the list is found, returns
    /// `Ok(None)`.
    pub fn match_list_value(self) -> IonParseResult<'top, Option<LazyRawTextValue_1_0<'top>>> {
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

    /// Matches either:
    /// * An e-expression (i.e. macro invocation)
    /// * An optional annotations sequence and a value
    pub fn match_list_value_1_1(
        self,
    ) -> IonParseResult<'top, Option<LazyRawValueExpr<'top, TextEncoding_1_1>>> {
        whitespace_and_then(alt((
            terminated(
                Self::match_e_expression,
                Self::match_delimiter_after_list_value,
            )
            .map(|matched| Some(RawValueExpr::MacroInvocation(matched))),
            value(None, tag("]")),
            terminated(
                Self::match_annotated_value_1_1.map(Some),
                // ...followed by a comma or end-of-list
                Self::match_delimiter_after_list_value,
            )
            .map(|maybe_matched| maybe_matched.map(RawValueExpr::ValueLiteral)),
        )))
        .parse(self)
    }

    /// Matches syntax that is expected to follow a value in a list: any amount of whitespace and/or
    /// comments followed by either a comma (consumed) or an end-of-list `]` (not consumed).
    fn match_delimiter_after_list_value(self) -> IonMatchResult<'top> {
        preceded(
            Self::match_optional_comments_and_whitespace,
            alt((tag(","), peek(tag("]")))),
        )(self)
    }

    /// Matches an s-expression (sexp).
    ///
    /// If the input does not contain the entire s-expression, returns `IonError::Incomplete(_)`.
    pub fn match_sexp(self) -> IonMatchResult<'top> {
        if self.bytes().first() != Some(&b'(') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this sexp
        let sexp_body = self.slice_to_end(1);
        let sexp_iter = RawTextSExpIterator_1_0::new(sexp_body);
        let span = match sexp_iter.find_span(1) {
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
    pub fn match_struct(self) -> IonMatchResult<'top> {
        // If it doesn't start with {, it isn't a struct.
        if self.bytes().first() != Some(&b'{') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this struct.
        let struct_body = self.slice_to_end(1);
        let struct_iter = RawTextStructIterator_1_0::new(struct_body);
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

    pub fn match_struct_1_1(
        self,
    ) -> IonParseResult<
        'top,
        (
            TextBufferView<'top>,
            &'top [LazyRawFieldExpr<'top, TextEncoding_1_1>],
        ),
    > {
        // If it doesn't start with {, it isn't a struct.
        if self.bytes().first() != Some(&b'{') {
            let error = InvalidInputError::new(self);
            return Err(nom::Err::Error(IonParseError::Invalid(error)));
        }
        // Scan ahead to find the end of this struct.
        let struct_body = self.slice_to_end(1);
        let struct_iter = RawTextStructIterator_1_1::new(struct_body);
        let (span, fields) =
            match TextStructSpanFinder_1_1::new(self.allocator, struct_iter).find_span() {
                Ok((span, fields)) => (span, fields),
                // If the complete container isn't available, return an incomplete.
                Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
                // If invalid syntax was encountered, return a failure to prevent nom from trying
                // other parser kinds.
                Err(e) => {
                    return {
                        let error = InvalidInputError::new(self)
                            .with_label("matching a v1.1 struct")
                            .with_description(format!("{}", e));
                        Err(nom::Err::Failure(IonParseError::Invalid(error)))
                    }
                }
            };

        // For the matched span, we use `self` again to include the opening `{`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        Ok((remaining, (matched, fields)))
    }

    /// Matches an e-expression invoking a macro.
    ///
    /// If the input does not contain the entire e-expression, returns `IonError::Incomplete(_)`.
    pub fn match_e_expression(self) -> IonParseResult<'top, RawTextEExpression_1_1<'top>> {
        let (exp_body, _) = tag("(:")(self)?;
        // TODO: Support macro ID kinds besides unqualified names
        let (exp_body_after_id, (macro_id_bytes, _matched_symbol)) =
            consumed(Self::match_identifier)(exp_body)?;
        // Because the macro_id used identifier syntax, its bytes must be ASCII. We can safely unwrap.
        let macro_name = macro_id_bytes.as_text().unwrap();
        let macro_id = MacroIdRef::LocalName(macro_name);

        // The rest of the e-expression uses s-expression syntax. Scan ahead to find the end of this
        // expression.
        let sexp_iter = RawTextSExpIterator_1_1::new(exp_body_after_id);
        // The sexp iterator holds the body of the expression. When finding the input span it occupies,
        // we tell the iterator how many bytes comprised the head of the expression: two bytes
        // for `(:` plus the length of the macro ID.
        let initial_bytes_skipped = 2 + macro_id_bytes.len();
        let (span, child_expr_cache) = match TextSExpSpanFinder_1_1::new(self.allocator, sexp_iter)
            .find_span(initial_bytes_skipped)
        {
            Ok((span, child_expr_cache)) => (span, child_expr_cache),
            // If the complete container isn't available, return an incomplete.
            Err(IonError::Incomplete(_)) => return Err(nom::Err::Incomplete(Needed::Unknown)),
            // If invalid syntax was encountered, return a failure to prevent nom from trying
            // other parser kinds.
            Err(e) => {
                return {
                    let error = InvalidInputError::new(self)
                        .with_label(format!(
                            "matching an e-expression invoking macro {}",
                            macro_name
                        ))
                        .with_description(format!("{}", e));
                    Err(nom::Err::Failure(IonParseError::Invalid(error)))
                }
            }
        };
        // For the matched span, we use `self` again to include the opening `(:`
        let matched = self.slice(0, span.len());
        let remaining = self.slice_to_end(span.len());
        let macro_invocation = RawTextEExpression_1_1::new(
            macro_id,
            EncodedTextMacroInvocation::new(macro_id_bytes.len() as u16),
            matched,
            child_expr_cache,
        );

        Ok((remaining, macro_invocation))
    }

    /// Matches and returns a boolean value.
    pub fn match_bool(self) -> IonParseResult<'top, bool> {
        terminated(
            alt((value(true, tag("true")), value(false, tag("false")))),
            Self::peek_stop_character,
        )(self)
    }

    /// Matches and returns any type of null. (`null`, `null.null`, `null.int`, etc)
    pub fn match_null(self) -> IonParseResult<'top, IonType> {
        delimited(
            complete_tag("null"),
            opt(preceded(complete_char('.'), Self::match_ion_type)),
            Self::peek_stop_character,
        )
        .map(|explicit_ion_type| explicit_ion_type.unwrap_or(IonType::Null))
        .parse(self)
    }

    /// Matches and returns an Ion type.
    fn match_ion_type(self) -> IonParseResult<'top, IonType> {
        alt((
            value(IonType::Null, complete_tag("null")),
            value(IonType::Bool, complete_tag("bool")),
            value(IonType::Int, complete_tag("int")),
            value(IonType::Float, complete_tag("float")),
            value(IonType::Decimal, complete_tag("decimal")),
            value(IonType::Timestamp, complete_tag("timestamp")),
            value(IonType::Symbol, complete_tag("symbol")),
            value(IonType::String, complete_tag("string")),
            value(IonType::Clob, complete_tag("clob")),
            value(IonType::Blob, complete_tag("blob")),
            value(IonType::List, complete_tag("list")),
            value(IonType::SExp, complete_tag("sexp")),
            value(IonType::Struct, complete_tag("struct")),
        ))(self)
    }

    /// Matches any one of Ion's stop characters.
    fn match_stop_character(self) -> IonMatchResult<'top> {
        alt((eof, recognize(one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}"))))(self)
    }

    /// Matches--but does not consume--any one of Ion's stop characters.
    fn peek_stop_character(self) -> IonMatchResult<'top> {
        peek(Self::match_stop_character).parse(self)
    }

    /// Matches the three parts of an int--its base, its sign, and its digits--without actually
    /// constructing an Int from them.
    pub fn match_int(self) -> IonParseResult<'top, MatchedInt> {
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
    fn match_base_2_int(self) -> IonParseResult<'top, MatchedInt> {
        separated_pair(
            opt(char('-')),
            alt((complete_tag("0b"), complete_tag("0B"))),
            Self::match_base_2_int_digits,
        )
        .map(|(maybe_sign, digits)| {
            MatchedInt::new(2, maybe_sign.is_some(), digits.offset() - self.offset())
        })
        .parse(self)
    }

    /// Matches the digits of a base-2 integer.
    fn match_base_2_int_digits(self) -> IonMatchResult<'top> {
        recognize(terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(complete_is_a("01"), complete_tag("_"))),
            // One or more digits
            complete_is_a("01"),
        ))(self)
    }

    /// Matches a base-10 notation integer (e.g. `0`, `255`, or `-1_024`) and returns the partially
    /// parsed value as a [`MatchedInt`].
    fn match_base_10_int(self) -> IonParseResult<'top, MatchedInt> {
        pair(opt(char('-')), Self::match_base_10_int_digits)
            .map(|(maybe_sign, digits)| {
                MatchedInt::new(10, maybe_sign.is_some(), digits.offset() - self.offset())
            })
            .parse(self)
    }

    /// Matches the digits of a base-10 integer. (i.e. An integer without a sign.)
    fn match_base_10_int_digits(self) -> IonMatchResult<'top> {
        Self::match_base_10_digits_before_dot(self)
    }

    /// Matches either:
    /// * a zero
    /// * a non-zero followed by some number of digits with optional underscores
    fn match_base_10_digits_before_dot(self) -> IonMatchResult<'top> {
        alt((
            // The number is either a zero...
            complete_tag("0"),
            // Or it's a non-zero followed by some number of '_'-separated digits
            recognize(pair(
                Self::match_base_10_leading_digit,
                Self::match_base_10_trailing_digits,
            )),
        ))(self)
    }

    /// Matches the first digit of a multi-digit base-10 integer. (i.e. Any digit but zero.)
    fn match_base_10_leading_digit(self) -> IonMatchResult<'top> {
        recognize(one_of("123456789"))(self)
    }

    /// Matches any number of digits with underscores optionally appearing in the middle.
    /// This parser accepts leading zeros, which is why it cannot be used for the beginning
    /// of a number.
    fn match_base_10_trailing_digits(self) -> IonMatchResult<'top> {
        recognize(many0_count(pair(opt(complete_char('_')), complete_digit1)))(self)
    }

    /// Matches a base-10 notation integer (e.g. `0x0`, `0X20`, or `-0xCAFE`) and returns the
    /// partially parsed value as a [`MatchedInt`].
    fn match_base_16_int(self) -> IonParseResult<'top, MatchedInt> {
        separated_pair(
            opt(char('-')),
            alt((complete_tag("0x"), complete_tag("0X"))),
            Self::match_base_16_int_trailing_digits,
        )
        .map(|(maybe_sign, digits)| {
            MatchedInt::new(16, maybe_sign.is_some(), digits.offset() - self.offset())
        })
        .parse(self)
    }

    /// Matches the digits that follow the '0x' or '0X' in a base-16 integer
    fn match_base_16_int_trailing_digits(self) -> IonMatchResult<'top> {
        recognize(terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(Self::take_base_16_digits1, complete_tag("_"))),
            // One or more digits
            Self::take_base_16_digits1,
        ))(self)
    }

    /// Recognizes 1 or more consecutive base-16 digits.
    // This function's "1" suffix is a style borrowed from `nom`.
    fn take_base_16_digits1(self) -> IonMatchResult<'top> {
        complete_take_while1(|b: u8| b.is_ascii_hexdigit())(self)
    }

    /// Matches `n` consecutive hex digits.
    pub(crate) fn match_n_hex_digits(
        count: usize,
    ) -> impl Parser<TextBufferView<'top>, TextBufferView<'top>, IonParseError<'top>> {
        // `fold_many_m_n` allows us to repeat the same parser between 'm' and 'n' times,
        // specifying an operation to perform on each match. In our case, we just need the parser
        // to run 'n' times exactly so `recognize` can return the accepted slice; our operation
        // is a no-op.
        recognize(fold_many_m_n(
            count,
            count,
            satisfy(|c| c.is_ascii_hexdigit()),
            || 0,
            // no-op
            |accum, _item| accum,
        ))
    }

    /// Matches an Ion float of any syntax
    fn match_float(self) -> IonParseResult<'top, MatchedFloat> {
        terminated(
            alt((
                Self::match_float_special_value,
                Self::match_float_numeric_value,
            )),
            Self::peek_stop_character,
        )(self)
    }

    /// Matches special IEEE-754 values, including +/- infinity and NaN.
    fn match_float_special_value(self) -> IonParseResult<'top, MatchedFloat> {
        alt((
            value(MatchedFloat::NotANumber, complete_tag("nan")),
            value(MatchedFloat::PositiveInfinity, complete_tag("+inf")),
            value(MatchedFloat::NegativeInfinity, complete_tag("-inf")),
        ))(self)
    }

    /// Matches numeric IEEE-754 floating point values.
    fn match_float_numeric_value(self) -> IonParseResult<'top, MatchedFloat> {
        recognize(pair(
            Self::match_number_with_optional_dot_and_digits,
            Self::match_float_exponent_marker_and_digits,
        ))
        .map(|_matched| MatchedFloat::Numeric)
        .parse(self)
    }

    /// Matches a number that may or may not have a decimal place and trailing fractional digits.
    /// If a decimal place is present, there must also be trailing digits.
    /// For example:
    ///   1000
    ///   1000.559
    ///   -25.2
    fn match_number_with_optional_dot_and_digits(self) -> IonMatchResult<'top> {
        recognize(tuple((
            opt(complete_tag("-")),
            Self::match_base_10_digits_before_dot,
            opt(Self::match_dot_followed_by_base_10_digits),
        )))(self)
    }

    /// In a float or decimal, matches the digits that are permitted before the decimal point.
    /// This includes either a single zero, or a non-zero followed by any sequence of digits.
    fn match_digits_before_dot(self) -> IonMatchResult<'top> {
        alt((
            complete_tag("0"),
            recognize(pair(Self::match_leading_digit, Self::match_trailing_digits)),
        ))(self)
    }

    /// Matches a single non-zero base 10 digit.
    fn match_leading_digit(self) -> IonMatchResult<'top> {
        recognize(one_of("123456789"))(self)
    }

    /// Matches any number of base 10 digits, allowing underscores at any position except the end.
    fn match_trailing_digits(self) -> IonMatchResult<'top> {
        recognize(many0_count(preceded(
            opt(complete_char('_')),
            complete_digit1,
        )))(self)
    }

    /// Recognizes a decimal point followed by any number of base-10 digits.
    fn match_dot_followed_by_base_10_digits(self) -> IonMatchResult<'top> {
        recognize(preceded(
            complete_tag("."),
            opt(Self::match_digits_after_dot),
        ))(self)
    }

    /// Like `match_digits_before_dot`, but allows leading zeros.
    fn match_digits_after_dot(self) -> IonMatchResult<'top> {
        recognize(terminated(
            // Zero or more digits-followed-by-underscores
            many0_count(pair(complete_digit1, complete_char('_'))),
            // One or more digits
            complete_digit1,
        ))(self)
    }

    /// Matches an `e` or `E` followed by an optional sign (`+` or `-`) followed by one or more
    /// base 10 digits.
    fn match_float_exponent_marker_and_digits(self) -> IonMatchResult<'top> {
        preceded(
            complete_one_of("eE"),
            recognize(Self::match_exponent_sign_and_digits),
        )(self)
    }

    /// Matches the exponent portion of a decimal (everything after the 'd') or float
    /// (everything after the 'e'). This includes:
    /// * an optional '+' OR '-'
    /// * any number of decimal digits, which may:
    ///    * have underscores in between them: `1_000_000`
    ///    * have one or more leading zeros: `0005`
    ///
    /// Returns a boolean indicating whether the sign was negative (vs absent or positive)
    /// and the buffer slice containing the digits.
    fn match_exponent_sign_and_digits(self) -> IonParseResult<'top, (bool, Self)> {
        pair(
            // Optional leading sign; if there's no sign, it's not negative.
            opt(Self::match_any_sign).map(|s| s == Some('-')),
            Self::match_digits_after_dot,
        )(self)
    }

    /// Matches `-` OR `+`.
    ///
    /// This is used for matching exponent signs; most places in Ion do not allow `+`.
    pub fn match_any_sign(self) -> IonParseResult<'top, char> {
        complete_one_of("-+")(self)
    }

    pub fn match_decimal_exponent(self) -> IonParseResult<'top, (bool, TextBufferView<'top>)> {
        preceded(complete_one_of("dD"), Self::match_exponent_sign_and_digits)(self)
    }

    /// Match an optional sign (if present), digits before the decimal point, then digits after the
    /// decimal point (if present).
    pub fn match_decimal(self) -> IonParseResult<'top, MatchedDecimal> {
        terminated(
            tuple((
                opt(complete_tag("-")),
                Self::match_digits_before_dot,
                alt((
                    // Either a decimal point and digits and optional d/D and exponent
                    tuple((
                        complete_tag("."),
                        opt(Self::match_digits_after_dot),
                        opt(Self::match_decimal_exponent),
                    ))
                    .map(|(dot, maybe_digits_after_dot, maybe_exponent)| {
                        let digits_after_dot = match maybe_digits_after_dot {
                            Some(digits) => digits,
                            None => dot.slice(1, 0),
                        };
                        let (exp_is_negative, exp_digits) = match maybe_exponent {
                            Some(exponent) => exponent,
                            None => (false, digits_after_dot.slice(digits_after_dot.len(), 0)),
                        };
                        (digits_after_dot, exp_is_negative, exp_digits)
                    }),
                    // or just a d/D and exponent
                    consumed(Self::match_decimal_exponent).map(
                        |(matched, (exp_is_negative, exp_digits))| {
                            // Make an empty slice to represent the (absent) digits after dot
                            let digits_after_dot = matched.slice(0, 0);
                            (digits_after_dot, exp_is_negative, exp_digits)
                        },
                    ),
                )),
            )),
            Self::peek_stop_character,
        )
        .map(
            |(maybe_sign, leading_digits, (digits_after_dot, exponent_is_negative, exp_digits))| {
                let is_negative = maybe_sign.is_some();
                let digits_offset = (leading_digits.offset() - self.offset()) as u16;
                let digits_length = match digits_after_dot.len() {
                    0 => leading_digits.len() as u16,
                    trailing_digits_length => {
                        // The `+1` accounts for the decimal point
                        (leading_digits.len() + 1 + trailing_digits_length) as u16
                    }
                };
                let num_trailing_digits = digits_after_dot
                    .bytes()
                    .iter()
                    .filter(|b| b.is_ascii_digit())
                    .count() as u16;
                let exponent_digits_offset = (exp_digits.offset() - self.offset()) as u16;
                let exponent_digits_length = exp_digits.len() as u16;
                MatchedDecimal::new(
                    is_negative,
                    digits_offset,
                    digits_length,
                    num_trailing_digits,
                    exponent_is_negative,
                    exponent_digits_offset,
                    exponent_digits_length,
                )
            },
        )
        .parse(self)
    }

    /// Matches short- or long-form string.
    pub fn match_string(self) -> IonParseResult<'top, MatchedString> {
        alt((Self::match_short_string, Self::match_long_string))(self)
    }

    /// Matches a short string. For example: `"foo"`
    pub(crate) fn match_short_string(self) -> IonParseResult<'top, MatchedString> {
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
    pub(crate) fn match_short_string_body(self) -> IonParseResult<'top, (Self, bool)> {
        Self::match_text_until_unescaped(self, b'\"', false)
    }

    /// Matches a long string comprised of any number of `'''`-enclosed segments interleaved
    /// with optional comments and whitespace.
    pub(crate) fn match_long_string(self) -> IonParseResult<'top, MatchedString> {
        fold_many1(
            // Parser to keep applying repeatedly
            whitespace_and_then(Self::match_long_string_segment),
            // Initial accumulator value: segment count and whether the string contains escaped characters
            || (0usize, false),
            // Function to merge the current match's information with the accumulator
            |(segment_count, string_contains_escapes),
             (_matched_segment, segment_contains_escapes)| {
                (
                    segment_count + 1,
                    string_contains_escapes || segment_contains_escapes,
                )
            },
        )
        .map(
            |(segment_count, contains_escapes)| match (segment_count, contains_escapes) {
                (1, false) => MatchedString::LongSingleSegmentWithoutEscapes,
                (1, true) => MatchedString::LongSingleSegmentWithEscapes,
                _ => MatchedString::Long,
            },
        )
        .parse(self)
    }

    /// Matches a single long string segment enclosed by `'''` delimiters.
    pub fn match_long_string_segment(self) -> IonParseResult<'top, (Self, bool)> {
        delimited(
            complete_tag("'''"),
            Self::match_long_string_segment_body,
            complete_tag("'''"),
        )(self)
    }

    /// Matches all input up to (but not including) the first unescaped instance of `'''`.
    fn match_long_string_segment_body(self) -> IonParseResult<'top, (Self, bool)> {
        Self::match_text_until_unescaped_str(self, "'''")
    }

    /// Matches an operator symbol, which can only legally appear within an s-expression
    fn match_operator<E: TextEncoding<'top>>(
        self,
    ) -> IonParseResult<'top, LazyRawTextValue<'top, E>> {
        is_a("!#%&*+-./;<=>?@^`|~")
            .map(|text: TextBufferView| LazyRawTextValue {
                input: text,
                encoded_value: EncodedTextValue::new(MatchedValue::Symbol(MatchedSymbol::Operator)),
            })
            .parse(self)
    }

    /// Matches a symbol ID (`$28`), an identifier (`foo`), or a quoted symbol (`'foo'`).
    fn match_symbol(self) -> IonParseResult<'top, MatchedSymbol> {
        alt((
            Self::match_symbol_id,
            Self::match_identifier,
            Self::match_quoted_symbol,
        ))(self)
    }

    /// Matches a symbol ID (`$28`).
    fn match_symbol_id(self) -> IonParseResult<'top, MatchedSymbol> {
        recognize(terminated(
            // Discard a `$` and parse an integer representing the symbol ID.
            // Note that symbol ID integers:
            //   * CANNOT have underscores in them. For example: `$1_0` is considered an identifier.
            //   * CAN have leading zeros. There's precedent for this in ion-java.
            preceded(tag("$"), complete_digit1),
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
    fn match_identifier(self) -> IonParseResult<'top, MatchedSymbol> {
        let (remaining, identifier_text) = recognize(terminated(
            pair(
                Self::identifier_initial_character,
                Self::identifier_trailing_characters,
            ),
            Self::identifier_terminator,
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

    fn identifier_terminator(self) -> IonMatchResult<'top> {
        alt((
            eof,
            recognize(peek(not(Self::identifier_trailing_character))),
        ))(self)
    }

    /// Matches any character that can appear at the start of an identifier.
    fn identifier_initial_character(self) -> IonParseResult<'top, Self> {
        recognize(alt((one_of("$_"), satisfy(|c| c.is_ascii_alphabetic()))))(self)
    }

    /// Matches any character that is legal in an identifier, though not necessarily at the beginning.
    fn identifier_trailing_character(self) -> IonParseResult<'top, Self> {
        recognize(alt((one_of("$_"), satisfy(|c| c.is_ascii_alphanumeric()))))(self)
    }

    /// Matches characters that are legal in an identifier, though not necessarily at the beginning.
    fn identifier_trailing_characters(self) -> IonParseResult<'top, Self> {
        complete_take_while(|c: u8| c.is_ascii_alphanumeric() || b"$_".contains(&c))(self)
    }

    /// Matches a quoted symbol (`'foo'`).
    fn match_quoted_symbol(self) -> IonParseResult<'top, MatchedSymbol> {
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
    fn match_quoted_symbol_body(self) -> IonParseResult<'top, (Self, bool)> {
        Self::match_text_until_unescaped(self, b'\'', false)
    }

    /// A helper method for matching bytes until the specified delimiter. Ignores any byte
    /// (including the delimiter) that is prefaced by the escape character `\`.
    fn match_text_until_unescaped(
        self,
        delimiter: u8,
        allow_unescaped_newlines: bool,
    ) -> IonParseResult<'top, (Self, bool)> {
        let mut contains_escaped_chars = false;
        // This de-sugared syntax allows us to modify `iter` mid-loop.
        let mut iter = self.bytes().iter().copied().enumerate();
        while let Some((index, byte)) = iter.next() {
            if byte == b'\\' {
                // It's an escape sequence. For the purposes of finding the end delimiter, we can
                // skip the next 1 byte unless this is \r\n, in which case we need to skip two.
                // Other escape sequences that are followed by more than one byte (e.g. \u and \U)
                // are always followed by ASCII letters, which aren't used as delimiters.
                contains_escaped_chars = true;
                // Peek at the next two bytes to see if this is a \r\n
                let next_two_bytes = self.bytes().get(index + 1..index + 3);
                let bytes_to_skip = if next_two_bytes == Some(&[b'\r', b'\n']) {
                    2
                } else {
                    1
                };
                // Eagerly skip the next iterator values
                let _ = iter.nth(bytes_to_skip - 1);
                continue;
            }
            if byte == delimiter {
                let matched = self.slice(0, index);
                let remaining = self.slice_to_end(index);
                return Ok((remaining, (matched, contains_escaped_chars)));
            }
            // If this is a control character, make sure it's a legal one.
            if byte < 0x20 {
                if byte == b'\r' {
                    // Carriage returns are not actual escapes, but do require a substitution
                    // as part of newline normalization when the string is read.
                    contains_escaped_chars = true;
                } else {
                    self.validate_string_control_character(byte, index, allow_unescaped_newlines)?;
                }
            }
        }
        Err(nom::Err::Incomplete(Needed::Unknown))
    }

    #[cold]
    fn validate_string_control_character(
        self,
        byte: u8,
        index: usize,
        allow_unescaped_newlines: bool,
    ) -> IonParseResult<'top, ()> {
        if byte == b'\n' && !allow_unescaped_newlines {
            let error = InvalidInputError::new(self.slice_to_end(index))
                .with_description("unescaped newlines are not allowed in short string literals");
            return Err(nom::Err::Failure(IonParseError::Invalid(error)));
        }
        if !WHITESPACE_CHARACTERS_AS_STR.as_bytes().contains(&byte) {
            let error = InvalidInputError::new(self.slice_to_end(index))
                .with_description("unescaped control characters are not allowed in text literals");
            return Err(nom::Err::Failure(IonParseError::Invalid(error)));
        }
        Ok((self.slice_to_end(1), ()))
    }

    /// A helper method for matching bytes until the specified delimiter. Ignores any byte
    /// that is prefaced by the escape character `\`.
    ///
    /// The specified delimiter cannot be empty.
    fn match_text_until_unescaped_str(self, delimiter: &str) -> IonParseResult<'top, (Self, bool)> {
        // The first byte in the delimiter
        let delimiter_head = delimiter.as_bytes()[0];
        // Whether we've encountered any escapes while looking for the delimiter
        let mut contained_escapes = false;
        // The input left to search
        let mut remaining = self;
        loop {
            // Look for the first unescaped instance of the delimiter's head.
            // If the input doesn't contain one, this will return an `Incomplete`.
            // `match_text_until_escaped` does NOT include the delimiter byte in the match,
            // so `remaining_after_match` starts at the delimiter byte.
            let (remaining_after_match, (_, segment_contained_escapes)) =
                remaining.match_text_until_unescaped(delimiter_head, true)?;
            contained_escapes |= segment_contained_escapes;
            remaining = remaining_after_match;

            // If the remaining input starts with the complete delimiter, it's a match.
            if remaining.bytes().starts_with(delimiter.as_bytes()) {
                let relative_match_end = remaining.offset() - self.offset();
                let matched_input = self.slice(0, relative_match_end);
                let remaining_input = self.slice_to_end(relative_match_end);
                return Ok((remaining_input, (matched_input, contained_escapes)));
            } else {
                // Otherwise, advance by one and try again.
                remaining = remaining.slice_to_end(1);
            }
        }
    }

    /// Matches a single base-10 digit, 0-9.
    fn match_any_digit(self) -> IonParseResult<'top, char> {
        satisfy(|c| c.is_ascii_digit())(self)
    }

    /// Matches a timestamp of any precision.
    pub fn match_timestamp(self) -> IonParseResult<'top, MatchedTimestamp> {
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
    fn match_timestamp_y(self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            Self::match_timestamp_year,
            pair(complete_tag("T"), Self::peek_stop_character),
        )
        .map(|_year| MatchedTimestamp::new(TimestampPrecision::Year))
        .parse(self)
    }

    /// Matches a timestamp with month precision.
    fn match_timestamp_ym(self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            pair(Self::match_timestamp_year, Self::match_timestamp_month),
            pair(complete_tag("T"), Self::peek_stop_character),
        )
        .map(|(_year, _month)| MatchedTimestamp::new(TimestampPrecision::Month))
        .parse(self)
    }

    /// Matches a timestamp with day precision.
    fn match_timestamp_ymd(self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            tuple((
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
            )),
            pair(opt(complete_tag("T")), Self::peek_stop_character),
        )
        .map(|_| MatchedTimestamp::new(TimestampPrecision::Day))
        .parse(self)
    }

    /// Matches a timestamp with hour-and-minute precision.
    fn match_timestamp_ymd_hm(self) -> IonParseResult<'top, MatchedTimestamp> {
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
    fn match_timestamp_ymd_hms(self) -> IonParseResult<'top, MatchedTimestamp> {
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
    fn match_timestamp_ymd_hms_fractional(self) -> IonParseResult<'top, MatchedTimestamp> {
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
    fn match_timestamp_year(self) -> IonMatchResult<'top> {
        recognize(take_while_m_n(4, 4, |c: u8| c.is_ascii_digit()))(self)
    }

    /// Matches the month component of a timestamp, including a leading `-`.
    fn match_timestamp_month(self) -> IonMatchResult<'top> {
        preceded(
            complete_tag("-"),
            recognize(alt((
                pair(complete_char('0'), complete_one_of("123456789")),
                pair(complete_char('1'), complete_one_of("012")),
            ))),
        )(self)
    }

    /// Matches the day component of a timestamp, including a leading `-`.
    fn match_timestamp_day(self) -> IonMatchResult<'top> {
        preceded(
            complete_tag("-"),
            recognize(alt((
                pair(complete_char('0'), complete_one_of("123456789")),
                pair(complete_one_of("12"), Self::match_any_digit),
                pair(complete_char('3'), complete_one_of("01")),
            ))),
        )(self)
    }

    /// Matches a leading `T`, a two-digit hour component of a timestamp, a delimiting ':', and a
    /// two-digit minute component.
    fn match_timestamp_hour_and_minute(
        self,
    ) -> IonParseResult<'top, (TextBufferView<'top>, TextBufferView<'top>)> {
        preceded(
            tag("T"),
            separated_pair(
                // Hour
                recognize(alt((
                    pair(complete_one_of("01"), Self::match_any_digit),
                    pair(complete_char('2'), complete_one_of("0123")),
                ))),
                // Delimiter
                complete_tag(":"),
                // Minutes
                recognize(pair(complete_one_of("012345"), Self::match_any_digit)),
            ),
        )(self)
    }

    /// Matches a leading `:`, and any two-digit second component from `00` to `59` inclusive.
    fn match_timestamp_seconds(self) -> IonMatchResult<'top> {
        preceded(
            complete_tag(":"),
            recognize(pair(complete_one_of("012345"), Self::match_any_digit)),
        )(self)
    }

    /// Matches the fractional seconds component of a timestamp, including a leading `.`.
    fn match_timestamp_fractional_seconds(self) -> IonMatchResult<'top> {
        preceded(complete_tag("."), digit1)(self)
    }

    /// Matches a timestamp offset of any format.
    fn match_timestamp_offset(self) -> IonParseResult<'top, MatchedTimestampOffset> {
        alt((
            value(MatchedTimestampOffset::Zulu, complete_tag("Z")),
            value(MatchedTimestampOffset::Zulu, complete_tag("+00:00")),
            value(MatchedTimestampOffset::Unknown, complete_tag("-00:00")),
            map(
                pair(
                    complete_one_of("-+"),
                    Self::match_timestamp_offset_hours_and_minutes,
                ),
                |(sign, (_hours, _minutes))| {
                    if sign == '-' {
                        MatchedTimestampOffset::NegativeHoursAndMinutes
                    } else {
                        MatchedTimestampOffset::PositiveHoursAndMinutes
                    }
                },
            ),
        ))(self)
    }

    /// Matches a timestamp offset encoded as a two-digit hour, a delimiting `:`, and a two-digit
    /// minute.
    fn match_timestamp_offset_hours_and_minutes(self) -> IonParseResult<'top, (Self, Self)> {
        separated_pair(
            // Hour
            recognize(alt((
                pair(complete_one_of("01"), Self::match_any_digit),
                pair(complete_char('2'), complete_one_of("0123")),
            ))),
            // Delimiter
            complete_tag(":"),
            // Minutes
            recognize(pair(complete_one_of("012345"), Self::match_any_digit)),
        )(self)
    }

    /// Matches a complete blob, including the opening `{{` and closing `}}`.
    pub fn match_blob(self) -> IonParseResult<'top, MatchedBlob> {
        delimited(
            tag("{{"),
            // Only whitespace (not comments) can appear within the blob
            recognize(Self::match_base64_content),
            preceded(Self::match_optional_whitespace, tag("}}")),
        )
        .map(|base64_data| {
            MatchedBlob::new(base64_data.offset() - self.offset(), base64_data.len())
        })
        .parse(self)
    }

    /// Matches a clob of either short- or long-form syntax.
    pub fn match_clob(self) -> IonParseResult<'top, MatchedClob> {
        delimited(
            tag("{{"),
            preceded(
                Self::match_optional_whitespace,
                alt((
                    value(MatchedClob::Short, Self::match_short_clob_body),
                    value(MatchedClob::Long, Self::match_long_clob_body),
                )),
            ),
            preceded(Self::match_optional_whitespace, tag("}}")),
        )(self)
    }

    /// Matches the body (inside the `{{` and `}}`) of a short-form clob.
    fn match_short_clob_body(self) -> IonMatchResult<'top> {
        let (remaining, (body, _matched_string)) = consumed(Self::match_short_string)(self)?;
        body.validate_clob_text()?;
        Ok((remaining, body))
    }

    /// Matches the body (inside the `{{` and `}}`) of a long-form clob.
    fn match_long_clob_body(self) -> IonMatchResult<'top> {
        recognize(many1_count(preceded(
            Self::match_optional_whitespace,
            Self::match_long_clob_body_segment,
        )))(self)
    }

    /// Matches a single segment of a long-form clob's content.
    fn match_long_clob_body_segment(self) -> IonMatchResult<'top> {
        let (remaining, (body, _matched_string)) = consumed(Self::match_long_string_segment)(self)?;
        body.validate_clob_text()?;
        Ok((remaining, body))
    }

    /// Returns an error if the buffer contains any byte that is not legal inside a clob.
    fn validate_clob_text(self) -> IonMatchResult<'top> {
        for byte in self.bytes().iter().copied() {
            if !Self::byte_is_legal_clob_ascii(byte) {
                let message = format!("found an illegal byte '{:0x}' in clob", byte);
                let error = InvalidInputError::new(self).with_description(message);
                return Err(nom::Err::Failure(IonParseError::Invalid(error)));
            }
        }
        // Return success without consuming
        Ok((self, self.slice(0, 0)))
    }

    /// Returns `false` if the specified byte cannot appear unescaped in a clob.
    fn byte_is_legal_clob_ascii(b: u8) -> bool {
        // Depending on where you look in the spec and/or `ion-tests`, you'll find conflicting
        // information about which ASCII characters can appear unescaped in a clob. Some say
        // "characters >= 0x20", but that excludes lots of whitespace characters that are < 0x20.
        // Some say "displayable ASCII", but DEL (0x7F) is shown to be legal in one of the ion-tests.
        // The definition used here has largely been inferred from the contents of `ion-tests`.
        b.is_ascii()
            && (u32::from(b) >= 0x20 || WHITESPACE_CHARACTERS_AS_STR.as_bytes().contains(&b))
    }
    /// Matches the base64 content within a blob. Ion allows the base64 content to be broken up with
    /// whitespace, so the matched input region may need to be stripped of whitespace before
    /// the data can be decoded.
    fn match_base64_content(self) -> IonMatchResult<'top> {
        recognize(terminated(
            many0_count(preceded(
                Self::match_optional_whitespace,
                alt((alphanumeric1, is_a("+/"))),
            )),
            opt(preceded(
                Self::match_optional_whitespace,
                alt((tag("=="), tag("="))),
            )),
        ))(self)
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
        let buffer_before = TextBufferView::new_with_offset(self.allocator, before, self.offset());
        let buffer_after =
            TextBufferView::new_with_offset(self.allocator, after, self.offset() + count);
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
    use rstest::rstest;

    use super::*;

    /// Stores an input string that can be tested against a given parser.
    struct MatchTest {
        input: String,
        allocator: BumpAllocator,
    }

    impl MatchTest {
        /// Takes an `input` string and appends a trailing value to it, guaranteeing that the
        /// contents of the input are considered a complete token.
        fn new(input: &str) -> Self {
            MatchTest {
                input: input.to_string(),
                allocator: BumpAllocator::new(),
            }
        }

        fn try_match<'data, P, O>(&'data self, parser: P) -> IonParseResult<'data, usize>
        where
            P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
        {
            let buffer = TextBufferView::new(&self.allocator, self.input.as_bytes());
            match_length(parser).parse(buffer)
        }

        fn expect_match<'data, P, O>(&'data self, parser: P)
        where
            P: Parser<TextBufferView<'data>, O, IonParseError<'data>>,
        {
            let result = self.try_match(parser);
            let (_remaining, match_length) = result.unwrap_or_else(|e| {
                panic!("Unexpected parse fail for input '{}'\n{e}", self.input)
            });
            // Inputs have a trailing newline and `0` that should _not_ be part of the match
            assert_eq!(
                match_length,
                self.input.len(),
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
                    self.input.len(),
                    "parser unexpectedly matched the complete input: {:?}\nResult: {:?}",
                    self.input,
                    result
                );
            }
        }
    }

    #[test]
    fn test_match_stop_char() {
        MatchTest::new(" ").expect_match(match_length(TextBufferView::match_stop_character));
        MatchTest::new("").expect_match(match_length(TextBufferView::match_stop_character));
    }

    #[test]
    fn test_match_ivm() {
        fn match_ivm(input: &str) {
            MatchTest::new(input)
                .expect_match(match_length(TextBufferView::match_ivm::<TextEncoding_1_0>));
        }
        fn mismatch_ivm(input: &str) {
            MatchTest::new(input)
                .expect_mismatch(match_length(TextBufferView::match_ivm::<TextEncoding_1_1>));
        }

        match_ivm("$ion_1_0");
        match_ivm("$ion_1_1");
        match_ivm("$ion_1_2");
        match_ivm("$ion_124_17");

        mismatch_ivm("ion_1_0");
        mismatch_ivm("$ion__1_0");
        mismatch_ivm("$ion_1_0_0");
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
            "305.0e1", "0.279e3", "0.279e-3", "279e0", "279.5e0", "279.5E0",
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
            "2023",                          // No 'T'
            "2023-08",                       // No 'T'
            "20233T",                        // 5-digit year
            "2023-13T",                      // Out of bounds month
            "2023-08-41T",                   // Out of bounds day
            "2023-08+18T",                   // Wrong delimiter
            "2023-08-18T25:00Z",             // Out of bounds hour
            "2023-08-18T14:00",              // No offset
            "2023-08-18T14:62",              // Out of bounds minute
            "2023-08-18T14:35:61",           // Out of bounds second
            "2023-08-18T14:35:52.Z",         // Dot but no fractional
            "2023-08-18T14:35:52.000+24:30", // Out of bounds offset hour
            "2023-08-18T14:35:52.000+00:60", // Out of bounds offset minute
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
            r#" '''hi''' "#,
            r#"
            '''foo'''
            '''bar'''
            '''baz''' 
            "#,
            r#"
            '''hello,''' /*comment*/ ''' world!'''
            "#,
            r#"
            ''''''
            "#, // empty string
            r#"
            '''''' ''''''
            "#, // concatenated empty string
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

        let bad_inputs = &["foo::", "foo:bar", "foo:::bar"];
        for input in bad_inputs {
            mismatch_annotated_value(input);
        }
    }

    #[test]
    fn test_match_decimal() {
        fn match_decimal(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_decimal));
        }
        fn mismatch_decimal(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_decimal));
        }
        let good_inputs = &[
            "5.", "-5.", "5.0", "-5.0", "5d0", "5.d0", "5.0d0", "-5.0d0", "5.0D0", "-5.0D0",
            "5.0d+1", "-5.0d-1",
        ];
        for input in good_inputs {
            match_decimal(input);
        }

        let bad_inputs = &[
            "123._456", "5", "5d", "05d", "-5d", "5.d", "-5.d", "5.D", "-5.D", "5.1d", "-5.1d",
            "5.1D", "-5.1D", "-5.0+0",
        ];
        for input in bad_inputs {
            mismatch_decimal(input);
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
            "(a+=b)",
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
    #[test]
    fn test_match_sexp_1_1() {
        fn match_sexp(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_sexp_1_1));
        }
        fn mismatch_sexp(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_sexp_1_1));
        }
        let good_inputs = &[
            "()",
            "(1)",
            "(1 2)",
            "(a)",
            "(a b)",
            "(a++)",
            "(++a)",
            "(a+=b)",
            "(())",
            "((()))",
            "(1 (2 (3 4) 5) 6)",
            "(1 (:foo 2 3))",
        ];
        for input in good_inputs {
            match_sexp(input);
        }

        let bad_inputs = &["foo", "1", "(", "(1 2 (3 4 5)"];
        for input in bad_inputs {
            mismatch_sexp(input);
        }
    }

    #[test]
    fn test_match_list_1_1() {
        fn match_list(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_list_1_1));
        }
        fn mismatch_list(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_list_1_1));
        }
        let good_inputs = &["[]", "[1]", "[1, 2]", "[[]]", "[([])]", "[1, (:foo 2 3)]"];
        for input in good_inputs {
            match_list(input);
        }

        let bad_inputs = &["foo", "1", "[", "[1, 2, [3, 4]"];
        for input in bad_inputs {
            mismatch_list(input);
        }
    }

    #[test]
    fn test_match_macro_invocation() {
        fn match_macro_invocation(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_e_expression));
        }
        fn mismatch_macro_invocation(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_e_expression));
        }
        let good_inputs = &[
            "(:foo)",
            "(:foo 1)",
            "(:foo 1 2 3)",
            "(:foo (1 2 3))",
            "(:foo \"foo\")",
            "(:foo foo)",
        ];
        for input in good_inputs {
            println!("test: {input}");
            match_macro_invocation(input);
        }

        let bad_inputs = &[
            "foo",   // No parens
            "(foo)", // No `:` after opening paren
        ];
        for input in bad_inputs {
            mismatch_macro_invocation(input);
        }
    }

    #[rstest]
    #[case::simple_e_exp("(:foo)")]
    #[case::e_exp_in_e_exp("(:foo (:bar 1))")]
    #[case::e_exp_in_list("[a, b, (:foo 1)]")]
    #[case::e_exp_in_sexp("(a (:foo 1) c)")]
    // #[case::e_exp_in_struct_field("{a:(:foo)}")]
    // #[case::e_exp_in_struct_field_with_comma("{a:(:foo),}")]
    #[case::e_exp_in_struct_field_with_comma_and_second_field("{a:(:foo), b:2}")]
    // #[case::e_exp_in_struct_field_with_space_before("{ a:(:foo)}")]
    // #[case::e_exp_in_struct_field_with_space_after("{a:(:foo) }")]
    #[case::e_exp_in_list_in_struct_field("{ a: [(:foo)] }")]
    #[case::e_exp_in_sexp_in_struct_field("{ a: ((:foo)) }")]
    #[case::e_exp_in_sexp_in_list("[a, b, ((:foo 1))]")]
    #[case::e_exp_in_sexp_in_sexp("(a ((:foo 1)) c)")]
    #[case::e_exp_in_list_in_list("[a, b, [(:foo 1)]]")]
    #[case::e_exp_in_list_in_sexp("(a [(:foo 1)] c)")]
    // TODO: Uncomment the above cases when fixing https://github.com/amazon-ion/ion-rust/issues/653
    fn test_match_macro_invocation_in_context(#[case] input: &str) {
        MatchTest::new(input).expect_match(match_length(TextBufferView::match_top_level_item_1_1));
    }

    #[test]
    fn test_match_blob() {
        fn match_blob(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_blob));
        }
        fn mismatch_blob(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_blob));
        }
        // Base64 encodings of utf-8 strings
        let good_inputs = &[
            // <empty blobs>
            "{{}}",
            "{{    }}",
            "{{\n\t}}",
            // hello
            "{{aGVsbG8=}}",
            "{{  aGVsbG8=}}",
            "{{aGVsbG8=  }}",
            "{{\taGVsbG8=\n\n}}",
            "{{aG  Vs  bG   8 =}}",
            r#"{{
                aG Vs  
                bG 8=
            }}"#,
            // hello!
            "{{aGVsbG8h}}",
            "{{  aGVsbG8h}}",
            "{{aGVsbG8h  }}",
            "{{  aGVsbG8h  }}",
            // razzle dazzle root beer
            "{{cmF6emxlIGRhenpsZSByb290IGJlZXI=}}",
            "{{\ncmF6emxlIGRhenpsZSByb290IGJlZXI=\r}}",
        ];
        for input in good_inputs {
            match_blob(input);
        }

        let bad_inputs = &[
            // illegal character $
            "{{$aGVsbG8=}}",
            // comment within braces
            r#"{{
                // Here's the data:
                aGVsbG8=
            }}"#,
            // padding at the beginning
            "{{=aGVsbG8}}",
            // too much padding
            "{{aGVsbG8===}}",
        ];
        for input in bad_inputs {
            mismatch_blob(input);
        }
    }

    #[test]
    fn test_match_clob() {
        fn match_clob(input: &str) {
            MatchTest::new(input).expect_match(match_length(TextBufferView::match_clob));
        }
        fn mismatch_blob(input: &str) {
            MatchTest::new(input).expect_mismatch(match_length(TextBufferView::match_clob));
        }
        // Base64 encodings of utf-8 strings
        let good_inputs = &[
            r#"{{""}}"#,
            r#"{{''''''}}"#,
            r#"{{"foo"}}"#,
            r#"{{  "foo"}}"#,
            r#"{{  "foo"  }}"#,
            r#"{{"foo"  }}"#,
            r#"{{'''foo'''}}"#,
            r#"{{"foobar"}}"#,
            r#"{{'''foo''' '''bar'''}}"#,
            r#"{{
                '''foo'''
                '''bar'''
                '''baz'''
            }}"#,
        ];
        for input in good_inputs {
            match_clob(input);
        }

        let bad_inputs = &[
            r#"{{foo}}"#,                         // No quotes
            r#"{{"foo}}"#,                        // Missing closing quote
            r#"{{"foo"}"#,                        // Missing closing brace
            r#"{{'''foo'''}"#,                    // Missing closing brace
            r#"{{'''foo''' /*hi!*/ '''bar'''}}"#, // Interleaved comments
            r#"{{'''foo''' "bar"}}"#,             // Mixed quote style
            r#"{{"😎🙂🙃"}}"#,                    // Contains unescaped non-ascii characters
        ];
        for input in bad_inputs {
            mismatch_blob(input);
        }
    }

    fn test_match_text_until_unescaped_str() {
        let allocator = BumpAllocator::new();
        let input = TextBufferView::new(&allocator, r" foo bar \''' baz''' quux ".as_bytes());
        let (_remaining, (matched, contains_escapes)) =
            input.match_text_until_unescaped_str(r#"'''"#).unwrap();
        assert_eq!(matched.as_text().unwrap(), " foo bar \\''' baz");
        assert!(contains_escapes);
    }
}
