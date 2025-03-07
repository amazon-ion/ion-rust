use std::fmt::{Debug, Formatter};
use std::ops::Range;
use std::str::FromStr;

use winnow::ascii::alphanumeric1;
use winnow::combinator::{
    alt, delimited, empty, eof, not, opt, peek, preceded, repeat, separated_pair, terminated,
};
use winnow::error::{ErrMode, Needed};
use winnow::stream::{
    Accumulate, CompareResult, ContainsToken, FindSlice, Location, SliceLen, Stream,
    StreamIsPartial,
};
use winnow::token::{one_of, rest, take_till, take_until, take_while};
use winnow::{dispatch, Parser};

use crate::lazy::decoder::{LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::{
    MatchedBlob, MatchedClob, MatchedDecimal, MatchedFieldName, MatchedFieldNameSyntax,
    MatchedFloat, MatchedInt, MatchedString, MatchedSymbol, MatchedTimestamp,
    MatchedTimestampOffset, MatchedValue,
};
use crate::lazy::text::parse_result::IonParseError;
use crate::lazy::text::parse_result::{IonMatchResult, IonParseResult};
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr, TextEExpArgGroup};
use crate::lazy::text::raw::v1_1::reader::{MacroIdRef, SystemMacroAddress, TextEExpression_1_1};
use crate::lazy::text::value::{
    LazyRawTextValue, LazyRawTextValue_1_0, LazyRawTextValue_1_1, LazyRawTextVersionMarker,
};
use crate::result::DecodingError;
use crate::{
    Encoding, HasRange, IonError, IonResult, IonType, RawSymbolRef, Span, TimestampPrecision,
};

use crate::lazy::expanded::macro_table::{MacroDef, ION_1_1_SYSTEM_MACROS};
use crate::lazy::expanded::template::{Parameter, RestSyntaxPolicy};
use crate::lazy::text::as_utf8::AsUtf8;
use crate::lazy::text::raw::sequence::RawTextSExpIterator;
use crate::lazy::text::token_kind::{ValueTokenKind, TEXT_ION_TOKEN_KINDS};
use bumpalo::collections::Vec as BumpVec;
use winnow::ascii::{digit0, digit1};

/// Generates parser functions that map from an Ion type representation (`Decimal`, `Int`, etc)
/// to an `EncodedTextValue`.
macro_rules! scalar_value_matchers {
    ($($parser:expr =>  $variant:ident => $new_parser:ident),*$(,)?) => {
        $(fn $new_parser<E: TextEncoding>(&mut self) -> IonParseResult<'top, EncodedTextValue<'top, E>> {
            $parser.map(|matched| EncodedTextValue::new(MatchedValue::$variant(matched))).parse_next(self)
        })*
    };
}

impl Debug for TextBuffer<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        const CHARS_TO_SHOW: usize = 32;
        write!(f, "TextBuffer {{")?;
        // Try to read the next several bytes from the buffer as UTF-8...
        let text_result = std::str::from_utf8(self.bytes());
        // ...if it works, print the first 32 Unicode scalars...
        if let Ok(text) = text_result {
            let mut chars = text.chars();
            let text_head = (&mut chars).take(CHARS_TO_SHOW).collect::<String>();
            let ellipse = if chars.next().is_some() { "..." } else { "" };
            write!(f, "text=\"{text_head}\"{ellipse}",)?;
        } else {
            // ...if it doesn't, print the first 32 bytes in hex.
            write!(f, "Invalid UTF-8, bytes=")?;
            for byte in self.bytes().iter().take(CHARS_TO_SHOW) {
                write!(f, "{:x?} ", *byte)?;
            }
            if self.bytes().len() > CHARS_TO_SHOW {
                write!(f, "...{} more bytes", self.bytes().len() - CHARS_TO_SHOW)?;
            }
        }
        let range = self.range();
        write!(f, ", range={}..{}}}", range.start, range.end)
    }
}

/// The Ion specification's enumeration of whitespace characters.
///
/// ' ',    Space
/// '\t',   Tab
/// '\r',   Carriage return
/// '\n',   Newline
/// '\x09', Horizontal tab
/// '\x0B', Vertical tab
/// '\x0C', Form feed
pub(crate) const WHITESPACE_BYTES: &[u8] = b" \t\r\n\x09\x0B\x0C";

/// A slice of unsigned bytes that can be cheaply copied and which defines methods for parsing
/// the various encoding elements of a text Ion stream.
///
/// Parsing methods have names that begin with `match_` and each return a `(match, remaining_input)`
/// pair. The `match` may be either the slice of the input that was matched (represented as another
/// `TextBuffer`) or a `MatchedValue` that retains information discovered during parsing that
/// will be useful if the match is later fully materialized into a value.
#[derive(Clone, Copy)]
pub struct TextBuffer<'top> {
    // `data` is a slice of remaining data in the larger input stream.
    input_span: Span<'top>,
    #[cfg(feature = "source-location")]
    // `row` is the row position of the input data in this buffer.
    row: usize,
    #[cfg(feature = "source-location")]
    // `prev_newline_offset` is the previously encountered newline byte's offset value.
    // this is useful in calculating the column position of the input data in this buffer.
    prev_newline_offset: usize,
    pub(crate) context: EncodingContextRef<'top>,
    is_final_data: bool,
}

impl PartialEq for TextBuffer<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.input_span == other.input_span
    }
}

impl<'top> TextBuffer<'top> {
    /// Constructs a new `TextBuffer` that wraps `input_span`.
    pub fn from_span(
        context: EncodingContextRef<'top>,
        input_span: Span<'top>,
        is_final_data: bool,
    ) -> TextBuffer<'top> {
        TextBuffer {
            context,
            input_span,
            #[cfg(feature = "source-location")]
            row: 1,
            #[cfg(feature = "source-location")]
            prev_newline_offset: 0,
            is_final_data,
        }
    }

    // This is for largely for testing.
    pub fn new(context: EncodingContextRef<'top>, bytes: &'top [u8]) -> TextBuffer<'top> {
        Self::with_offset(context, 0, bytes, true)
    }

    // This is for largely for testing.
    pub fn with_offset(
        context: EncodingContextRef<'top>,
        offset: usize,
        bytes: &'top [u8],
        is_final_data: bool,
    ) -> TextBuffer<'top> {
        TextBuffer {
            context,
            input_span: Span::with_offset(offset, bytes),
            #[cfg(feature = "source-location")]
            row: 1,
            #[cfg(feature = "source-location")]
            prev_newline_offset: 0,
            is_final_data,
        }
    }

    /// Modifies the `TextBuffer` in place, discarding `num_bytes` bytes.
    pub fn consume(&mut self, num_bytes: usize) {
        debug_assert!(
            self.len() >= num_bytes,
            "tried to conusume {num_bytes} bytes, but only {} were available",
            self.len()
        );
        self.input_span = self.input_span.slice_to_end(num_bytes);
    }

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    /// Returns a subslice of the [`TextBuffer`] that starts at `offset` and continues for
    /// `length` bytes. The subslice is considered to be 'final' data (i.e. not a potentially
    /// incomplete buffer).
    ///
    /// Note that `offset` is relative to the beginning of the buffer, not the beginning of the
    /// larger stream of which the buffer is a piece.
    pub fn slice(&self, offset: usize, length: usize) -> TextBuffer<'top> {
        TextBuffer {
            input_span: self.input_span.slice(offset, length),
            is_final_data: true,
            ..*self
        }
    }

    /// Returns a subslice of the [`TextBuffer`] that starts at `offset` and continues
    /// to the end.
    ///
    /// Note that `offset` is relative to the beginning of the buffer, not the beginning of the
    /// larger stream of which the buffer is a piece.
    pub fn slice_to_end(&self, offset: usize) -> TextBuffer<'top> {
        TextBuffer {
            input_span: self.input_span.slice_to_end(offset),
            ..*self
        }
    }

    /// Returns a slice containing all of the buffer's bytes.
    pub fn bytes(&self) -> &'top [u8] {
        self.input_span.bytes()
    }

    pub fn peek_byte(&self) -> IonParseResult<'top, u8> {
        let Some(byte) = self.bytes().first().copied() else {
            return self.incomplete("a value");
        };
        Ok(byte)
    }

    /// Returns the number of bytes between the start of the original input byte array and the
    /// subslice of that byte array that this `TextBuffer` represents.
    pub fn offset(&self) -> usize {
        self.input_span.offset()
    }

    #[cfg(feature = "source-location")]
    /// Returns the row position for this buffer.
    /// _Note: Row positions are calculated based on newline characters `\n` and `\r`. `\r\n` together in this order is considered a single newline._
    pub fn row(&self) -> usize {
        self.row
    }

    #[cfg(feature = "source-location")]
    /// Returns the column position for this buffer.
    /// _Note: Column positions are calculated based on current offset and previous newline byte offset._
    pub fn column(&self) -> usize {
        self.offset() - self.prev_newline_offset + 1
    }

    /// Returns the number of bytes in the buffer.
    pub fn len(&self) -> usize {
        self.input_span.len()
    }

    /// Returns the stream byte offset range that this buffer contains.
    pub fn range(&self) -> Range<usize> {
        self.input_span.range()
    }

    /// Returns `true` if there are no bytes in the buffer. Otherwise, returns `false`.
    pub fn is_empty(&self) -> bool {
        self.input_span.is_empty()
    }

    /// Attempts to view the contents of the buffer as a UTF-8 `&str`.
    pub fn as_text<'a>(&'a self) -> IonResult<&'top str> {
        // On its surface, this method very closely resembles the `AsUtf8` trait's method.
        // However, this one returns a `&'data str` instead of a `&'a str`, which is to say
        // that the string that's returned lives as long as the data itself, not just the duration
        // of the lifetime introduced by this method call.
        std::str::from_utf8(self.bytes()).map_err(move |_| {
            let decoding_error =
                DecodingError::new("encountered invalid UTF-8").with_position(self.offset());
            IonError::Decoding(decoding_error)
        })
    }

    /// Always succeeds and consumes none of the input. Returns an empty slice of the buffer.
    // This method is useful for parsers that need to match an optional construct but don't want
    // to return an Option<_>. For an example, see its use in `match_optional_whitespace`.
    #[inline]
    fn match_nothing(&mut self) -> IonMatchResult<'top> {
        // use winnow's `empty` parser to return an empty slice from the head position
        empty.take().parse_next(self)
    }

    /// Matches one or more whitespace characters.
    pub fn match_whitespace1(&mut self) -> IonMatchResult<'top> {
        let result = take_while(1.., WHITESPACE_BYTES).parse_next(self)?;
        #[cfg(feature = "source-location")]
        self.update_location_metadata(result.bytes());
        Ok(result)
    }

    #[cfg(feature = "source-location")]
    /// Updates the location metadata based on the matched whitespace bytes in the consumed buffer
    fn update_location_metadata(&mut self, data: &'top [u8]) {
        if !data.is_empty() {
            // Calculate `rows` based on occurrence of newline bytes. If we encounter:
            // 1. b'\r' then increment row count by 1.
            // 2.a. If there was no b'\r' encountered before b'\n' then increment row count by 1.
            // 2.b. If there was no b'\r' encountered before b'\n' then don't increment as b'\r\n' should be counted as 1 based on windows line ending pattern.
            // Calculate `prev_newline_offset` based on the index/offset value of the last seen newline byte.
            // Adding 1 to the index because we want to include everything after the newline -
            // if newline is at index 5, we want to start counting from index 6 (5 + 1).
            let (_, rows, prev_newline_offset) = data.iter().enumerate().fold(
                (false, 0, 0),
                |(follows_cr, rows, offset), (i, b)| {
                    match (b, follows_cr) {
                        // When there's a '\r', add a row and update the offset as this newline offset value
                        (b'\r', _) => (true, rows + 1, i + 1),
                        // When there's a '\n' not after '\r', add a row and update the offset as this newline offset value
                        (b'\n', false) => (false, rows + 1, i + 1),
                        // When there's '\n' immediately following '\r', update the offset without adding a row
                        (b'\n', true) => (false, rows, i + 1),
                        _ => (false, rows, offset),
                    }
                },
            );
            // Set the previous newline offset by subtracting non newline match length from current offset,
            // where non newline match length is the non newline bytes found after last newline byte.
            if rows > 0 {
                self.prev_newline_offset = self.offset() - (data.len() - prev_newline_offset);
                self.row += rows;
            }
        }
    }

    /// Matches zero or more whitespace characters.
    pub fn match_whitespace0(&mut self) -> IonMatchResult<'top> {
        let result = take_while(0.., WHITESPACE_BYTES).parse_next(self)?;
        #[cfg(feature = "source-location")]
        self.update_location_metadata(result.bytes());
        Ok(result)
    }

    /// Matches any amount of contiguous comments and whitespace, including none.
    #[inline]
    pub fn match_optional_comments_and_whitespace(&mut self) -> IonMatchResult<'top> {
        pub fn full_match_optional_comments_and_whitespace<'t>(
            input: &mut TextBuffer<'t>,
        ) -> IonMatchResult<'t> {
            zero_or_more(alt((
                TextBuffer::match_whitespace1,
                TextBuffer::match_comment,
            )))
            .parse_next(input)
        }

        if let Some(&byte) = self.bytes().first() {
            if WHITESPACE_BYTES.contains_token(byte) || byte == b'/' {
                return full_match_optional_comments_and_whitespace
                    .context("reading whitespace/comments")
                    .parse_next(self);
            }
        }
        self.match_nothing()
    }

    /// Matches a single
    ///     // Rest-of-the-line
    /// or
    ///     /* multi
    ///        line */
    /// comment
    pub fn match_comment(&mut self) -> IonMatchResult<'top> {
        alt((
            Self::match_rest_of_line_comment,
            Self::match_multiline_comment,
        ))
        .parse_next(self)
    }

    /// Matches a single rest-of-the-line comment.
    fn match_rest_of_line_comment(&mut self) -> IonMatchResult<'top> {
        ("//", take_till(.., b"\r\n")).take().parse_next(self)
    }

    /// Matches a single multiline comment.
    fn match_multiline_comment(&mut self) -> IonMatchResult<'top> {
        let result = (
            // Matches a leading "/*"...
            "/*",
            // ...any number of non-"*/" characters...
            take_until(.., "*/"),
            // ...and then a closing "*/"
            "*/",
        )
            .take()
            .parse_next(self)?;
        #[cfg(feature = "source-location")]
        self.update_location_metadata(result.bytes());
        Ok(result)
    }

    /// Matches an Ion version marker (e.g. `$ion_1_0` or `$ion_1_1`.)
    pub fn match_ivm<E: TextEncoding>(
        &mut self,
    ) -> IonParseResult<'top, LazyRawTextVersionMarker<'top, E>> {
        let ((matched_major, matched_minor), matched_marker) = terminated(
            preceded("$ion_", separated_pair(digit1, "_", digit1)),
            // Look ahead to make sure the IVM isn't followed by a '::'. If it is, then it's not
            // an IVM, it's an annotation.
            peek(whitespace_and_then(not(":"))),
        )
        .with_taken()
        .parse_next(self)?;
        // `major` and `minor` are base 10 digits. Turning them into `&str`s is guaranteed to succeed.
        let major_version = u8::from_str(matched_major.as_text().unwrap()).map_err(|_| {
            matched_major
                .invalid("value did not fit in an unsigned byte")
                .context("reading an IVM major version")
                .cut_err()
        })?;
        let minor_version = u8::from_str(matched_minor.as_text().unwrap()).map_err(|_| {
            matched_major
                .invalid("value did not fit in an unsigned byte")
                .context("reading an IVM minor version")
                .cut_err()
        })?;
        let marker =
            LazyRawTextVersionMarker::<E>::new(matched_marker, major_version, minor_version);

        Ok(marker)
    }

    /// Matches one or more annotations.
    #[inline]
    pub fn match_annotations(&mut self) -> IonMatchResult<'top> {
        #[inline(never)]
        fn full_match_annotations<'t>(input: &mut TextBuffer<'t>) -> IonMatchResult<'t> {
            let matched = one_or_more(TextBuffer::match_annotation).parse_next(input)?;
            if matched.len() > u16::MAX as usize {
                matched
                    .invalid("the maximum supported annotations sequence length is 65KB")
                    .context("reading an annotations sequence")
                    .cut()
            } else {
                Ok(matched)
            }
        }

        if let Some(&byte) = self.bytes().first() {
            if [b'\'', b'$', b'_'].contains(&byte) || byte.is_ascii_alphabetic() {
                return full_match_annotations(self);
            }
        };
        self.match_nothing()
    }

    /// Matches an annotation (symbol token) and a terminating '::'.
    pub fn match_annotation(&mut self) -> IonParseResult<'top, (MatchedSymbol, TextBuffer<'top>)> {
        terminated(
            whitespace_and_then(Self::match_symbol.with_taken()),
            whitespace_and_then(("::", Self::match_optional_comments_and_whitespace)),
        )
        .parse_next(self)
    }

    /// Matches either:
    /// * A macro invocation
    /// * An optional annotations sequence and a value
    pub fn match_sexp_item_1_1(
        &mut self,
    ) -> IonParseResult<'top, Option<LazyRawValueExpr<'top, TextEncoding_1_1>>> {
        let input = *self;
        let result = whitespace_and_then(alt((
            Self::match_e_expression.map(|matched| Some(RawValueExpr::EExp(matched))),
            peek(")").value(None),
            (
                opt(Self::match_annotations),
                // We need the s-expression parser to recognize the input `--3` as the operator `--` and the
                // int `3` while recognizing the input `-3` as the int `-3`. If `match_operator` runs before
                // `match_value`, it will consume the sign (`-`) of negative number values, treating
                // `-3` as an operator (`-`) and an int (`3`). Thus, we run `match_value` first.
                whitespace_and_then(alt((
                    Self::match_value::<TextEncoding_1_1>,
                    Self::match_operator,
                ))),
            )
                .map(|(maybe_annotations, value)| input.apply_annotations(maybe_annotations, value))
                .map(RawValueExpr::ValueLiteral)
                .map(Some),
        )))
        .parse_next(self);
        result
    }

    #[inline]
    pub(crate) fn apply_annotations<Encoding: TextEncoding>(
        &self,
        maybe_annotations: Option<TextBuffer<'top>>,
        mut value: LazyRawTextValue<'top, Encoding>,
    ) -> LazyRawTextValue<'top, Encoding> {
        // This is a separately defined function so the common case (no annotations) is more readily
        // inlined.
        fn full_apply_annotations<'t, T: TextEncoding>(
            input: &TextBuffer<'t>,
            annotations: &TextBuffer<'t>,
            value: &mut LazyRawTextValue<'t, T>,
        ) {
            let annotations_length =
                u16::try_from(annotations.len()).expect("already length checked");
            // Update the encoded value's record of how many bytes of annotations precede the data.
            value.encoded_value = value
                .encoded_value
                .with_annotations_sequence(annotations_length);
            let unannotated_value_length = value.input.len();
            // Rewind the value's input to include the annotations sequence.
            value.input = input.slice(
                annotations.offset() - input.offset(),
                annotations_length as usize + unannotated_value_length,
            );
        }

        if let Some(annotations) = maybe_annotations {
            full_apply_annotations(self, &annotations, &mut value);
        }
        value
    }

    /// Matches an optional annotation sequence and a trailing value.
    pub fn match_annotated_value<E: TextEncoding>(
        &mut self,
    ) -> IonParseResult<'top, E::Value<'top>> {
        let input = *self;
        (
            opt(Self::match_annotations),
            whitespace_and_then(Self::match_value::<E>),
        )
            .map(|(maybe_annotations, value)| input.apply_annotations(maybe_annotations, value))
            .parse_next(self)
    }

    /// Matches a struct field name. That is:
    /// * A quoted symbol
    /// * An identifier
    /// * A symbol ID
    /// * A short-form string
    pub fn match_struct_field_name(&mut self) -> IonParseResult<'top, MatchedFieldName<'top>> {
        alt((
            Self::match_string.map(MatchedFieldNameSyntax::String),
            Self::match_symbol.map(MatchedFieldNameSyntax::Symbol),
        ))
        .with_taken()
        .map(
            #[inline]
            |(syntax, matched_input)| MatchedFieldName::new(matched_input, syntax),
        )
        .parse_next(self)
    }

    /// Matches a single top-level value, an IVM, or the end of the stream.
    pub fn match_top_level_item_1_0(
        &mut self,
    ) -> IonParseResult<'top, LazyRawStreamItem<'top, TextEncoding_1_0>> {
        // If only whitespace/comments remain, we're at the end of the stream.
        let _discarded_ws = self.match_optional_comments_and_whitespace()?;
        if self.is_empty() {
            return Ok(RawStreamItem::EndOfStream(EndPosition::new(
                TextEncoding_1_0.encoding(),
                self.offset(),
            )));
        }
        // Otherwise, the next item must be an IVM or a value.
        // We check for IVMs first because the rules for a symbol identifier will match them.
        alt((
            Self::match_ivm::<TextEncoding_1_0>.map(RawStreamItem::VersionMarker),
            Self::match_annotated_value::<TextEncoding_1_0>
                .map(LazyRawTextValue_1_0::from)
                .map(RawStreamItem::Value),
        ))
        .parse_next(self)
    }

    /// Matches a single top-level value, e-expression (macro invocation), IVM, or the end of
    /// the stream.
    pub fn match_top_level_item_1_1(
        &mut self,
    ) -> IonParseResult<'top, LazyRawStreamItem<'top, TextEncoding_1_1>> {
        // If only whitespace/comments remain, we're at the end of the stream.
        let _discarded_whitespace = self.match_optional_comments_and_whitespace()?;
        if self.is_empty() {
            return Ok(RawStreamItem::EndOfStream(EndPosition::new(
                TextEncoding_1_1.encoding(),
                self.offset(),
            )));
        }
        // Otherwise, the next item must be an IVM or a value.
        // We check for IVMs first because the rules for a symbol identifier will match them.
        alt((
            Self::match_ivm::<TextEncoding_1_1>.map(RawStreamItem::VersionMarker),
            Self::match_e_expression.map(RawStreamItem::EExp),
            Self::match_annotated_value::<TextEncoding_1_1>
                .map(LazyRawTextValue_1_1::from)
                .map(RawStreamItem::Value),
        ))
        .context("reading a v1.1 top-level expression")
        .parse_next(self)
    }

    /// Matches a single Ion 1.0 value.
    pub fn match_value<E: TextEncoding>(&mut self) -> IonParseResult<'top, E::Value<'top>> {
        use ValueTokenKind::*;
        dispatch! {
            |input: &mut TextBuffer<'top>| Ok(TEXT_ION_TOKEN_KINDS[input.peek_byte()? as usize]);
            NumberOrTimestamp => alt((
                Self::match_int_value,
                Self::match_float_value,
                Self::match_decimal_value,
                Self::match_timestamp_value,
            )),
            Letter => alt((
                Self::match_null_value,
                Self::match_bool_value,
                Self::match_identifier_value,
                Self::match_float_special_value, // nan
            )),
            Symbol => Self::match_symbol_value,
            QuotedText => alt((Self::match_string_value, Self::match_symbol_value)),
            List => E::list_matcher(),
            SExp => E::sexp_matcher(),
            LobOrStruct => alt((
                Self::match_blob_value,
                Self::match_clob_value,
                E::struct_matcher(),
            )),
            Invalid(_byte) => |input: &mut TextBuffer<'top>| {
                input
                    .unrecognized()
                    .context("reading a value")
                   .backtrack()
            },
        }
        .with_taken()
        .map(|(encoded_value, input)| E::new_value(input, encoded_value))
        .parse_next(self)
    }

    pub fn match_e_expression_arg_group(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, TextEExpArgGroup<'top>> {
        alt((
            Self::parser_with_arg(Self::match_explicit_arg_group, parameter),
            Self::parser_with_arg(Self::match_rest, parameter),
        ))
        .parse_next(self)
    }

    /// Higher-order helper that takes a closure and an argument to pass and constructs a new
    /// parser that calls the closure with the provided argument.
    pub fn parser_with_arg<A: 'top, O>(
        mut parser: impl FnMut(&mut Self, &'top A) -> IonParseResult<'top, O>,
        arg_to_pass: &'top A,
    ) -> impl IonParser<'top, O> {
        move |input: &mut TextBuffer<'top>| parser(input, arg_to_pass)
    }

    pub fn match_explicit_arg_group(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, TextEExpArgGroup<'top>> {
        TextEncoding_1_1::container_matcher(
            "an explicit argument group",
            "(::",
            RawTextSExpIterator::<TextEncoding_1_1>::new,
            whitespace_and_then(")"),
        )
        .with_taken()
        .map(|(expr_cache, input)| TextEExpArgGroup::new(parameter, input, expr_cache))
        .parse_next(self)
    }

    pub fn match_e_expression_name(&mut self) -> IonParseResult<'top, MacroIdRef<'top>> {
        let (matched_symbol, macro_id_bytes) =
            Self::match_identifier.with_taken().parse_next(self)?;
        let name = match matched_symbol
            .read(self.context.allocator(), macro_id_bytes)
            .expect("matched identifier but failed to read its bytes")
        {
            RawSymbolRef::SymbolId(_) => unreachable!("matched a text identifier, returned a SID"),
            RawSymbolRef::Text(text) => text,
            RawSymbolRef::SystemSymbol_1_1(system_symbol) => system_symbol.text(),
        };
        Ok(MacroIdRef::LocalName(name))
    }

    pub fn match_e_expression_address(&mut self) -> IonParseResult<'top, MacroIdRef<'top>> {
        let address = Self::match_address(self)?;
        let id = MacroIdRef::LocalAddress(address);
        Ok(id)
    }

    pub fn match_system_eexp_id(&mut self) -> IonParseResult<'top, MacroIdRef<'top>> {
        let _matched_system_annotation =
            ("$ion", whitespace_and_then("::"), Self::match_whitespace0)
                .take()
                .parse_next(self)?;

        let id = alt((
            Self::match_e_expression_address,
            Self::match_e_expression_name,
        ))
        .parse_next(self)?;

        let system_id = match id {
            MacroIdRef::LocalName(name) => {
                let Some(macro_address) = ION_1_1_SYSTEM_MACROS.address_for_name(name) else {
                    return self
                        .invalid(format!("found unrecognized system macro name: '{}'", name))
                        .context("reading an e-expression's macro ID as a local name")
                        .cut();
                };
                // This address came from the system table, so we don't need to validate it.
                MacroIdRef::SystemAddress(SystemMacroAddress::new_unchecked(macro_address))
            }
            MacroIdRef::LocalAddress(address) => {
                let Some(system_address) = SystemMacroAddress::new(address) else {
                    return self
                        .invalid(format!(
                            "found out-of-bounds system macro address {}",
                            address
                        ))
                        .context("reading an e-expression's macro ID as a system address")
                        .cut();
                };
                MacroIdRef::SystemAddress(system_address)
            }
            MacroIdRef::SystemAddress(_) => {
                unreachable!("`match_e_expression_address` always returns a LocalAddress")
            }
        };
        Ok(system_id)
    }

    pub fn match_e_expression_id(&mut self) -> IonParseResult<'top, MacroIdRef<'top>> {
        let id = alt((
            Self::match_system_eexp_id,
            Self::match_e_expression_name,
            Self::match_e_expression_address,
        ))
        .parse_next(self)?;

        Ok(id)
    }

    /// Matches an e-expression invoking a macro.
    ///
    /// If the input does not contain the entire e-expression, returns `IonError::Incomplete(_)`.
    pub fn match_e_expression(&mut self) -> IonParseResult<'top, TextEExpression_1_1<'top>> {
        let original_input = *self;
        let parser = |input: &mut TextBuffer<'top>| {
            let _opening_tag = "(:".parse_next(input)?;
            let id = Self::match_e_expression_id(input)?;
            let mut arg_expr_cache = BumpVec::new_in(input.context.allocator());

            let macro_ref: &'top MacroDef = input
                .context()
                .macro_table()
                .macro_with_id(id)
                .ok_or_else(|| {
                    (*input)
                        .invalid(format!("could not find macro with id {:?}", id))
                        .context("reading an e-expression")
                        .cut_err()
                })?
                .reference();
            let signature_params: &'top [Parameter] = macro_ref.signature().parameters();
            for (index, param) in signature_params.iter().enumerate() {
                let maybe_arg = input.match_argument_for(param)?;
                match maybe_arg {
                    Some(arg) => arg_expr_cache.push(arg),
                    None => {
                        for param in &signature_params[index..] {
                            if !param.can_be_omitted() {
                                return input
                                    .invalid(format!(
                                        "e-expression did not include an argument for param '{}'",
                                        param.name()
                                    ))
                                    .context("reading an e-expression")
                                    .cut();
                            }
                        }
                        break;
                    }
                }
            }
            match whitespace_and_then(")").parse_next(input) {
                Ok(_closing_delimiter) => Ok((id, macro_ref, arg_expr_cache)),
                Err(ErrMode::Incomplete(_)) => input.incomplete("an e-expression"),
                Err(_e) => {
                    (*input)
                        .invalid(format!(
                            "macro {id} signature has {} parameter(s), e-expression had an extra argument",
                            signature_params.len()
                        ))
                        .context("reading an e-expression's arguments")
                        .cut()
                }
            }
        };
        let ((macro_id, macro_ref, mut arg_expr_cache), matched_input) =
            parser.with_taken().parse_next(self)?;

        let parameters = macro_ref.signature().parameters();
        if arg_expr_cache.len() < parameters.len() {
            // If expressions were not provided for all arguments, it was due to rest syntax.
            // Non-required expressions in trailing position can be omitted.
            // If we reach this point, the rest syntax check in the argument parsing logic above
            // has already verified that using rest syntax was legal. We can add empty argument
            // groups for each missing expression.

            // Find the end of the last explicit argument. If there were no explicit arguments,
            // then the 'end' is the TextBuffer's stream offset. (i.e. self.offset())
            let last_explicit_arg_end = arg_expr_cache
                .last()
                .map(|arg| arg.expr().range().end)
                .unwrap_or(self.offset());

            // Get an empty slice at the end position that we just calculated.
            // This will be the backing slice for all implicitly empty arguments.
            let empty_end_slice =
                original_input.slice(last_explicit_arg_end - original_input.offset(), 0);

            // Add an empty argument group for each remaining argument to the expr cache.
            for parameter in &parameters[arg_expr_cache.len()..] {
                arg_expr_cache.push(EExpArg::new(
                    parameter,
                    EExpArgExpr::ArgGroup(TextEExpArgGroup::new(parameter, empty_end_slice, &[])),
                ));
            }
        }
        debug_assert!(
            arg_expr_cache.len() == parameters.len(),
            "every parameter must have an argument, explicit or implicit"
        );

        Ok(TextEExpression_1_1::new(
            macro_id,
            matched_input,
            arg_expr_cache.into_bump_slice(),
        ))
    }

    pub fn match_argument_for(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, Option<EExpArg<'top, TextEncoding_1_1>>> {
        use crate::lazy::expanded::template::ParameterCardinality::*;
        match parameter.cardinality() {
            ExactlyOne => {
                let arg = self.match_exactly_one(parameter)?;
                Ok(Some(arg))
            }
            ZeroOrOne => self.match_zero_or_one(parameter),
            ZeroOrMore => self.match_zero_or_more(parameter),
            OneOrMore => self.match_one_or_more(parameter),
        }
    }

    pub fn match_exactly_one(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, EExpArg<'top, TextEncoding_1_1>> {
        let _whitespace = self.match_optional_comments_and_whitespace()?;
        // This check exists to offer a more human-friendly error message; without it,
        // the user simply sees a parsing failure.
        if self.bytes().starts_with(b"(::") {
            return self
                .invalid(format!("parameter '{}' has cardinality `ExactlyOne`; it cannot accept an expression group", parameter.name()))
                .context("reading an e-expression argument with `exactly-one` cardinality")
                .cut();
        }
        let maybe_expr = Self::match_sexp_item_1_1
            .map(|expr| expr.map(EExpArgExpr::<TextEncoding_1_1>::from))
            .parse_next(self)?;
        match maybe_expr {
            Some(expr) => Ok(EExpArg::new(parameter, expr)),
            None => self
                .invalid(format!(
                    "expected argument for required parameter '{}'",
                    parameter.name()
                ))
                .context("reading an e-expression argument with `exactly-one` cardinality")
                .cut(),
        }
    }

    pub fn match_empty_arg_group(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, EExpArg<'top, TextEncoding_1_1>> {
        ("(::", whitespace_and_then(")"))
            .take()
            .map(|matched_expr| {
                let arg_group = TextEExpArgGroup::new(parameter, matched_expr, &[]);
                EExpArg::new(parameter, EExpArgExpr::ArgGroup(arg_group))
            })
            .parse_next(self)
    }

    pub fn match_zero_or_one(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, Option<EExpArg<'top, TextEncoding_1_1>>> {
        whitespace_and_then(alt((
            Self::parser_with_arg(Self::match_empty_arg_group, parameter).map(Some),
            // TODO: Match a non-empty arg group and turn it into a failure with a helpful error message
            Self::match_sexp_item_1_1.map(|maybe_expr| {
                maybe_expr.map(|expr| {
                    EExpArg::new(parameter, EExpArgExpr::<TextEncoding_1_1>::from(expr))
                })
            }),
        )))
        .parse_next(self)
    }

    pub fn match_zero_or_more(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, Option<EExpArg<'top, TextEncoding_1_1>>> {
        let maybe_expr = preceded(
            Self::match_optional_comments_and_whitespace,
            alt((
                Self::parser_with_arg(Self::match_e_expression_arg_group, parameter)
                    .map(|group| Some(EExpArg::new(parameter, EExpArgExpr::ArgGroup(group)))),
                Self::match_sexp_item_1_1.map(|expr| {
                    expr.map(EExpArgExpr::from)
                        .map(|expr| EExpArg::new(parameter, expr))
                }),
                peek(")").value(None),
            )),
        )
        .parse_next(self)?;
        Ok(maybe_expr)
    }

    pub fn match_one_or_more(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, Option<EExpArg<'top, TextEncoding_1_1>>> {
        if self.match_empty_arg_group(parameter).is_ok() {
            return self
                .unrecognized()
                .context("reading an e-expression argument with `one-or-more` cardinality")
                .backtrack();
        }

        self.match_zero_or_more(parameter)
    }

    pub fn match_rest(
        &mut self,
        parameter: &'top Parameter,
    ) -> IonParseResult<'top, TextEExpArgGroup<'top>> {
        if parameter.rest_syntax_policy() == RestSyntaxPolicy::NotAllowed {
            return self
                .unrecognized()
                .context("reading a parameter that does not support rest syntax")
                .backtrack();
        }
        let mut cache = BumpVec::new_in(self.context().allocator());
        let parser = |input: &mut TextBuffer<'top>| {
            while let Some(expr) = alt((
                whitespace_and_then(peek(")")).value(None),
                Self::match_sexp_item_1_1,
            ))
            .parse_next(input)?
            {
                cache.push(expr);
            }
            Ok(())
        };
        let (_, matched_input) = parser.with_taken().parse_next(self)?;

        Ok(TextEExpArgGroup::new(
            parameter,
            matched_input,
            cache.into_bump_slice(),
        ))
    }

    /// Matches and returns a boolean value.
    pub fn match_bool(&mut self) -> IonParseResult<'top, bool> {
        terminated(
            alt(("true".value(true), "false".value(false))),
            Self::peek_stop_character,
        )
        .parse_next(self)
    }

    /// Matches and returns any type of null. (`null`, `null.null`, `null.int`, etc)
    pub fn match_null(&mut self) -> IonParseResult<'top, IonType> {
        terminated(
            alt((
                ("null.", Self::match_ion_type).map(|(_, ion_type)| ion_type),
                "null".value(IonType::Null),
            )),
            Self::peek_stop_character,
        )
        .parse_next(self)
    }

    /// Matches and returns an Ion type.
    fn match_ion_type(&mut self) -> IonParseResult<'top, IonType> {
        alt((
            "null".value(IonType::Null),
            "bool".value(IonType::Bool),
            "int".value(IonType::Int),
            "float".value(IonType::Float),
            "decimal".value(IonType::Decimal),
            "timestamp".value(IonType::Timestamp),
            "symbol".value(IonType::Symbol),
            "string".value(IonType::String),
            "clob".value(IonType::Clob),
            "blob".value(IonType::Blob),
            "list".value(IonType::List),
            "sexp".value(IonType::SExp),
            "struct".value(IonType::Struct),
        ))
        .parse_next(self)
    }

    /// Matches any one of Ion's stop characters.
    fn match_stop_character(&mut self) -> IonMatchResult<'top> {
        alt((
            eof,
            one_of("{}[](),\"' \t\n\r\u{0b}\u{0c}".as_bytes()).take(),
        ))
        .parse_next(self)
    }

    /// Matches--but does not consume--any one of Ion's stop characters.
    fn peek_stop_character(&mut self) -> IonMatchResult<'top> {
        peek(Self::match_stop_character).parse_next(self)
    }

    /// Matches the three parts of an int--its base, its sign, and its digits--without actually
    /// constructing an Int from them.
    pub fn match_int(&mut self) -> IonParseResult<'top, MatchedInt> {
        terminated(
            // We test for base 16 and base 2 so the '0x' or '0b' isn't confused for a leading zero
            // in a base 10 number, which would be illegal.
            alt((
                Self::match_base_2_int,
                Self::match_base_16_int,
                Self::match_base_10_int,
            )),
            Self::peek_stop_character,
        )
        .parse_next(self)
    }

    scalar_value_matchers!(
        Self::match_null => Null => match_null_value,
        Self::match_bool => Bool => match_bool_value,
        Self::match_int => Int => match_int_value,
        Self::match_float => Float => match_float_value,
        Self::match_float_special => Float => match_float_special_value,
        Self::match_decimal => Decimal => match_decimal_value,
        Self::match_timestamp => Timestamp => match_timestamp_value,
        Self::match_string => String => match_string_value,
        Self::match_symbol => Symbol => match_symbol_value,
        Self::match_identifier => Symbol => match_identifier_value,
        Self::match_blob => Blob => match_blob_value,
        Self::match_clob => Clob => match_clob_value,
    );

    /// Matches a base-2 notation integer (e.g. `0b0`, `0B1010`, or `-0b0111`) and returns the
    /// partially parsed value as a [`MatchedInt`].
    fn match_base_2_int(&mut self) -> IonParseResult<'top, MatchedInt> {
        let initial_offset = self.offset();
        separated_pair(opt("-"), alt(("0b", "0B")), Self::match_base_2_int_digits)
            .map(|(maybe_sign, digits)| {
                MatchedInt::new(2, maybe_sign.is_some(), digits.offset() - initial_offset)
            })
            .parse_next(self)
    }

    /// Matches the digits of a base-2 integer.
    fn match_base_2_int_digits(&mut self) -> IonMatchResult<'top> {
        terminated(
            // Zero or more digits-followed-by-underscores
            zero_or_more((take_while(1.., b"01"), "_")),
            // One or more digits
            one_or_more(one_of(b"01")),
        )
        .take()
        .parse_next(self)
    }

    /// Matches a base-10 notation integer (e.g. `0`, `255`, or `-1_024`) and returns the partially
    /// parsed value as a [`MatchedInt`].
    fn match_base_10_int(&mut self) -> IonParseResult<'top, MatchedInt> {
        let initial_offset = self.offset();
        (opt("-"), Self::match_base_10_int_digits)
            .map(|(maybe_sign, digits)| {
                MatchedInt::new(10, maybe_sign.is_some(), digits.offset() - initial_offset)
            })
            .parse_next(self)
    }

    /// Matches the digits of a base-10 integer. (i.e. An integer without a sign.)
    fn match_base_10_int_digits(&mut self) -> IonMatchResult<'top> {
        Self::match_base_10_digits_before_dot(self)
    }

    /// Matches either:
    /// * a zero
    /// * a non-zero followed by some number of digits with optional underscores
    fn match_base_10_digits_before_dot(&mut self) -> IonMatchResult<'top> {
        alt((
            // The number is either a zero...
            "0",
            // Or it's a non-zero followed by some number of '_'-separated digits
            (
                Self::match_base_10_leading_digit,
                Self::match_base_10_trailing_digits,
            )
                .take(),
        ))
        .parse_next(self)
    }

    /// Matches the first digit of a multi-digit base-10 integer. (i.e. Any digit but zero.)
    fn match_base_10_leading_digit(&mut self) -> IonMatchResult<'top> {
        one_of(b"123456789").take().parse_next(self)
    }

    /// Matches any number of digits with underscores optionally appearing in the middle.
    /// This parser accepts leading zeros, which is why it cannot be used for the beginning
    /// of a number.
    fn match_base_10_trailing_digits(&mut self) -> IonMatchResult<'top> {
        // A sequence of zero or more...
        zero_or_more(alt((
            //...underscore-followed-by-a-digit...
            ("_", one_of(|b: u8| b.is_ascii_digit())).take(),
            //...or one or more digits.
            digit1,
        )))
        .parse_next(self)
    }

    /// Matches a base-10 notation integer (e.g. `0x0`, `0X20`, or `-0xCAFE`) and returns the
    /// partially parsed value as a [`MatchedInt`].
    fn match_base_16_int(&mut self) -> IonParseResult<'top, MatchedInt> {
        let initial_offset = self.offset();
        separated_pair(
            opt("-"),
            alt(("0x", "0X")),
            Self::match_base_16_int_trailing_digits,
        )
        .map(|(maybe_sign, digits)| {
            MatchedInt::new(16, maybe_sign.is_some(), digits.offset() - initial_offset)
        })
        .parse_next(self)
    }

    /// Matches the digits that follow the '0x' or '0X' in a base-16 integer
    fn match_base_16_int_trailing_digits(&mut self) -> IonMatchResult<'top> {
        terminated(
            // Zero or more digits-followed-by-underscores
            zero_or_more((Self::take_base_16_digits1, "_")),
            // One or more digits
            Self::take_base_16_digits1,
        )
        .take()
        .parse_next(self)
    }

    /// Recognizes 1 or more consecutive base-16 digits.
    // This function's "1" suffix is a style borrowed from `nom`.
    fn take_base_16_digits1(&mut self) -> IonMatchResult<'top> {
        (
            one_of(|b: u8| b.is_ascii_hexdigit()),
            // After we have our digit, take digits until we find a non-digit (including EOF).
            take_while(.., |b: u8| b.is_ascii_hexdigit()),
        )
            .take()
            .parse_next(self)
    }

    /// Matches `n` consecutive hex digits.
    pub(crate) fn match_n_hex_digits(
        count: usize,
    ) -> impl Parser<TextBuffer<'top>, TextBuffer<'top>, IonParseError<'top>> {
        n_times(count, one_of(|b: u8| b.is_ascii_hexdigit())).take()
    }

    /// Matches an Ion float of any syntax
    fn match_float(&mut self) -> IonParseResult<'top, MatchedFloat> {
        terminated(
            alt((Self::match_float_special, Self::match_float_numeric_value)),
            Self::peek_stop_character,
        )
        .parse_next(self)
    }

    /// Matches special IEEE-754 values, including +/- infinity and NaN.
    fn match_float_special(&mut self) -> IonParseResult<'top, MatchedFloat> {
        alt((
            "nan".value(MatchedFloat::NotANumber),
            "+inf".value(MatchedFloat::PositiveInfinity),
            "-inf".value(MatchedFloat::NegativeInfinity),
        ))
        .parse_next(self)
    }

    /// Matches numeric IEEE-754 floating point values.
    fn match_float_numeric_value(&mut self) -> IonParseResult<'top, MatchedFloat> {
        (
            Self::match_number_with_optional_dot_and_digits,
            Self::match_float_exponent_marker_and_digits,
        )
            .take()
            .value(MatchedFloat::Numeric)
            .parse_next(self)
    }

    /// Matches a number that may or may not have a decimal place and trailing fractional digits.
    /// If a decimal place is present, there must also be trailing digits.
    /// For example:
    ///   1000
    ///   1000.559
    ///   -25.2
    fn match_number_with_optional_dot_and_digits(&mut self) -> IonMatchResult<'top> {
        (
            opt("-"),
            Self::match_base_10_digits_before_dot,
            opt(Self::match_dot_followed_by_base_10_digits),
        )
            .take()
            .parse_next(self)
    }

    /// In a float or decimal, matches the digits that are permitted before the decimal point.
    /// This includes either a single zero, or a non-zero followed by any sequence of digits.
    fn match_digits_before_dot(&mut self) -> IonMatchResult<'top> {
        alt((
            "0",
            (Self::match_leading_digit, Self::match_trailing_digits).take(),
        ))
        .parse_next(self)
    }

    /// Matches a single non-zero base 10 digit.
    fn match_leading_digit(&mut self) -> IonMatchResult<'top> {
        one_of(b"123456789").take().parse_next(self)
    }

    /// Matches any number of base 10 digits, allowing underscores at any position except the end.
    fn match_trailing_digits(&mut self) -> IonMatchResult<'top> {
        zero_or_more(preceded(opt("_"), digit1)).parse_next(self)
    }

    /// Recognizes a decimal point followed by any number of base-10 digits.
    fn match_dot_followed_by_base_10_digits(&mut self) -> IonMatchResult<'top> {
        (".", opt(Self::match_zero_or_more_digits_after_dot))
            .take()
            .parse_next(self)
    }

    /// Like `match_digits_before_dot`, but allows leading zeros.
    fn match_one_or_more_digits_after_dot(&mut self) -> IonMatchResult<'top> {
        (
            // Any number of digit-sequence-with-trailing-underscores...
            zero_or_more((digit1, "_")),
            // ...and at least one trailing digit. Inputs that don't have any underscores
            // will be handled by this parser branch.
            (one_of(|b: u8| b.is_ascii_digit()), digit0),
        )
            .take()
            .parse_next(self)
    }

    /// Like `match_digits_before_dot`, but allows leading zeros.
    fn match_zero_or_more_digits_after_dot(&mut self) -> IonMatchResult<'top> {
        terminated(
            // Zero or more digits-followed-by-underscores.
            zero_or_more((
                digit1,
                terminated(
                    // The digit sequence can be followed by an underscore...
                    "_",
                    // ...as long as the character after the underscore is another digit.
                    peek(one_of(|b: u8| b.is_ascii_digit())),
                ),
            )),
            // ...and one or more trailing digits. This parser branch handles
            // inputs that don't have any underscores.
            digit1,
        )
        .take()
        .parse_next(self)
    }

    /// Matches an `e` or `E` followed by an optional sign (`+` or `-`) followed by one or more
    /// base 10 digits.
    fn match_float_exponent_marker_and_digits(&mut self) -> IonMatchResult<'top> {
        preceded(
            one_of(b"eE"),
            Self::match_exponent_sign_and_one_or_more_digits.take(),
        )
        .parse_next(self)
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
    fn match_exponent_sign_and_one_or_more_digits(&mut self) -> IonParseResult<'top, (bool, Self)> {
        (
            // Optional leading sign; if there's no sign, it's not negative.
            opt(Self::match_any_sign).map(|s| s == Some(b'-')),
            Self::match_one_or_more_digits_after_dot,
        )
            .parse_next(self)
    }

    /// Matches `-` OR `+`.
    ///
    /// This is used for matching exponent signs; most places in Ion do not allow `+`.
    pub fn match_any_sign(&mut self) -> IonParseResult<'top, std::primitive::u8> {
        one_of(b"-+").parse_next(self)
    }

    pub fn match_decimal_exponent(&mut self) -> IonParseResult<'top, (bool, TextBuffer<'top>)> {
        preceded(
            one_of(b"dD"),
            Self::match_exponent_sign_and_one_or_more_digits,
        )
        .parse_next(self)
    }

    /// Match an optional sign (if present), digits before the decimal point, then digits after the
    /// decimal point (if present).
    pub fn match_decimal(&mut self) -> IonParseResult<'top, MatchedDecimal> {
        let initial_offset = self.offset();
        terminated(
            (
                opt("-"),
                Self::match_digits_before_dot,
                alt((
                    (
                        ".",
                        opt(Self::match_zero_or_more_digits_after_dot),
                        opt(Self::match_decimal_exponent),
                    )
                        .map(
                            |(dot, maybe_digits_after_dot, maybe_exponent)| {
                                let digits_after_dot = match maybe_digits_after_dot {
                                    Some(digits) => digits,
                                    None => dot.slice(1, 0),
                                };
                                let (exp_is_negative, exp_digits) = match maybe_exponent {
                                    Some(exponent) => exponent,
                                    None => {
                                        (false, digits_after_dot.slice(digits_after_dot.len(), 0))
                                    }
                                };
                                (digits_after_dot, exp_is_negative, exp_digits)
                            },
                        ),
                    // or just a d/D and exponent
                    Self::match_decimal_exponent.with_taken().map(
                        |((exp_is_negative, exp_digits), matched)| {
                            // Make an empty slice to represent the (absent) digits after dot
                            let digits_after_dot = matched.slice(0, 0);
                            (digits_after_dot, exp_is_negative, exp_digits)
                        },
                    ),
                )),
            ),
            Self::peek_stop_character,
        )
        .map(
            |(maybe_sign, leading_digits, (digits_after_dot, exponent_is_negative, exp_digits))| {
                let is_negative = maybe_sign.is_some();
                let digits_offset = (leading_digits.offset() - initial_offset) as u16;
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
                let exponent_digits_offset = (exp_digits.offset() - initial_offset) as u16;
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
        .parse_next(self)
    }

    /// Matches short- or long-form string.
    pub fn match_string(&mut self) -> IonParseResult<'top, MatchedString> {
        alt((Self::match_short_string, Self::match_long_string)).parse_next(self)
    }

    /// Matches a short string. For example: `"foo"`
    pub(crate) fn match_short_string(&mut self) -> IonParseResult<'top, MatchedString> {
        delimited("\"", Self::match_short_string_body, "\"")
            .map(|(_matched, contains_escaped_chars)| {
                if contains_escaped_chars {
                    MatchedString::ShortWithEscapes
                } else {
                    MatchedString::ShortWithoutEscapes
                }
            })
            .parse_next(self)
    }

    /// Returns a matched buffer and a boolean indicating whether any escaped characters were
    /// found in the short string.
    pub(crate) fn match_short_string_body(&mut self) -> IonParseResult<'top, (Self, bool)> {
        Self::match_text_until_unescaped(self, b'\"', false)
    }

    pub fn match_long_string(&mut self) -> IonParseResult<'top, MatchedString> {
        Self::match_long_string_segments.parse_next(self)
    }

    /// Matches a long string comprised of any number of `'''`-enclosed segments interleaved
    /// with optional comments and whitespace.
    pub(crate) fn match_long_string_segments(&mut self) -> IonParseResult<'top, MatchedString> {
        struct Stats(usize, bool);

        impl Accumulate<bool> for Stats {
            fn initial(_capacity: Option<usize>) -> Self {
                Stats(0, false)
            }

            fn accumulate(&mut self, acc: bool) {
                self.0 += 1;
                self.1 |= acc;
            }
        }

        repeat(1.., |input: &mut TextBuffer<'top>| {
            let (_segment, found_escape) =
                whitespace_and_then(Self::match_long_string_segment).parse_next(input)?;
            Ok(found_escape)
        })
        .map(move |stats: Stats| match stats {
            Stats(1, false) => MatchedString::LongSingleSegmentWithoutEscapes,
            Stats(1, true) => MatchedString::LongSingleSegmentWithEscapes,
            _ => MatchedString::Long,
        })
        .parse_next(self)
    }

    /// Matches a single long string segment enclosed by `'''` delimiters.
    /// Returns the match and a boolean indicating whether the body contained escape sequences.
    pub fn match_long_string_segment(&mut self) -> IonParseResult<'top, (Self, bool)> {
        delimited("'''", Self::match_long_string_segment_body, "'''").parse_next(self)
    }

    /// Matches all input up to (but not including) the first unescaped instance of `'''`.
    /// Returns the match and a boolean indicating whether the body contained escape sequences.
    fn match_long_string_segment_body(&mut self) -> IonParseResult<'top, (Self, bool)> {
        Self::match_text_until_unescaped_str(self, "'''")
    }

    /// Matches an operator symbol, which can only legally appear within an s-expression
    pub(crate) fn match_operator<E: TextEncoding>(
        &mut self,
    ) -> IonParseResult<'top, LazyRawTextValue<'top, E>> {
        one_or_more(one_of(b"!#%&*+-./;<=>?@^`|~"))
            .map(|text: TextBuffer<'_>| LazyRawTextValue {
                input: text,
                encoded_value: EncodedTextValue::new(MatchedValue::Symbol(MatchedSymbol::Operator)),
            })
            .parse_next(self)
    }

    /// Matches a symbol ID (`$28`), an identifier (`foo`), or a quoted symbol (`'foo'`).
    fn match_symbol(&mut self) -> IonParseResult<'top, MatchedSymbol> {
        alt((
            Self::match_symbol_id,
            Self::match_identifier,
            Self::match_quoted_symbol,
        ))
        .parse_next(self)
    }

    /// Matches a symbol ID (`$28`).
    fn match_symbol_id(&mut self) -> IonParseResult<'top, MatchedSymbol> {
        ("$", Self::match_address)
            .value(MatchedSymbol::SymbolId)
            .parse_next(self)
    }

    /// Matches the integer portion of a symbol ID or a macro address.
    /// Addresses
    ///   * CANNOT have underscores in them. For example: `$1_0` and `$100_200_300` are considered
    ///     identifiers, not symbol IDs.
    ///   * CAN have leading zeros. For example, `$0003` is the same as `$3`.
    // There's precedent for allowing leading zeros in ion-java, so we support it here for consistency.
    fn match_address(&mut self) -> IonParseResult<'top, usize> {
        // Any number of base-10 digits followed by something that is NOT an underscore.
        // We do this to make sure that input like `$1_02` gets parsed like an identifier;
        // If we didn't check for a trailing underscore, it would be a SID (`$1`) and an
        // identifier (`_02`).
        let initial_offset = self.offset();
        terminated(digit1, not("_"))
            .map(|buffer: TextBuffer<'_>| {
                // The matched buffer is ascii base 10 digits, parsing must succeed
                usize::from_str(buffer.as_utf8(initial_offset).unwrap()).unwrap()
            })
            .parse_next(self)
    }

    /// Matches items that match the syntactic definition of an identifier but which have special
    /// meaning. (`true`, `false`, `nan`, `null`)
    pub(crate) fn match_keyword(&mut self) -> IonMatchResult<'top> {
        terminated(
            alt(("true", "false", "null", "nan")),
            Self::identifier_terminator,
        )
        .parse_next(self)
    }

    /// Matches an identifier (`foo`).
    pub(crate) fn match_identifier(&mut self) -> IonParseResult<'top, MatchedSymbol> {
        (
            not(Self::match_keyword),
            Self::identifier_initial_character,
            Self::identifier_trailing_characters,
            Self::identifier_terminator,
        )
            .value(MatchedSymbol::Identifier)
            .parse_next(self)
    }

    fn identifier_terminator(&mut self) -> IonMatchResult<'top> {
        not(Self::identifier_trailing_character)
            .take()
            .parse_next(self)
    }

    /// Matches any character that can appear at the start of an identifier.
    fn identifier_initial_character(&mut self) -> IonParseResult<'top, Self> {
        alt((one_of(b"$_"), one_of(|b: u8| b.is_ascii_alphabetic())))
            .take()
            .parse_next(self)
    }

    /// Matches any character that is legal in an identifier, though not necessarily at the beginning.
    fn identifier_trailing_character(&mut self) -> IonParseResult<'top, Self> {
        alt((one_of(b"$_"), one_of(|c: u8| c.is_ascii_alphanumeric())))
            .take()
            .parse_next(self)
    }

    /// Matches characters that are legal in an identifier, though not necessarily at the beginning.
    fn identifier_trailing_characters(&mut self) -> IonParseResult<'top, Self> {
        zero_or_more(one_of(|b: u8| {
            b.is_ascii_alphanumeric() || b"$_".contains(&b)
        }))
        .parse_next(self)
    }

    /// Matches a quoted symbol (`'foo'`).
    fn match_quoted_symbol(&mut self) -> IonParseResult<'top, MatchedSymbol> {
        delimited("'", Self::match_quoted_symbol_body, "'")
            .map(|(_matched, contains_escaped_chars)| {
                if contains_escaped_chars {
                    MatchedSymbol::QuotedWithEscapes
                } else {
                    MatchedSymbol::QuotedWithoutEscapes
                }
            })
            .parse_next(self)
    }

    /// Returns a matched buffer and a boolean indicating whether any escaped characters were
    /// found in the short string.
    fn match_quoted_symbol_body(&mut self) -> IonParseResult<'top, (Self, bool)> {
        Self::match_text_until_unescaped(self, b'\'', false)
    }

    /// A helper method for matching bytes until the specified delimiter. Ignores any byte
    /// (including the delimiter) that is prefaced by the escape character `\`.
    fn match_text_until_unescaped(
        &mut self,
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
                let bytes_to_skip = if next_two_bytes == Some(b"\r\n") {
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
                self.consume(index);
                return Ok((matched, contains_escaped_chars));
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
        self.incomplete("reading a text value without closing delimiter")
    }

    #[cold]
    fn validate_string_control_character(
        &mut self,
        byte: u8,
        index: usize,
        allow_unescaped_newlines: bool,
    ) -> IonParseResult<'top, ()> {
        if byte == b'\n' && !allow_unescaped_newlines {
            return self
                .slice_to_end(index)
                .invalid("unescaped newlines are not allowed in short string literals")
                .context("reading a string")
                .cut();
        }
        if !WHITESPACE_BYTES.contains(&byte) {
            return self
                .slice_to_end(index)
                .invalid(format!("unescaped control characters are not allowed in text literals; byte {byte:02X}"))
                .context("reading a string")
                .cut();
        }
        Ok(())
    }

    /// A helper method for matching bytes until the specified delimiter. Ignores any byte
    /// that is prefaced by the escape character `\`.
    ///
    /// The specified delimiter cannot be empty.
    fn match_text_until_unescaped_str(
        &mut self,
        delimiter: &str,
    ) -> IonParseResult<'top, (Self, bool)> {
        // The first byte in the delimiter
        let delimiter_head = delimiter.as_bytes()[0];
        // Whether we've encountered any escapes while looking for the delimiter
        let mut contained_escapes = false;
        // The input left to search
        let mut remaining = *self;
        loop {
            // Look for the first unescaped instance of the delimiter's head.
            // If the input doesn't contain one, this will return an `Incomplete`.
            // `match_text_until_escaped` does NOT include the delimiter byte in the match,
            // so `remaining_after_match` starts at the delimiter byte.
            // Note: `matched_input_buffer` is used under a feature flag, hence suppress clippy warnings for this.
            #[allow(unused_variables)]
            let (matched_input_buffer, segment_contained_escapes) =
                remaining.match_text_until_unescaped(delimiter_head, true)?;
            contained_escapes |= segment_contained_escapes;

            // If the remaining input starts with the complete delimiter, it's a match.
            if remaining.bytes().starts_with(delimiter.as_bytes()) {
                let relative_match_end = remaining.offset() - self.offset();
                let matched_input = self.slice(0, relative_match_end);
                self.consume(relative_match_end);
                // This input may contain newline characters hence update the location metadata.
                #[cfg(feature = "source-location")]
                self.update_location_metadata(matched_input_buffer.bytes());
                return Ok((matched_input, contained_escapes));
            } else {
                // Otherwise, advance by one and try again.
                remaining.consume(1);
            }
        }
    }

    /// Matches a single base-10 digit, 0-9.
    fn match_any_digit(&mut self) -> IonParseResult<'top, std::primitive::u8> {
        one_of(|b: u8| b.is_ascii_digit()).parse_next(self)
    }

    /// Matches a timestamp of any precision.
    #[inline]
    pub fn match_timestamp(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        #[inline(never)]
        pub fn full_match_timestamp<'t>(
            input: &mut TextBuffer<'t>,
        ) -> IonParseResult<'t, MatchedTimestamp> {
            // TODO: As-is, matching common timestamps (those with greater than second precision)
            //       is slow because the parser tries each shorter arrangement in turn. We should
            //       rewrite this to use a single path that can accept any precision.
            alt((
                TextBuffer::match_timestamp_y,
                TextBuffer::match_timestamp_ym,
                TextBuffer::match_timestamp_ymd,
                TextBuffer::match_timestamp_ymd_hm,
                TextBuffer::match_timestamp_ymd_hms,
                TextBuffer::match_timestamp_ymd_hms_fractional,
            ))
            .parse_next(input)
        }

        match self.bytes().first() {
            Some(byte) if byte.is_ascii_digit() => full_match_timestamp(self),
            Some(_) => self.unrecognized().backtrack(),
            None => self.incomplete("a timestamp"),
        }
    }

    /// Matches a timestamp with year precision.
    fn match_timestamp_y(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(Self::match_timestamp_year, ("T", Self::peek_stop_character))
            .map(|_year| MatchedTimestamp::new(TimestampPrecision::Year))
            .parse_next(self)
    }

    /// Matches a timestamp with month precision.
    fn match_timestamp_ym(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            (Self::match_timestamp_year, Self::match_timestamp_month),
            ("T", Self::peek_stop_character),
        )
        .map(|(_year, _month)| MatchedTimestamp::new(TimestampPrecision::Month))
        .parse_next(self)
    }

    /// Matches a timestamp with day precision.
    fn match_timestamp_ymd(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            (
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
            ),
            (opt("T"), Self::peek_stop_character),
        )
        .map(|_| MatchedTimestamp::new(TimestampPrecision::Day))
        .parse_next(self)
    }

    /// Matches a timestamp with hour-and-minute precision.
    fn match_timestamp_ymd_hm(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            (
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
                Self::match_timestamp_hour_and_minute,
                Self::match_timestamp_offset,
            ),
            Self::peek_stop_character,
        )
        .map(|(_y, _m, _d, _hm, offset)| {
            MatchedTimestamp::new(TimestampPrecision::HourAndMinute).with_offset(offset)
        })
        .parse_next(self)
    }

    /// Matches a timestamp with second precision.
    fn match_timestamp_ymd_hms(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            (
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
                Self::match_timestamp_hour_and_minute,
                Self::match_timestamp_seconds,
                Self::match_timestamp_offset,
            ),
            Self::peek_stop_character,
        )
        .map(|(_y, _m, _d, _hm, _s, offset)| {
            MatchedTimestamp::new(TimestampPrecision::Second).with_offset(offset)
        })
        .parse_next(self)
    }

    /// Matches a timestamp with second precision, including a fractional seconds component.
    fn match_timestamp_ymd_hms_fractional(&mut self) -> IonParseResult<'top, MatchedTimestamp> {
        terminated(
            (
                Self::match_timestamp_year,
                Self::match_timestamp_month,
                Self::match_timestamp_day,
                Self::match_timestamp_hour_and_minute,
                Self::match_timestamp_seconds,
                Self::match_timestamp_fractional_seconds,
                Self::match_timestamp_offset,
            ),
            Self::peek_stop_character,
        )
        .map(|(_y, _m, _d, _hm, _s, _f, offset)| {
            MatchedTimestamp::new(TimestampPrecision::Second).with_offset(offset)
        })
        .parse_next(self)
    }

    /// Matches the year component of a timestamp.
    fn match_timestamp_year(&mut self) -> IonMatchResult<'top> {
        n_times(4, one_of(|c: u8| c.is_ascii_digit())).parse_next(self)
    }

    /// Matches the month component of a timestamp, including a leading `-`.
    fn match_timestamp_month(&mut self) -> IonMatchResult<'top> {
        preceded(
            "-",
            alt((("0", one_of(b"123456789")), ("1", one_of(b"012")))).take(),
        )
        .parse_next(self)
    }

    /// Matches the day component of a timestamp, including a leading `-`.
    fn match_timestamp_day(&mut self) -> IonMatchResult<'top> {
        preceded(
            "-",
            alt((
                (b"0", one_of(b"123456789")),
                // pair(one_of([b'1' as u8, b'2' as u8]), Self::match_any_digit),
                (one_of(b"12".as_slice()).take(), Self::match_any_digit),
                (b"3", one_of(b"01")),
            ))
            .take(),
        )
        .parse_next(self)
    }

    /// Matches a leading `T`, a two-digit hour component of a timestamp, a delimiting ':', and a
    /// two-digit minute component.
    fn match_timestamp_hour_and_minute(
        &mut self,
    ) -> IonParseResult<'top, (TextBuffer<'top>, TextBuffer<'top>)> {
        preceded(
            "T",
            separated_pair(
                // Hour
                alt((
                    (one_of(b"01").take(), Self::match_any_digit),
                    ("2", one_of(b"0123")),
                ))
                .take(),
                // Delimiter
                ":",
                // Minutes
                (one_of(b"012345"), Self::match_any_digit).take(),
            ),
        )
        .parse_next(self)
    }

    /// Matches a leading `:`, and any two-digit second component from `00` to `59` inclusive.
    fn match_timestamp_seconds(&mut self) -> IonMatchResult<'top> {
        preceded(":", (one_of(b"012345"), Self::match_any_digit).take()).parse_next(self)
    }

    /// Matches the fractional seconds component of a timestamp, including a leading `.`.
    fn match_timestamp_fractional_seconds(&mut self) -> IonMatchResult<'top> {
        preceded(".", digit1).parse_next(self)
    }

    /// Matches a timestamp offset of any format.
    fn match_timestamp_offset(&mut self) -> IonParseResult<'top, MatchedTimestampOffset> {
        alt((
            "Z".value(MatchedTimestampOffset::Zulu),
            "+00:00".value(MatchedTimestampOffset::Zulu),
            "-00:00".value(MatchedTimestampOffset::Unknown),
            (
                one_of(b"-+"),
                Self::match_timestamp_offset_hours_and_minutes,
            )
                .map(|(sign, (_hours, _minutes))| {
                    if sign == b'-' {
                        MatchedTimestampOffset::NegativeHoursAndMinutes
                    } else {
                        MatchedTimestampOffset::PositiveHoursAndMinutes
                    }
                }),
        ))
        .parse_next(self)
    }

    /// Matches a timestamp offset encoded as a two-digit hour, a delimiting `:`, and a two-digit
    /// minute.
    fn match_timestamp_offset_hours_and_minutes(&mut self) -> IonParseResult<'top, (Self, Self)> {
        separated_pair(
            // Hour
            alt((
                (one_of(b"01").take(), Self::match_any_digit),
                ("2", one_of(b"0123")),
            ))
            .take(),
            // Delimiter
            ":",
            // Minutes
            (one_of(b"012345"), Self::match_any_digit).take(),
        )
        .parse_next(self)
    }

    /// Matches a complete blob, including the opening `{{` and closing `}}`.
    pub fn match_blob(&mut self) -> IonParseResult<'top, MatchedBlob> {
        let initial_offset = self.offset();
        delimited(
            "{{",
            // Only whitespace (not comments) can appear within the blob
            Self::match_base64_content,
            (Self::match_whitespace0, "}}"),
        )
        .map(|base64_data| {
            MatchedBlob::new(base64_data.offset() - initial_offset, base64_data.len())
        })
        .parse_next(self)
    }

    /// Matches a clob of either short- or long-form syntax.
    pub fn match_clob(&mut self) -> IonParseResult<'top, MatchedClob> {
        delimited(
            "{{",
            preceded(
                Self::match_whitespace0,
                alt((
                    Self::match_short_clob_body.value(MatchedClob::Short),
                    Self::match_long_clob_body.value(MatchedClob::Long),
                )),
            ),
            preceded(Self::match_whitespace0, "}}"),
        )
        .parse_next(self)
    }

    /// Matches the body (inside the `{{` and `}}`) of a short-form clob.
    fn match_short_clob_body(&mut self) -> IonMatchResult<'top> {
        let (_matched_string, body) = Self::match_short_string.with_taken().parse_next(self)?;
        body.validate_clob_text()?;
        Ok(body)
    }

    /// Matches the body (inside the `{{` and `}}`) of a long-form clob.
    fn match_long_clob_body(&mut self) -> IonMatchResult<'top> {
        one_or_more(preceded(
            Self::match_whitespace0,
            Self::match_long_clob_body_segment,
        ))
        .take()
        .parse_next(self)
    }

    /// Matches a single segment of a long-form clob's content.
    fn match_long_clob_body_segment(&mut self) -> IonMatchResult<'top> {
        let (_matched_string, body) = Self::match_long_string_segment
            .with_taken()
            .parse_next(self)?;
        body.validate_clob_text()?;
        Ok(body)
    }

    /// Returns an error if the buffer contains any byte that is not legal inside a clob.
    fn validate_clob_text(&self) -> IonParseResult<'top, ()> {
        for byte in self.bytes().iter().copied() {
            if !Self::byte_is_legal_clob_ascii(byte) {
                let message = format!("found an illegal byte '{:0x}' in clob", byte);
                return self.invalid(message).context("reading a clob").cut();
            }
        }
        // Return success without consuming
        Ok(())
    }

    /// Returns `false` if the specified byte cannot appear unescaped in a clob.
    fn byte_is_legal_clob_ascii(b: u8) -> bool {
        // Depending on where you look in the spec and/or `ion-tests`, you'll find conflicting
        // information about which ASCII characters can appear unescaped in a clob. Some say
        // "characters >= 0x20", but that excludes lots of whitespace characters that are < 0x20.
        // Some say "displayable ASCII", but DEL (0x7F) is shown to be legal in one of the ion-tests.
        // The definition used here has largely been inferred from the contents of `ion-tests`.
        b.is_ascii() && (u32::from(b) >= 0x20 || WHITESPACE_BYTES.contains(&b))
    }
    /// Matches the base64 content within a blob. Ion allows the base64 content to be broken up with
    /// whitespace, so the matched input region may need to be stripped of whitespace before
    /// the data can be decoded.
    fn match_base64_content(&mut self) -> IonMatchResult<'top> {
        (
            zero_or_more((
                Self::match_whitespace0,
                alt((alphanumeric1, one_of(b"+/").take())),
            )),
            opt(preceded(Self::match_whitespace0, alt(("==", "=")))),
        )
            .take()
            .parse_next(self)
    }

    pub fn is_final_data(&self) -> bool {
        self.is_final_data
    }
}

pub trait IonParser<'top, O>: Parser<TextBuffer<'top>, O, IonParseError<'top>> {
    // No additional functionality, this is just a trait alias
}

impl<'top, Output, P> IonParser<'top, Output> for P where
    P: Parser<TextBuffer<'top>, Output, IonParseError<'top>>
{
}

impl SliceLen for TextBuffer<'_> {
    fn slice_len(&self) -> usize {
        self.len()
    }
}

impl<'data> Stream for TextBuffer<'data> {
    type Token = u8;
    type Slice = Self;
    type IterOffsets = <&'data [u8] as Stream>::IterOffsets;
    type Checkpoint = Self;

    fn iter_offsets(&self) -> Self::IterOffsets {
        self.bytes().iter_offsets()
    }

    fn eof_offset(&self) -> usize {
        self.bytes().eof_offset()
    }

    fn next_token(&mut self) -> Option<Self::Token> {
        let byte = *self.bytes().first()?;
        self.consume(1);
        Some(byte)
    }

    fn offset_for<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Token) -> bool,
    {
        self.bytes().offset_for(predicate)
    }

    fn offset_at(&self, tokens: usize) -> Result<usize, Needed> {
        self.bytes().offset_at(tokens)
    }

    fn next_slice(&mut self, offset: usize) -> Self::Slice {
        let head = self.slice(0, offset);
        self.consume(offset);
        head
    }

    fn checkpoint(&self) -> Self::Checkpoint {
        *self
    }

    fn reset(&mut self, checkpoint: &Self::Checkpoint) {
        #[cfg(feature = "source-location")]
        let (current_row, prev_column_value) = (self.row, self.prev_newline_offset);

        *self = *checkpoint;

        #[cfg(feature = "source-location")]
        {
            self.row = current_row;
            self.prev_newline_offset = prev_column_value;
        }
    }

    fn raw(&self) -> &dyn Debug {
        &self.input_span
    }
}

impl StreamIsPartial for TextBuffer<'_> {
    type PartialState = ();

    fn complete(&mut self) -> Self::PartialState {}

    fn restore_partial(&mut self, _state: Self::PartialState) {
        // No-op.
    }

    fn is_partial_supported() -> bool {
        true
    }

    fn is_partial(&self) -> bool {
        !self.is_final_data
    }
}

impl<'a> winnow::stream::Compare<&'a str> for TextBuffer<'_> {
    fn compare(&self, t: &'a str) -> CompareResult {
        self.bytes().compare(t.as_bytes())
    }
}

impl<'a> winnow::stream::Compare<&'a [u8]> for TextBuffer<'_> {
    fn compare(&self, t: &'a [u8]) -> CompareResult {
        self.bytes().compare(t)
    }
}

impl<'a, const N: usize> winnow::stream::Compare<&'a [u8; N]> for TextBuffer<'_> {
    fn compare(&self, t: &'a [u8; N]) -> CompareResult {
        self.bytes().compare(t.as_slice())
    }
}

impl winnow::stream::Offset for TextBuffer<'_> {
    fn offset_from(&self, start: &Self) -> usize {
        self.offset() - start.offset()
    }
}

impl FindSlice<&str> for TextBuffer<'_> {
    fn find_slice(&self, substr: &str) -> Option<Range<usize>> {
        self.bytes().find_slice(substr)
    }
}

impl Location for TextBuffer<'_> {
    fn location(&self) -> usize {
        self.offset()
    }
}

/// Takes a given parser and returns a new one that accepts any amount of leading whitespace before
/// calling the original parser.
pub fn whitespace_and_then<'data, P, Output>(
    parser: P,
) -> impl Parser<TextBuffer<'data>, Output, IonParseError<'data>>
where
    P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
{
    preceded(TextBuffer::match_optional_comments_and_whitespace, parser)
}

pub fn zero_or_more<'data, P, Output>(
    parser: P,
) -> impl Parser<TextBuffer<'data>, TextBuffer<'data>, IonParseError<'data>>
where
    P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
{
    repeat::<_, _, (), _, _>(.., parser).take()
}

pub fn one_or_more<'data, P, Output>(
    parser: P,
) -> impl Parser<TextBuffer<'data>, TextBuffer<'data>, IonParseError<'data>>
where
    P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
{
    repeat::<_, _, (), _, _>(1.., parser).take()
}

pub fn n_times<'data, P, Output>(
    n: usize,
    parser: P,
) -> impl Parser<TextBuffer<'data>, TextBuffer<'data>, IonParseError<'data>>
where
    P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
{
    repeat::<_, _, (), _, _>(n, parser).take()
}

pub fn incomplete_is_ok<'data, P>(
    parser: P,
) -> impl Parser<TextBuffer<'data>, TextBuffer<'data>, IonParseError<'data>>
where
    P: Parser<TextBuffer<'data>, TextBuffer<'data>, IonParseError<'data>>,
{
    // If we run out of input while applying the parser, consider the rest of the input to match.
    alt((parser.complete_err(), rest))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::any_encoding::IonVersion;
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::template::{ParameterCardinality, ParameterEncoding};
    use crate::lazy::expanded::EncodingContext;
    use crate::{AnyEncoding, Reader};
    use rstest::rstest;

    /// Returns a parser that discards the output and instead reports the number of bytes that matched.
    fn match_length<'data, P, Output>(
        parser: P,
    ) -> impl Parser<TextBuffer<'data>, usize, IonParseError<'data>>
    where
        P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
    {
        parser
            .with_span()
            .map(|(_output, match_range)| match_range.len())
    }

    /// Stores an input string that can be tested against a given parser.
    struct MatchTest {
        input: String,
        context: EncodingContext,
    }

    impl MatchTest {
        /// Takes an `input` string and appends a trailing value to it, guaranteeing that the
        /// contents of the input are considered a complete token.
        fn new(input: &str) -> Self {
            MatchTest {
                input: input.to_string(),
                context: EncodingContext::for_ion_version(IonVersion::v1_1),
            }
        }

        fn new_1_0(input: &str) -> Self {
            MatchTest {
                input: input.to_string(),
                context: EncodingContext::for_ion_version(IonVersion::v1_0),
            }
        }

        fn register_macro(&mut self, text: &str) -> &mut Self {
            let new_macro =
                TemplateCompiler::compile_from_source(self.context.macro_table(), text).unwrap();
            self.context
                .macro_table_mut()
                .add_template_macro(new_macro)
                .unwrap();
            self
        }

        fn try_match<'data, P, Output>(
            &'data self,
            parser: P,
        ) -> IonParseResult<'data, (TextBuffer<'data>, usize)>
        where
            P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
        {
            let mut buffer = TextBuffer::new(self.context.get_ref(), self.input.as_bytes());
            let matched_length = match_length(parser).parse_next(&mut buffer)?;
            Ok((buffer, matched_length))
        }

        fn expect_match<'data, P, Output>(&'data self, parser: P)
        where
            P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
        {
            let result = self.try_match(parser).unwrap_or_else(|e| {
                panic!("Unexpected parse fail for input <{}>\n{e}", self.input)
            });
            let match_length = result.1;
            // Inputs have a trailing newline and `0` that should _not_ be part of the match
            assert_eq!(
                match_length,
                self.input.len(),
                "\nInput: '{}'\nMatched: '{}'\n",
                self.input,
                &self.input[..match_length]
            );
        }

        #[cfg(feature = "source-location")]
        fn expect_match_location<'data, P, O>(
            &'data self,
            parser: P,
            expected_location: (usize, usize),
        ) where
            P: Parser<TextBuffer<'data>, O, IonParseError<'data>>,
        {
            let result = self.try_match(parser).unwrap_or_else(|e| {
                panic!("Unexpected parse fail for input <{}>\n{e}", self.input)
            });
            let match_length = result.1;
            // Inputs have a trailing newline and `0` that should _not_ be part of the match
            assert_eq!(
                match_length,
                self.input.len(),
                "\nInput: '{}'\nMatched: '{}'\n",
                self.input,
                &self.input[..match_length]
            );

            // Assert the location metadata
            assert_eq!(expected_location, (result.0.row(), result.0.column()));
        }

        fn expect_mismatch<'data, P, Output>(&'data self, parser: P)
        where
            P: Parser<TextBuffer<'data>, Output, IonParseError<'data>>,
        {
            let result = self.try_match(parser);
            // We expect that only part of the input will match or that the entire
            // input will be rejected outright.

            match result {
                Ok((_, match_length)) => {
                    assert_ne!(
                        match_length,
                        self.input.len(),
                        "parser unexpectedly matched the complete input: {:?}\nResult: {:?}",
                        self.input,
                        result
                    );
                }
                Err(e) if e.is_incomplete() => {
                    panic!(
                        "parser reported an incomplete match rather than a mismatch: {}",
                        self.input
                    )
                }
                Err(_) => {}
            }
        }
    }

    /// A macro to concisely define basic test cases for matchers.
    /// Suitable when the input strings can be trimmed.
    macro_rules! matcher_tests {
        ($parser:ident $($expect:ident: [$($input:literal),+$(,)?]),+$(,)?) => {
            matcher_tests!($parser => TextBuffer::$parser, $($expect: [$($input),+]),+,);
        };
        ($mod_name:ident => $parser:expr, $($expect:ident: [$($input:literal),+$(,)?]),+$(,)?) => {
            mod $mod_name {
                use super::*;
                $(
                #[test]
                fn $expect() {
                    $(MatchTest::new_1_0($input.trim()).$expect(match_length($parser) );)
                    +
                }
                )+
            }
        }
    }

    macro_rules! matcher_tests_with_macro {
        ($mod_name:ident => $parser:expr, $macro_src:literal $($expect:ident: [$($input:literal),+$(,)?]),+$(,)?) => {
            mod $mod_name {
                use super::*;
                $(
                #[test]
                fn $expect() {
                    $(MatchTest::new($input.trim()).register_macro($macro_src).$expect(match_length($parser));)
                    +
                }
                )+
            }
        };
    }

    #[test]
    fn test_match_stop_char() {
        MatchTest::new(" ").expect_match(match_length(TextBuffer::match_stop_character));
        MatchTest::new("").expect_match(match_length(TextBuffer::match_stop_character));
    }

    #[test]
    fn test_match_ivm() {
        fn match_ivm(input: &str) {
            MatchTest::new(input)
                .expect_match(match_length(TextBuffer::match_ivm::<TextEncoding_1_0>));
        }
        fn mismatch_ivm(input: &str) {
            MatchTest::new(input)
                .expect_mismatch(match_length(TextBuffer::match_ivm::<TextEncoding_1_1>));
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

    matcher_tests! {
        match_bool
        expect_match: [
            "true",
            "false"
        ],
        expect_mismatch: [
            "True",
            "tru",
            "TRUE",
            "False",
            "FALSE",
            "fals",
            "potato",
            "42"
        ],
    }

    matcher_tests! {
        match_null
        expect_match:[
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
        ],
        expect_mismatch: [
            "-1",
            "null.hello",
            "nullnull",
            "nullify",
            "null..int",
            "string.null",
            "null.timestam",
            "null.strin",
            "null.nul"
        ],
    }

    matcher_tests! {
        match_int
        expect_match: [
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
        ],
        expect_mismatch: [
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
        ],
    }

    matcher_tests! {
        match_float
        expect_match: [
            "0.0e0", "0E0", "0e0", "305e1", "305e+1", "305e-1", "305e100", "305e-100", "305e+100",
            "305.0e1", "0.279e3", "0.279e-3", "279e0", "279.5e0", "279.5E0",
        ],
        expect_mismatch: [
            "305",      // Integer
            ".305e",    // No digits before the decimal point
            "305e0.5",  // Fractional exponent
            "305e-0.5", // Negative fractional exponent
            "0305e1",   // Leading zero
            "+305e1",   // Leading plus sign
            "--305e1",  // Multiple negative signs
            "305e",     // Has exponent delimiter but no exponent
        ]
    }

    matcher_tests! {
        match_timestamp
        expect_match: [
            "2023T",
            "2023-08T",
            "2023-08-13", // T is optional for ymd
            "2023-08-13T",
            "2023-08-13T14:18Z",
            "2023-08-13T14:18+05:00",
            "2023-08-13T14:18-05:00",
            "2023-08-13T14:18:35-05:00",
            "2023-08-13T14:18:35.994-05:00",
        ],
        expect_mismatch: [
            "20233T",                        // 5-digit year
            "2023-13T",                      // Out of bounds month
            "2023-08-41T",                   // Out of bounds day
            "2023-08+18T",                   // Wrong delimiter
            "2023-08-18T25:00Z",             // Out of bounds hour
            "2023-08-18T14:62",              // Out of bounds minute
            "2023-08-18T14:35:61",           // Out of bounds second
            "2023-08-18T14:35:52.Z",         // Dot but no fractional
            "2023-08-18T14:35:52.000+24:30", // Out of bounds offset hour
            "2023-08-18T14:35:52.000+00:60", // Out of bounds offset minute
            "2023",                          // No 'T'; it's an int
            "2023-08",                       // No 'T'; it's incomplete
            "2023-08-18T14:00",              // No offset
        ]
    }

    matcher_tests! {
        match_string
        expect_match: [
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
        ],
        expect_mismatch: [
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
        ],
    }

    matcher_tests! {
        match_symbol
        expect_match: [
            "''",
            "'hello'",
            "'😀😀😀'",
            "'this has an escaped quote \\' right in the middle'",
            "$308",
            "$0",
            "foo",
            "name",
            "$bar",
            "_baz_quux",
        ],
        expect_mismatch: [
            "$-8",       // Negative SID
            "'hello",    // No closing quote
            "'hello\\'", // Closing quote is escaped
        ],
    }

    matcher_tests! {
        match_annotated_value => TextBuffer::match_annotated_value::<TextEncoding_1_1>,
        expect_match: [
            "foo::5",
            "foo::bar::5",
            "foo :: 5",
            "foo::bar::baz::5",
            "foo :: /*comment*/ bar /*comment*/    :: baz :: 5",
            "foo::bar::baz::quux::quuz::5",
            "foo::'bar'::baz::$10::5",
        ],
        expect_mismatch: ["foo::", "foo:bar", "foo:::bar"],
    }

    matcher_tests! {
        match_decimal
        expect_match: [
            "5.", "-5.", "5.0", "-5.0", "5d0", "5.d0", "5.0d0", "-5.0d0", "5.0D0", "-5.0D0",
            "5.0d+1", "-5.0d-1",
        ],
        expect_mismatch: [
            "123._456", "5", "05d", "-5.0+0",
            "5d",
            "-5d",
            "5.d",
            "-5.d",
            "5.D",
            "-5.D",
            "5.1d", "-5.1d",
            "5.1D", "-5.1D",
        ]
    }

    matcher_tests! {
        match_sexp_1_0 => TextEncoding_1_0::sexp_matcher(),
        expect_match: [
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
        ],
        expect_mismatch: ["foo", "1", "(", "(1 2 (3 4 5)"]
    }

    matcher_tests_with_macro! {
        parsing_sexps => TextEncoding_1_1::sexp_matcher(),
        "(macro foo (x*) null)"
        expect_match: [
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
        ],
        expect_mismatch: ["foo", "1", "(", "(1 2 (3 4 5)"]
    }

    matcher_tests! {
        match_list_1_0 => TextEncoding_1_0::list_matcher(),
        expect_match: [
            "[]", "[1]", "[1, 2]", "[[]]", "[([])]",
        ],
        expect_mismatch: [
            "foo",
            "1",
            "[",
            "[1, 2, [3, 4]",
        ]
    }

    matcher_tests_with_macro! {
        match_list_1_1 => TextEncoding_1_1::list_matcher(),
        "(macro foo (x*) null)"
        expect_match: [
            "[]", "[1]", "[1, 2]", "[[]]", "[([])]", "[1, (:foo 2 3)]"
        ],
        expect_mismatch: [
            "foo", "1",
            "[", "[1, 2, [3, 4]"
        ]
    }

    matcher_tests! {
        match_struct_1_0 => TextEncoding_1_0::struct_matcher(),
        expect_match: [
            "{}",
            "{$0:$0}",
            "{'':''}",
            r#"{"":""}"#,
            "{foo:bar}",
            "{foo: bar, baz: quux}",
            "{'foo': bar, 'baz': quux}",
            r#"{foo: bar, "baz": quux}"#,
            r#"{'foo': bar, "baz": quux}"#,
            "{_:_}",
            "{foo: [1, 2, 3]}",
            "{foo: foo, foo: foo}",
            "{foo: foo::foo::foo, foo: foo::foo}"
        ],
        expect_mismatch: [
            "{", "{foo: bar",
            "{1: bar}",
            "{foo: bar baz: quux}",
            "{foo: bar,, baz: quux}",
            "{foo:: bar, baz: quux}",
            "{, foo: bar, baz: quux}",
            "{,}"
        ]
    }

    matcher_tests_with_macro! {
        match_struct_1_1 => TextEncoding_1_1::struct_matcher(),
        "(macro foo (x*) {quux: quuz})"
        expect_match: [
            "{}", "{$0:$0}", "{'':''}", r#"{"":""}"#, "{foo:bar}",
            "{foo: bar, baz: quux}", "{'foo': bar, 'baz': quux}",
            r#"{foo: bar, "baz": quux}"#, r#"{'foo': bar, "baz": quux}"#,
            "{_:_}", "{foo: [1, 2, 3]}", "{foo: foo, foo: foo}",
            "{a: (:foo 1 2 3)}",
            // With e-expressions
            "{(:foo)}",
            "{ (:foo)}",
            "{(:foo) }",
            "{(:foo), (:foo)}",
            "{   (:foo)   ,   (:foo)   }",
            "{ a : (:foo 1 2 3) , b : (:foo 4 5 6) }",
            "{a:(:foo 1 2 3),b:(:foo 4 5 6)}",  "{(:foo), (:foo)}",
            "{a: (:foo 1 2 3), b: (:foo 4 5 6)}"
        ],
        expect_mismatch: [
            "{", "{foo: bar",
            "{1: bar}",
            "{foo: bar baz: quux}",
            "{foo: bar,, baz: quux}",
            "{foo:: bar, baz: quux}",
            "{, foo: bar, baz: quux}",
            "{,}",
            "{(:foo}",
            "{(:foo]}",
            "{[:foo}",
            "{(foo)}",
            "{(:foo): bar}",
            "{bar: (:foo}",
            "{bar: (:foo) baz: quux}",
        ]
    }

    matcher_tests_with_macro! {
        parsing_eexps => TextBuffer::match_e_expression,
        "(macro foo (x*) null)"
        expect_match: [
            "(:foo)",
            "(:foo 1)",
            "(:foo 1 2 3)",
            "(:foo (1 2 3))",
            "(:foo \"foo\")",
            "(:foo foo)",
            "(:5)",
            "(:5 1)",
            "(:5 1 2 3)",
            "(:5 (1 2 3))",
            "(:5 \"foo\")",
            "(:5 foo)",
            "(:005 foo)", // Leading zeros are ok/ignored
        ],
        expect_mismatch: [
            "foo",   // No parens
            "(foo)", // No `:` after opening paren
            "(5",    // No parens
            "(5)",   // No `:` after opening paren
            "(:0x5)",   // Hexadecimal not allowed
            "(:5_000)", // Underscores not allowed
            "(:foo", // Incomplete
            "(:5"    // Incomplete
        ]
    }

    matcher_tests_with_macro! {
        allow_omitting_trailing_optionals => TextBuffer::match_e_expression,
        "(macro foo (a b+ c? d*) null)"
        expect_match: [
            "(:foo 1 2)",
            "(:foo 1 2 3)",
            "(:foo 1 2 3 4)",
            "(:foo 1 2 3 4 5 6)", // implicit rest
            "(:foo 1 2 3 (::))",   // explicit empty stream
            "(:foo 1 2 (::) 4)",
            "(:foo 1 2 (::) (::))",
        ],
        expect_mismatch: [
            "(:foo 1)",
            "(:foo)",
        ]
    }

    #[rstest]
    #[case::empty("(::)")]
    #[case::empty_with_extra_spacing("(:: )")]
    #[case::single_value("(:: 1)")]
    #[case::multiple_values("(:: 1 2 3)")]
    #[case::eexp("(::foo 1 2 3)")]
    #[case::eexp_with_sexp("(::(foo 1 2 3))")]
    #[case::eexp_with_mixed_values("(:: 1 2 3 {quux: [1, 2, 3]} 4 bar::5 baz::6)")]
    fn match_eexp_arg_group(#[case] input: &str) {
        let parameter = Parameter::new(
            "x",
            ParameterEncoding::Tagged,
            ParameterCardinality::ZeroOrMore,
            RestSyntaxPolicy::NotAllowed,
        );
        MatchTest::new(input)
            .register_macro("(macro foo (x*) null)")
            .expect_match(match_length(TextBuffer::parser_with_arg(
                TextBuffer::match_explicit_arg_group,
                &parameter,
            )))
    }

    #[rstest]
    #[case::simple_e_exp("(:foo)")]
    #[case::e_exp_in_e_exp("(:foo (bar 1))")]
    #[case::e_exp_in_list("[a, b, (:foo 1)]")]
    #[case::e_exp_in_sexp("(a (:foo 1) c)")]
    #[case::e_exp_in_struct_field("{a:(:foo)}")]
    #[case::e_exp_in_struct_field_with_comma("{a:(:foo),}")]
    #[case::e_exp_in_struct_field_with_comma_and_second_field("{a:(:foo), b:2}")]
    #[case::e_exp_in_struct_field_with_space_before("{ a:(:foo)}")]
    #[case::e_exp_in_struct_field_with_space_after("{a:(:foo) }")]
    #[case::e_exp_in_list_in_struct_field("{ a: [(:foo)] }")]
    #[case::e_exp_in_sexp_in_struct_field("{ a: ((:foo)) }")]
    #[case::e_exp_in_sexp_in_list("[a, b, ((:foo 1))]")]
    #[case::e_exp_in_sexp_in_sexp("(a ((:foo 1)) c)")]
    #[case::e_exp_in_list_in_list("[a, b, [(:foo 1)]]")]
    #[case::e_exp_in_list_in_sexp("(a [(:foo 1)] c)")]
    fn test_match_macro_invocation_in_context(#[case] input: &str) {
        MatchTest::new(input)
            .register_macro("(macro foo (x*) null)")
            .expect_match(match_length(TextBuffer::match_top_level_item_1_1));
    }

    matcher_tests! {
        match_blob
        expect_match: [
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
        ],
        expect_mismatch: [
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
            "{{aGVsbG8h",
            "{{aGVsbG8h}"
        ]
    }

    matcher_tests! {
        match_clob
        expect_match: [
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
        ],
        expect_mismatch: [
            r#"{{foo}}"#,                         // No quotes
            r#"{{'''foo''' /*hi!*/ '''bar'''}}"#, // Interleaved comments
            r#"{{'''foo''' "bar"}}"#,             // Mixed quote style
            r#"{{"😎🙂🙃"}}"#,                    // Contains unescaped non-ascii characters
            r#"{{"foo}}"#,     // Missing closing quote
            r#"{{"foo"}"#,     // Missing closing brace
            r#"{{'''foo'''}"#, // Missing closing brace
        ],
    }

    #[test]
    fn test_match_text_until_unescaped_str() {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let mut input = TextBuffer::new(context, r" foo bar \''' baz''' quux ".as_bytes());
        let (matched, contains_escapes) = input.match_text_until_unescaped_str(r#"'''"#).unwrap();
        assert_eq!(matched.as_text().unwrap(), " foo bar \\''' baz");
        assert!(contains_escapes);
    }

    #[rstest]
    #[case::no_whitespace("", (1,1))]
    #[case::no_crlf_1("\t", (1,2))]
    #[case::no_crlf_2("\t\t", (1,3))]
    #[case::cr("\r", (2,1))]
    #[case::lf("\n", (2,1))]
    // all combinations of 3 newline bytes; check number of rows
    #[case::lf_3("\n\n\n", (4,1))]
    #[case::lf_lf_cr("\n\n\r", (4,1))]
    #[case::lf_cr_lf("\n\r\n", (3,1))]
    #[case::lf_cr_cr("\n\r\r", (4,1))]
    #[case::cr_lf_lf("\r\n\n", (3,1))]
    #[case::cr_lf_cr("\r\n\r", (3,1))]
    #[case::cr_cr_lf("\r\r\n", (3,1))]
    #[case::cr_3("\r\r\r", (4,1))]
    #[case::newlines("\n\r", (3,1))]
    #[case::crlf("\r\n\r\n", (3,1))]
    #[case::mixed("\r\n\n\r\n", (4,1))]
    // tabs before newline does not affect column count
    #[case::tabs_before_newline_1("\t\t\t\n", (2,1))]
    #[case::tabs_before_newline_2("\n\t\n", (3,1))]
    // tabs after newline affects the column count
    #[case::tabs_after_newline_1("\n\t\t\t", (2,4))]
    #[case::tabs_after_newline_2("\t\n\t\t", (2,3))]
    #[case::tabs_after_newline_3("\n\t\n\t", (3,2))]
    #[case::mix_tabs_and_newlines("\n\t\n", (3,1))]
    #[cfg(feature = "source-location")]
    fn expect_whitespace(#[case] input: &str, #[case] expected_location: (usize, usize)) {
        MatchTest::new_1_0(input).expect_match_location(
            match_length(TextBuffer::match_whitespace0),
            expected_location,
        );
    }

    #[rstest]
    #[case::empty_input("", (1,1))]
    #[case::inline_comment("//comment", (1,10))]
    #[case::newline_before_inline_comment("\n//comment", (2,10))]
    #[case::newline_after_inline_comment("//comment\n", (2,1))]
    #[case::two_inline_comments("//comment\n//comment", (2,10))]
    #[case::comment("/*comment*/", (1,12))]
    #[case::newline_before_comment("\n/*comment*/", (2,12))]
    #[case::newline_after_comment("/*comment*/\n", (2,1))]
    #[case::newline_inside_comment("/*multiline \n comment*/", (2,11))]
    #[case::newlines_inside_comment("/*this is a \n multiline \n comment*/", (3,11))]
    #[cfg(feature = "source-location")]
    fn expect_whitespace_with_comment(
        #[case] input: &str,
        #[case] expected_location: (usize, usize),
    ) {
        MatchTest::new_1_0(input).expect_match_location(
            match_length(TextBuffer::match_optional_comments_and_whitespace),
            expected_location,
        );
    }

    #[rstest]
    #[case::single_segment_empty("''''''", (1, 7))]
    #[case::single_segment_with_newlines("'''\n\n\r\n'''", (4, 4))]
    #[case::single_segment_long_string("'''long string'''", (1, 18))]
    #[case::single_segment_with_tabs("'''long\tstring'''", (1, 18))]
    #[case::two_segment_long_string("'''long''' '''string'''", (1, 24))]
    #[case::two_segment_with_newline_between("'''long''' \n '''string'''", (2, 14))]
    #[case::two_segment_with_newlines("'''long\n''' '''string\n'''", (3, 4))]
    #[case::two_segment_long_string_mixed("'''long\n''' \n '''string\n'''", (4, 4))]
    #[case::single_segment_with_whitespace("'''long \n\r\n\t hello'''", (3, 11))]
    #[cfg(feature = "source-location")]
    fn expect_newline_long_text(#[case] input: &str, #[case] expected_location: (usize, usize)) {
        MatchTest::new_1_0(input)
            .expect_match_location(match_length(TextBuffer::match_string), expected_location);
    }

    #[test]
    fn expect_foo() {
        MatchTest::new_1_0("\"hello\"").expect_match(match_length(TextBuffer::match_string));
    }

    #[test]
    fn expect_long_foo() {
        MatchTest::new_1_0("'''long hello'''").expect_match(match_length(TextBuffer::match_string));
    }

    #[test]
    fn expect_bootstrap() -> IonResult<()> {
        // MatchTest::new("\"foo\"").expect_match(match_length(TextBuffer::match_string));
        let mut reader = Reader::new(AnyEncoding, "()")?;
        let value = reader.expect_next()?;
        let _ = value.read()?.expect_sexp().unwrap();
        Ok(())
    }

    #[test]
    fn expect_clob() {
        MatchTest::new_1_0(r#"{{''''''}}"#).expect_match(match_length(TextBuffer::match_clob));
    }
}
