use std::fmt::{Debug, Formatter};
use std::iter::{Copied, Enumerate};
use std::ops::{RangeFrom, RangeTo};
use std::slice::Iter;

use nom::branch::alt;
use nom::bytes::streaming::{is_a, is_not, tag, take_until, take_while1};
use nom::character::streaming::{char, digit1, one_of};
use nom::combinator::{fail, map, opt, peek, recognize, success, value};
use nom::error::{ErrorKind, ParseError};
use nom::multi::many0_count;
use nom::sequence::{delimited, pair, preceded, separated_pair, terminated, tuple};
use nom::{CompareResult, IResult, InputLength, InputTake, Needed, Parser};

use crate::lazy::encoding::TextEncoding;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::{
    MatchedFloat, MatchedInt, MatchedShortString, MatchedString, MatchedValue,
};
use crate::lazy::text::parse_result::IonParseError;
use crate::lazy::text::parse_result::{IonMatchResult, IonParseResult};
use crate::lazy::text::value::LazyRawTextValue;
use crate::result::DecodingError;
use crate::{IonError, IonResult, IonType};

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

    /// Matches a single top-level scalar value, the beginning of a container, or an IVM.
    pub fn match_top_level(self) -> IonParseResult<'data, RawStreamItem<'data, TextEncoding>> {
        let (remaining, value) = match self.match_value() {
            Ok(value) => value,
            Err(e) => return Err(e),
        };

        // TODO: Augment this method to take an `is_complete` flag that indicates whether the absence
        //       of further values should return an `Incomplete` or a `RawStreamItem::EndOfStream`.

        // TODO: Check to see if `value` is actually an IVM.
        //       => If it's a symbol, try the IVM parser on it and see if it succeeds.
        //       For now, we just return the value.
        Ok((remaining, RawStreamItem::Value(value)))
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
                match_and_length(Self::match_string),
                |(matched_string, length)| {
                    EncodedTextValue::new(
                        MatchedValue::String(matched_string),
                        self.offset(),
                        length,
                    )
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
                MatchedString::Short(MatchedShortString::new(contains_escaped_chars))
            })
            .parse(self)
    }

    /// Returns a matched buffer and a boolean indicating whether any escaped characters were
    /// found in the short string.
    fn match_short_string_body(self) -> IonParseResult<'data, (Self, bool)> {
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
            if *byte == b'\"' {
                let matched = self.slice(0, index);
                let remaining = self.slice_to_end(index);
                return Ok((remaining, (matched, contains_escaped_chars)));
            }
        }
        Err(nom::Err::Incomplete(Needed::Unknown))
    }

    fn match_long_string(self) -> IonParseResult<'data, MatchedString> {
        // TODO: implement long string matching
        //       The `fail` parser is a nom builtin that never matches.
        fail(self)
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
            // We expect this to fail for one reason or another
            assert!(
                result.is_err(),
                "Expected a parse failure for input: {:?}\nResult: {:?}",
                self.input,
                result
            );
        }
    }

    #[test]
    fn test_match_stop_char() {
        MatchTest::new(" ").expect_match(match_length(TextBufferView::match_stop_character));
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
            // Missing a trailing quote
            r#"
            "hello
            "#,
        ];
        for input in bad_inputs {
            mismatch_string(input);
        }
    }
}
