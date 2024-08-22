//! Types in this module represent partially parsed values from the text Ion input stream.
//!
//! Ion readers are not necessarily interested in every value in the input. While the binary reader
//! is able to skip over uninteresting values using their length prefix, text readers must parse
//! every value in the stream in order to access the ones that follow.
//!
//! A somewhat naive implementation of a text reader might fully read each value in the input
//! stream eagerly, simply discarding values that the user doesn't request. This approach is
//! technically correct, but incurs the expense of validating and materializing data that will
//! ultimately be ignored. (As an example: consider a timestamp, which can have up to ~9 subfields
//! to check for syntactic and semantic correctness.)
//!
//! In contrast, when the lazy text reader is asked for the `next()` value in the stream, it uses its
//! Ion parser to identify the next slice of input that contains either a complete scalar value or
//! the beginning of a container. It stores an intermediate representation (IR) of that value using
//! one of the types defined in this module. The IR stores the value's Ion type, subfield offsets,
//! and other information that is identified in the process of parsing the next value. Later, if the
//! application asks to `read()` the value, the reader does not have to start from scratch. It can
//! use the previously recorded information to minimize the amount of information that needs to be
//! re-discovered.

use std::num::IntErrorKind;
use std::ops::{Neg, Range};
use std::str::FromStr;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use ice_code::ice as cold_path;
use nom::branch::alt;
use nom::bytes::streaming::tag;
use nom::character::is_hex_digit;
use nom::sequence::preceded;
use nom::{AsBytes, AsChar, Parser};
use num_traits::Zero;
use smallvec::SmallVec;

use crate::decimal::coefficient::Coefficient;
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{Decoder, LazyRawFieldExpr, LazyRawValueExpr};
use crate::lazy::span::Span;
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::as_utf8::AsUtf8;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::InvalidInputError;
use crate::result::{DecodingError, IonFailure};
use crate::{
    Decimal, Int, IonError, IonResult, IonType, RawSymbolRef, Timestamp, TimestampPrecision,
};

/// A partially parsed Ion value.
#[derive(Clone, Copy, Debug)]
pub enum MatchedValue<'top, D: Decoder> {
    // `Null` and `Bool` are fully parsed because they only involve matching a keyword.
    Null(IonType),
    Bool(bool),
    Int(MatchedInt),
    Float(MatchedFloat),
    Decimal(MatchedDecimal),
    Timestamp(MatchedTimestamp),
    String(MatchedString),
    Symbol(MatchedSymbol),
    Blob(MatchedBlob),
    Clob(MatchedClob),
    List(&'top [LazyRawValueExpr<'top, D>]),
    SExp(&'top [LazyRawValueExpr<'top, D>]),
    Struct(&'top [LazyRawFieldExpr<'top, D>]),
}

impl<'top, D: Decoder> PartialEq for MatchedValue<'top, D> {
    fn eq(&self, other: &Self) -> bool {
        use MatchedValue::*;
        match (self, other) {
            (Null(n1), Null(n2)) => n1 == n2,
            (Bool(b1), Bool(b2)) => b1 == b2,
            (Int(i1), Int(i2)) => i1 == i2,
            (Float(f1), Float(f2)) => f1 == f2,
            (Decimal(d1), Decimal(d2)) => d1 == d2,
            (Timestamp(t1), Timestamp(t2)) => t1 == t2,
            (String(s1), String(s2)) => s1 == s2,
            (Symbol(s1), Symbol(s2)) => s1 == s2,
            (Blob(b1), Blob(b2)) => b1 == b2,
            (Clob(c1), Clob(c2)) => c1 == c2,
            // The container variants hold raw representations of the containers themselves.
            // We cannot compare their equality without recursively reading those containers,
            // which introduces many opportunities to encounter an error that this method cannot
            // surface. Because this is `PartialEq`, we have the option of returning `false` for
            // values that cannot be compared to one another.
            _ => false,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum MatchedFieldNameSyntax {
    Symbol(MatchedSymbol),
    String(MatchedString),
}

impl MatchedFieldNameSyntax {
    pub fn read<'data>(
        &self,
        // TODO: Remove allocator, use the one in TBV
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolRef<'data>> {
        match self {
            MatchedFieldNameSyntax::Symbol(matched_symbol) => {
                matched_symbol.read(allocator, matched_input)
            }
            MatchedFieldNameSyntax::String(matched_string) => matched_string
                .read(allocator, matched_input)
                .map(|s| s.into()),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct MatchedFieldName<'top> {
    // This is stored as a tuple to allow this type to be `Copy`; Range<usize> is not `Copy`.
    input: TextBufferView<'top>,
    syntax: MatchedFieldNameSyntax,
}

impl<'top> MatchedFieldName<'top> {
    pub fn new(input: TextBufferView<'top>, syntax: MatchedFieldNameSyntax) -> Self {
        Self { input, syntax }
    }

    pub fn syntax(&self) -> MatchedFieldNameSyntax {
        self.syntax
    }

    pub fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        self.syntax.read(self.input.context.allocator(), self.input)
    }

    pub fn range(&self) -> Range<usize> {
        self.input.range()
    }

    pub fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

/// A partially parsed Ion int.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct MatchedInt {
    radix: u8, // Can only be 2, 10, or 16
    // Offset of the digits from the beginning of the value
    digits_offset: u8,
    is_negative: bool,
}

impl MatchedInt {
    // Integers that take more than 32 bytes to represent will heap allocate a larger buffer.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 32;

    /// Constructs a new `MatchedInt`.
    pub fn new(radix: u8, is_negative: bool, digits_offset: usize) -> Self {
        debug_assert!(
            digits_offset < u8::MAX as usize,
            "digits offset can only be 0-3 to accommodate a sign and/or leading radix like `0x`"
        );
        Self {
            radix,
            digits_offset: digits_offset as u8,
            is_negative,
        }
    }

    /// Whether the partially parsed int began with a `-`
    pub fn is_negative(&self) -> bool {
        self.is_negative
    }

    /// One of: `2`, `10`, or `16`, as determined by whether the partially parsed integer began
    /// with a `0b`/`0B`, `0x`/`0X`, or no prefix.
    pub fn radix(&self) -> u32 {
        self.radix as u32
    }

    /// Attempts to finish reading the partially parsed integer.
    pub fn read(&self, matched_input: TextBufferView) -> IonResult<Int> {
        let digits = matched_input.slice_to_end(self.digits_offset as usize);
        let mut sanitized: SmallVec<[u8; Self::STACK_ALLOC_BUFFER_CAPACITY]> =
            SmallVec::with_capacity(Self::STACK_ALLOC_BUFFER_CAPACITY);
        // Copy the input text over to the sanitization buffer, discarding any underscores. These
        // are legal input, but Rust's integer `from_str_radix` method does not support them.
        sanitized.extend(digits.bytes().iter().copied().filter(|b| *b != b'_'));
        // Note: This UTF-8 validation step should be unnecessary as the parser only recognizes
        //       ASCII integer characters. If this shows up in profiling, we could consider skipping it.
        let text = sanitized.as_utf8(matched_input.offset())?;
        let int: Int = match i128::from_str_radix(text, self.radix()) {
            Ok(i) => i.into(),
            Err(parse_int_error) => {
                debug_assert!(
                    // `from_str_radix` can fail for a variety of reasons, but our rules for matching an
                    // int rule out most of them (empty str, invalid digit, etc). The only ones that should
                    // happen are overflow and underflow. In those cases, we fall back to using `BigInt`.
                    parse_int_error.kind() == &IntErrorKind::NegOverflow
                        || parse_int_error.kind() == &IntErrorKind::PosOverflow
                );
                return cold_path!(IonResult::decoding_error(format!(
                    "encountered an int whose value was exceeded the supported range: '{}'",
                    std::str::from_utf8(matched_input.bytes()).unwrap_or("invalid UTF-8")
                )));
            }
        };

        if self.is_negative {
            Ok(-int)
        } else {
            Ok(int)
        }
    }
}

/// A partially parsed Ion float.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum MatchedFloat {
    /// `+inf`
    PositiveInfinity,
    /// `-inf`
    NegativeInfinity,
    /// `nan`
    NotANumber,
    /// Any numeric float value
    Numeric,
}

impl MatchedFloat {
    // Floats that take more than 32 bytes of text to represent will heap allocate a larger buffer.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 32;

    pub fn read(&self, matched_input: TextBufferView) -> IonResult<f64> {
        match self {
            MatchedFloat::PositiveInfinity => return Ok(f64::INFINITY),
            MatchedFloat::NegativeInfinity => return Ok(f64::NEG_INFINITY),
            MatchedFloat::NotANumber => return Ok(f64::NAN),
            MatchedFloat::Numeric => {} // fall through
        };

        let mut sanitized: SmallVec<[u8; Self::STACK_ALLOC_BUFFER_CAPACITY]> =
            SmallVec::with_capacity(Self::STACK_ALLOC_BUFFER_CAPACITY);
        sanitized.extend(matched_input.bytes().iter().copied().filter(|b| *b != b'_'));

        let text = sanitized.as_utf8(matched_input.offset())?;
        let float = f64::from_str(text).map_err(|e| {
            let error: IonError = InvalidInputError::new(matched_input)
                .with_description(format!("encountered an unexpected error ({:?})", e))
                .with_label("parsing a float")
                .into();
            error
        })?;
        Ok(float)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct MatchedDecimal {
    is_negative: bool,
    digits_offset: u16,
    digits_length: u16,
    num_trailing_digits: u16,
    exponent_is_negative: bool,
    exponent_digits_offset: u16,
    exponent_digits_length: u16,
}

impl MatchedDecimal {
    // Decimals that take more than 32 bytes of text to represent will heap allocate a larger buffer.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 32;

    pub fn new(
        is_negative: bool,
        digits_offset: u16,
        digits_length: u16,
        num_trailing_digits: u16,
        exponent_is_negative: bool,
        exponent_offset: u16,
        exponent_length: u16,
    ) -> Self {
        Self {
            is_negative,
            digits_offset,
            digits_length,
            num_trailing_digits,
            exponent_is_negative,
            exponent_digits_offset: exponent_offset,
            exponent_digits_length: exponent_length,
        }
    }

    pub fn read(&self, matched_input: TextBufferView) -> IonResult<Decimal> {
        let mut sanitized: SmallVec<[u8; Self::STACK_ALLOC_BUFFER_CAPACITY]> =
            SmallVec::with_capacity(Self::STACK_ALLOC_BUFFER_CAPACITY);

        let digits = matched_input.slice(self.digits_offset as usize, self.digits_length as usize);

        // Copy all of the digits (but not the decimal point or underscores) over to the buffer.
        sanitized.extend(
            digits
                .bytes()
                .iter()
                .copied()
                .filter(|b| b.is_ascii_digit()),
        );

        let digits_text = sanitized.as_utf8(digits.offset())?;
        let magnitude: Int = i128::from_str(digits_text)
            .map_err(|e| {
                IonError::decoding_error(format!(
                    "decimal magnitude '{digits_text}' was larger than supported size ({e:?}"
                ))
            })?
            .into();

        let coefficient = if self.is_negative {
            if magnitude.is_zero() {
                Coefficient::negative_zero()
            } else {
                Coefficient::new(magnitude.neg())
            }
        } else {
            Coefficient::new(magnitude)
        };

        let mut exponent: i64 = match self.exponent_digits_length {
            0 => 0,
            _ => {
                sanitized.clear();
                let exponent_digits = matched_input.slice(
                    self.exponent_digits_offset as usize,
                    self.exponent_digits_length as usize,
                );
                // Copy all of the digits over to the buffer.
                sanitized.extend(
                    exponent_digits
                        .bytes()
                        .iter()
                        .copied()
                        .filter(|b| b.is_ascii_digit()),
                );
                let exponent_text = sanitized
                    .as_utf8(matched_input.offset() + self.exponent_digits_offset as usize)?;
                let exponent_magnitude = i64::from_str(exponent_text).map_err(|e| {
                    IonError::decoding_error(format!(
                        "failed to parse decimal exponent '{exponent_text}': {e:?}"
                    ))
                })?;
                if self.exponent_is_negative {
                    -exponent_magnitude
                } else {
                    exponent_magnitude
                }
            }
        };

        exponent -= self.num_trailing_digits as i64;

        Ok(Decimal::new(coefficient, exponent))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MatchedString {
    /// The string only has one segment. (e.g. "foo")
    ShortWithoutEscapes,
    ShortWithEscapes,
    /// The string is in multiple segments:
    ///     """hello,"""
    ///     """ world!"""
    Long,
    /// The string uses long-format delimiters, but is a single segment. We still have to
    /// allocate a fresh String to store the version with decoded escapes, but we don't need
    /// to re-parse the input because there's only one segment.
    LongSingleSegmentWithEscapes,
    /// The string uses long-format delimiters, but is a single segment and contains no escapes.
    /// This allows us to return a slice of the input as-is. It also greatly simplifies the
    /// reading process because we don't need to re-parse the input.
    LongSingleSegmentWithoutEscapes,
}

impl MatchedString {
    // Strings longer than 64 bytes will allocate a larger space on the heap.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 64;

    pub fn read<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        match self {
            MatchedString::ShortWithoutEscapes => {
                self.read_short_string_without_escapes(matched_input)
            }
            MatchedString::ShortWithEscapes => {
                self.read_short_string_with_escapes(allocator, matched_input)
            }
            MatchedString::LongSingleSegmentWithoutEscapes => {
                self.read_long_string_single_segment_without_escapes(matched_input)
            }
            MatchedString::LongSingleSegmentWithEscapes => {
                self.read_long_string_single_segment_with_escapes(allocator, matched_input)
            }
            MatchedString::Long => self.read_long_string(allocator, matched_input),
        }
    }

    fn read_long_string_single_segment_without_escapes<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // Take a slice of the input that ignores the first and last three bytes, which are quotes.
        let body = matched_input.slice(3, matched_input.len() - 6);
        // There are no escaped characters, so we can just validate the string in-place.
        let text = body.as_text()?;
        let str_ref = StrRef::from(text);
        Ok(str_ref)
    }

    fn read_long_string_single_segment_with_escapes<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // Take a slice of the input that ignores the first and last three bytes, which are quotes.
        let body = matched_input.slice(3, matched_input.len() - 6);
        // There are no escaped characters, so we can just validate the string in-place.
        let mut sanitized = BumpVec::with_capacity_in(matched_input.len(), allocator);
        replace_escapes_with_byte_values(
            body,
            &mut sanitized,
            // Normalize newlines
            true,
            // Support unicode escapes
            true,
        )?;
        let text = std::str::from_utf8(sanitized.into_bump_slice()).unwrap();
        Ok(StrRef::from(text))
    }

    fn read_long_string<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // We're going to re-parse the input to visit each segment, copying its sanitized bytes into
        // a contiguous buffer.

        // Create a new buffer to hold the sanitized data.
        let mut sanitized = BumpVec::with_capacity_in(matched_input.len(), allocator);
        let mut remaining = matched_input;

        // Iterate over the string segments using the match_long_string_segment parser.
        // This is the same parser that matched the input initially, which means that the only
        // reason it wouldn't succeed here is if the input is empty, meaning we're done reading.
        while let Ok((remaining_after_match, (segment_body, _has_escapes))) = preceded(
            TextBufferView::match_optional_comments_and_whitespace,
            TextBufferView::match_long_string_segment,
        )(remaining)
        {
            remaining = remaining_after_match;
            replace_escapes_with_byte_values(
                segment_body,
                &mut sanitized,
                // Normalize newlines
                true,
                // Support unicode escapes
                true,
            )?;
        }
        let text = std::str::from_utf8(sanitized.into_bump_slice()).unwrap();
        Ok(StrRef::from(text))
    }

    fn read_short_string_without_escapes<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);
        // There are no escaped characters, so we can just validate the string in-place.
        let text = body.as_text()?;
        let str_ref = StrRef::from(text);
        Ok(str_ref)
    }

    fn read_short_string_with_escapes<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);
        // There are escaped characters. We need to build a new version of our string
        // that replaces the escaped characters with their corresponding bytes.
        let mut sanitized = BumpVec::with_capacity_in(matched_input.len(), allocator);
        replace_escapes_with_byte_values(
            body,
            &mut sanitized,
            // Do not normalize newlines
            false,
            // Support Unicode escapes
            true,
        )?;
        let text = std::str::from_utf8(sanitized.into_bump_slice()).unwrap();
        Ok(StrRef::from(text))
    }
}

fn replace_escapes_with_byte_values(
    matched_input: TextBufferView,
    sanitized: &mut BumpVec<u8>,
    // If the text being escaped is in a long string or a clob, then unescaped \r\n and \r get
    // normalized to \n.
    normalize_newlines: bool,
    // Clobs use string-y syntax, but do not support `\u` or `\U` Unicode escapes because the
    // data they contain may not be Unicode.
    support_unicode_escapes: bool,
) -> IonResult<()> {
    let mut remaining = matched_input;

    // For ways to optimize this in the future, look at the `memchr` crate.
    let match_byte = |byte: &u8| *byte == b'\\' || *byte == b'\r';

    while !remaining.is_empty() {
        let next_index_to_inspect = remaining.bytes().iter().position(match_byte);
        remaining = match next_index_to_inspect {
            // It's an unescaped carriage return: 0x0A.
            Some(carriage_return_offset)
                if remaining.bytes().get(carriage_return_offset) == Some(&b'\r') =>
            {
                // Add all of the data up to the \r is clean. Add that slice to `sanitized`.
                sanitized.extend_from_slice(remaining.slice(0, carriage_return_offset).bytes());
                if normalize_newlines {
                    normalize_newline(remaining, sanitized, carriage_return_offset)
                } else {
                    // Add it to the sanitized data as-is
                    sanitized.push(b'\r');
                    remaining.slice_to_end(carriage_return_offset + 1)
                }
            }
            // It's an escape character: `\`
            Some(escape_offset) => {
                // Add all of the data up to the `\` is clean. Add that slice to `sanitized`.
                sanitized.extend_from_slice(remaining.slice(0, escape_offset).bytes());
                // Everything starting from the '\' needs to be evaluated.
                let contains_escapes = remaining.slice_to_end(escape_offset);
                decode_escape_into_bytes(contains_escapes, sanitized, support_unicode_escapes)?
            }
            None => {
                sanitized.extend_from_slice(remaining.bytes());
                // 'remaining' is now empty. Return an empty slice.
                remaining.slice_to_end(remaining.len())
            }
        }
    }
    Ok(())
}

// This code is only called when a \r is encountered in either a clob or long-form string
#[cold]
fn normalize_newline<'data>(
    remaining: TextBufferView<'data>,
    sanitized: &mut BumpVec<u8>,
    escape_offset: usize,
) -> TextBufferView<'data> {
    // Insert the normalized newline
    sanitized.push(b'\n');
    // Check whether we're skipping one byte (\r) or two (\r\n).
    if remaining.bytes().get(escape_offset + 1).copied() == Some(b'\n') {
        // The next byte is an unescaped newline; we normalize \r\n to \n, so we need
        // to skip an extra byte.
        remaining.slice_to_end(escape_offset + 2)
    } else {
        // We only processed a single byte: `\r`
        remaining.slice_to_end(escape_offset + 1)
    }
}

/// Matches an escape sequence at the beginning of `input` and pushes its corresponding
/// byte values onto the end of `sanitized`. Returns the remaining input following the escape
/// sequence.
fn decode_escape_into_bytes<'data>(
    input: TextBufferView<'data>,
    sanitized: &mut BumpVec<u8>,
    support_unicode_escapes: bool,
) -> IonResult<TextBufferView<'data>> {
    // Note that by the time this method has been called, the parser has already confirmed that
    // there is an appropriate closing delimiter. Thus, if any of the branches below run out of
    // data, it means that it's a fatal error and not just an Incomplete.
    debug_assert!(!input.is_empty());
    debug_assert!(input.bytes()[0] == b'\\');
    if input.len() == 1 {
        return Err(IonError::Decoding(
            DecodingError::new("found an escape ('\\') with no subsequent character")
                .with_position(input.offset()),
        ));
    }
    let input_after_escape = input.slice_to_end(2); // After (e.g.) '\x'
    let escape_id = input.bytes()[1];
    let substitute = match escape_id {
        b'n' => b'\n',
        b'r' => b'\r',
        b't' => b'\t',
        b'\\' => b'\\',
        b'/' => b'/',
        b'"' => b'"',
        b'\'' => b'\'',
        b'?' => b'?',
        b'0' => 0x00u8, // NUL
        b'a' => 0x07u8, // alert BEL
        b'b' => 0x08u8, // backspace
        b'v' => 0x0Bu8, // vertical tab
        b'f' => 0x0Cu8, // form feed
        // If the bytes following the '\' are an unescaped CR/LF, discard both.
        b'\r' if input_after_escape.bytes().first() == Some(&b'\n') => {
            return Ok(input_after_escape.slice_to_end(1))
        }
        // If the next byte is a CR or LF, discard it.
        b'\r' | b'\n' => return Ok(input_after_escape),
        // These cases require more sophisticated parsing, not just a 1-to-1 mapping of bytes
        b'x' => {
            return decode_hex_digits_escape(
                2,
                input_after_escape,
                sanitized,
                support_unicode_escapes,
            )
        }
        b'u' => {
            return decode_hex_digits_escape(
                4,
                input_after_escape,
                sanitized,
                support_unicode_escapes,
            )
        }
        b'U' => {
            return decode_hex_digits_escape(
                8,
                input_after_escape,
                sanitized,
                support_unicode_escapes,
            )
        }
        _ => {
            return Err(IonError::Decoding(
                DecodingError::new(format!("invalid escape sequence '\\{}", escape_id))
                    .with_position(input.offset()),
            ))
        }
    };

    sanitized.push(substitute);
    Ok(input_after_escape)
}

/// Reads the next `num_digits` bytes from `input` as a `char`, then writes that `char`'s UTF8 bytes
/// to `sanitized`.
fn decode_hex_digits_escape<'data>(
    num_digits: usize,
    input: TextBufferView<'data>,
    sanitized: &mut BumpVec<u8>,
    support_unicode_escapes: bool,
) -> IonResult<TextBufferView<'data>> {
    if input.len() < num_digits {
        return Err(IonError::Decoding(
            DecodingError::new(format!(
                "found a {}-hex-digit escape sequence with only {} digits",
                num_digits,
                input.len()
            ))
            .with_position(input.offset()),
        ));
    }

    // Clobs represent text of some encoding, but it may or may not be a flavor of Unicode.
    // As such, clob syntax does not support Unicode escape sequences like `\u` or `\U`.
    if num_digits != 2 && !support_unicode_escapes {
        return Err(IonError::Decoding(
            DecodingError::new("Unicode escape sequences (\\u, \\U) are not legal in this context")
                .with_position(input.offset()),
        ));
    }

    let hex_digit_bytes = &input.bytes()[..num_digits];

    let all_are_hex_digits = hex_digit_bytes
        .iter()
        .take(num_digits)
        .copied()
        .all(is_hex_digit);
    if !all_are_hex_digits {
        return Err(IonError::Decoding(
            DecodingError::new(format!(
                "found a {}-hex-digit escape sequence that contained an invalid hex digit",
                num_digits,
            ))
            .with_position(input.offset()),
        ));
    }
    // Isolate the portion of the input that follows the hex digits so we can return it.
    let remaining_input = input.slice_to_end(num_digits);

    // We just confirmed all of the digits are ASCII hex digits, so this step cannot fail.
    let hex_digits = std::str::from_utf8(hex_digit_bytes).unwrap();

    if !support_unicode_escapes {
        // Inside a clob, \x is a byte literal, not a Unicode code point.
        let byte_literal = u8::from_str_radix(hex_digits, 16).unwrap();
        sanitized.push(byte_literal);
        return Ok(remaining_input);
    }

    let code_point = u32::from_str_radix(hex_digits, 16).unwrap();

    // Check to see if this is a high surrogate; if it is, our code point isn't complete. Another
    // unicode escape representing the low surrogate has to be next in the input to complete it.
    // See the docs for the `code_point_is_a_high_surrogate` helper function for details.
    // (Note: this will only ever be true for 4- and 8-digit escape sequences. `\x` escapes don't
    // have enough digits to represent a high surrogate.)
    if code_point_is_a_high_surrogate(code_point) {
        // The spec has MAY-style language around supporting high surrogates. Supporting them is
        // allowed but discouraged. The ion-tests spec conformance tests include cases with UTF-16
        // surrogates, so ion-rust supports them.
        return complete_surrogate_pair(sanitized, code_point, remaining_input);
    }

    // A Rust `char` can represent any Unicode scalar value--a code point that is not part of a
    // surrogate pair. If the value we found isn't a high surrogate, then it's a complete scalar
    // value. We can safely convert it to a `char`.
    let character = char::from_u32(code_point).unwrap();
    let utf8_buffer: &mut [u8; 4] = &mut [0; 4];
    let utf8_encoded = character.encode_utf8(utf8_buffer);
    sanitized.extend_from_slice(utf8_encoded.as_bytes());

    // Skip beyond the digits we just processed
    Ok(remaining_input)
}

/// Reads another escaped code point from the buffer, treating it as the low surrogate to be paired
/// with the specified high surrogate. Appends the UTF-8 encoding of the resulting Unicode scalar
/// to `sanitized` and returns the remaining text in the buffer.
fn complete_surrogate_pair<'data>(
    sanitized: &mut BumpVec<u8>,
    high_surrogate: u32,
    input: TextBufferView<'data>,
) -> IonResult<TextBufferView<'data>> {
    let mut match_next_codepoint = preceded(
        tag("\\"),
        alt((
            preceded(tag("x"), TextBufferView::match_n_hex_digits(2)),
            preceded(tag("u"), TextBufferView::match_n_hex_digits(4)),
            preceded(tag("U"), TextBufferView::match_n_hex_digits(8)),
        )),
    );
    let (remaining, hex_digits) = match match_next_codepoint.parse(input) {
        Ok((remaining, hex_digits)) => (remaining, hex_digits),
        Err(_) => {
            return {
                let error =
                    DecodingError::new("found a high surrogate not followed by a low surrogate")
                        .with_position(input.offset());
                Err(IonError::Decoding(error))
            }
        }
    };
    let high_surrogate = high_surrogate as u16;

    let hex_digits = std::str::from_utf8(hex_digits.bytes()).unwrap();
    let low_surrogate = u16::from_str_radix(hex_digits, 16).map_err(|_| {
        let error =
            DecodingError::new("low surrogate did not fit in a u16").with_position(input.offset());
        IonError::Decoding(error)
    })?;

    let character = char::decode_utf16([high_surrogate, low_surrogate])
        .next()
        .unwrap()
        .map_err(|_| {
            let error = DecodingError::new("encountered invalid surrogate pair")
                .with_position(input.offset());
            IonError::Decoding(error)
        })?;

    let utf8_buffer: &mut [u8; 4] = &mut [0; 4];
    let utf8_encoded = character.encode_utf8(utf8_buffer);
    sanitized.extend_from_slice(utf8_encoded.as_bytes());
    Ok(remaining)
}

/// Returns `true` if the provided code point is a utf-16 high surrogate.
///
/// Terse primer: Unicode text is made up of a stream of unsigned integers called 'code points'.
/// What a person might think of as a 'character' (for example: 'a', '本', or '🥸') can be made up
/// of one or more code points.
///
/// A single code point can require up to 21 bits. Depending on which Unicode encoding you're using,
/// these 21 bits can come with different amounts of additional overhead bits:
/// * In utf-8, a code point can be 1, 2, 3, or 4 bytes, with some bits in each byte being used
///   for the code point and others being used to indicate whether more bytes are coming.
/// * In utf-16, a code point can be 2 bytes or 4 bytes. If it's four bytes, the first two bytes will
///   be a 'high surrogate' (a value between 0xD800 and 0xDFFF) to communicate that another two
///   bytes are coming to complete the code point.
/// * In utf-32, a code point is always 32 bits. This is a bit wasteful, but makes for simple
///   processing.
///
/// This helper function detects high surrogates (which are only used in utf-16) so the parser
/// can know to require a second one immediately following.
///
/// Further reading:
/// * <https://doc.rust-lang.org/std/primitive.char.html>
/// * <https://www.unicode.org/glossary/#surrogate_code_point>
fn code_point_is_a_high_surrogate(value: u32) -> bool {
    (0xD800..=0xDFFF).contains(&value)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MatchedSymbol {
    /// A numeric symbol ID (e.g. `$21`)
    SymbolId,
    /// The symbol is an unquoted identifier (e.g. `foo`)
    Identifier,
    /// The symbol is delimited by single quotes but contains no escape sequences.
    QuotedWithoutEscapes,
    /// The symbol is delimited by single quotes and has at least one escape sequence.
    QuotedWithEscapes,
    /// An operator within an S-expression
    Operator,
}

impl MatchedSymbol {
    pub fn read<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolRef<'data>> {
        use MatchedSymbol::*;
        match self {
            SymbolId => self.read_symbol_id(matched_input),
            Identifier | Operator => self.read_unquoted(matched_input),
            QuotedWithEscapes => self.read_quoted_with_escapes(allocator, matched_input),
            QuotedWithoutEscapes => self.read_quoted_without_escapes(matched_input),
        }
    }

    pub(crate) fn read_quoted_without_escapes<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);
        // There are no escaped characters, so we can just validate the string in-place.
        let text = body
            .as_text()
            .expect("successfully lexed symbol later found to be invalid UTF-8");
        let str_ref = RawSymbolRef::Text(text);
        Ok(str_ref)
    }

    pub(crate) fn read_quoted_with_escapes<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);

        // There are escaped characters. We need to build a new version of our symbol
        // that replaces the escaped characters with their corresponding bytes.
        let mut sanitized = BumpVec::with_capacity_in(matched_input.len(), allocator);
        replace_escapes_with_byte_values(body, &mut sanitized, false, true)?;
        let text = std::str::from_utf8(sanitized.into_bump_slice()).unwrap();
        Ok(RawSymbolRef::Text(text))
    }

    /// Reads a symbol with no surrounding quotes (and therefore no escapes).
    /// This is used for both identifiers and (within s-expressions) operators.
    pub(crate) fn read_unquoted<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolRef<'data>> {
        matched_input.as_text().map(RawSymbolRef::Text)
    }

    fn read_symbol_id<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolRef<'data>> {
        // Skip past the first byte, which has to be a `$`.
        let text = matched_input.slice_to_end(1).as_text()?;
        // It's not possible for the number parsing to fail because the matcher's rules
        // guarantee that this string contains only decimal digits.
        let sid = usize::from_str(text).expect("loading symbol ID as usize");
        Ok(RawSymbolRef::SymbolId(sid))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MatchedTimestamp {
    precision: TimestampPrecision,
    offset: MatchedTimestampOffset,
}

impl MatchedTimestamp {
    pub fn new(precision: TimestampPrecision) -> Self {
        Self {
            precision,
            offset: MatchedTimestampOffset::Unknown,
        }
    }
}

impl MatchedTimestamp {
    pub fn with_offset(mut self, offset: MatchedTimestampOffset) -> Self {
        self.offset = offset;
        self
    }

    pub(crate) fn read(&self, matched_input: TextBufferView) -> IonResult<Timestamp> {
        // The parser has already confirmed that each subfield is made of ASCII digits,
        // so UTF-8 validation and parsing cannot fail. `unwrap()` is used in such cases
        // throughout.
        let year_text = matched_input.slice(0, 4).as_text().unwrap();
        let year = u32::from_str(year_text).unwrap();
        let timestamp = Timestamp::with_year(year);

        if self.precision == TimestampPrecision::Year {
            return timestamp.build();
        }

        // Thanks to the conventions of RFC-3339, each subfield will always have the same offset
        // and length. We can hardcode the location of each one. (Offset is an exception, as we will
        // see later.)
        let month_text = matched_input.slice(5, 2).as_text().unwrap();
        let month = u32::from_str(month_text).unwrap();
        let timestamp = timestamp.with_month(month);

        if self.precision == TimestampPrecision::Month {
            return timestamp.build();
        }

        let day_text = matched_input.slice(8, 2).as_text().unwrap();
        let day = u32::from_str(day_text).unwrap();
        let timestamp = timestamp.with_day(day);

        if self.precision == TimestampPrecision::Day {
            return timestamp.build();
        }

        // For precisions greater than `Day`, the offset is mandatory.
        let offset_minutes = match self.offset {
            // If it's Zulu or unknown, we don't need to parse it; we already have the
            // information we need.
            MatchedTimestampOffset::Zulu => Some(0),
            MatchedTimestampOffset::Unknown => None,
            // If it's any other offset, we need to parse the sign, hours, and minutes.
            // This is the only field that doesn't have a fixed location; it's always at the end
            // of the timestamp, and the timestamp's length varies by its precision.
            // The `MatchedHoursAndMinutes` stores the offset at which `hours` begins.
            MatchedTimestampOffset::PositiveHoursAndMinutes
            | MatchedTimestampOffset::NegativeHoursAndMinutes => {
                // There has to be a day for there to also be an offset. The last day index is 9.
                // Starting at index 10, look for the next '-' or '+'.
                let hours_start = &matched_input.bytes()[10..]
                    .iter()
                    .position(|b| *b == b'-' || *b == b'+')
                    .expect("the parser reported that this timestamp had an HH:MM component")
                    + 11; // The position reported is relative to the offset where the search began
                let hours_text = matched_input.slice(hours_start, 2).as_text().unwrap();
                let hours = i32::from_str(hours_text).unwrap();
                let minutes_start = hours_start + 3;
                let minutes_text = matched_input.slice(minutes_start, 2).as_text().unwrap();
                let minutes = i32::from_str(minutes_text).unwrap();
                let offset_magnitude_minutes = (hours * 60) + minutes;
                if self.offset == MatchedTimestampOffset::NegativeHoursAndMinutes {
                    Some(-offset_magnitude_minutes)
                } else {
                    Some(offset_magnitude_minutes)
                }
            }
        };

        let hour_text = matched_input.slice(11, 2).as_text().unwrap();
        let hour = u32::from_str(hour_text).unwrap();
        let minute_text = matched_input.slice(14, 2).as_text().unwrap();
        let minute = u32::from_str(minute_text).unwrap();

        let timestamp = timestamp.with_hour_and_minute(hour, minute);

        if self.precision == TimestampPrecision::HourAndMinute {
            if let Some(offset) = offset_minutes {
                return timestamp.with_offset(offset).build();
            } else {
                return timestamp.build();
            }
        }

        let second_text = matched_input.slice(17, 2).as_text().unwrap();
        let seconds = u32::from_str(second_text).unwrap();
        let timestamp = timestamp.with_second(seconds);

        // There's guaranteed to be a 19th byte. It will either be a `.`, indicating the beginning
        // of fractional seconds or a `+`/`-`/`Z` comprising part of the offset.
        if matched_input.bytes()[19] != b'.' {
            // There are no fractional seconds; we can apply the offset (if any) and return.
            if let Some(offset) = offset_minutes {
                return timestamp.with_offset(offset).build();
            } else {
                return timestamp.build();
            }
        }

        // There are fractional seconds. We need to scan ahead to the first non-digit byte in the
        // input following the leading `.`.
        let fractional_start = 20;
        let mut fractional_end = fractional_start;
        for byte in matched_input.slice_to_end(fractional_start).bytes() {
            if !byte.is_dec_digit() {
                break;
            }
            fractional_end += 1;
        }
        let fractional_text = matched_input
            .slice(fractional_start, fractional_end - fractional_start)
            .as_text()
            .unwrap();
        let timestamp = match fractional_text.len() {
            len if len <= 9 => {
                let fraction = u32::from_str(fractional_text).unwrap();
                let multiplier = 10u32.pow(9 - len as u32);
                let nanoseconds = fraction * multiplier;
                timestamp.with_nanoseconds_and_precision(nanoseconds, len as u32)
            }
            _ => {
                // For less common precisions, store a Decimal
                let coefficient = i128::from_str(fractional_text).unwrap();
                let decimal = Decimal::new(coefficient, -(fractional_text.len() as i64));
                timestamp.with_fractional_seconds(decimal)
            }
        };

        if let Some(offset) = offset_minutes {
            timestamp.with_offset(offset).build()
        } else {
            timestamp.build()
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MatchedTimestampOffset {
    Zulu,
    PositiveHoursAndMinutes,
    NegativeHoursAndMinutes,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MatchedBlob {
    // Position within the blob at which the base64 characters begin
    content_offset: usize,
    // Length of the base64 characters
    content_length: usize,
}

impl MatchedBlob {
    pub fn new(content_offset: usize, content_length: usize) -> Self {
        Self {
            content_offset,
            content_length,
        }
    }

    pub(crate) fn read<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<BytesRef<'data>> {
        let base64_text = matched_input.slice(self.content_offset, self.content_length);
        let matched_bytes = base64_text.bytes();

        // Ion allows whitespace to appear in the middle of the base64 data; if the match
        // has inner whitespace, we need to strip it out.
        let contains_whitespace = matched_bytes.iter().any(|b| b.is_ascii_whitespace());

        let max_decoded_size = (matched_bytes.len() + 3) / 4 * 3;
        let mut decoding_buffer = BumpVec::with_capacity_in(max_decoded_size, allocator);

        decoding_buffer.resize(max_decoded_size, 0u8);
        let decode_result = if contains_whitespace {
            // This allocates a fresh Vec to store the sanitized bytes. It could be replaced by
            // a reusable buffer if this proves to be a bottleneck.
            let mut sanitized_base64_text =
                BumpVec::with_capacity_in(matched_bytes.len(), allocator);
            let non_whitespaces_bytes = matched_bytes
                .iter()
                .copied()
                .filter(|b| !b.is_ascii_whitespace());
            sanitized_base64_text.extend(non_whitespaces_bytes);
            base64::decode_config_slice(
                sanitized_base64_text.as_bytes(),
                base64::STANDARD,
                decoding_buffer.as_mut_slice(),
            )
        } else {
            base64::decode_config_slice(
                matched_bytes,
                base64::STANDARD,
                decoding_buffer.as_mut_slice(),
            )
        };

        let decoded_size = match decode_result {
            Ok(size) => size,
            Err(e) => {
                return IonResult::decoding_error(format!(
                    "failed to parse blob with invalid base64 data:\n'{:?}'\n{e:?}:",
                    matched_input.bytes()
                ))
            }
        };

        let decoded_bytes = decoding_buffer
            .into_bump_slice()
            .get(..decoded_size)
            .expect("decoding buffer was shorter than indicated");

        Ok(BytesRef::from(decoded_bytes))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MatchedClob {
    // Indicates that the content of the clob was written using short-form string syntax.
    Short,
    // Indicates that the content of the clob was written using long-form string syntax.
    Long,
}

impl MatchedClob {
    pub(crate) fn read<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<BytesRef<'data>> {
        // `matched_input` contains the entire clob, including the opening {{ and closing }}.
        // We can trim those off, but each function below will need to find the nested short- or
        // long-form string content.
        let matched_inside_braces = matched_input.slice(2, matched_input.len() - 4);
        match self {
            MatchedClob::Short => self.read_short_clob(allocator, matched_inside_braces),
            MatchedClob::Long => self.read_long_clob(allocator, matched_inside_braces),
        }
    }
    fn read_short_clob<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_inside_braces: TextBufferView<'data>,
    ) -> IonResult<BytesRef<'data>> {
        // There can be whitespace between the leading {{ and the `"`, so we need to scan ahead
        // to the `"`.
        let open_quote_position = matched_inside_braces
            .bytes()
            .iter()
            .position(|b| *b == b'"')
            .unwrap();
        // Get a slice that contains all of the bytes after the opening `"`.
        let remaining = matched_inside_braces.slice_to_end(open_quote_position + 1);
        // Use the existing short string body parser to identify all of the bytes up to the
        // unescaped closing `"`. This parser succeeded once during matching, so we know it will
        // succeed again here; it's safe to unwrap().
        let (_, (body, _has_escapes)) = remaining.match_short_string_body().unwrap();
        // There are escaped characters. We need to build a new version of our string
        // that replaces the escaped characters with their corresponding bytes.
        let mut sanitized = BumpVec::with_capacity_in(body.len(), allocator);
        replace_escapes_with_byte_values(
            body,
            &mut sanitized,
            // Do not normalize newlines
            false,
            // Unicode escapes are not supported
            false,
        )?;
        Ok(BytesRef::from(sanitized.into_bump_slice()))
    }
    fn read_long_clob<'data>(
        &self,
        allocator: &'data BumpAllocator,
        matched_inside_braces: TextBufferView<'data>,
    ) -> IonResult<BytesRef<'data>> {
        // We're going to re-parse the input to visit each segment, copying its sanitized bytes into
        // a contiguous buffer.

        // Create a new buffer to hold the sanitized data.
        let mut sanitized = BumpVec::with_capacity_in(matched_inside_braces.len(), allocator);
        let mut remaining = matched_inside_braces;

        // Iterate over the string segments using the match_long_string_segment parser.
        // This is the same parser that matched the input initially, which means that the only
        // reason it wouldn't succeed here is if the input is empty, meaning we're done reading.
        while let Ok((remaining_after_match, (segment_body, _has_escapes))) = preceded(
            TextBufferView::match_optional_whitespace,
            TextBufferView::match_long_string_segment,
        )(remaining)
        {
            remaining = remaining_after_match;
            replace_escapes_with_byte_values(
                segment_body,
                &mut sanitized,
                // Normalize newlines
                true,
                // Unicode escapes are not supported
                false,
            )?;
        }
        Ok(BytesRef::from(sanitized.into_bump_slice()))
    }
}

#[cfg(test)]
mod tests {

    use crate::lazy::bytes_ref::BytesRef;
    use crate::lazy::expanded::{EncodingContext, EncodingContextRef};
    use crate::lazy::text::buffer::TextBufferView;
    use crate::{Decimal, Int, IonResult, Timestamp};

    #[test]
    fn read_ints() -> IonResult<()> {
        fn expect_int(data: &str, expected: impl Into<Int>) {
            let expected: Int = expected.into();
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let buffer = TextBufferView::new(context, data.as_bytes());
            let (_remaining, matched) = buffer.match_int().unwrap();
            let actual = matched.read(buffer).unwrap();
            assert_eq!(
                actual, expected,
                "Actual didn't match expected for input '{}'.\n{:?}\n!=\n{:?}",
                data, actual, expected
            );
        }

        let tests = [
            ("-5", Int::from(-5)),
            ("0", Int::from(0)),
            (
                "1234567890_1234567890_1234567890",
                Int::from(1234567890_1234567890_1234567890i128),
            ),
            (
                "-1234567890_1234567890_1234567890",
                Int::from(-1234567890_1234567890_1234567890i128),
            ),
        ];

        for (input, expected) in tests {
            expect_int(input, expected);
        }
        Ok(())
    }

    #[test]
    fn read_timestamps() -> IonResult<()> {
        fn expect_timestamp(data: &str, expected: Timestamp) {
            let data = format!("{data} "); // Append a space
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let buffer = TextBufferView::new(context, data.as_bytes());
            let (_remaining, matched) = buffer.match_timestamp().unwrap();
            let actual = matched.read(buffer).unwrap();
            assert_eq!(
                actual, expected,
                "Actual didn't match expected for input '{}'.\n{:?}\n!=\n{:?}",
                data, actual, expected
            );
        }

        let tests = [
            ("2023T", Timestamp::with_year(2023).build()?),
            (
                "2023-08T",
                Timestamp::with_year(2023).with_month(8).build()?,
            ),
            ("2023-08-13", Timestamp::with_ymd(2023, 8, 13).build()?),
            ("2023-08-13T", Timestamp::with_ymd(2023, 8, 13).build()?),
            (
                "2023-08-13T10:30-00:00",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .build()?,
            ),
            (
                "2023-08-13T10:30Z",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_offset(0)
                    .build()?,
            ),
            (
                "2023-08-13T10:30-05:00",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_offset(-300)
                    .build()?,
            ),
            (
                "2023-08-13T10:30+05:00",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_offset(300)
                    .build()?,
            ),
            (
                "2023-08-13T10:30:45Z",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_second(45)
                    .with_offset(0)
                    .build()?,
            ),
            (
                "2023-08-13T10:30:45.226Z",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_second(45)
                    .with_milliseconds(226)
                    .with_offset(0)
                    .build()?,
            ),
            (
                "2023-08-13T10:30:45.226226Z",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_second(45)
                    .with_microseconds(226226)
                    .with_offset(0)
                    .build()?,
            ),
            (
                "2023-08-13T10:30:45.226226226Z",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_second(45)
                    .with_nanoseconds(226226226)
                    .with_offset(0)
                    .build()?,
            ),
            (
                "2023-08-13T10:30:45.226226226337337Z",
                Timestamp::with_ymd(2023, 8, 13)
                    .with_hour_and_minute(10, 30)
                    .with_second(45)
                    .with_fractional_seconds(Decimal::new(226_226_226_337_337_i64, -15))
                    .with_offset(0)
                    .build()?,
            ),
        ];

        for (input, expected) in tests {
            expect_timestamp(input, expected);
        }

        Ok(())
    }

    #[test]
    fn read_decimals() -> IonResult<()> {
        fn expect_decimal(data: &str, expected: Decimal) {
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let buffer = TextBufferView::new(context, data.as_bytes());
            let result = buffer.match_decimal();
            assert!(
                result.is_ok(),
                "Unexpected match error for input: '{data}': {:?}",
                result
            );
            let (_remaining, matched) = buffer.match_decimal().expect("match decimal");
            let result = matched.read(buffer);
            assert!(
                result.is_ok(),
                "Unexpected read error for input '{data}': {:?}",
                result
            );
            let actual = result.unwrap();
            assert_eq!(
                actual, expected,
                "Actual didn't match expected for input '{}'.\n{:?}\n!=\n{:?}",
                data, actual, expected
            );
            assert_eq!(
                actual.coefficient(),
                expected.coefficient(),
                "Actual coefficient didn't match expected coefficient for input '{}' .\n{:?}\n!=\n{:?}",
                data, actual, expected
            );
            assert_eq!(
                actual.exponent(),
                expected.exponent(),
                "Actual exponent didn't match expected exponent for input '{}' .\n{:?}\n!=\n{:?}",
                data,
                actual,
                expected
            );
        }

        let tests = [
            ("0.", Decimal::new(0, 0)),
            ("-0.", Decimal::negative_zero()),
            ("0.0", Decimal::new(0, -1)),
            ("0.00", Decimal::new(0, -2)),
            ("0d-1", Decimal::new(0, -1)),
            ("0d0", Decimal::new(0, 0)),
            ("0d1", Decimal::new(0, 1)),
            ("0d2", Decimal::new(0, 2)),
            ("0.0d1", Decimal::new(0, 0)),
            ("0.0d0", Decimal::new(0, -1)),
            ("0.0d-1", Decimal::new(0, -2)),
            ("5.", Decimal::new(5, 0)),
            ("-5.", Decimal::new(-5, 0)),
            ("5.d0", Decimal::new(5, 0)),
            ("-5.d0", Decimal::new(-5, 0)),
            ("5.0", Decimal::new(50, -1)),
            ("5.0d1", Decimal::new(50, 0)),
            ("5.0d0", Decimal::new(50, -1)),
            ("5.0d-1", Decimal::new(50, -2)),
            ("-5.0", Decimal::new(-50, -1)),
            ("500d0", Decimal::new(500, 0)),
            ("-500d0", Decimal::new(-500, 0)),
            ("0.005", Decimal::new(5, -3)),
            ("0.0050", Decimal::new(50, -4)),
            ("-0.005", Decimal::new(-5, -3)),
            ("0.005D2", Decimal::new(5, -1)),
            ("-0.005D2", Decimal::new(-5, -1)),
            ("0.005d+2", Decimal::new(5, -1)),
            ("-0.005d+2", Decimal::new(-5, -1)),
            ("0.005D-2", Decimal::new(5, -5)),
            ("-0.005D-2", Decimal::new(-5, -5)),
        ];

        for (input, expected) in tests {
            expect_decimal(input, expected);
        }

        Ok(())
    }

    #[test]
    fn read_blobs() -> IonResult<()> {
        fn expect_blob(data: &str, expected: &str) {
            let data = format!("{data} "); // Append a space
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let buffer = TextBufferView::new(context, data.as_bytes());
            let (_remaining, matched) = buffer.match_blob().unwrap();
            let actual = matched.read(context.allocator(), buffer).unwrap();
            assert_eq!(
                actual,
                expected.as_ref(),
                "Actual didn't match expected for input '{}'.\n{:?}\n!=\n{:?}",
                data,
                actual,
                expected
            );
        }

        let tests = [
            ("{{TWVyY3VyeQ==}}", "Mercury"),
            ("{{VmVudXM=}}", "Venus"),
            ("{{RWFydGg=}}", "Earth"),
            ("{{TWFycw==}}", "Mars"),
            ("{{     TWFycw==      }}", "Mars"),
            ("{{\nTWFycw==\t\t }}", "Mars"),
        ];

        for (input, expected) in tests {
            expect_blob(input, expected);
        }

        Ok(())
    }

    #[test]
    fn read_strings() -> IonResult<()> {
        fn expect_string(data: &str, expected: &str) {
            // Ordinarily the reader is responsible for indicating that the input is complete.
            // For the sake of these tests, we're going to append one more value (`0`) to the input
            // stream so the parser knows that the long-form strings are complete. We then trim
            // our fabricated value off of the input before reading.
            let data = format!("{data}\n0");
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let buffer = TextBufferView::new(context, data.as_bytes());
            let (_remaining, matched) = buffer.match_string().unwrap();
            let matched_input = buffer.slice(0, buffer.len() - 2);
            let actual = matched.read(context.allocator(), matched_input).unwrap();
            assert_eq!(
                actual, expected,
                "Actual didn't match expected for input '{}'.\n{:?}\n!=\n{:?}",
                data, actual, expected
            );
        }

        let tests = [
            (r#""hello""#, "hello"),
            (r"'''hello'''", "hello"),
            (r"'''he''' '''llo'''", "hello"),
            (r"'''he''' '''llo'''", "hello"),
            (r#""😎🙂🙃""#, "😎🙂🙃"),
            (r"'''😎🙂''' '''🙃'''", "😎🙂🙃"),
            (r"'''\u2764\uFE0F'''", "❤️"),
            (r"'''\U00002764\U0000FE0F'''", "❤️"),
            // In short strings, carriage returns are not normalized.
            ("\"foo\rbar\rbaz\"", "foo\rbar\rbaz"),
            // In long-form strings, all unescaped newlines are converted to `\n`.
            ("'''foo\rbar\r\nbaz'''", "foo\nbar\nbaz"),
        ];

        for (input, expected) in tests {
            expect_string(input, expected);
        }

        Ok(())
    }

    #[test]
    fn read_clobs() -> IonResult<()> {
        fn read_clob<'a>(
            context: EncodingContextRef<'a>,
            data: &'a str,
        ) -> IonResult<BytesRef<'a>> {
            let buffer = TextBufferView::new(context, data.as_bytes());
            // All `read_clob` usages should be accepted by the matcher, so we can `unwrap()` the
            // call to `match_clob()`.
            let (_remaining, matched) = buffer.match_clob().unwrap();
            // The resulting buffer slice may be rejected during reading.
            matched.read(context.allocator(), buffer)
        }

        fn expect_clob_error(context: EncodingContextRef, data: &str) {
            let actual = read_clob(context, data);
            assert!(
                actual.is_err(),
                "Successfully read a clob from illegal input."
            );
        }

        fn expect_clob(context: EncodingContextRef, data: &str, expected: &str) {
            let result = read_clob(context, data);
            assert!(
                result.is_ok(),
                "Unexpected read failure for input '{data}': {:?}",
                result
            );
            let actual = result.unwrap();
            assert_eq!(
                actual,
                expected.as_ref(),
                "Actual didn't match expected for input '{}'.\n{:?} ({})\n!=\n{:?} ({:0x?})",
                data,
                actual,
                std::str::from_utf8(actual.data()).unwrap(),
                expected,
                expected.as_bytes()
            );
        }

        // These tests compare a clob containing UTF-8 data to the expected string's bytes.
        // This is just an example; clobs' data does not have to be (and often would not be) UTF-8.
        let tests = [
            (r#"{{""}}"#, ""),
            (r#"{{''''''}}"#, ""),
            (r#"{{'''''' '''''' ''''''}}"#, ""),
            (r#"{{"hello"}}"#, "hello"),
            (r#"{{"\x4D"}}"#, "M"),
            (r#"{{"\x4d \x4d \x4d"}}"#, "M M M"),
            (r"{{'''\x4d''' '''\x4d''' '''\x4d'''}}", "MMM"),
            // The below byte literals are the UTF-8 encoding of Unicode code points: U+2764 U+FE0F
            (r#"{{"\xe2\x9d\xa4\xef\xb8\x8f"}}"#, "❤️"),
            (r#"{{'''hel''' '''lo'''}}"#, "hello"),
            (
                r"{{
                    '''\xe2'''
                    '''\x9d\xa4'''
                    '''\xef\xb8\x8f'''
                }}
            ",
                "❤️",
            ),
            // In a long-form clob, unescaped `\r` and `\r\n` are normalized into unescaped `\n`
            ("{{'''foo\rbar\r\nbaz'''}}", "foo\nbar\nbaz"),
            // In a short-form clob, carriage returns are not normalized.
            ("{{\"foo\rbar\rbaz\"}}", "foo\rbar\rbaz"),
        ];

        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        for (input, expected) in tests {
            expect_clob(context, input, expected);
        }

        let illegal_inputs = [
            // Clobs represent text of some encoding, but it may or may not be a flavor of Unicode.
            // As such, clob syntax does not support Unicode escape sequences like `\u` or `\U`.
            // Byte literals may be written using `\x`, however.
            r#"{{"\u004D" }}"#,
            r#"{{"\U0000004D" }}"#,
            // Escape sequence that terminates early
            r#"{{"\x4"}}"#,
            // Escape sequence split across long-form segments
            r"{{
                    '''\xe'''
                    '''2\x9d\xa'''
                    '''4\xef\xb8\x8f'''
                }}
            ",
        ];

        for input in illegal_inputs {
            expect_clob_error(context, input);
        }

        Ok(())
    }
}
