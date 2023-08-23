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

use std::borrow::Cow;
use std::num::IntErrorKind;
use std::str::FromStr;

use nom::character::is_hex_digit;
use nom::AsChar;
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use smallvec::SmallVec;

use crate::decimal::coefficient::{Coefficient, Sign};
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::as_utf8::AsUtf8;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::InvalidInputError;
use crate::result::{DecodingError, IonFailure};
use crate::{
    Decimal, Int, IonError, IonResult, IonType, RawSymbolTokenRef, Timestamp, TimestampPrecision,
    UInt,
};

/// A partially parsed Ion value.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum MatchedValue {
    // `Null` and `Bool` are fully parsed because they only involve matching a keyword.
    Null(IonType),
    Bool(bool),
    Int(MatchedInt),
    Float(MatchedFloat),
    Decimal(MatchedDecimal),
    Timestamp(MatchedTimestamp),
    String(MatchedString),
    Symbol(MatchedSymbol),
    List,
    SExp,
    Struct,
    // TODO: ...the other types
}

/// A partially parsed Ion int.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct MatchedInt {
    radix: u32,
    // Offset of the digits from the beginning of the value
    digits_offset: usize,
    is_negative: bool,
}

impl MatchedInt {
    // Integers that take more than 32 bytes to represent will heap allocate a larger buffer.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 32;

    /// Constructs a new `MatchedInt`.
    pub fn new(radix: u32, is_negative: bool, digits_offset: usize) -> Self {
        Self {
            radix,
            digits_offset,
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
        self.radix
    }

    /// Attempts to finish reading the partially parsed integer.
    pub fn read(&self, matched_input: TextBufferView) -> IonResult<Int> {
        let digits = matched_input.slice_to_end(self.digits_offset);
        let mut sanitized: SmallVec<[u8; Self::STACK_ALLOC_BUFFER_CAPACITY]> =
            SmallVec::with_capacity(Self::STACK_ALLOC_BUFFER_CAPACITY);
        // Copy the input text over to the sanitization buffer, discarding any underscores. These
        // are legal input, but Rust's integer `from_str_radix` method does not support them.
        sanitized.extend(digits.bytes().iter().copied().filter(|b| *b != b'_'));
        // Note: This UTF-8 validation step should be unnecessary as the parser only recognizes
        //       ASCII integer characters. If this shows up in profiling, we could consider skipping it.
        let text = sanitized.as_utf8(matched_input.offset())?;
        let int: Int = match i64::from_str_radix(text, self.radix()) {
            Ok(i) => i.into(),
            Err(parse_int_error) => {
                debug_assert!(
                    // `from_str_radix` can fail for a variety of reasons, but our rules for matching an
                    // int rule out most of them (empty str, invalid digit, etc). The only ones that should
                    // happen are overflow and underflow. In those cases, we fall back to using `BigInt`.
                    parse_int_error.kind() == &IntErrorKind::NegOverflow
                        || parse_int_error.kind() == &IntErrorKind::PosOverflow
                );

                match BigInt::from_str_radix(text, self.radix()) {
                    Ok(big_int) => big_int.into(),
                    Err(_big_parse_int_error) => {
                        return IonResult::decoding_error(format!(
                            "unexpected error while parsing int: '{}'",
                            std::str::from_utf8(matched_input.bytes()).unwrap_or("invalid UTF-8")
                        ))
                    }
                }
            }
        };

        Ok(int)
    }
}

/// A partially parsed Ion float.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum MatchedFloat {
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
pub(crate) struct MatchedDecimal {
    is_negative: bool,
    digits_offset: u16,
    digits_length: u16,
    trailing_digits_length: u16,
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
        trailing_digits_length: u16,
        exponent_is_negative: bool,
        exponent_offset: u16,
        exponent_length: u16,
    ) -> Self {
        Self {
            is_negative,
            digits_offset,
            digits_length,
            trailing_digits_length,
            exponent_is_negative,
            exponent_digits_offset: exponent_offset,
            exponent_digits_length: exponent_length,
        }
    }

    pub fn read(&self, matched_input: TextBufferView) -> IonResult<Decimal> {
        // The longest number that can fit into a u64 without finer-grained bounds checks.
        const MAX_U64_DIGITS: usize = 19;
        // u64::MAX is a 20-digit number starting with `1`. For simplicity, we'll turn any number
        // with 19 or fewer digits into a u64 and anything else into a BigUint.

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
        let magnitude: UInt = if sanitized.len() <= MAX_U64_DIGITS {
            u64::from_str(digits_text).unwrap().into()
        } else {
            BigUint::from_str(digits_text).unwrap().into()
        };

        let sign = if self.is_negative {
            Sign::Negative
        } else {
            Sign::Positive
        };
        let coefficient = Coefficient::new(sign, magnitude);

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

        exponent -= self.trailing_digits_length as i64;

        Ok(Decimal::new(coefficient, exponent))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum MatchedString {
    /// The string only has one segment. (e.g. "foo")
    ShortWithoutEscapes,
    ShortWithEscapes,
    /// The string is in multiple segments:
    ///     """hello,"""
    ///     """ world!"""
    Long,
}

impl MatchedString {
    // Strings longer than 64 bytes will allocate a larger space on the heap.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 64;

    pub fn read<'data>(&self, matched_input: TextBufferView<'data>) -> IonResult<StrRef<'data>> {
        match self {
            MatchedString::ShortWithoutEscapes => {
                self.read_short_string_without_escapes(matched_input)
            }
            MatchedString::ShortWithEscapes => self.read_short_string_with_escapes(matched_input),
            MatchedString::Long => todo!("long-form strings"),
        }
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
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);
        // There are escaped characters. We need to build a new version of our string
        // that replaces the escaped characters with their corresponding bytes.
        let mut sanitized = Vec::with_capacity(matched_input.len());
        escape_text(body, &mut sanitized)?;
        let text = String::from_utf8(sanitized).unwrap();
        Ok(StrRef::from(text.to_string()))
    }
}

fn escape_text(matched_input: TextBufferView, sanitized: &mut Vec<u8>) -> IonResult<()> {
    let mut remaining = matched_input;
    while !remaining.is_empty() {
        let next_escape = remaining.bytes().iter().position(|byte| *byte == b'\\');
        remaining = if let Some(escape_offset) = next_escape {
            // Everything up to the '\' is already clean. Write that slice to 'sanitized'.
            let already_clean = remaining.slice(0, escape_offset);
            sanitized.extend_from_slice(already_clean.bytes());
            // Everything starting from the '\' needs to be evaluated.
            let contains_escapes = remaining.slice_to_end(escape_offset);
            write_escaped(contains_escapes, sanitized)?
        } else {
            sanitized.extend_from_slice(remaining.bytes());
            // 'remaining' is now empty
            remaining.slice_to_end(remaining.len())
        };
    }

    Ok(())
}

fn write_escaped<'data>(
    input: TextBufferView<'data>,
    sanitized: &mut Vec<u8>,
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
        // If the byte following the '\' is a real newline (that is: 0x0A), we discard it.
        b'\n' => return Ok(input_after_escape),
        // These cases require more sophisticated parsing, not just a 1-to-1 mapping of bytes
        b'x' => return hex_digits_code_point(2, input_after_escape, sanitized),
        b'u' => return hex_digits_code_point(4, input_after_escape, sanitized),
        b'U' => return hex_digits_code_point(8, input_after_escape, sanitized),
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
fn hex_digits_code_point<'data>(
    num_digits: usize,
    input: TextBufferView<'data>,
    sanitized: &mut Vec<u8>,
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
    // We just confirmed all of the digits are ASCII hex digits, so these steps cannot fail.
    let hex_digits = std::str::from_utf8(hex_digit_bytes).unwrap();
    let code_point = u32::from_str_radix(hex_digits, 16).unwrap();

    // Check to see if this is a high surrogate; if it is, our code point isn't complete. Another
    // unicode escape representing the low surrogate has to be next in the input to complete it.
    // See the docs for this helper function for details. (Note: this will only ever be true for
    // 4- and 8-digit escape sequences. `\x` escapes don't have enough digits to represent a
    // high surrogate.)
    if code_point_is_a_high_surrogate(code_point) {
        todo!("support surrogate pairs")
    }

    // A Rust `char` can represent any Unicode scalar value--a code point that is not part of a
    // surrogate pair. If the value we found isn't a high surrogate, then it's a complete scalar
    // value. We can safely convert it to a `char`.
    let character = char::from_u32(code_point).unwrap();
    let utf8_buffer: &mut [u8; 4] = &mut [0; 4];
    let utf8_encoded = character.encode_utf8(utf8_buffer);
    sanitized.extend_from_slice(utf8_encoded.as_bytes());

    // Skip beyond the digits we just processed
    Ok(input.slice_to_end(num_digits))
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
pub(crate) enum MatchedSymbol {
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
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolTokenRef<'data>> {
        use MatchedSymbol::*;
        match self {
            SymbolId => self.read_symbol_id(matched_input),
            Identifier | Operator => self.read_unquoted(matched_input),
            QuotedWithEscapes => self.read_quoted_with_escapes(matched_input),
            QuotedWithoutEscapes => self.read_quoted_without_escapes(matched_input),
        }
    }

    pub(crate) fn read_quoted_without_escapes<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolTokenRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);
        // There are no escaped characters, so we can just validate the string in-place.
        let text = body.as_text()?;
        let str_ref = RawSymbolTokenRef::Text(text.into());
        Ok(str_ref)
    }

    pub(crate) fn read_quoted_with_escapes<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolTokenRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);

        // There are escaped characters. We need to build a new version of our symbol
        // that replaces the escaped characters with their corresponding bytes.
        let mut sanitized = Vec::with_capacity(matched_input.len());

        escape_text(body, &mut sanitized)?;
        let text = String::from_utf8(sanitized).unwrap();
        Ok(RawSymbolTokenRef::Text(text.into()))
    }

    /// Reads a symbol with no surrounding quotes (and therefore no escapes).
    /// This is used for both identifiers and (within s-expressions) operators.
    pub(crate) fn read_unquoted<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolTokenRef<'data>> {
        matched_input
            .as_text()
            .map(|t| RawSymbolTokenRef::Text(Cow::Borrowed(t)))
    }

    fn read_symbol_id<'data>(
        &self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<RawSymbolTokenRef<'data>> {
        // Skip past the first byte, which has to be a `$`.
        let text = matched_input.slice_to_end(1).as_text()?;
        // It's not possible for the number parsing to fail because the matcher's rules
        // guarantee that this string contains only decimal digits.
        let sid = usize::from_str(text).expect("loading symbol ID as usize");
        Ok(RawSymbolTokenRef::SymbolId(sid))
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
            MatchedTimestampOffset::HoursAndMinutes(matched_offset) => {
                let hours_start = matched_offset.hours_offset() - matched_input.offset();
                let hours_text = matched_input.slice(hours_start, 2).as_text().unwrap();
                let hours = i32::from_str(hours_text).unwrap();
                let minutes_start = hours_start + 3;
                let minutes_text = matched_input.slice(minutes_start, 2).as_text().unwrap();
                let minutes = i32::from_str(minutes_text).unwrap();
                let offset_magnitude_minutes = (hours * 60) + minutes;
                if matched_offset.is_negative {
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
                let coefficient = BigUint::from_str(fractional_text).unwrap();
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
    HoursAndMinutes(MatchedHoursAndMinutes),
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MatchedHoursAndMinutes {
    is_negative: bool,
    /// This is the offset of the first `H` in the offset string `HH:MM`.
    hours_offset: usize,
}

impl MatchedHoursAndMinutes {
    pub fn new(is_negative: bool, hours_offset: usize) -> Self {
        Self {
            is_negative,
            hours_offset,
        }
    }
    pub fn is_negative(&self) -> bool {
        self.is_negative
    }
    pub fn hours_offset(&self) -> usize {
        self.hours_offset
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::text::buffer::TextBufferView;
    use crate::{Decimal, IonResult, Timestamp};

    #[test]
    fn read_timestamps() -> IonResult<()> {
        fn expect_timestamp(data: &str, expected: Timestamp) {
            let data = format!("{data} "); // Append a space
            let buffer = TextBufferView::new(data.as_bytes());
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
            let data = format!("{data} "); // Append a space
            let buffer = TextBufferView::new(data.as_bytes());
            let (_remaining, matched) = buffer.match_decimal().unwrap();
            let actual = matched.read(buffer).unwrap();
            assert_eq!(
                actual, expected,
                "Actual didn't match expected for input '{}'.\n{:?}\n!=\n{:?}",
                data, actual, expected
            );
        }

        let tests = [
            ("0.", Decimal::new(0, 0)),
            ("-0.", Decimal::negative_zero()),
            ("5.", Decimal::new(5, 0)),
            ("-5.", Decimal::new(-5, 0)),
            ("5.d0", Decimal::new(5, 0)),
            ("-5.d0", Decimal::new(-5, 0)),
            ("5.0", Decimal::new(50, -1)),
            ("-5.0", Decimal::new(-50, -1)),
            ("5.0d", Decimal::new(50, -1)),
            ("-5.0d", Decimal::new(-50, -1)),
            ("500d0", Decimal::new(5, 2)),
            ("-500d0", Decimal::new(-5, 2)),
            ("0.005", Decimal::new(5, -3)),
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
}
