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

use nom::character::is_hex_digit;
use std::num::IntErrorKind;
use std::ops::Range;

use num_bigint::BigInt;
use num_traits::Num;
use smallvec::SmallVec;

use crate::lazy::str_ref::StrRef;
use crate::lazy::text::as_utf8::AsUtf8;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::InvalidInputError;
use crate::result::{DecodingError, IonFailure};
use crate::{Int, IonError, IonResult, IonType};

/// A partially parsed Ion value.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum MatchedValue {
    // `Null` and `Bool` are fully parsed because they only involve matching a keyword.
    Null(IonType),
    Bool(bool),
    Int(MatchedInt),
    Float(MatchedFloat),
    String(MatchedString),
    // TODO: ...the other types
}

/// A partially parsed Ion int.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct MatchedInt {
    radix: u32,
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
        use std::str::FromStr;

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

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum MatchedString {
    /// The string only has one segment. (e.g. "foo")
    Short(MatchedShortString),
    /// The string is in multiple segments:
    ///     """hello,"""
    ///     """ world!"""
    Long(MatchedLongString),
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct MatchedLongString {
    // Keep a list of all the string segment ranges we found.
    // If the user asks to read the string, we'll collate the segments into a single string.
    slices: Vec<Range<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct MatchedShortString {
    contains_escaped_chars: bool,
}

impl MatchedShortString {
    pub fn new(contains_escaped_chars: bool) -> Self {
        Self {
            contains_escaped_chars,
        }
    }
    pub fn contains_escaped_chars(&self) -> bool {
        self.contains_escaped_chars
    }
}

impl MatchedString {
    // Strings longer than 64 bytes will allocate a larger space on the heap.
    const STACK_ALLOC_BUFFER_CAPACITY: usize = 64;

    pub fn read<'a, 'data>(
        &'a self,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        match self {
            MatchedString::Short(short) => self.read_short_string(*short, matched_input),
            MatchedString::Long(_) => todo!("long-form strings"),
        }
    }

    fn read_short_string<'a, 'data>(
        &'a self,
        short: MatchedShortString,
        matched_input: TextBufferView<'data>,
    ) -> IonResult<StrRef<'data>> {
        // Take a slice of the input that ignores the first and last bytes, which are quotes.
        let body = matched_input.slice(1, matched_input.len() - 2);
        if !short.contains_escaped_chars() {
            // There are no escaped characters, so we can just validate the string in-place.
            let text = body.as_text()?;
            let str_ref = StrRef::from(text);
            return Ok(str_ref);
        }
        // Otherwise, there are escaped characters. We need to build a new version of our string
        // that replaces the escaped characters with their corresponding bytes.
        let mut sanitized = Vec::with_capacity(matched_input.len());

        Self::escape_short_string(body, &mut sanitized)?;
        let text = String::from_utf8(sanitized).unwrap();
        Ok(StrRef::from(text.to_string()))
    }

    fn escape_short_string(
        matched_input: TextBufferView,
        sanitized: &mut Vec<u8>,
    ) -> IonResult<()> {
        let mut remaining = matched_input;
        while !remaining.is_empty() {
            let next_escape = remaining.bytes().iter().position(|byte| *byte == b'\\');
            remaining = if let Some(escape_offset) = next_escape {
                // Everything up to the '\' is already clean. Write that slice to 'sanitized'.
                let already_clean = remaining.slice(0, escape_offset);
                sanitized.extend_from_slice(already_clean.bytes());
                // Everything starting from the '\' needs to be evaluated.
                let contains_escapes = remaining.slice_to_end(escape_offset);
                Self::write_escaped(contains_escapes, sanitized)?
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
            b'x' => return Self::hex_digits_code_point(2, input_after_escape, sanitized),
            b'u' => return Self::hex_digits_code_point(4, input_after_escape, sanitized),
            b'U' => return Self::hex_digits_code_point(8, input_after_escape, sanitized),
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

    fn hex_digits_code_point<'a, 'data>(
        num_digits: usize,
        input: TextBufferView<'data>,
        sanitized: &'a mut Vec<u8>,
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
