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

use num_bigint::BigInt;
use num_traits::Num;
use smallvec::SmallVec;

use crate::lazy::text::as_utf8::AsUtf8;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::InvalidInputError;
use crate::result::IonFailure;
use crate::{Int, IonError, IonResult, IonType};

/// A partially parsed Ion value.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum MatchedValue {
    // `Null` and `Bool` are fully parsed because they only involve matching a keyword.
    Null(IonType),
    Bool(bool),
    Int(MatchedInt),
    Float(MatchedFloat),
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
