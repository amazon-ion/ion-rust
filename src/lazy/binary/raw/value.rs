#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;
use std::{fmt, mem};

use crate::binary::int::DecodedInt;
use crate::binary::uint::DecodedUInt;
use crate::constants::MAX_READ_WRITE_DEPTH;
use crate::lazy::binary::binary_buffer::BinaryBuffer;
use crate::lazy::binary::encoded_value::EncodedBinaryValue;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct_1_0;
use crate::lazy::binary::raw::sequence::{
    LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0, LazyRawBinarySequence_1_0,
};
use crate::lazy::binary::raw::type_descriptor::Header;
use crate::lazy::decoder::{HasRange, HasSpan, LazyRawValue, RawVersionMarker};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::str_ref::StrRef;
use crate::read_config::max_read_depth_exceeded_message;
use crate::result::IonFailure;
use crate::types::SymbolId;
use crate::{
    Decimal, Decoder, Int, IonEncoding, IonError, IonResult, IonType, RawSymbolRef, Timestamp,
};
use ice_code::ice as cold_path;

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryVersionMarker_1_0<'top> {
    major: u8,
    minor: u8,
    input: BinaryBuffer<'top>,
}

impl<'top> LazyRawBinaryVersionMarker_1_0<'top> {
    pub fn new(input: BinaryBuffer<'top>, major: u8, minor: u8) -> Self {
        Self {
            major,
            minor,
            input,
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawBinaryVersionMarker_1_0<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl HasRange for LazyRawBinaryVersionMarker_1_0<'_> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> RawVersionMarker<'top> for LazyRawBinaryVersionMarker_1_0<'top> {
    fn major_minor(&self) -> (u8, u8) {
        (self.major, self.minor)
    }

    fn stream_encoding_before_marker(&self) -> IonEncoding {
        IonEncoding::Binary_1_0
    }
}

/// A value that has been identified in the input stream but whose data has not yet been read.
///
/// If only part of the value is in the input buffer, calls to [`LazyRawBinaryValue_1_0::read`] (which examines
/// bytes beyond the value's header) may return [crate::IonError::Incomplete].
///
/// `LazyRawValue`s are "unresolved," which is to say that symbol values, annotations, and
/// struct field names may or may not include a text definition. For a resolved lazy value that
/// includes a text definition for these items whenever one exists, see
/// [`crate::lazy::value::LazyValue`].
#[derive(Clone, Copy)]
pub struct LazyRawBinaryValue_1_0<'top> {
    pub(crate) encoded_value: EncodedBinaryValue<Header>,
    pub(crate) input: BinaryBuffer<'top>,
}

impl Debug for LazyRawBinaryValue_1_0<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LazyRawBinaryValue_1_0 {{\n  val={:?},\n  buf={:?}\n}}\n",
            self.encoded_value, self.input
        )
    }
}

pub type ValueParseResult<'top, F> = IonResult<RawValueRef<'top, F>>;

impl<'top> HasSpan<'top> for &'top LazyRawBinaryValue_1_0<'top> {
    fn span(&self) -> Span<'top> {
        let range = self.range();
        // Subtract the `offset()` of the BinaryBuffer to get the local indexes for start/end
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }
}

impl HasRange for &'_ LazyRawBinaryValue_1_0<'_> {
    fn range(&self) -> Range<usize> {
        self.encoded_value.annotated_value_range()
    }
}

impl<'top> LazyRawValue<'top, BinaryEncoding_1_0> for &'top LazyRawBinaryValue_1_0<'top> {
    fn ion_type(&self) -> IonType {
        (*self).ion_type()
    }

    fn is_null(&self) -> bool {
        (*self).is_null()
    }

    fn is_delimited(&self) -> bool {
        false
    }

    fn has_annotations(&self) -> bool {
        (*self).has_annotations()
    }

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        (*self).annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'top, BinaryEncoding_1_0>> {
        (*self).read()
    }

    fn annotations_span(&self) -> Span<'top> {
        let Some(range) = self.encoded_value.annotations_range() else {
            // If there are no annotations, return an empty slice positioned at the opcode
            return Span::with_offset(self.encoded_value.header_offset, &[]);
        };
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }

    fn value_span(&self) -> Span<'top> {
        let range = self.encoded_value.unannotated_value_range();
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Binary_1_0
    }
}

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
pub trait BinaryValueLiteral<'top, D: Decoder>: LazyRawValue<'top, D> {
    fn length_length(&self) -> usize;
    fn body_length(&self) -> usize;
    fn annotations_sequence_length(&self) -> usize;

    /// The span containing the annotations sequence's opcode.
    fn annotations_opcode_span(&self) -> Span<'top> {
        let annotations_span = self.annotations_span();
        if annotations_span.is_empty() {
            return annotations_span;
        }
        Span::with_offset(
            annotations_span.range().start,
            &annotations_span.bytes()[0..1],
        )
    }
    /// The span containing the annotations sequence's encoded length. In Ion 1.1, the sequence
    /// length is optional; if it is not present, the returned span will be empty.
    fn annotations_sequence_length_span(&self) -> Span<'top>;

    /// The span containing the annotations sequence wrapper's length. This span will always be
    /// empty for Ion 1.1 values.
    fn annotations_wrapper_length_span(&self) -> Span<'top>;
    /// The span containing both the opcode and length(s), but not the annotations sequence.
    fn annotations_header_span(&self) -> Span<'top> {
        let annotations_span = self.annotations_span();
        let sequence_length = self.annotations_sequence_length();
        let local_end = annotations_span.len() - sequence_length;
        let bytes = &annotations_span.bytes()[..local_end];
        Span::with_offset(annotations_span.range().start, bytes)
    }
    /// The span containing the annotations sequence.
    fn annotations_sequence_span(&self) -> Span<'top> {
        let annotations_span = self.annotations_span();
        let sequence_length = self.annotations_sequence_length();
        let local_sequence_offset = annotations_span.len() - sequence_length;
        let bytes = &annotations_span.bytes()[local_sequence_offset..];
        Span::with_offset(
            annotations_span.range().start + local_sequence_offset,
            bytes,
        )
    }
    /// The span containing the value's opcode.
    fn value_opcode_span(&self) -> Span<'top> {
        let value_span = self.value_span();
        Span::with_offset(value_span.range().start, &value_span.bytes()[0..1])
    }

    /// The span containing the value's encoded length (if it is not encoded within the opcode.)
    fn value_length_span(&self) -> Span<'top> {
        let value_span = self.value_span();
        let value_range = value_span.range();
        let opcode_length = 1;
        let length_length = self.length_length();
        let length_bytes = &value_span.bytes()[opcode_length..opcode_length + length_length];
        Span::with_offset(value_range.start + opcode_length, length_bytes)
    }

    /// The span containing the value's opcode and length.
    fn value_header_span(&self) -> Span<'top> {
        let value_span = self.value_span();
        let opcode_length = 1;
        let length_length = self.length_length();
        let header_bytes = &value_span.bytes()[..opcode_length + length_length];
        Span::with_offset(value_span.range().start, header_bytes)
    }

    /// The span containing the value's body.
    fn value_body_span(&self) -> Span<'top> {
        let value_span = self.value_span();
        let body_length = self.body_length();
        let body_bytes = &value_span.bytes()[value_span.len() - body_length..];
        Span::with_offset(value_span.range().end - body_length, body_bytes)
    }

    fn delimited_end_span(&self) -> Span<'top> {
        let bytes = self.span().bytes();
        let end = bytes.len();
        let range = if !self.is_delimited() {
            end..end
        } else {
            debug_assert!(bytes[end - 1] == 0xF0);
            end - 1..end
        };
        let end_bytes = bytes.get(range).unwrap();
        Span::with_offset(self.range().end - end_bytes.len(), end_bytes)
    }
}

impl<'top> BinaryValueLiteral<'top, BinaryEncoding_1_0> for &'top LazyRawBinaryValue_1_0<'top> {
    fn length_length(&self) -> usize {
        self.encoded_value.length_length as usize
    }

    fn body_length(&self) -> usize {
        self.encoded_value.value_body_length
    }

    fn annotations_sequence_length(&self) -> usize {
        self.encoded_value.annotations_sequence_length()
    }

    fn annotations_sequence_length_span(&self) -> Span<'top> {
        let header_span = self.annotations_header_span();
        let wrapper_length_span = self.annotations_wrapper_length_span();
        let sequence_length_offset = wrapper_length_span.range().end;
        let sequence_length_bytes = &header_span.bytes()[sequence_length_offset..];
        Span::with_offset(sequence_length_offset, sequence_length_bytes)
    }

    fn annotations_wrapper_length_span(&self) -> Span<'top> {
        let annotations_span = self.annotations_span();
        let wrapper_length_input = &annotations_span.bytes()[1..];
        // Don't read the VarUInt, but skim along looking for the END flag
        let mut num_varuint_bytes = 1;
        for &byte in wrapper_length_input {
            if byte >= 0b1000_0000 {
                break;
            }
            num_varuint_bytes += 1;
        }
        let sequence_length_bytes = &wrapper_length_input[..num_varuint_bytes];
        Span::with_offset(annotations_span.range().start + 1, sequence_length_bytes)
    }
}

#[derive(Copy, Clone)]
pub struct EncodedBinaryAnnotations_1_0<'a, 'top> {
    value: &'a LazyRawBinaryValue_1_0<'top>,
}

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
impl<'top> EncodedBinaryAnnotations_1_0<'_, 'top> {
    /// Returns the input stream index range that contains the bytes representing the complete
    /// annotations wrapper, including its opcode, wrapper length, annotations sequence length,
    /// and the sequence itself.
    pub fn range(&self) -> Range<usize> {
        self.value.encoded_value.annotations_range().unwrap()
    }

    /// Returns the encoded bytes representing the complete annotations wrapper, including its
    /// opcode, wrapper length, annotations sequence length, and the sequence itself.
    pub fn span(&self) -> Span<'top> {
        let range = self.range();
        let start = range.start - self.value.input.offset();
        let end = start + range.len();
        let bytes = &self.value.input.bytes()[start..end];
        Span::with_offset(range.start, bytes)
    }

    /// Returns the input stream index range that contains the bytes representing the annotations
    /// wrapper's opcode.
    pub fn opcode_range(&self) -> Range<usize> {
        let stream_start = self.range().start;
        stream_start..stream_start + 1
    }

    /// Returns the encoded bytes representing the annotations wrapper's opcode.
    pub fn opcode_span(&self) -> Span<'top> {
        let stream_range = self.opcode_range();
        let local_range = 0..1;
        let bytes = &self.span().bytes()[local_range];
        Span::with_offset(stream_range.start, bytes)
    }

    /// Returns the encoded bytes representing the annotations wrapper's header (that is: the opcode,
    /// wrapper length, and sequence length, but not the annotations sequence).
    pub fn header_span(&self) -> Span<'top> {
        let range = self.range();
        let sequence_length = self.value.encoded_value.annotations_sequence_length as usize;
        let local_end = range.len() - sequence_length;
        let bytes = &self.span().bytes()[..local_end];
        Span::with_offset(range.start, bytes)
    }

    // TODO: separate span accessors for the wrapper length and sequence length?

    /// Returns the encoded bytes representing the annotations wrapper's annotations sequence.
    pub fn sequence_span(&self) -> Span<'top> {
        let range = self.range();
        let sequence_length = self.value.encoded_value.annotations_sequence_length as usize;
        let local_start = range.len() - sequence_length;
        let bytes = &self.span().bytes()[local_start..];
        let stream_start = range.start + local_start;
        Span::with_offset(stream_start, bytes)
    }
}

#[derive(Copy, Clone)]
pub struct EncodedBinaryValueData_1_0<'a, 'top> {
    value: &'a LazyRawBinaryValue_1_0<'top>,
}

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
impl<'top> EncodedBinaryValueData_1_0<'_, 'top> {
    /// Returns the input stream index range that contains the bytes representing the complete value,
    /// including its opcode, length, and body.
    pub fn range(&self) -> Range<usize> {
        let encoded = &self.value.encoded_value;
        encoded.unannotated_value_range()
    }

    /// Returns the encoded bytes that represent the complete value, including its opcode, length,
    /// and body.
    pub fn span(&self) -> Span<'top> {
        let stream_range = self.range();
        let offset = self.value.input.offset();
        let local_range = stream_range.start - offset..stream_range.end - offset;
        let bytes = &self.value.input.bytes()[local_range];
        Span::with_offset(stream_range.start, bytes)
    }

    /// Returns the input stream index range that contains the bytes representing the
    /// value's opcode. In Ion 1.0, this is always a range of a single byte.
    fn opcode_range(&self) -> Range<usize> {
        let offset = self.range().start;
        offset..offset + 1
    }

    /// Returns the encoded bytes representing the value's opcode. In Ion 1.0, this is always a
    /// slice of a single byte.
    pub fn opcode_span(&self) -> Span<'top> {
        let stream_range = self.opcode_range();
        let bytes = &self.span().bytes()[0..1];
        Span::with_offset(stream_range.start, bytes)
    }

    /// Returns the input stream index range that contains the bytes representing the
    /// value's length as a `VarUInt`. If the value's length was able to be encoded directly in
    /// the type descriptor byte, the range returned will be empty.
    pub fn trailing_length_range(&self) -> Range<usize> {
        let range = self.range();
        range.start + 1..range.start + 1 + self.value.encoded_value.length_length as usize
    }

    /// Returns the encoded bytes representing the value's length as a `VarUInt`.
    /// If the value's length was able to be encoded directly in the type descriptor byte,
    /// the slice returned will be empty.
    pub fn trailing_length_span(&self) -> Span<'top> {
        let stream_range = self.trailing_length_range();
        let offset = self.value.input.offset();
        let local_range = stream_range.start - offset..stream_range.end - offset;
        let bytes = &self.value.input.bytes()[local_range];
        Span::with_offset(stream_range.start, bytes)
    }

    /// Returns the input stream index range that contains the bytes representing the
    /// value's body (that is: the content of the value that follows its opcode and length).
    pub fn body_range(&self) -> Range<usize> {
        let encoded = &self.value.encoded_value;
        let body_offset = encoded.header_length();
        let body_length = encoded.value_body_length();
        let start = self.range().start + body_offset;
        let end = start + body_length;
        start..end
    }

    /// Returns the encoded bytes representing the value's body (that is: the content of the value
    /// that follows its opcode and length).
    pub fn body_span(&self) -> Span<'top> {
        let body_range = self.body_range();
        let body_length = body_range.len();
        let value_bytes = self.span().bytes();
        let body_bytes = &value_bytes[value_bytes.len() - body_length..];
        Span::with_offset(body_range.start, body_bytes)
    }
}

impl<'top> LazyRawBinaryValue_1_0<'top> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.input.context()
    }

    #[cfg(feature = "experimental-tooling-apis")]
    pub fn encoded_annotations(&self) -> Option<EncodedBinaryAnnotations_1_0<'_, 'top>> {
        if self.has_annotations() {
            Some(EncodedBinaryAnnotations_1_0 { value: self })
        } else {
            None
        }
    }

    #[cfg(feature = "experimental-tooling-apis")]
    pub fn encoded_data(&self) -> EncodedBinaryValueData_1_0<'_, 'top> {
        EncodedBinaryValueData_1_0 { value: self }
    }

    /// Indicates the Ion data type of this value. Calling this method does not require additional
    /// parsing of the input stream.
    pub fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    pub fn is_null(&self) -> bool {
        self.encoded_value.header().is_null()
    }

    /// Returns `true` if this value has a non-empty annotations sequence; otherwise, returns `false`.
    fn has_annotations(&self) -> bool {
        self.encoded_value.has_annotations()
    }

    /// Returns an `BinaryBuffer` that contains the bytes comprising this value's encoded
    /// annotations sequence.
    fn annotations_sequence(&self) -> BinaryBuffer<'top> {
        let offset_and_length = self
            .encoded_value
            .annotations_sequence_offset()
            .map(|offset| (offset, self.encoded_value.annotations_sequence_length()));
        let (sequence_offset, sequence_length) = match offset_and_length {
            None => {
                // If there are no annotations, return an empty slice positioned on the type
                // descriptor.
                return self.input.slice(0, 0);
            }
            Some(offset_and_length) => offset_and_length,
        };
        let local_sequence_offset = sequence_offset - self.input.offset();

        self.input.slice(local_sequence_offset, sequence_length)
    }

    /// Returns an iterator over this value's unresolved annotation symbols.
    pub fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        RawBinaryAnnotationsIterator::new(self.annotations_sequence())
    }

    /// Reads this value's data, returning it as a [`RawValueRef`]. If this value is a container,
    /// calling this method will not read additional data; the `RawValueRef` will provide a
    /// [`LazyRawBinaryList_1_0`], [`LazyRawBinarySExp_1_0`], or [`LazyRawBinaryStruct_1_0`]
    /// that can be traversed to access the container's contents.
    pub fn read(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        if self.is_null() {
            let raw_value_ref = RawValueRef::Null(self.ion_type());
            return Ok(raw_value_ref);
        }

        match self.ion_type() {
            IonType::Null => unreachable!("all null types handled above"),
            IonType::Bool => self.read_bool(),
            IonType::Int => self.read_int(),
            IonType::Float => self.read_float(),
            IonType::Decimal => self.read_decimal(),
            IonType::Timestamp => self.read_timestamp(),
            IonType::Symbol => self.read_symbol(),
            IonType::String => self.read_string(),
            IonType::Clob => self.read_clob(),
            IonType::Blob => self.read_blob(),
            IonType::List => self.read_list(),
            IonType::SExp => self.read_sexp(),
            IonType::Struct => self.read_struct(),
        }
    }

    /// Returns the encoded byte slice representing this value's data.
    pub fn value_body(&self) -> &'top [u8] {
        let value_total_length = self.encoded_value.total_length();
        debug_assert!(self.input.len() >= value_total_length);
        let value_body_length = self.encoded_value.value_body_length();
        let value_offset = value_total_length - value_body_length;
        self.input.bytes_range(value_offset, value_body_length)
    }

    /// Returns an [`BinaryBuffer`] containing whatever bytes of this value's body are currently
    /// available. This method is used to construct lazy containers, which are not required to be
    /// fully buffered before reading begins.
    pub(crate) fn available_body(&self) -> BinaryBuffer<'top> {
        let value_total_length = self.encoded_value.total_length();
        let value_body_length = self.encoded_value.value_body_length();
        let value_offset = value_total_length - value_body_length;

        let bytes_needed = std::cmp::min(self.input.len() - value_offset, value_body_length);
        let buffer_slice = self.input.slice(value_offset, bytes_needed);
        buffer_slice
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a bool.
    fn read_bool(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Bool);
        let representation = self.encoded_value.header().length_code;
        let value = match representation {
            0 => false,
            1 => true,
            invalid => {
                return IonResult::decoding_error(format!(
                "found a boolean value with an illegal representation (must be 0 or 1): {invalid}",
            ))
            }
        };
        Ok(RawValueRef::Bool(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as an int.
    fn read_int(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Int);
        // `value_body()` returns a buffer starting at the body of the value.
        let uint_bytes = self.value_body();
        let magnitude: Int = DecodedUInt::uint_from_slice(uint_bytes).into();

        use crate::binary::type_code::IonTypeCode::*;
        let value = match (self.encoded_value.header.ion_type_code, magnitude) {
            (PositiveInteger, integer) => integer,
            (NegativeInteger, integer) if integer.is_zero() => {
                return IonResult::decoding_error(
                    "found a negative integer (typecode=3) with a value of 0",
                );
            }
            (NegativeInteger, integer) => integer.neg(),
            _itc => return IonResult::decoding_error("unexpected ion type code"),
        };
        Ok(RawValueRef::Int(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a float.
    fn read_float(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Float);
        let ieee_bytes = self.value_body();
        let number_of_bytes = self.encoded_value.value_body_length();
        let value = match number_of_bytes {
            0 => 0f64,
            4 => f64::from(f32::from_be_bytes(
                ieee_bytes.try_into().expect("already confirmed length"),
            )),
            8 => f64::from_be_bytes(ieee_bytes.try_into().expect("already confirmed length")),
            _ => return IonResult::decoding_error("encountered a float with an illegal length"),
        };
        Ok(RawValueRef::Float(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a decimal.
    fn read_decimal(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Decimal);

        if self.encoded_value.value_body_length() == 0 {
            return Ok(RawValueRef::Decimal(Decimal::new(0i32, 0i64)));
        }

        // Skip the type descriptor and length bytes
        let input = BinaryBuffer::new(self.context(), self.value_body());

        let (exponent_var_int, remaining) = input.read_var_int()?;
        let coefficient_size_in_bytes =
            self.encoded_value.value_body_length() - exponent_var_int.size_in_bytes();

        let exponent = exponent_var_int.value();
        let (coefficient, _remaining) = remaining.read_int(coefficient_size_in_bytes)?;

        if coefficient.is_negative_zero() {
            return Ok(RawValueRef::Decimal(Decimal::negative_zero_with_exponent(
                exponent,
            )));
        }

        Ok(RawValueRef::Decimal(Decimal::new(coefficient, exponent)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a timestamp.
    fn read_timestamp(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Timestamp);

        let input = BinaryBuffer::new(self.context(), self.value_body());

        let (offset, input) = input.read_var_int()?;
        let is_known_offset = !offset.is_negative_zero();
        let offset_minutes = offset.value() as i32;
        let (year_var_uint, input) = input.read_var_uint()?;
        let year = year_var_uint.value() as u32;

        // Year precision

        let builder = Timestamp::with_year(year);
        if input.is_empty() {
            let timestamp = builder.build()?;
            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Month precision

        let (month_var_uint, input) = input.read_var_uint()?;
        let month = month_var_uint.value() as u32;
        let builder = builder.with_month(month);
        if input.is_empty() {
            let timestamp = builder.build()?;
            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Day precision

        let (day_var_uint, input) = input.read_var_uint()?;
        let day = day_var_uint.value() as u32;
        let builder = builder.with_day(day);
        if input.is_empty() {
            let timestamp = builder.build()?;
            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Hour-and-minute precision

        let (hour_var_uint, input) = input.read_var_uint()?;
        let hour = hour_var_uint.value() as u32;
        if input.is_empty() {
            return IonResult::decoding_error("timestamps with an hour must also specify a minute");
        }
        let (minute_var_uint, input) = input.read_var_uint()?;
        let minute = minute_var_uint.value() as u32;
        let builder = builder.with_hour_and_minute(hour, minute);
        if input.is_empty() {
            let timestamp = if is_known_offset {
                builder.localize_to_offset(offset_minutes).build()
            } else {
                builder.build()
            }?;
            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Second precision

        let (second_var_uint, input) = input.read_var_uint()?;
        let second = second_var_uint.value() as u32;
        let builder = builder.with_second(second);
        if input.is_empty() {
            let timestamp = if is_known_offset {
                builder.localize_to_offset(offset_minutes).build()
            } else {
                builder.build()
            }?;
            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Fractional second precision

        let (subsecond_exponent_var_uint, input) = input.read_var_int()?;
        let subsecond_exponent = subsecond_exponent_var_uint.value();
        // The remaining bytes represent the coefficient.
        let coefficient_size_in_bytes = self.encoded_value.value_body_length() - input.offset();
        let (subsecond_coefficient, _input) = if coefficient_size_in_bytes == 0 {
            (DecodedInt::zero(), input)
        } else {
            input.read_int(coefficient_size_in_bytes)?
        };

        let builder = builder
            .with_fractional_seconds(Decimal::new(subsecond_coefficient, subsecond_exponent));
        let timestamp = if is_known_offset {
            builder.localize_to_offset(offset_minutes).build()
        } else {
            builder.build()
        }?;

        Ok(RawValueRef::Timestamp(timestamp))
    }

    /// Helper method called by [`Self::read_symbol`]. Reads the current value as a symbol ID.
    fn read_symbol_id(&self) -> IonResult<SymbolId> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Symbol);
        let uint_bytes = self.value_body();
        if uint_bytes.len() > mem::size_of::<usize>() {
            return IonResult::decoding_error(
                "found a symbol ID that was too large to fit in a usize",
            );
        }
        // We've already confirmed that the uint fits in a `usize`, so we can `unwrap()` the result
        // of this method and then cast its output to a `usize`.
        let mut buffer = [0u8; size_of::<usize>()];
        buffer[size_of::<usize>() - uint_bytes.len()..].copy_from_slice(uint_bytes);
        let magnitude = usize::from_be_bytes(buffer);
        Ok(magnitude)
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a symbol.
    fn read_symbol(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Symbol);
        self.read_symbol_id()
            .map(|sid| RawValueRef::Symbol(RawSymbolRef::SymbolId(sid)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a string.
    fn read_string(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::String);
        let raw_bytes = self.value_body();
        let text = std::str::from_utf8(raw_bytes)
            .map_err(|_| IonError::decoding_error("found a string with invalid utf-8 data"))?;
        Ok(RawValueRef::String(StrRef::from(text)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a blob.
    fn read_blob(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Blob);
        let bytes = self.value_body();
        Ok(RawValueRef::Blob(bytes.into()))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a clob.
    fn read_clob(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Clob);
        let bytes = self.value_body();
        Ok(RawValueRef::Clob(bytes.into()))
    }

    /// Returns an error if this container's children would be nested more deeply than
    /// [`MAX_READ_WRITE_DEPTH`]. The stored depth saturates at 255, so with a limit greater than
    /// 255, this never returns an error.
    #[inline]
    fn check_container_depth(&self) -> IonResult<()> {
        if u16::from(self.encoded_value.depth) >= MAX_READ_WRITE_DEPTH {
            return cold_path!(IonResult::decoding_error(max_read_depth_exceeded_message()));
        }
        Ok(())
    }

    /// Helper method called by [`Self::read`]. Reads the current value as an S-expression.
    fn read_sexp(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::SExp);
        self.check_container_depth()?;
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let allocator = self.context().allocator();
        let value_ref = allocator.alloc_with(|| lazy_value);
        let lazy_sequence = LazyRawBinarySequence_1_0 { value: value_ref };
        let lazy_sexp = LazyRawBinarySExp_1_0 {
            sequence: lazy_sequence,
        };
        Ok(RawValueRef::SExp(lazy_sexp))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a list.
    fn read_list(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::List);
        self.check_container_depth()?;
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let allocator = self.context().allocator();
        let value_ref = allocator.alloc_with(|| lazy_value);
        let lazy_sequence = LazyRawBinarySequence_1_0 { value: value_ref };
        let lazy_list = LazyRawBinaryList_1_0 {
            sequence: lazy_sequence,
        };
        Ok(RawValueRef::List(lazy_list))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a struct.
    fn read_struct(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Struct);
        self.check_container_depth()?;
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let allocator = self.context().allocator();
        let value_ref = allocator.alloc_with(|| lazy_value);
        let lazy_struct = LazyRawBinaryStruct_1_0 { value: value_ref };
        Ok(RawValueRef::Struct(lazy_struct))
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::constants::MAX_READ_WRITE_DEPTH;
    use crate::lazy::any_encoding::AnyEncoding;
    use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
    use crate::lazy::binary::test_utilities::{
        binary_nested, binary_type_descriptor, binary_value, to_binary_ion,
        LAZY_BINARY_DEPTH_IS_CHECKED,
    };
    use crate::lazy::decoder::LazyRawSequence;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::read_config::assert_max_read_depth_exceeded;
    use crate::result::IonFailure;
    use crate::{
        v1_0, Decoder, EncodingContext, IonError, IonInput, IonResult, IonType, IonVersion,
        LazyValue, Reader, ValueRef,
    };

    const MAX: usize = MAX_READ_WRITE_DEPTH as usize;

    #[test]
    fn annotations_sequence() -> IonResult<()> {
        let data = &to_binary_ion(
            r#"
            $ion_symbol_table::{symbols: ["foo"]}
            foo // binary writer will omit the symtab if we don't use a symbol 
        "#,
        )?;
        let context = EncodingContext::empty();
        let mut reader = LazyRawBinaryReader_1_0::new(context.get_ref(), data);
        let _ivm = reader.next()?.expect_ivm()?;
        let value = reader.next()?.expect_value()?;
        let annotations_sequence = value.annotations_sequence();
        assert_eq!(annotations_sequence.len(), 1);
        assert_eq!(annotations_sequence.offset(), 6);
        assert_eq!(annotations_sequence.bytes()[0], 0x83u8); // 0x83 == $3 == $ion_symbol_table
        Ok(())
    }

    /// The encoding of the int `1`.
    const INT: [u8; 2] = [0x21, 0x01];

    /// Encodes a container of type `kind` whose only child is `child`. A struct's field is named
    /// `name` (`$4`), as in `binary_nested`.
    fn container_of(kind: IonType, child: &[u8]) -> Vec<u8> {
        let field_name: &[u8] = if kind == IonType::Struct {
            &[0x84]
        } else {
            &[]
        };
        binary_value(binary_type_descriptor(kind), [field_name, child].concat())
    }

    /// Wraps `value` in an annotations wrapper with one annotation, `name` (`$4`).
    fn annotated(value: Vec<u8>) -> Vec<u8> {
        binary_value(0xE0, [&[0x81, 0x84][..], &value].concat())
    }

    /// With the raw binary reader, reads the value at `depth` in the first top-level value of
    /// `data`, reaching it through the first child of each enclosing container. Returns an error if
    /// reaching the value fails, and otherwise the result of reading it.
    fn read_at_depth(data: &[u8], depth: usize) -> IonResult<IonResult<()>> {
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        let mut reader = LazyRawBinaryReader_1_0::new(context.get_ref(), data);
        let _ivm = reader.next()?.expect_ivm()?;
        let mut value = reader.next()?.expect_value()?;
        for _ in 0..depth {
            let child = match value.read()? {
                RawValueRef::List(list) => list.iter().next(),
                RawValueRef::SExp(sexp) => sexp.iter().next(),
                RawValueRef::Struct(struct_) => struct_
                    .iter()
                    .next()
                    .map(|field| Ok(field?.expect_name_value()?.1)),
                other => return IonResult::illegal_operation(format!("{other:?} has no children")),
            };
            value = child.ok_or_else(|| IonError::illegal_operation("empty container"))??;
        }
        Ok(value.read().map(|_| ()))
    }

    /// Asserts that `result`, from reading a container at depth `MAX`, is a maximum read depth
    /// error. With a limit greater than 255, lazy binary navigation does not check the limit, so
    /// the read succeeds instead.
    #[track_caller]
    fn assert_rejected_at_max(result: IonResult<()>) {
        if LAZY_BINARY_DEPTH_IS_CHECKED {
            assert_max_read_depth_exceeded(result);
        } else {
            assert!(result.is_ok(), "{result:?}");
        }
    }

    #[rstest]
    fn reads_values_at_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        #[values(false, true)] null_innermost: bool,
    ) -> IonResult<()> {
        let innermost = if null_innermost {
            vec![binary_type_descriptor(kind) | 0x0F]
        } else {
            INT.to_vec()
        };
        read_at_depth(&binary_nested(kind, MAX, innermost), MAX)?
    }

    /// Reading the container at depth `MAX` fails whether or not it has children, and whether or
    /// not it is annotated. Its parent can still be read.
    #[rstest]
    fn rejects_containers_whose_children_exceed_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        #[values(false, true)] empty: bool,
        #[values(false, true)] annotate: bool,
    ) -> IonResult<()> {
        let mut container = if empty {
            vec![binary_type_descriptor(kind)]
        } else {
            container_of(kind, &INT)
        };
        if annotate {
            container = annotated(container);
        }
        let data = binary_nested(kind, MAX, container);
        read_at_depth(&data, MAX - 1)??;
        assert_rejected_at_max(read_at_depth(&data, MAX)?);
        Ok(())
    }

    /// Only reading a container past the limit fails, not reading the top-level value that
    /// encloses it.
    #[rstest]
    fn reads_top_level_values_with_children_beyond_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
    ) -> IonResult<()> {
        let data = binary_nested(kind, 2 * MAX + 1, INT.to_vec());
        read_at_depth(&data, 0)??;
        assert_rejected_at_max(read_at_depth(&data, MAX)?);
        Ok(())
    }

    /// Asserts that `text`, the `Debug` output of a value nested past the limit, has a placeholder
    /// for the container that cannot be read, or that it has none when lazy binary navigation does
    /// not check the limit.
    #[track_caller]
    fn assert_has_placeholder(text: &str) {
        let has_placeholder = text.contains("<error: ");
        assert_eq!(has_placeholder, LAZY_BINARY_DEPTH_IS_CHECKED, "{text}");
    }

    /// The raw struct's `Debug` impl reads its fields; the raw list and s-expression impls do not.
    #[test]
    fn formats_raw_structs_nested_beyond_the_maximum_depth() -> IonResult<()> {
        let data = binary_nested(IonType::Struct, MAX + 1, INT.to_vec());
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        let mut reader = LazyRawBinaryReader_1_0::new(context.get_ref(), &data);
        let _ivm = reader.next()?.expect_ivm()?;
        let text = format!("{:?}", reader.next()?.expect_value()?.read()?);
        assert_has_placeholder(&text);
        Ok(())
    }

    /// Returns the first child of `value`, a list, s-expression, or struct.
    fn first_child<D: Decoder>(value: LazyValue<'_, D>) -> IonResult<LazyValue<'_, D>> {
        let child = match value.read()? {
            ValueRef::List(list) => list.iter().next(),
            ValueRef::SExp(sexp) => sexp.iter().next(),
            ValueRef::Struct(struct_) => struct_.iter().next().map(|field| Ok(field?.value())),
            other => return IonResult::illegal_operation(format!("{other:?} has no children")),
        };
        child.ok_or_else(|| IonError::illegal_operation("empty container"))?
    }

    /// Returns the value at `depth` in the next top-level value that `reader` reads, reaching it
    /// through the first child of each enclosing container.
    fn value_at_depth<D: Decoder, I: IonInput>(
        reader: &mut Reader<D, I>,
        depth: usize,
    ) -> IonResult<LazyValue<'_, D>> {
        let mut value = reader.expect_next()?;
        for _ in 0..depth {
            value = first_child(value)?;
        }
        Ok(value)
    }

    /// With a `Reader` for `AnyEncoding` if `any_encoding` is true and for `v1_0::Binary`
    /// otherwise, reads the value at depth `MAX` in the first top-level value of `data`. Returns
    /// an error if reaching the value fails, and otherwise the result of reading it.
    fn reader_read_at_max(data: Vec<u8>, any_encoding: bool) -> IonResult<IonResult<()>> {
        let result = if any_encoding {
            value_at_depth(&mut Reader::new(AnyEncoding, data)?, MAX)?
                .read()
                .map(drop)
        } else {
            value_at_depth(&mut Reader::new(v1_0::Binary, data)?, MAX)?
                .read()
                .map(drop)
        };
        Ok(result)
    }

    #[rstest]
    fn reader_reads_values_at_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        #[values(false, true)] any_encoding: bool,
    ) -> IonResult<()> {
        reader_read_at_max(binary_nested(kind, MAX, INT.to_vec()), any_encoding)?
    }

    #[rstest]
    fn reader_rejects_containers_whose_children_exceed_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
        #[values(false, true)] any_encoding: bool,
    ) -> IonResult<()> {
        let data = binary_nested(kind, MAX + 1, INT.to_vec());
        assert_rejected_at_max(reader_read_at_max(data, any_encoding)?);
        Ok(())
    }

    /// A `LazyElement` made from a value keeps the value's depth, so it is limited as the value is.
    #[rstest]
    fn lazy_elements_keep_the_depth_of_their_values(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
    ) -> IonResult<()> {
        let data = binary_nested(kind, MAX + 1, INT.to_vec());
        let parent =
            value_at_depth(&mut Reader::new(v1_0::Binary, data.clone())?, MAX - 1)?.to_owned();
        let container = value_at_depth(&mut Reader::new(v1_0::Binary, data)?, MAX)?.to_owned();
        parent.read()?;
        assert_rejected_at_max(container.read().map(drop));
        Ok(())
    }

    /// Reads the first top-level value in `data` with `expect_i64`, whose error describes the value
    /// it found using `Debug`.
    fn expect_i64(data: Vec<u8>) -> IonResult<i64> {
        Reader::new(v1_0::Binary, data)?
            .expect_next()?
            .read()?
            .expect_i64()
    }

    #[track_caller]
    fn assert_not_an_int(result: IonResult<i64>) {
        match result {
            Err(IonError::Decoding(e)) if e.description().starts_with("expected an int") => {}
            other => panic!("expected an error for a value that is not an int, found {other:?}"),
        }
    }

    #[rstest]
    fn expect_i64_rejects_containers_nested_beyond_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
    ) {
        assert_not_an_int(expect_i64(binary_nested(kind, MAX + 1, INT.to_vec())));
    }

    #[rstest]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn expect_i64_rejects_containers_nested_far_beyond_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
    ) {
        // Formatting the value recurses once per level until a container cannot be read, so
        // without the depth check it would recurse 100,000 times.
        if !LAZY_BINARY_DEPTH_IS_CHECKED {
            return;
        }
        assert_not_an_int(expect_i64(binary_nested(kind, 100_000, INT.to_vec())));
    }

    /// Formatting a value writes a placeholder for a container that cannot be read.
    #[rstest]
    fn formats_values_nested_beyond_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
    ) -> IonResult<()> {
        let mut reader = Reader::new(v1_0::Binary, binary_nested(kind, MAX + 1, INT.to_vec()))?;
        let text = format!("{:?}", reader.expect_next()?);
        assert_has_placeholder(&text);
        Ok(())
    }

    /// Formatting the container at the maximum depth, and the struct field that holds it,
    /// writes a placeholder for the container's contents.
    #[rstest]
    fn formats_the_container_at_the_maximum_depth(
        #[values(IonType::List, IonType::SExp, IonType::Struct)] kind: IonType,
    ) -> IonResult<()> {
        let data = binary_nested(kind, MAX + 1, INT.to_vec());
        let mut reader = Reader::new(v1_0::Binary, data)?;
        let mut value = reader.expect_next()?;
        for level in 0..MAX {
            value = match value.read()? {
                ValueRef::List(list) => list.iter().next().expect("a child")?,
                ValueRef::SExp(sexp) => sexp.iter().next().expect("a child")?,
                ValueRef::Struct(strukt) => {
                    let field = strukt.iter().next().expect("a field")?;
                    if level == MAX - 1 {
                        assert_has_placeholder(&format!("{field:?}"));
                    }
                    field.value()
                }
                other => panic!("expected a container, found {other:?}"),
            };
        }
        assert_has_placeholder(&format!("{value:?}"));
        Ok(())
    }
}
