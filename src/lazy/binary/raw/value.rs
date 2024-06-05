#![allow(non_camel_case_types)]

use crate::binary::int::DecodedInt;
use crate::binary::uint::DecodedUInt;
use crate::lazy::binary::encoded_value::EncodedValue;
use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct_1_0;
use crate::lazy::binary::raw::sequence::{
    LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0, LazyRawBinarySequence_1_0,
};
use crate::lazy::binary::raw::type_descriptor::Header;
use crate::lazy::decoder::{HasRange, HasSpan, LazyRawValue, RawVersionMarker};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::span::Span;
use crate::lazy::str_ref::StrRef;
use crate::result::IonFailure;
use crate::types::SymbolId;
use crate::{Decimal, Int, IonError, IonResult, IonType, RawSymbolRef, Timestamp};
use std::fmt::{Debug, Formatter};
use std::ops::Range;
use std::{fmt, mem};

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryVersionMarker_1_0<'top> {
    major: u8,
    minor: u8,
    input: ImmutableBuffer<'top>,
}

impl<'top> LazyRawBinaryVersionMarker_1_0<'top> {
    pub fn new(input: ImmutableBuffer<'top>, major: u8, minor: u8) -> Self {
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

impl<'top> HasRange for LazyRawBinaryVersionMarker_1_0<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> RawVersionMarker<'top> for LazyRawBinaryVersionMarker_1_0<'top> {
    fn version(&self) -> (u8, u8) {
        (self.major, self.minor)
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
    pub(crate) encoded_value: EncodedValue<Header>,
    pub(crate) input: ImmutableBuffer<'top>,
}

impl<'top> Debug for LazyRawBinaryValue_1_0<'top> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LazyRawBinaryValue_1_0 {{\n  val={:?},\n  buf={:?}\n}}\n",
            self.encoded_value, self.input
        )
    }
}

pub type ValueParseResult<'top, F> = IonResult<RawValueRef<'top, F>>;

impl<'top> HasSpan<'top> for LazyRawBinaryValue_1_0<'top> {
    fn span(&self) -> Span<'top> {
        let range = self.range();
        // Subtract the `offset()` of the ImmutableBuffer to get the local indexes for start/end
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }
}

impl<'top> HasRange for LazyRawBinaryValue_1_0<'top> {
    fn range(&self) -> Range<usize> {
        self.encoded_value.annotated_value_range()
    }
}

impl<'top> LazyRawValue<'top, BinaryEncoding_1_0> for LazyRawBinaryValue_1_0<'top> {
    fn ion_type(&self) -> IonType {
        self.ion_type()
    }

    fn is_null(&self) -> bool {
        self.is_null()
    }

    fn has_annotations(&self) -> bool {
        self.has_annotations()
    }

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'top, BinaryEncoding_1_0>> {
        self.read()
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
}

#[derive(Copy, Clone)]
pub struct EncodedBinaryAnnotations_1_0<'a, 'top> {
    value: &'a LazyRawBinaryValue_1_0<'top>,
}

impl<'a, 'top> EncodedBinaryAnnotations_1_0<'a, 'top> {
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

impl<'a, 'top> EncodedBinaryValueData_1_0<'a, 'top> {
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
        let body_offset = encoded.annotations_header_length as usize + encoded.header_length();
        let body_length = encoded.value_body_length();
        let start = self.range().start + body_offset;
        let end = start + body_length;
        start..end
    }

    /// Returns the encoded bytes representing the value's body (that is: the content of the value
    /// that follows its opcode and length).
    pub fn body_span(&self) -> Span<'top> {
        let stream_range = self.body_range();
        let offset = self.value.input.offset();
        let local_range = stream_range.start - offset..stream_range.end - offset;
        let bytes = &self.span().bytes()[local_range];
        Span::with_offset(stream_range.start, bytes)
    }
}

impl<'top> LazyRawBinaryValue_1_0<'top> {
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

    /// Returns an `ImmutableBuffer` that contains the bytes comprising this value's encoded
    /// annotations sequence.
    fn annotations_sequence(&self) -> ImmutableBuffer<'top> {
        let offset_and_length = self
            .encoded_value
            .annotations_sequence_offset()
            .map(|offset| {
                (
                    offset,
                    self.encoded_value.annotations_sequence_length().unwrap(),
                )
            });
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

    /// Returns an [`ImmutableBuffer`] containing whatever bytes of this value's body are currently
    /// available. This method is used to construct lazy containers, which are not required to be
    /// fully buffered before reading begins.
    pub(crate) fn available_body(&self) -> ImmutableBuffer<'top> {
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
                    "found a boolean value with an illegal representation (must be 0 or 1): {}",
                    invalid
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
        let magnitude: Int = DecodedUInt::uint_from_slice(uint_bytes)?.try_into()?;

        use crate::binary::type_code::IonTypeCode::*;
        use num_traits::Zero;
        let value = match (self.encoded_value.header.ion_type_code, magnitude) {
            (PositiveInteger, integer) => integer,
            (NegativeInteger, integer) if integer.is_zero() => {
                return IonResult::decoding_error(
                    "found a negative integer (typecode=3) with a value of 0",
                );
            }
            (NegativeInteger, integer) => -integer,
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
        let input = ImmutableBuffer::new(self.value_body());

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

        let input = ImmutableBuffer::new(self.value_body());

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
                builder.build_utc_fields_at_offset(offset_minutes)
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
                builder.build_utc_fields_at_offset(offset_minutes)
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
            builder.build_utc_fields_at_offset(offset_minutes)
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
        let magnitude = DecodedUInt::uint_from_slice_unchecked(uint_bytes);
        Ok(magnitude as usize)
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

    /// Helper method called by [`Self::read`]. Reads the current value as an S-expression.
    fn read_sexp(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::SExp);
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let lazy_sequence = LazyRawBinarySequence_1_0 { value: lazy_value };
        let lazy_sexp = LazyRawBinarySExp_1_0 {
            sequence: lazy_sequence,
        };
        Ok(RawValueRef::SExp(lazy_sexp))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a list.
    fn read_list(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::List);
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let lazy_sequence = LazyRawBinarySequence_1_0 { value: lazy_value };
        let lazy_list = LazyRawBinaryList_1_0 {
            sequence: lazy_sequence,
        };
        Ok(RawValueRef::List(lazy_list))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a struct.
    fn read_struct(&self) -> ValueParseResult<'top, BinaryEncoding_1_0> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Struct);
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let lazy_struct = LazyRawBinaryStruct_1_0 { value: lazy_value };
        Ok(RawValueRef::Struct(lazy_struct))
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::IonResult;

    #[test]
    fn annotations_sequence() -> IonResult<()> {
        let data = &to_binary_ion(
            r#"
            $ion_symbol_table::{symbols: ["foo"]}
            foo // binary writer will omit the symtab if we don't use a symbol 
        "#,
        )?;
        let mut reader = LazyRawBinaryReader_1_0::new(data);
        let _ivm = reader.next()?.expect_ivm()?;
        let value = reader.next()?.expect_value()?;
        let annotations_sequence = value.annotations_sequence();
        assert_eq!(annotations_sequence.len(), 1);
        assert_eq!(annotations_sequence.offset(), 6);
        assert_eq!(annotations_sequence.bytes()[0], 0x83u8); // 0x83 == $3 == $ion_symbol_table
        Ok(())
    }
}
