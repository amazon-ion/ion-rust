#![allow(non_camel_case_types)]

use std::fmt::Debug;
use std::ops::Range;

use crate::lazy::decoder::{HasRange, HasSpan, RawVersionMarker};
use crate::lazy::span::Span;
use crate::{
    lazy::{
        binary::{
            encoded_value::{EncodedHeader, EncodedValue},
            raw::{
                v1_1::{
                    annotations_iterator::RawBinaryAnnotationsIterator_1_1,
                    immutable_buffer::ImmutableBuffer, type_descriptor::ION_1_1_TYPED_NULL_TYPES,
                    Header, OpcodeType,
                },
                value::ValueParseResult,
            },
        },
        decoder::{Decoder, LazyRawFieldExpr, LazyRawValue, LazyRawValueExpr},
        encoder::binary::v1_1::fixed_int::FixedInt,
        encoding::BinaryEncoding_1_1,
        raw_value_ref::RawValueRef,
    },
    result::IonFailure,
    types::{HasMinute, SymbolId, Timestamp, TimestampBuilder},
    IonError, IonResult, IonType, RawSymbolRef,
};
use num_traits::PrimInt;

const LONG_TIMESTAMP_OFFSET_BIAS: i32 = -60 * 24;

trait ExtractBitmask: PrimInt {
    /// Given a bitmask, and a value, extract_bitmask extracts the desired bits from value and shifts
    /// to align the extracted bits to the least significant bit in the returned value.
    #[inline(always)]
    fn extract_bitmask(self, mask: Self) -> Self {
        (self & mask) >> (mask.trailing_zeros() as usize)
    }
}

impl ExtractBitmask for u8 {}
impl ExtractBitmask for u16 {}
impl ExtractBitmask for u32 {}
impl ExtractBitmask for u64 {}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryVersionMarker_1_1<'top> {
    major: u8,
    minor: u8,
    input: ImmutableBuffer<'top>,
}

impl<'top> LazyRawBinaryVersionMarker_1_1<'top> {
    pub fn new(input: ImmutableBuffer<'top>, major: u8, minor: u8) -> Self {
        Self {
            major,
            minor,
            input,
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawBinaryVersionMarker_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top> HasRange for LazyRawBinaryVersionMarker_1_1<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> RawVersionMarker<'top> for LazyRawBinaryVersionMarker_1_1<'top> {
    fn version(&self) -> (u8, u8) {
        (self.major, self.minor)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum DelimitedContents<'top> {
    None,
    Values(&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]),
    Fields(&'top [LazyRawFieldExpr<'top, BinaryEncoding_1_1>]),
}

impl<'top> DelimitedContents<'top> {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryValue_1_1<'top> {
    pub(crate) encoded_value: EncodedValue<Header>,
    pub(crate) input: ImmutableBuffer<'top>,
    pub(crate) delimited_contents: DelimitedContents<'top>,
}

impl<'top> HasSpan<'top> for LazyRawBinaryValue_1_1<'top> {
    fn span(&self) -> Span<'top> {
        let range = self.range();
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        let bytes = &self.input.bytes()[local_range];
        Span::with_offset(range.start, bytes)
    }
}

impl<'top> HasRange for LazyRawBinaryValue_1_1<'top> {
    fn range(&self) -> Range<usize> {
        self.encoded_value.annotated_value_range()
    }
}

impl<'top> LazyRawValue<'top, BinaryEncoding_1_1> for LazyRawBinaryValue_1_1<'top> {
    fn ion_type(&self) -> IonType {
        self.ion_type()
    }

    fn is_null(&self) -> bool {
        self.is_null()
    }

    fn has_annotations(&self) -> bool {
        self.encoded_value.has_annotations()
    }

    fn annotations(&self) -> <BinaryEncoding_1_1 as Decoder>::AnnotationsIterator<'top> {
        self.annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'top, BinaryEncoding_1_1>> {
        self.read()
    }

    fn annotations_span(&self) -> Span<'top> {
        let Some(range) = self.encoded_value.annotations_range() else {
            // If there are no annotations, return an empty slice positioned at the opcode
            return Span::with_offset(self.encoded_value.header_offset, &[]);
        };
        // Subtract the `offset()` of the ImmutableBuffer to get the local indexes for start/end
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }

    fn value_span(&self) -> Span<'top> {
        let range = self.encoded_value.unannotated_value_range();
        let local_range = (range.start - self.input.offset())..(range.end - self.input.offset());
        Span::with_offset(range.start, &self.input.bytes()[local_range])
    }
}

impl<'top> LazyRawBinaryValue_1_1<'top> {
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
        let annotations_header_length = self.encoded_value.annotations_header_length as usize;
        let sequence_length = self.encoded_value.annotations_sequence_length as usize;
        let sequence = self
            .input
            .slice(annotations_header_length - sequence_length, sequence_length);
        sequence
    }

    /// Returns an iterator over this value's unresolved annotation symbols.
    pub fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        RawBinaryAnnotationsIterator_1_1::new(
            self.annotations_sequence(),
            self.encoded_value.annotations_encoding,
        )
    }

    /// Reads this value's data, returning it as a [`RawValueRef`]. If this value is a container,
    /// calling this method will not read additional data; the `RawValueRef` will provide a
    /// [`LazyRawBinarySequence_1_1`](crate::lazy::binary::raw::v1_1::sequence::LazyRawBinarySequence_1_1)
    /// or [`LazyStruct`](crate::lazy::struct::LazyStruct) that can be traversed to access the container's contents.
    pub fn read(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        if self.is_null() {
            let ion_type = if self.encoded_value.header.ion_type_code == OpcodeType::TypedNull {
                let body = self.value_body()?;
                ION_1_1_TYPED_NULL_TYPES[body[0] as usize]
            } else {
                IonType::Null
            };
            return Ok(RawValueRef::Null(ion_type));
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

    pub fn is_delimited(&self) -> bool {
        self.encoded_value.header.ion_type_code.is_delimited()
    }

    /// Returns the encoded byte slice representing this value's data.
    pub(crate) fn value_body(&self) -> IonResult<&'top [u8]> {
        let value_total_length = self.encoded_value.total_length();
        if self.input.len() < value_total_length {
            return IonResult::incomplete(
                "only part of the requested value is available in the buffer",
                self.input.offset(),
            );
        }
        let value_body_length = self.encoded_value.value_body_length();
        let value_offset = value_total_length - value_body_length;
        Ok(self.input.bytes_range(value_offset, value_body_length))
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
    fn read_bool(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Bool);
        let header = &self.encoded_value.header();
        let representation = header.type_code();
        let value = match (representation, header.low_nibble) {
            (OpcodeType::Boolean, 0xE) => true,
            (OpcodeType::Boolean, 0xF) => false,
            _ => unreachable!("found a boolean value with an illegal length code."),
        };
        Ok(RawValueRef::Bool(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as an int.
    fn read_int(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Int);

        let header = &self.encoded_value.header();
        let representation = header.type_code();
        let value = match (representation, header.low_nibble as usize) {
            (OpcodeType::Integer, 0x0) => 0.into(),
            (OpcodeType::Integer, n) => {
                // We have n bytes following that make up our integer.
                self.available_body().read_fixed_int(n)?.0.into()
            }
            (OpcodeType::LargeInteger, 0x6) => {
                // We have a FlexUInt size, then big int.
                let value_bytes = self.value_body()?;
                FixedInt::read(value_bytes, value_bytes.len(), 0)?.into()
            }
            _ => unreachable!("integer encoding with illegal length_code found"),
        };
        Ok(RawValueRef::Int(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a float.
    fn read_float(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Float);

        let value = match self.encoded_value.value_body_length {
            8 => {
                let mut buffer = [0; 8];
                let val_bytes = self.available_body().bytes_range(0, 8);
                buffer[..8].copy_from_slice(val_bytes);

                f64::from_le_bytes(buffer)
            }
            4 => {
                let mut buffer = [0; 4];
                let val_bytes = self.available_body().bytes_range(0, 4);
                buffer[..4].copy_from_slice(val_bytes);

                f32::from_le_bytes(buffer).into()
            }
            2 => todo!("implement half-precision floats"),
            0 => 0.0f64,
            _ => unreachable!("found a float value with illegal byte size"),
        };
        Ok(RawValueRef::Float(value))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a decimal.
    fn read_decimal(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::types::decimal::*;

        debug_assert!(self.encoded_value.ion_type() == IonType::Decimal);
        let decimal: Decimal = if self.encoded_value.value_body_length == 0 {
            Decimal::new(0, 0)
        } else {
            use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;

            let value_bytes = self.value_body()?;
            let exponent = FlexInt::read(value_bytes, 0)?;
            let coefficient_size = self.encoded_value.value_body_length - exponent.size_in_bytes();
            let coefficient = FixedInt::read(
                &value_bytes[exponent.size_in_bytes()..],
                coefficient_size,
                0,
            )?;

            // Handle special -0 encoding.
            if coefficient_size > 0 && coefficient.value().as_i64() == Some(0) {
                Decimal::negative_zero_with_exponent(exponent.value())
            } else {
                Decimal::new(coefficient, exponent.value())
            }
        };

        Ok(RawValueRef::Decimal(decimal))
    }

    // Helper method called by [`Self::read_timestamp_short`]. Reads the time information from a
    // timestamp with Unknown or UTC offset.
    fn read_timestamp_short_no_offset_after_minute(
        &self,
        value_bytes: &[u8],
        ts_builder: TimestampBuilder<HasMinute>,
    ) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        const SECONDS_MASK_16BIT: u16 = 0x03_F0;
        const MILLISECONDS_MASK_16BIT: u16 = 0x0F_FC;
        const MICROSECONDS_MASK_32BIT: u32 = 0x3F_FF_FC_00;

        let length_code = self.encoded_value.header.low_nibble();
        // An offset bit of `1` indicates UTC while a `0` indicates 'unknown'
        let is_utc = (value_bytes[3] & 0x08) == 0x08;

        // Hour & Minute (populated from [`Self::read_timestamp_short`]), just need to know if UTC.
        if length_code == 3 {
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Read Second
        let second = u16::from_le_bytes(value_bytes[3..=4].try_into().unwrap())
            .extract_bitmask(SECONDS_MASK_16BIT);
        let ts_builder = ts_builder.with_second(second as u32);

        // Second Precision
        if length_code == 4 {
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Millisecond Precision
        if length_code == 5 {
            let millisecond = u16::from_le_bytes(value_bytes[4..=5].try_into().unwrap())
                .extract_bitmask(MILLISECONDS_MASK_16BIT);
            let ts_builder = ts_builder.with_milliseconds(millisecond.into());
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Microsecond Precision
        if length_code == 6 {
            let microsecond = u32::from_le_bytes(value_bytes[3..=6].try_into().unwrap())
                .extract_bitmask(MICROSECONDS_MASK_32BIT);
            let ts_builder = ts_builder.with_microseconds(microsecond);
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Nanosecond Precision
        if length_code == 7 {
            let nanoseconds = u32::from_le_bytes(value_bytes[4..=7].try_into().unwrap()) >> 2;
            let ts_builder = ts_builder.with_nanoseconds(nanoseconds);
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        unreachable!("invalid length code for short-form timestamp");
    }

    // Helper method callsed by [`Self::read_timestamp_short`]. Reads the time information from a
    // timestamp with a provided offset.
    fn read_timestamp_short_offset_after_minute(
        &self,
        value_bytes: &[u8],
        ts_builder: TimestampBuilder<HasMinute>,
    ) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        const OFFSET_MASK_16BIT: u16 = 0x03_F8;
        const MILLISECOND_MASK_16BIT: u16 = 0x03_FF;
        const MICROSECOND_MASK_32BIT: u32 = 0x0F_FF_00;
        const NANOSECOND_MASK_32BIT: u32 = 0x3F_FF_FF_FF;

        let length_code = self.encoded_value.header.low_nibble();

        // Read offset as 15min multiple
        let offset: u16 = u16::from_le_bytes(value_bytes[3..=4].try_into().unwrap())
            .extract_bitmask(OFFSET_MASK_16BIT);
        const MIN_OFFSET: i32 = -14 * 60; // Western hemisphere, -14:00
        let offset: i32 = ((offset as i32) * 15) + MIN_OFFSET;

        // Hour and Minutes at known offset
        if length_code == 8 {
            let ts_builder = ts_builder.with_offset(offset);
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Read seconds
        let second = value_bytes[4] as u32 >> 2; // Read all 6 bits
        let ts_builder = ts_builder.with_second(second);

        // Seconds precision at known offset.
        if length_code == 9 {
            let ts_builder = ts_builder.with_offset(offset);
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Opcodes 7A, 7B, and 7C, differ in subsecond precision.
        if length_code == 0xA {
            // Read milliseconds
            let millisecond = u16::from_le_bytes(value_bytes[5..=6].try_into().unwrap())
                .extract_bitmask(MILLISECOND_MASK_16BIT);
            let ts_builder = ts_builder
                .with_milliseconds(millisecond.into())
                .with_offset(offset);

            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        } else if length_code == 0xB {
            // Read microseconds
            let microsecond = u32::from_le_bytes(value_bytes[4..=7].try_into().unwrap())
                .extract_bitmask(MICROSECOND_MASK_32BIT);
            let ts_builder = ts_builder
                .with_microseconds(microsecond)
                .with_offset(offset);

            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        } else if length_code == 0xC {
            // Read nanoseconds
            let nanoseconds =
                u32::from_le_bytes(value_bytes[5..=8].try_into().unwrap()) & NANOSECOND_MASK_32BIT;
            let ts_builder = ts_builder.with_nanoseconds(nanoseconds).with_offset(offset);

            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        unreachable!();
    }

    // Helper method called by [`Self::read_timestamp`]. Reads the time information from a
    // timestamp encoded in short form.
    fn read_timestamp_short(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        const MONTH_MASK_16BIT: u16 = 0x07_80;

        let length_code = self.encoded_value.header.low_nibble();
        let value_bytes = self.value_body()?;

        // Year is biased offset by 1970, and is held in the lower 7 bits of the first byte.
        let ts_builder = Timestamp::with_year((value_bytes[0] & 0x7F) as u32 + 1970);

        // Year Precision.
        if length_code == 0 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Read month..
        // let month = (u16::from_le_bytes(value_bytes[0..=1].try_into().unwrap()) >> 7) & 0x0F;
        let month = u16::from_le_bytes(value_bytes[0..=1].try_into().unwrap())
            .extract_bitmask(MONTH_MASK_16BIT);
        let ts_builder = ts_builder.with_month(month as u32);

        // Month Precision
        if length_code == 1 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Read day.
        let day = (value_bytes[1] & 0xF8) >> 3; // All 5 bits.
        let ts_builder = ts_builder.with_day(day as u32);

        // Day Precision
        if length_code == 2 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Hour and Minute
        let hour = value_bytes[2] & 0x1F; // All 5 bits of the hour.
        let min = (u16::from_le_bytes(value_bytes[2..=3].try_into().unwrap()) >> 5) & 0x3F;
        let ts_builder = ts_builder.with_hour_and_minute(hour as u32, min as u32);

        // We're at least Hour&Minute so we need either an offset, or indicator that the timestamp
        // is UTC or Unknown.

        // UTC / Unknown Offset
        if length_code < 8 {
            self.read_timestamp_short_no_offset_after_minute(value_bytes, ts_builder)
        } else {
            // Known Offset
            self.read_timestamp_short_offset_after_minute(value_bytes, ts_builder)
        }
    }

    // Helper method called by [`Self::read_timestamp`]. Reads the time information from a
    // timestamp encoded in long form.
    fn read_timestamp_long(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
        use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
        use crate::types::decimal::{coefficient::Coefficient, *};

        const YEAR_MASK_16BIT: u16 = 0x3FFF;
        const MONTH_MASK_16BIT: u16 = 0x03_C0;
        const DAY_MASK_8BIT: u8 = 0x7C;
        const HOUR_MASK_16BIT: u16 = 0x0F_80;
        const MINUTE_MASK_16BIT: u16 = 0x03_F0;
        const SECOND_MASK_16BIT: u16 = 0x0F_C0;
        const OFFSET_MASK_16BIT: u16 = 0x3F_FC;

        let value_bytes = self.value_body()?;
        let value_length = self.encoded_value.value_body_length;

        if value_length < 2 || value_length == 4 || value_length == 5 {
            return Err(IonError::decoding_error("invalid timestamp length"));
        }

        let year = u16::from_le_bytes(value_bytes[0..=1].try_into().unwrap()) & YEAR_MASK_16BIT;
        let ts_builder = Timestamp::with_year(year.into());
        if value_length == 2 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let month = u16::from_le_bytes(value_bytes[1..=2].try_into().unwrap())
            .extract_bitmask(MONTH_MASK_16BIT);
        let day = value_bytes[2].extract_bitmask(DAY_MASK_8BIT);
        let ts_builder = ts_builder.with_month(month.into());
        if value_length == 3 && day == 0 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let ts_builder = ts_builder.with_day(day as u32);
        if value_length == 3 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let hour = u16::from_le_bytes(value_bytes[2..=3].try_into().unwrap())
            .extract_bitmask(HOUR_MASK_16BIT);
        let minute = u16::from_le_bytes(value_bytes[3..=4].try_into().unwrap())
            .extract_bitmask(MINUTE_MASK_16BIT);
        let offset = u16::from_le_bytes(value_bytes[4..=5].try_into().unwrap())
            .extract_bitmask(OFFSET_MASK_16BIT);
        let offset: Option<i32> = if offset == 0xFFF {
            None
        } else {
            Some((offset as i32) + LONG_TIMESTAMP_OFFSET_BIAS)
        };

        let ts_builder = ts_builder.with_hour_and_minute(hour.into(), minute.into());

        if value_length == 6 {
            if let Some(offset) = offset {
                let ts_builder = ts_builder.with_offset(offset);
                return Ok(RawValueRef::Timestamp(ts_builder.build()?));
            }
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let second = u16::from_le_bytes(value_bytes[5..=6].try_into().unwrap())
            .extract_bitmask(SECOND_MASK_16BIT);
        let ts_builder = ts_builder.with_second(second.into());

        if value_length == 7 {
            if let Some(offset) = offset {
                let ts_builder = ts_builder.with_offset(offset);
                return Ok(RawValueRef::Timestamp(ts_builder.build()?));
            }
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let scale = FlexUInt::read(&value_bytes[7..], 0)?;
        let coefficient_start = 7 + scale.size_in_bytes();
        let coefficient_len = value_length - coefficient_start;
        let coefficient = FixedUInt::read(&value_bytes[coefficient_start..], coefficient_len, 0)?;

        let decimal_coefficient: Coefficient = coefficient.try_into()?;

        let frac_sec = Decimal::new(decimal_coefficient, -(scale.value() as i64));

        let ts_builder = ts_builder.with_fractional_seconds(frac_sec);
        if let Some(offset) = offset {
            let ts_builder = ts_builder.with_offset(offset);
            Ok(RawValueRef::Timestamp(ts_builder.build()?))
        } else {
            Ok(RawValueRef::Timestamp(ts_builder.build()?))
        }
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a timestamp.
    fn read_timestamp(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Timestamp);

        match self.encoded_value.header.type_code() {
            OpcodeType::TimestampShort => self.read_timestamp_short(),
            OpcodeType::TimestampLong => self.read_timestamp_long(),
            _ => unreachable!("invalid timestamp type_code"),
        }
    }

    /// Helper method called by [`Self::read_symbol`]. Reads the current value as a symbol ID.
    fn read_symbol_id(&self) -> IonResult<SymbolId> {
        let biases: [usize; 3] = [0, 256, 65792];
        let length_code = self.encoded_value.header.low_nibble;
        if (1..=3).contains(&length_code) {
            let (id, _) = self.available_body().read_fixed_uint(length_code.into())?;
            let id = usize::try_from(id.value())?;
            Ok(id + biases[(length_code - 1) as usize])
        } else {
            unreachable!("invalid length code for symbol ID");
        }
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a symbol.
    fn read_symbol(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Symbol);
        let type_code = self.encoded_value.header.ion_type_code;
        if type_code == OpcodeType::InlineSymbol {
            let raw_bytes = self.value_body()?;
            let text = std::str::from_utf8(raw_bytes)
                .map_err(|_| IonError::decoding_error("found symbol with invalid UTF-8 data"))?;
            Ok(RawValueRef::Symbol(RawSymbolRef::from(text)))
        } else if type_code == OpcodeType::SymbolAddress {
            let symbol_id = self.read_symbol_id()?;
            Ok(RawValueRef::Symbol(RawSymbolRef::SymbolId(symbol_id)))
        } else {
            unreachable!("invalid Opcode type found for symbol");
        }
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a string.
    fn read_string(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::str_ref::StrRef;

        debug_assert!(self.encoded_value.ion_type() == IonType::String);
        let raw_bytes = self.value_body()?;
        let text = std::str::from_utf8(raw_bytes)
            .map_err(|_| IonError::decoding_error("found string with invalid UTF-8 data"))?;
        Ok(RawValueRef::String(StrRef::from(text)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a blob.
    fn read_blob(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Blob);

        let raw_bytes = self.value_body()?;
        Ok(RawValueRef::Blob(raw_bytes.into()))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a clob.
    fn read_clob(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Clob);

        let raw_bytes = self.value_body()?;
        Ok(RawValueRef::Clob(raw_bytes.into()))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as an S-expression.
    fn read_sexp(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::binary::raw::v1_1::sequence::LazyRawBinarySExp_1_1;
        use crate::lazy::decoder::private::LazyContainerPrivate;
        debug_assert!(self.encoded_value.ion_type() == IonType::SExp);
        Ok(RawValueRef::SExp(LazyRawBinarySExp_1_1::from_value(*self)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a list.
    fn read_list(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::binary::raw::v1_1::sequence::LazyRawBinaryList_1_1;
        use crate::lazy::decoder::private::LazyContainerPrivate;
        debug_assert!(self.encoded_value.ion_type() == IonType::List);
        Ok(RawValueRef::List(LazyRawBinaryList_1_1::from_value(*self)))
    }

    /// Helper method called by [`Self::read`]. Reads the current value as a struct.
    fn read_struct(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::binary::raw::v1_1::r#struct::LazyRawBinaryStruct_1_1;
        use crate::lazy::decoder::private::LazyContainerPrivate;
        Ok(RawValueRef::Struct(LazyRawBinaryStruct_1_1::from_value(
            *self,
        )))
    }
}
