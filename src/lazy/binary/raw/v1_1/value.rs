#![allow(non_camel_case_types)]

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
                    immutable_buffer::ImmutableBuffer, Header, OpcodeType,
                },
                value::ValueParseResult,
            },
        },
        decoder::{Decoder, LazyRawValue},
        encoder::binary::v1_1::fixed_int::FixedInt,
        encoding::BinaryEncoding_1_1,
        raw_value_ref::RawValueRef,
    },
    result::IonFailure,
    types::{
        timestamp::{HasMinute, TimestampBuilder},
        SymbolId, Timestamp,
    },
    IonError, IonResult, IonType, RawSymbolRef,
};

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
pub struct LazyRawBinaryValue_1_1<'top> {
    pub(crate) encoded_value: EncodedValue<Header>,
    pub(crate) input: ImmutableBuffer<'top>,
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

    fn annotations(&self) -> <BinaryEncoding_1_1 as Decoder>::AnnotationsIterator<'top> {
        self.annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'top, BinaryEncoding_1_1>> {
        self.read()
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
                // If there are no annotations, return an empty slice starting at the opcode.
                return self.input.slice(0, 0);
            }
            Some(offset_and_length) => offset_and_length,
        };
        let local_sequence_offset = sequence_offset - self.input.offset();

        self.input.slice(local_sequence_offset, sequence_length)
    }

    /// Returns an iterator over this value's unresolved annotation symbols.
    pub fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        RawBinaryAnnotationsIterator_1_1::new(self.annotations_sequence())
    }

    /// Reads this value's data, returning it as a [`RawValueRef`]. If this value is a container,
    /// calling this method will not read additional data; the `RawValueRef` will provide a
    /// [`LazyRawBinarySequence_1_1`](crate::lazy::binary::raw::v1_1::sequence::LazyRawBinarySequence_1_1)
    /// or [`LazyStruct`](crate::lazy::struct::LazyStruct) that can be traversed to access the container's contents.
    pub fn read(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
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
    fn value_body(&self) -> IonResult<&'top [u8]> {
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
        let value = match (representation, header.length_code) {
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
        let value = match (representation, header.length_code as usize) {
            (OpcodeType::Integer, 0x0) => 0.into(),
            (OpcodeType::Integer, n) => {
                // We have n bytes following that make up our integer.
                self.input.consume(1).read_fixed_int(n)?.0.into()
            }
            (OpcodeType::LargeInteger, 0x5) => {
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
                let val_bytes = self.input.bytes_range(1, 8);
                buffer[..8].copy_from_slice(val_bytes);

                f64::from_le_bytes(buffer)
            }
            4 => {
                let mut buffer = [0; 4];
                let val_bytes = self.input.bytes_range(1, 4);
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

    // Helper method callsed by [`Self::read_timestamp_short`]. Reads the time information from a
    // timestamp with Unknown or UTC offset.
    fn read_timestamp_short_no_offset(
        &self,
        value_bytes: &[u8],
        ts_builder: TimestampBuilder<HasMinute>,
    ) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        let length_code = self.encoded_value.header.length_code();
        let is_utc = (value_bytes[3] & 0x08) == 0x08;

        if length_code == 3 {
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Second
        let second = ((value_bytes[3] & 0xF0) >> 4) | ((value_bytes[4] & 0x03) << 4);
        let ts_builder = ts_builder.with_second(second as u32);

        if length_code == 4 {
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        if length_code == 5 {
            let millisecond = ((value_bytes[4] >> 2) as u32) | (value_bytes[5] as u32) << 6;
            let ts_builder = ts_builder.with_milliseconds(millisecond);
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        if length_code == 6 {
            let microsecond = ((value_bytes[4] >> 2) as u32)
                | (value_bytes[5] as u32) << 6
                | (value_bytes[6] as u32) << 14;
            let ts_builder = ts_builder.with_microseconds(microsecond);
            let timestamp = if is_utc {
                ts_builder.build_utc_fields_at_offset(0)?
            } else {
                ts_builder.build()?
            };

            return Ok(RawValueRef::Timestamp(timestamp));
        }

        if length_code == 7 {
            let nanoseconds = ((value_bytes[4] >> 2) as u32)
                | (value_bytes[5] as u32) << 6
                | (value_bytes[6] as u32) << 14
                | (value_bytes[7] as u32) << 22;
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

    fn read_timestamp_short_offset(
        &self,
        value_bytes: &[u8],
        ts_builder: TimestampBuilder<HasMinute>,
    ) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        let length_code = self.encoded_value.header.length_code();

        // Read offset.
        let offset = ((((value_bytes[3] & 0xF8) as u32) >> 3 | ((value_bytes[4] & 0x3) as u32) << 5)
            as i32)
            * 15;

        if length_code == 8 {
            return Ok(RawValueRef::Timestamp(
                ts_builder.build_utc_fields_at_offset(offset)?,
            ));
        }

        let second = (value_bytes[4] & 0xFC) as u32 >> 2;
        let ts_builder = ts_builder.with_second(second);

        if length_code == 9 {
            let ts_builder = ts_builder.with_offset(offset);
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        if length_code == 0xA {
            let millisecond = (value_bytes[5] as u32) | ((value_bytes[6] & 0x03) as u32) << 8;
            let ts_builder = ts_builder
                .with_milliseconds(millisecond)
                .with_offset(offset);

            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        } else if length_code == 0xB {
            let microsecond = (value_bytes[5] as u32)
                | ((value_bytes[6] as u32) << 8)
                | ((value_bytes[7] & 0x0F) as u32) << 16;
            let ts_builder = ts_builder
                .with_microseconds(microsecond)
                .with_offset(offset);

            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        } else if length_code == 0xC {
            let nanoseconds = (value_bytes[5] as u32)
                | ((value_bytes[6] as u32) << 8)
                | (value_bytes[7] as u32) << 16;
            let ts_builder = ts_builder.with_nanoseconds(nanoseconds).with_offset(offset);

            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        unreachable!();
    }

    fn read_timestamp_short(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        let length_code = self.encoded_value.header.length_code();
        let value_bytes = self.value_body()?;

        // Year is held in the low 7 bits, of the first byte.
        let ts_builder = Timestamp::with_year((value_bytes[0] & 0x7F) as u32 + 1970);
        if length_code == 0 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Month.
        let month = ((value_bytes[0] & 0x80) >> 7) | ((value_bytes[1] & 0x07) << 1);
        let ts_builder = ts_builder.with_month(month as u32);
        if length_code == 1 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        // Day.
        let day = (value_bytes[1] & 0xF8) >> 3;
        let ts_builder = ts_builder.with_day(day as u32);
        if length_code == 2 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let hour = value_bytes[2] & 0x1F;
        let min = ((value_bytes[2] & 0xE0) >> 5) | ((value_bytes[3] & 0x07) << 3);
        let ts_builder = ts_builder.with_hour_and_minute(hour as u32, min as u32);

        // UTC / Unkonwn Offset
        if length_code < 8 {
            self.read_timestamp_short_no_offset(value_bytes, ts_builder)
        } else {
            // Known Offset
            self.read_timestamp_short_offset(value_bytes, ts_builder)
        }
    }

    fn read_timestamp_long(&self) -> ValueParseResult<'top, BinaryEncoding_1_1> {
        use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
        use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
        use crate::types::decimal::{*, coefficient::Coefficient};

        let value_bytes = self.value_body()?;
        let value_length = self.encoded_value.value_length();

        if value_length < 2 || value_length == 4 || value_length == 5 {
            return Err(IonError::decoding_error("invalid timestamp length"));
        }

        let year = (value_bytes[0] as u32) | ((value_bytes[1] & 0x3F) as u32) << 8;
        let ts_builder = Timestamp::with_year(year);
        if value_length == 2 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let month = ((value_bytes[1] & 0xC0) as u32) >> 6 | ((value_bytes[2] & 0x03) as u32) << 2;
        let day = ((value_bytes[2] & 0x7C) as u32) >> 2;
        let ts_builder = ts_builder.with_month(month);
        if value_length == 3 && day == 0 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let ts_builder = ts_builder.with_day(day);
        if value_length == 3 {
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let hour = ((value_bytes[2] & 0x80) as u32) >> 7 | ((value_bytes[3] & 0x0F) as u32) << 1;
        let minute = ((value_bytes[3] & 0xF0) as u32) >> 4 | ((value_bytes[4] & 0x03) as u32) << 4;
        let offset = ((value_bytes[4] & 0xFC) as u32) >> 2 | ((value_bytes[5] & 0x3F) as u32) << 6;
        let offset = if (offset & 0x800) == 0x800 && offset != 0xFFF {
            (offset | !0xFFFu32) as i32 // Extend sign for negative 12-bit offsets.
        } else {
            offset as i32
        };
        let ts_builder = ts_builder.with_hour_and_minute(hour, minute);

        if value_length == 6 {
            if offset != 0x0FFF {
                let ts_builder = ts_builder.with_offset(offset);
                return Ok(RawValueRef::Timestamp(ts_builder.build()?));
            }
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let second = ((value_bytes[5] & 0xC0) as u32) >> 6 | ((value_bytes[6] & 0x0F) as u32) << 2;
        let ts_builder = ts_builder.with_second(second);

        if value_length == 7 {
            if offset != 0x0FFF {
                let ts_builder = ts_builder.with_offset(offset);
                return Ok(RawValueRef::Timestamp(ts_builder.build()?));
            }
            return Ok(RawValueRef::Timestamp(ts_builder.build()?));
        }

        let scale = FlexUInt::read(&value_bytes[7..], 0)?;
        let coefficient_start = 7 + scale.size_in_bytes();
        let coefficient_len = value_length - coefficient_start;
        let coefficient = FixedUInt::read(&value_bytes[coefficient_start..], coefficient_len, 0)?;

        if scale.value() == 0 {
            return Err(IonError::decoding_error(
                "invalid scale for timestamp fractional second",
            ));
        }

        let decimal_coefficient: Coefficient = coefficient.try_into()
            .map_err(|e| e.into())?;
        let frac_sec = Decimal::new(decimal_coefficient, -(scale.value() as i64));
        if frac_sec.is_greater_than_or_equal_to_one() {
            return Err(IonError::decoding_error(
                "invalid fractional second for timestamp",
            ));
        }

        let ts_builder = ts_builder.with_fractional_seconds(frac_sec);
        if offset != 0x0FFF {
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
        let length_code = self.encoded_value.header.length_code;
        if (1..=3).contains(&length_code) {
            let (id, _) = self.input.consume(1).read_fixed_uint(length_code.into())?;
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
        todo!();
    }
}
