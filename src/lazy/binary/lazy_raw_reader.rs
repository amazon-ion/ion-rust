use super::encoded_value::EncodedValue;
use crate::binary::int::DecodedInt;
use crate::binary::uint::DecodedUInt;
use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::result::{decoding_error, decoding_error_raw, incomplete_data_error};
use crate::types::SymbolId;
use crate::{Decimal, Int, IonResult, IonType, RawSymbolTokenRef, Timestamp};
use bytes::{BigEndian, ByteOrder};
use num_traits::Zero;
use std::fmt::{Debug, Formatter};
use std::{fmt, mem};

struct DataSource<'a> {
    buffer: ImmutableBuffer<'a>,
    bytes_to_skip: usize, // initially; try to advance on 'next'
}

impl<'a> DataSource<'a> {
    fn new(buffer: ImmutableBuffer<'a>) -> DataSource<'a> {
        DataSource {
            buffer,
            bytes_to_skip: 0,
        }
    }

    fn advance_to_next_item(&mut self) -> IonResult<ImmutableBuffer<'a>> {
        if self.buffer.len() < self.bytes_to_skip {
            return incomplete_data_error(
                "cannot advance to next item, insufficient data in buffer",
                self.buffer.offset(),
            );
        }

        if self.bytes_to_skip > 0 {
            Ok(self.buffer.consume(self.bytes_to_skip))
        } else {
            Ok(self.buffer)
        }
    }

    fn try_parse_next<F: Fn(ImmutableBuffer<'a>) -> IonResult<Option<LazyRawValue<'a>>>>(
        &mut self,
        parser: F,
    ) -> IonResult<Option<LazyRawValue<'a>>> {
        let buffer = self.advance_to_next_item()?;

        let lazy_value = match parser(buffer) {
            Ok(Some(output)) => output,
            Ok(None) => return Ok(None),
            Err(e) => return Err(e),
        };

        self.buffer = buffer;
        self.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(Some(lazy_value))
    }
}

pub struct LazyRawBinaryReader<'a> {
    data: DataSource<'a>,
}

pub struct RawSequenceIterator<'a> {
    source: DataSource<'a>,
}

pub struct RawStructIterator<'a> {
    source: DataSource<'a>,
}

pub struct LazyRawValue<'a> {
    pub(crate) encoded_value: EncodedValue,
    pub(crate) input: ImmutableBuffer<'a>,
}

pub struct LazyRawSequence<'a> {
    value: LazyRawValue<'a>,
}

pub struct LazyRawStruct<'a> {
    value: LazyRawValue<'a>,
}

pub struct LazyRawField<'a> {
    value: LazyRawValue<'a>,
}

impl<'a> LazyRawBinaryReader<'a> {
    pub fn new(data: &'a [u8]) -> LazyRawBinaryReader<'a> {
        Self::new_with_offset(data, 0)
    }

    fn new_with_offset(data: &'a [u8], offset: usize) -> LazyRawBinaryReader<'a> {
        let data = DataSource::new(ImmutableBuffer::new_with_offset(data, offset));
        LazyRawBinaryReader { data }
    }

    fn read_ivm(&mut self, buffer: ImmutableBuffer<'a>) -> IonResult<RawStreamItem<'a>> {
        let ((major, minor), _buffer_after_ivm) = buffer.read_ivm()?;
        if (major, minor) != (1, 0) {
            return decoding_error(format!(
                "unsupported version of Ion: v{}.{}; only 1.0 is supported",
                major, minor,
            ));
        }
        self.data.buffer = buffer;
        self.data.bytes_to_skip = 4; // IVM length
        return Ok(RawStreamItem::VersionMarker(1, 0));
    }

    fn read_value(&mut self, buffer: ImmutableBuffer<'a>) -> IonResult<RawStreamItem<'a>> {
        let lazy_value = match LazyRawValue::peek_value_without_field_id(buffer)? {
            Some(lazy_value) => lazy_value,
            None => return Ok(RawStreamItem::Nothing),
        };
        self.data.buffer = buffer;
        self.data.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(RawStreamItem::Value(lazy_value))
    }

    pub fn next(&mut self) -> IonResult<RawStreamItem<'a>> {
        let mut buffer = self.data.advance_to_next_item()?;
        if buffer.is_empty() {
            return Ok(RawStreamItem::Nothing);
        }
        let type_descriptor = buffer.peek_type_descriptor()?;
        if type_descriptor.is_nop() {
            (_, buffer) = buffer.consume_nop_padding(type_descriptor)?;
        } else if type_descriptor.is_ivm_start() {
            return self.read_ivm(buffer);
        }

        self.read_value(buffer)
    }
}

impl<'a> RawSequenceIterator<'a> {
    pub(crate) fn new(input: ImmutableBuffer<'a>) -> Self {
        RawSequenceIterator {
            source: DataSource::new(input),
        }
    }

    pub fn next(&mut self) -> IonResult<Option<LazyRawValue<'a>>> {
        self.source
            .try_parse_next(LazyRawValue::peek_value_without_field_id)
    }
}

impl<'a> LazyRawField<'a> {
    pub(crate) fn new(value: LazyRawValue<'a>) -> Self {
        LazyRawField { value }
    }

    pub fn name(&'a self) -> RawSymbolTokenRef<'a> {
        // We're in a struct field, the field ID must be populated.
        let field_id = self.value.encoded_value.field_id.unwrap();
        RawSymbolTokenRef::SymbolId(field_id)
    }

    pub fn value(&self) -> &LazyRawValue<'a> {
        &self.value
    }

    pub(crate) fn into_value(self) -> LazyRawValue<'a> {
        self.value
    }
}

impl<'a> Debug for LazyRawField<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "${}: {:?}",
            self.value.encoded_value.field_id.unwrap(),
            self.value()
        )
    }
}

impl<'a> RawStructIterator<'a> {
    pub(crate) fn new(input: ImmutableBuffer<'a>) -> Self {
        RawStructIterator {
            source: DataSource::new(input),
        }
    }

    pub fn next_field(&mut self) -> IonResult<Option<LazyRawField<'a>>> {
        if let Some(lazy_field) = self.source.try_parse_next(LazyRawValue::peek_field)? {
            Ok(Some(LazyRawField::new(lazy_field)))
        } else {
            Ok(None)
        }
    }
}

impl<'a> Debug for LazyRawStruct<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut reader = self.iter();
        write!(f, "{{")?;
        while let Some(field) = reader.next_field().unwrap() {
            let name = field.name();
            let lazy_value = field.value();
            let value = lazy_value.read().unwrap();
            write!(f, "{:?}:{:?},", name, value).unwrap();
        }
        write!(f, "}}").unwrap();
        Ok(())
    }
}

impl<'a> LazyRawStruct<'a> {
    pub fn iter(&self) -> RawStructIterator<'a> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawStructIterator::new(buffer_slice)
    }
}

impl<'a> LazyRawSequence<'a> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawSequenceIterator<'a> {
        // Get as much of the sequence's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawSequenceIterator::new(buffer_slice)
    }
}

impl<'a> Debug for LazyRawSequence<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut reader = self.iter();
        match self.value.encoded_value.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                while let Some(value) = reader.next().unwrap() {
                    write!(f, "{:?} ", value.read().unwrap()).unwrap();
                }
                write!(f, ")").unwrap();
            }
            IonType::List => {
                write!(f, "[")?;
                while let Some(value) = reader.next().unwrap() {
                    write!(f, "{:?},", value.read().unwrap()).unwrap();
                }
                write!(f, "]").unwrap();
            }
            _ => unreachable!("LazyRawSequence is only created for list and sexp"),
        }

        Ok(())
    }
}

impl<'a> Debug for LazyRawValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LazyRawValue {{\n  val={:?},\n  buf={:?}\n}}\n",
            self.encoded_value, self.input
        )
    }
}

type ValueParseResult<'a> = IonResult<RawValueRef<'a>>;

impl<'a> LazyRawValue<'a> {
    fn peek_field(input: ImmutableBuffer<'a>) -> IonResult<Option<LazyRawValue<'a>>> {
        Self::peek_value(true, input)
    }

    fn peek_value_without_field_id(
        input: ImmutableBuffer<'a>,
    ) -> IonResult<Option<LazyRawValue<'a>>> {
        Self::peek_value(false, input)
    }

    // This method consumes leading NOP bytes, but leaves the header representation in the buffer.
    // The resulting LazyRawValue's buffer slice always starts with the first non-NOP byte in the
    // header, which can be either a field ID, an annotations wrapper, or a type descriptor.
    fn peek_value(
        has_field: bool,
        initial_input: ImmutableBuffer<'a>,
    ) -> IonResult<Option<LazyRawValue<'a>>> {
        if initial_input.is_empty() {
            return Ok(None);
        }
        let (field_id, field_id_length, mut input) = if has_field {
            let (field_id_var_uint, input_after_field_id) = initial_input.read_var_uint()?;
            if input_after_field_id.is_empty() {
                return incomplete_data_error(
                    "found field name but no value",
                    input_after_field_id.offset(),
                );
            }
            let field_id_length = u8::try_from(field_id_var_uint.size_in_bytes())
                .map_err(|_| decoding_error_raw("found a field id with length over 255 bytes"))?;
            (
                Some(field_id_var_uint.value()),
                field_id_length,
                input_after_field_id,
            )
        } else {
            (None, 0, initial_input)
        };

        let mut annotations_header_length = 0u8;
        let mut annotations_sequence_length = 0u8;
        let mut expected_value_length = None;

        let mut type_descriptor = input.peek_type_descriptor()?;
        if type_descriptor.is_annotation_wrapper() {
            let (wrapper, input_after_annotations) =
                input.read_annotations_wrapper(type_descriptor)?;
            annotations_header_length = wrapper.header_length;
            annotations_sequence_length = wrapper.sequence_length;
            expected_value_length = Some(wrapper.expected_value_length);
            input = input_after_annotations;
            type_descriptor = input.peek_type_descriptor()?;
            if type_descriptor.is_annotation_wrapper() {
                return decoding_error("found an annotations wrapper ");
            }
        } else if type_descriptor.is_nop() {
            (_, input) = input.consume_nop_padding(type_descriptor)?;
        }

        let header = type_descriptor
            .to_header()
            .ok_or_else(|| decoding_error_raw("found a non-value in value position"))?;

        let header_offset = input.offset();
        let (length, _) = input.consume(1).read_value_length(header)?;
        let header_length = u8::try_from(length.size_in_bytes()).map_err(|_e| {
            decoding_error_raw("found a value with a header length field over 255 bytes long")
        })?;
        let value_length = length.value(); // ha
        let total_length = field_id_length as usize
            + annotations_header_length as usize
            + 1 // Header byte
            + header_length as usize
            + value_length;

        if let Some(expected_value_length) = expected_value_length {
            let actual_value_length = 1 + header_length as usize + value_length;
            if expected_value_length != actual_value_length {
                println!("{} != {}", expected_value_length, actual_value_length);
                return decoding_error(
                    "value length did not match length declared by annotations wrapper",
                );
            }
        }

        let encoded_value = EncodedValue {
            header,
            field_id_length,
            field_id,
            annotations_header_length,
            annotations_sequence_length,
            header_offset,
            header_length,
            value_length,
            total_length,
        };
        let lazy_value = LazyRawValue {
            encoded_value,
            input: initial_input,
        };
        Ok(Some(lazy_value))
    }

    pub fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn has_annotations(&self) -> bool {
        self.encoded_value.has_annotations()
    }

    fn annotations_sequence(&self) -> ImmutableBuffer<'a> {
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
            None => return self.input.slice(0, 0),
            Some(offset_and_length) => offset_and_length,
        };
        let local_sequence_offset = sequence_offset - self.input.offset();

        self.input.slice(local_sequence_offset, sequence_length)
    }

    pub fn annotations(&self) -> RawAnnotationsIterator<'a> {
        RawAnnotationsIterator::new(self.annotations_sequence())
    }

    // Return the part of the input buffer immediately following this encoded value
    fn consume_bytes(&self) -> IonResult<ImmutableBuffer<'a>> {
        let total_length = self.encoded_value.total_length();
        if self.input.len() < total_length {
            eprintln!("[consume_bytes] Incomplete {:?}", self);
            return incomplete_data_error(
                "only part of the current value is in the buffer",
                self.input.offset(),
            );
        }
        Ok(self.input.consume(total_length))
    }

    pub fn read(&self) -> ValueParseResult<'a> {
        if self.encoded_value.header().is_null() {
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

    // Can return Err if there aren't enough bytes available
    fn value_body(&self) -> IonResult<&'a [u8]> {
        let value_total_length = self.encoded_value.total_length();
        if self.input.len() < value_total_length {
            eprintln!("[value_body] Incomplete {:?}", self);
            return incomplete_data_error(
                "only part of the requested value is available in the buffer",
                self.input.offset(),
            );
        }
        let value_body_length = self.encoded_value.value_length();
        let value_offset = value_total_length - value_body_length;
        Ok(self.input.bytes_range(value_offset, value_body_length))
    }

    fn available_body(&self) -> ImmutableBuffer<'a> {
        let value_total_length = self.encoded_value.total_length();
        let value_body_length = self.encoded_value.value_length();
        let value_offset = value_total_length - value_body_length;

        let bytes_needed = std::cmp::min(self.input.len() - value_offset, value_body_length);
        let buffer_slice = self.input.slice(value_offset, bytes_needed);
        buffer_slice
    }

    pub(crate) fn field_name(&'a self) -> Option<SymbolId> {
        self.encoded_value.field_id
    }

    fn read_bool(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Bool);
        let representation = self.encoded_value.header().length_code;
        let value = match representation {
            0 => false,
            1 => true,
            invalid => {
                return decoding_error(format!(
                    "found a boolean value with an illegal representation (must be 0 or 1): {}",
                    invalid
                ))
            }
        };
        Ok(RawValueRef::Bool(value))
    }

    fn read_int(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Int);
        // `value_body()` returns a buffer starting at the body of the value.
        // It also confirms that the entire value is in the buffer.
        let uint_bytes = self.value_body()?;
        let magnitude: Int = if uint_bytes.len() <= mem::size_of::<u64>() {
            DecodedUInt::small_uint_from_slice(uint_bytes).into()
        } else {
            DecodedUInt::big_uint_from_slice(uint_bytes).into()
        };

        use crate::binary::type_code::IonTypeCode::*;
        let value = match (self.encoded_value.header.ion_type_code, magnitude) {
            (PositiveInteger, integer) => integer,
            (NegativeInteger, integer) if integer.is_zero() => {
                return decoding_error("found a negative integer (typecode=3) with a value of 0");
            }
            (NegativeInteger, integer) => -integer,
            _itc => return decoding_error("unexpected ion type code"),
        };
        Ok(RawValueRef::Int(value))
    }

    fn read_float(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Float);
        let ieee_bytes = self.value_body()?;
        let number_of_bytes = self.encoded_value.value_length();
        let value = match number_of_bytes {
            0 => 0f64,
            4 => f64::from(BigEndian::read_f32(ieee_bytes)),
            8 => BigEndian::read_f64(ieee_bytes),
            _ => return decoding_error("encountered a float with an illegal length"),
        };
        Ok(RawValueRef::Float(value))
    }

    fn read_decimal(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Decimal);

        if self.encoded_value.value_length() == 0 {
            return Ok(RawValueRef::Decimal(Decimal::new(0i32, 0i64)));
        }

        let (exponent_var_int, remaining) = self.input.read_var_int()?;
        let coefficient_size_in_bytes =
            self.encoded_value.value_length() - exponent_var_int.size_in_bytes();

        let exponent = exponent_var_int.value();
        let (coefficient, _remaining) = remaining.read_int(coefficient_size_in_bytes)?;

        if coefficient.is_negative_zero() {
            return Ok(RawValueRef::Decimal(Decimal::negative_zero_with_exponent(
                exponent,
            )));
        }

        Ok(RawValueRef::Decimal(Decimal::new(coefficient, exponent)))
    }

    fn read_timestamp(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Timestamp);

        let input = ImmutableBuffer::new(self.value_body()?);

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
            return decoding_error("timestamps with an hour must also specify a minute");
        }
        let (minute_var_uint, input) = input.read_var_uint()?;
        let minute = minute_var_uint.value() as u32;
        let builder = builder.with_hour_and_minute(hour, minute);
        if input.is_empty() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
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
                builder.build_at_unknown_offset()
            }?;
            return Ok(RawValueRef::Timestamp(timestamp));
        }

        // Fractional second precision

        let (subsecond_exponent_var_uint, input) = input.read_var_int()?;
        let subsecond_exponent = subsecond_exponent_var_uint.value();
        // The remaining bytes represent the coefficient.
        let coefficient_size_in_bytes = self.encoded_value.value_length() - input.offset();
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
            builder.build_at_unknown_offset()
        }?;

        Ok(RawValueRef::Timestamp(timestamp))
    }

    /// If the reader is currently positioned on a symbol value, parses that value into a `SymbolId`.
    pub fn read_symbol_id(&self) -> IonResult<SymbolId> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Symbol);
        let uint_bytes = self.value_body()?;
        if uint_bytes.len() > mem::size_of::<usize>() {
            return decoding_error("found a symbol ID that was too large to fit in a usize");
        }
        let magnitude = DecodedUInt::small_uint_from_slice(uint_bytes);
        // This cast is safe because we've confirmed the value was small enough to fit in a usize.
        Ok(magnitude as usize)
    }

    pub fn read_symbol(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Symbol);
        self.read_symbol_id()
            .map(|sid| RawValueRef::Symbol(RawSymbolTokenRef::SymbolId(sid)))
    }

    /// If the reader is currently positioned on a string, returns a [&str] containing its text.
    fn read_string(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::String);
        let raw_bytes = self.value_body()?;
        let text = std::str::from_utf8(raw_bytes)
            .map_err(|_| decoding_error_raw("found a string with invalid utf-8 data"))?;
        Ok(RawValueRef::String(text))
    }

    fn read_blob(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Blob);
        let bytes = self.value_body()?;
        Ok(RawValueRef::Blob(bytes))
    }

    fn read_clob(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Clob);
        let bytes = self.value_body()?;
        Ok(RawValueRef::Clob(bytes))
    }

    fn read_sexp(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::SExp);
        let lazy_value = LazyRawValue {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let lazy_sequence = LazyRawSequence { value: lazy_value };
        Ok(RawValueRef::SExp(lazy_sequence))
    }

    fn read_list(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::List);
        let lazy_value = LazyRawValue {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let lazy_sequence = LazyRawSequence { value: lazy_value };
        Ok(RawValueRef::List(lazy_sequence))
    }

    fn read_struct(&self) -> ValueParseResult<'a> {
        debug_assert!(self.encoded_value.ion_type() == IonType::Struct);
        let lazy_value = LazyRawValue {
            encoded_value: self.encoded_value,
            input: self.input,
        };
        let lazy_struct = LazyRawStruct { value: lazy_value };
        Ok(RawValueRef::Struct(lazy_struct))
    }
}

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct RawAnnotationsIterator<'a> {
    buffer: ImmutableBuffer<'a>,
}

impl<'a> RawAnnotationsIterator<'a> {
    pub(crate) fn new(buffer: ImmutableBuffer<'a>) -> RawAnnotationsIterator<'a> {
        RawAnnotationsIterator { buffer }
    }
}

impl<'a> Iterator for RawAnnotationsIterator<'a> {
    type Item = IonResult<RawSymbolTokenRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            return None;
        }
        let (var_uint, buffer_after_var_uint) = match self.buffer.read_var_uint() {
            Ok(output) => output,
            Err(error) => return Some(Err(error)),
        };
        // If this var_uint was longer than the declared annotations wrapper length, return an error.
        let symbol_id = RawSymbolTokenRef::SymbolId(var_uint.value());
        self.buffer = buffer_after_var_uint;
        Some(Ok(symbol_id))
    }
}

// TODO: set header cache to 'static'

#[cfg(test)]
mod tests {
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
    use crate::lazy::binary::lazy_raw_reader::{
        LazyRawBinaryReader, LazyRawValue, RawSequenceIterator,
    };
    use crate::lazy::raw_stream_item::RawStreamItem;
    use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
    use crate::{BinaryWriterBuilder, IonResult, IonType, IonWriter, RawSymbolTokenRef};

    fn to_10n(text_ion: &str) -> IonResult<Vec<u8>> {
        let mut buffer = Vec::new();
        let mut writer = BinaryWriterBuilder::default().build(&mut buffer)?;
        let elements = Element::read_all(text_ion)?;
        writer.write_elements(&elements)?;
        writer.flush()?;
        drop(writer);
        Ok(buffer)
    }

    #[test]
    fn test_single() -> IonResult<()> {
        let data = &to_10n("null 5 false true")?[4..]; // skip ivm
        let buffer = ImmutableBuffer::new(data);
        let lazy_value = LazyRawValue::peek_value_without_field_id(buffer)?.unwrap();
        let raw_value = lazy_value.read()?;
        println!("{:?}", raw_value);
        Ok(())
    }

    #[test]
    fn test_sequence() -> IonResult<()> {
        let data = &to_10n(
            r#"
            null 
            5
            false
            25e-1
            2.5
            2023-04-22T20:46:39.000-05:00
            "haha, hey!"
            name // A symbol that's already in the table so we don't need an LST
            (8 9 10)
            {name: "foo", symbols: ["bar", "baz", "quux"]}
        "#,
        )?[4..]; // skip ivm
        let buffer = ImmutableBuffer::new(data);
        let mut sequence_reader = RawSequenceIterator::new(buffer);
        while let Some(value) = sequence_reader.next()? {
            println!("{:?}", value.read()?);
        }
        Ok(())
    }

    #[test]
    fn test_struct() -> IonResult<()> {
        let data = &to_10n(
            r#"
            {name:"hi", name: "hello"}
        "#,
        )?[4..]; // skip ivm
        let buffer = ImmutableBuffer::new(data);
        let mut sequence_reader = RawSequenceIterator::new(buffer);
        while let Some(value) = sequence_reader.next()? {
            println!("{:?}", value.read()?);
        }
        Ok(())
    }

    #[test]
    fn test_top_level() -> IonResult<()> {
        let data = &to_10n(
            r#"
            "yo"
            77
            true
            {name:"hi", name: "hello"}
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(data);
        loop {
            match reader.next()? {
                RawStreamItem::VersionMarker(major, minor) => println!("IVM: v{}.{}", major, minor),
                RawStreamItem::Value(value) => println!("{:?}", value.read()?),
                RawStreamItem::Nothing => break,
            }
        }
        Ok(())
    }

    #[test]
    fn annotations_sequence() -> IonResult<()> {
        let data = &to_10n(
            r#"
            $ion_symbol_table::{symbols: ["foo"]}
            foo // binary writer will omit the symtab if we don't use a symbol 
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(data);
        let _ivm = reader.next()?.expect_ivm()?;
        let value = reader.next()?.expect_value()?;
        let annotations_sequence = value.annotations_sequence();
        assert_eq!(annotations_sequence.len(), 1);
        assert_eq!(annotations_sequence.offset(), 6);
        assert_eq!(annotations_sequence.bytes()[0], 0x83u8); // 0x83 == $3 == $ion_symbol_table
        Ok(())
    }

    #[test]
    fn annotations() -> IonResult<()> {
        let data = &to_10n(
            r#"
            $ion_symbol_table::{symbols: ["foo", "bar", "baz"]}
            foo::bar::baz::7             
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(data);
        let _ivm = reader.next()?.expect_ivm()?;

        // Read annotations from $ion_symbol_table::{...}
        let symbol_table = reader.next()?.expect_value()?;
        assert_eq!(symbol_table.ion_type(), IonType::Struct);
        let annotations = symbol_table
            .annotations()
            .collect::<IonResult<Vec<RawSymbolTokenRef<'_>>>>()?;
        assert_eq!(annotations.len(), 1);
        assert_eq!(annotations[0], 3.as_raw_symbol_token_ref());

        // Read annotations from foo::bar::baz::7
        let int = reader.next()?.expect_value()?;
        assert_eq!(int.ion_type(), IonType::Int);
        let annotations = int
            .annotations()
            .collect::<IonResult<Vec<RawSymbolTokenRef<'_>>>>()?;
        assert_eq!(annotations.len(), 3);
        assert_eq!(annotations[0], 10.as_raw_symbol_token_ref());
        assert_eq!(annotations[1], 11.as_raw_symbol_token_ref());
        assert_eq!(annotations[2], 12.as_raw_symbol_token_ref());
        Ok(())
    }
}
