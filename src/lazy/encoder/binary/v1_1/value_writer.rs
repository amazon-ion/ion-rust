use arrayvec::ArrayVec;
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::lazy::encoder::binary::v1_1::container_writers::{
    BinaryContainerWriter_1_1, BinaryListValuesWriter_1_1, BinaryListWriter_1_1,
    BinarySExpValuesWriter_1_1, BinarySExpWriter_1_1, BinaryStructFieldsWriter_1_1,
    BinaryStructWriter_1_1,
};
use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::{AnnotatableValueWriter, ValueWriter};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::types::integer::IntData;
use crate::{
    Decimal, FlexInt, FlexUInt, Int, IonResult, IonType, RawSymbolTokenRef, SymbolId, Timestamp,
};

pub struct BinaryValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    encoding_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryValueWriter_1_1<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryValueWriter_1_1<'value, 'top> {
        BinaryValueWriter_1_1 {
            allocator,
            encoding_buffer,
        }
    }

    #[inline]
    fn push_byte(&mut self, byte: u8) {
        self.encoding_buffer.push(byte);
    }

    #[inline]
    fn push_bytes(&mut self, bytes: &[u8]) {
        self.encoding_buffer.extend_from_slice(bytes)
    }

    pub(crate) fn buffer(&self) -> &[u8] {
        self.encoding_buffer.as_slice()
    }

    pub fn write_lob(self, _value: &[u8], _type_code: u8) -> IonResult<()> {
        todo!()
    }

    pub fn write_null(mut self, ion_type: IonType) -> IonResult<()> {
        let type_byte = match ion_type {
            IonType::Null => {
                self.push_byte(0xEA);
                // Untyped null (i.e. `null`, `null.null`) has no trailing type byte
                return Ok(());
            }
            IonType::Bool => 0,
            IonType::Int => 1,
            IonType::Float => 2,
            IonType::Decimal => 3,
            IonType::Timestamp => 4,
            IonType::String => 5,
            IonType::Symbol => 6,
            IonType::Blob => 7,
            IonType::Clob => 8,
            IonType::List => 9,
            IonType::SExp => 10,
            IonType::Struct => 11,
        };
        self.push_bytes(&[0xEB, type_byte]);
        Ok(())
    }

    pub fn write_bool(mut self, value: bool) -> IonResult<()> {
        let encoding = match value {
            true => 0x5E,
            false => 0x5F,
        };
        self.push_byte(encoding);
        Ok(())
    }

    #[inline]
    pub fn write_i64(mut self, value: i64) -> IonResult<()> {
        let mut opcode = 0x50;
        if value == 0 {
            self.push_byte(opcode);
            return Ok(());
        }
        let num_sign_bits = if value < 0 {
            value.leading_ones()
        } else {
            value.leading_zeros()
        };
        let num_magnitude_bits = 64 - num_sign_bits;
        let num_encoded_bytes = (num_magnitude_bits as usize / 8) + 1;
        opcode |= num_encoded_bytes as u8;

        let le_bytes = value.to_le_bytes();
        let encoded_bytes = &le_bytes[..num_encoded_bytes];

        self.push_byte(opcode);
        self.push_bytes(encoded_bytes);
        Ok(())
    }

    // Helper method for `write_int`.
    fn write_big_int(mut self, value: &BigInt) -> IonResult<()> {
        // Try downgrading the value to an i64 if it's small enough. This avoids a Vec allocation and handles the
        // zero case.
        if let Some(small_value) = value.to_i64() {
            return self.write_i64(small_value);
        }
        // If it's truly a big int, allocate a Vec of its little-endian bytes.
        let le_bytes = value.to_signed_bytes_le();
        let num_encoded_bytes = le_bytes.len();

        // Because we've ruled out numbers small enough to fit in an i64, its encoded length must be greater than 8.
        // Write the opcode for an integer with a FlexUInt length.
        self.push_byte(0xF5);
        // Write the length as a FlexUInt.
        FlexUInt::write_u64(self.encoding_buffer, num_encoded_bytes as u64)?;
        // Write the little endian bytes of the integer.
        self.push_bytes(le_bytes.as_slice());
        Ok(())
    }

    #[inline]
    pub fn write_int(self, value: &Int) -> IonResult<()> {
        match &value.data {
            IntData::I64(int) => self.write_i64(*int),
            IntData::BigInt(int) => self.write_big_int(int),
        }
    }

    // TODO: write_f16(...)

    pub fn write_f32(mut self, value: f32) -> IonResult<()> {
        if value == 0f32 && !value.is_sign_negative() {
            self.push_byte(0x5A);
            return Ok(());
        }
        self.push_byte(0x5C);
        // Float endianness is an open question.
        // See: https://github.com/amazon-ion/ion-docs/issues/294
        self.push_bytes(&value.to_le_bytes());
        Ok(())
    }

    pub fn write_f64(mut self, value: f64) -> IonResult<()> {
        if value == 0f64 && !value.is_sign_negative() {
            self.push_byte(0x5A);
            return Ok(());
        }
        self.push_byte(0x5D);
        // Float endianness is an open question.
        // See: https://github.com/amazon-ion/ion-docs/issues/294
        self.push_bytes(&value.to_le_bytes());
        Ok(())
    }

    pub fn write_decimal(mut self, value: &Decimal) -> IonResult<()> {
        // Insert a placeholder opcode; we'll overwrite the length nibble with the appropriate value when the encoding
        // is complete.
        let opcode_index = self.encoding_buffer.len();
        self.push_byte(0x60);

        // Whether the decimal has a positive zero coefficient (of any exponent). This value is needed in two places
        // and is non-trivial, so we compute it up front and store the result.
        let is_positive_zero = value.coefficient().is_positive_zero();

        // If the value is 0.0, then the encoding has no body. The 0x60 opcode is the complete encoding.
        if value.exponent() == 0 && is_positive_zero {
            return Ok(());
        }

        // For any value that is not 0.0, the encoding begins with a FlexInt representing the exponent.
        let encoded_exponent_size = FlexInt::write_i64(self.encoding_buffer, value.exponent())?;

        let encoded_coefficient_size = if is_positive_zero {
            // If the coefficient is zero but the exponent was non-zero, write nothing; an implicit zero is positive.
            0
        } else if value.coefficient.is_negative_zero() {
            // If the coefficient is negative zero (of any exponent), write a zero byte; an explicit zero is negative.
            self.push_byte(0x00);
            1
        } else {
            // This `TryInto` impl will only fail if the coefficient is negative zero, which we've already ruled out.
            let coefficient: Int = value.coefficient().try_into().unwrap();
            FixedInt::write(self.encoding_buffer, &coefficient)?
        };

        let Some(encoded_body_size) = encoded_exponent_size.checked_add(encoded_coefficient_size)
        else {
            // If the decimal's *length* cannot be stored in a `usize`, report an error.
            return IonResult::encoding_error(format!(
                "decimal {value} exceeds the currently supported maximum encoding size"
            ));
        };

        match encoded_body_size {
            0..=15 => {
                // In the common case, the body of a decimal will require fewer than 16 bytes to encode.
                // In this case, we can write the encoded body length in the low nibble of the opcode we already wrote.
                self.encoding_buffer[opcode_index] |= encoded_body_size as u8;
            }
            16.. => {
                // If the encoded size ends up being unusually large, we will splice in a corrected header.
                // Start by overwriting our original opcode with 0xF6, which indicates a Decimal with a FlexUInt length.
                self.encoding_buffer[opcode_index] = 0xF6;
                // We'll use an `ArrayVec` as our encoding buffer because it's stack-allocated and implements `io::Write`.
                // It has a capacity of 16 bytes because it's the smallest power of two that is still large enough to
                // hold a FlexUInt encoding of usize::MAX on a 64-bit platform.
                let mut buffer: ArrayVec<u8, 16> = ArrayVec::new();
                FlexUInt::write_u64(&mut buffer, encoded_body_size as u64)?;
                let encoded_length_start = opcode_index + 1;
                // `splice` allows you to overwrite Vec elements as well as insert them.
                // This is an empty range at the desired location, indicating that we're only inserting.
                let splice_range = encoded_length_start..encoded_length_start;
                self.encoding_buffer
                    .splice(splice_range, buffer.as_slice().iter().copied());
            }
        }
        Ok(())
    }

    pub fn write_timestamp(mut self, value: &Timestamp) -> IonResult<()> {
        use crate::TimestampPrecision::*;

        const MIN_OFFSET: i32 = -14 * 60; // Western hemisphere, 14:00
        const MAX_OFFSET: i32 = 14 * 60; // Eastern hemisphere, -14:00
        const SHORT_FORM_OFFSET_RANGE: std::ops::RangeInclusive<i32> = MIN_OFFSET..=MAX_OFFSET;

        let precision = value.precision();
        let scale = value.fractional_seconds_scale().unwrap_or(0);

        // Before encoding begins, see if this timestamp is one that can be written using the compact and easy-to-parse
        // short form. To be short-form eligible, we must confirm that...
        let is_short_form_eligible =
            // ...the year can be represented as a 7 bit offset from the epoch (1970)...
            (1970..2098).contains(&value.year())
                // ...the offset is either unknown or is a quarter-hour between -14:00 and 14:00...
                && value.offset().map(|offset| {
                SHORT_FORM_OFFSET_RANGE.contains(&offset) && offset % 15 == 0
            }).unwrap_or(true)
                // ...and if present, the subsecond precision is either milliseconds, microseconds, or nanoseconds.
                && match scale {
                // TODO: Is this faster than `scale <= 9 && scale % 3 == 0`?
                0 | 3 | 6 | 9 => true,
                _ => false,
            };

        // If the timestamp does not meet the above criteria, we must instead encode it as a long-form timestamp.
        if !is_short_form_eligible {
            return self.write_long_form_timestamp(value);
        }

        // The number of bits dedicated to each time unit in a short-form timestamp
        const NUM_YEAR_BITS: u32 = 7;
        const NUM_MONTH_BITS: u32 = 4;
        const NUM_DAY_BITS: u32 = 5;
        const NUM_HOUR_BITS: u32 = 5;
        const NUM_MINUTE_BITS: u32 = 6;
        const NUM_SECOND_BITS: u32 = 6;
        // The number of bits dedicated to representing the offset (known or unknown/UTC) in a short-form timestamp
        const NUM_UNKNOWN_OR_UTC_BITS: u32 = 1;
        const NUM_KNOWN_OFFSET_BITS: u32 = 7;

        // The bit offsets of each time unit within the encoding
        const YEAR_BIT_OFFSET: u32 = 0;
        const MONTH_BIT_OFFSET: u32 = NUM_YEAR_BITS;
        const DAY_BIT_OFFSET: u32 = MONTH_BIT_OFFSET + NUM_MONTH_BITS;
        const HOUR_BIT_OFFSET: u32 = DAY_BIT_OFFSET + NUM_DAY_BITS;
        const MINUTE_BIT_OFFSET: u32 = HOUR_BIT_OFFSET + NUM_HOUR_BITS;
        const OFFSET_BIT_OFFSET: u32 = MINUTE_BIT_OFFSET + NUM_MINUTE_BITS;

        // We encode all of the time unit fields regardless of the precision. This step is cheap, as it involves only
        // left shifting and bitwise ORs. Branching to avoid these operations would be more expensive than just doing
        // them.
        let mut encoding: u64 = value.year() as u64 - 1970u64;
        encoding |= (value.month() as u64) << MONTH_BIT_OFFSET;
        encoding |= (value.day() as u64) << DAY_BIT_OFFSET;
        encoding |= (value.hour() as u64) << HOUR_BIT_OFFSET;
        encoding |= (value.minute() as u64) << MINUTE_BIT_OFFSET;

        // Compute the offset, its width in bits, and how that will affect the opcode and encoded length.
        let (num_offset_bits, offset_value, opcode_adjustment, length_adjustment) =
            match value.offset() {
                None => (1, 1, 0, 0), // Unknown offset uses a single bit (1); opcode and length stay the same.
                Some(0) => (1, 0, 0, 0), // UTC uses a single bit (0); opcode and length stay the same.
                Some(offset_minutes) => {
                    // Bump the opcode to the one the corresponds to the same precision/scale but with a known offset
                    let opcode_adjustment = 5;
                    // `Seconds` is the only timestamp precision that does not change lengths when the offset is known.
                    let length_adjustment = if precision == Second && scale == 0 {
                        0
                    } else {
                        1
                    };
                    // The offset is encoded as the number of quarter-hours from offset -14:00.
                    let quarter_hours = ((offset_minutes - MIN_OFFSET) / 15) as u64;
                    // A known offset uses 7 bits; opcode increases by 5, length (often) increases by 1.
                    (7, quarter_hours, opcode_adjustment, length_adjustment)
                }
            };

        // These opcodes assume UTC or unknown offset--we adjust for known offsets afterwards.
        let (mut opcode, bits_populated, mut encoded_body_length, subseconds) =
            match (precision, scale) {
                (Year, _) => (0x70, 7, 1, 0),
                (Month, _) => (0x71, 11, 2, 0),
                (Day, _) => (0x72, 16, 2, 0),
                (HourAndMinute, _) => (0x73, 27 + num_offset_bits, 4, 0),
                // Seconds
                (Second, 0) => (0x74, 33 + num_offset_bits, 5, 0),
                // Milliseconds
                (Second, 3) => (0x75, 43 + num_offset_bits, 6, value.milliseconds()),
                // Microseconds
                (Second, 6) => (0x76, 53 + num_offset_bits, 7, value.microseconds()),
                // Nanoseconds
                (Second, 9) => (0x77, 63 + num_offset_bits, 8, value.nanoseconds()),
                _ => {
                    unreachable!("illegal precision / fractional second seconds scale encountered")
                }
            };

        // If the timestamp has a known offset, its opcode and encoded length must be adjusted.
        // If it is unknown or UTC, the adjustment values will be zero making these steps into no-ops.
        opcode += opcode_adjustment;
        encoded_body_length += length_adjustment;

        // Encode the offset
        encoding |= offset_value << OFFSET_BIT_OFFSET;

        // Because the seconds and subseconds follow the offset (which can be 1 bit or 7 bits) we need to dynamically
        // calculate their respective bit offsets.
        let seconds_bit_offset = OFFSET_BIT_OFFSET + num_offset_bits;
        encoding |= (value.second() as u64) << seconds_bit_offset;

        let subseconds_bit_offset = seconds_bit_offset + NUM_SECOND_BITS;
        encoding |= (subseconds as u64) << subseconds_bit_offset;

        // Because we eagerly (and branchless-ly) encoded all of the time units, we may have populated bits that are
        // irrelevant to the final encoding. To simplify unit testing (and in the current absence of a binary 1.1
        // reader), we calculate a mask of which bits are relevant to the current opcode and set any bits not in use
        // to `0`.
        // TODO: Remove this logic pending resolution of https://github.com/amazon-ion/ion-docs/issues/295, which
        //       suggests requiring readers to ignore bits not used by the specified opcode
        let mask = 1u64
            .checked_shl(bits_populated)
            .unwrap_or(0)
            .checked_sub(1)
            .unwrap_or(u64::MAX);
        encoding &= mask;

        self.push_byte(opcode);

        // If the timestamp is at a known offset and uses nanosecond precision...
        if opcode == 0x7C {
            // ...then its encoding requires 70 bits. We've been using a u64 to hold the encoding, so the most
            // significant 6 bits have been lost at this point. We need to get the most significant 6 bits of the
            // nanoseconds field and write them out as a final byte. Because `subseconds` represents a number of
            // nanoseconds between 0 and 999,999,999, its most significant 2 bits are guaranteed to be `00`. We can
            // isolate the most significant 6 bits of the magnitude by isolating the most significant 8 bits of
            // `subseconds`, which is a u32.
            let high_six = (subseconds >> 24) as u8;
            self.push_bytes(&encoding.to_le_bytes()[..]);
            self.push_byte(high_six);
        } else {
            self.push_bytes(&encoding.to_le_bytes()[..encoded_body_length]);
        }

        Ok(())
    }

    fn write_long_form_timestamp(self, _value: &Timestamp) -> IonResult<()> {
        todo!("long-form timestamp encoding is not yet implemented");
    }

    pub fn write_string<A: AsRef<str>>(mut self, value: A) -> IonResult<()> {
        const STRING_OPCODE: u8 = 0x80;
        const STRING_FLEX_UINT_LEN_OPCODE: u8 = 0xF8;
        self.write_text(STRING_OPCODE, STRING_FLEX_UINT_LEN_OPCODE, value.as_ref())
    }

    pub fn write_symbol<A: AsRawSymbolTokenRef>(mut self, value: A) -> IonResult<()> {
        const SYMBOL_OPCODE: u8 = 0x90;
        const SYMBOL_FLEX_UINT_LEN_OPCODE: u8 = 0xF9;
        match value.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => self.write_symbol_id(sid),
            RawSymbolTokenRef::Text(text) => {
                self.write_text(SYMBOL_OPCODE, SYMBOL_FLEX_UINT_LEN_OPCODE, text.as_ref())
            }
        }
    }

    #[inline]
    fn write_symbol_id(&mut self, symbol_id: SymbolId) -> IonResult<()> {
        match symbol_id {
            0..=255 => {
                self.push_bytes(&[0xE1, symbol_id as u8]);
            }
            // The u16::MAX range, but biased by 256.
            256..=65_791 => {
                self.push_byte(0xE2); // Two-byte biased FixedUInt follows
                let encoded_length = ((symbol_id - 256) as u16).to_le_bytes();
                self.push_bytes(encoded_length.as_slice());
            }
            // 65,792 and higher
            _ => {
                self.push_byte(0xE3); // Biased FlexUInt follows
                FlexUInt::write_u64(self.encoding_buffer, symbol_id as u64 - 65_792)?;
            }
        }
        Ok(())
    }

    /// Helper method for writing strings and symbols with inline UTF8 bytes.
    #[inline]
    fn write_text(&mut self, opcode: u8, var_len_opcode: u8, text: &str) -> IonResult<()> {
        match text.len() {
            num_utf8_bytes @ 0..=15 => {
                // The length is small enough to safely cast it to u8 and include it in the opcode.
                self.push_byte(opcode | num_utf8_bytes as u8);
            }
            num_utf8_bytes => {
                self.push_byte(var_len_opcode);
                FlexUInt::write_u64(self.encoding_buffer, num_utf8_bytes as u64)?;
            }
        };
        self.push_bytes(text.as_bytes());
        Ok(())
    }

    pub fn write_clob<A: AsRef<[u8]>>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    pub fn write_blob<A: AsRef<[u8]>>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    fn list_writer(&mut self) -> BinaryListWriter_1_1<'_, 'top> {
        todo!()
    }

    fn sexp_writer(&mut self) -> BinarySExpWriter_1_1<'_, 'top> {
        todo!()
    }

    fn struct_writer(&mut self) -> BinaryStructWriter_1_1<'_, 'top> {
        const STRUCT_TYPE_CODE: u8 = 0xD0;
        BinaryStructWriter_1_1::new(BinaryContainerWriter_1_1::new(
            STRUCT_TYPE_CODE,
            self.allocator,
            self.encoding_buffer,
        ))
    }

    fn write_list<
        F: for<'a> FnOnce(&mut <Self as ValueWriter>::ListWriter<'a>) -> IonResult<()>,
    >(
        mut self,
        list_fn: F,
    ) -> IonResult<()> {
        self.list_writer().write_values(list_fn)
    }
    fn write_sexp<
        F: for<'a> FnOnce(&mut <Self as ValueWriter>::SExpWriter<'a>) -> IonResult<()>,
    >(
        mut self,
        sexp_fn: F,
    ) -> IonResult<()> {
        self.sexp_writer().write_values(sexp_fn)
    }
    fn write_struct<
        F: for<'a> FnOnce(&mut <Self as ValueWriter>::StructWriter<'a>) -> IonResult<()>,
    >(
        mut self,
        struct_fn: F,
    ) -> IonResult<()> {
        self.struct_writer().write_fields(struct_fn)
    }
}

impl<'value, 'top> Sealed for BinaryValueWriter_1_1<'value, 'top> {}

impl<'value, 'top> ValueWriter for BinaryValueWriter_1_1<'value, 'top> {
    type ListWriter<'a> = BinaryListValuesWriter_1_1<'a>;
    type SExpWriter<'a> = BinarySExpValuesWriter_1_1<'a>;
    type StructWriter<'a> = BinaryStructFieldsWriter_1_1<'a>;

    delegate! {
        to self {
            fn write_null(self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_symbol(self, value: impl AsRawSymbolTokenRef) -> IonResult<()>;
            fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
                self,
                list_fn: F,
            ) -> IonResult<()>;
            fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
                self,
                sexp_fn: F,
            ) -> IonResult<()>;
            fn write_struct<
                F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>,
            >(
                self,
                struct_fn: F,
            ) -> IonResult<()>;
        }
    }
}

pub struct BinaryAnnotatableValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    encoding_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryAnnotatableValueWriter_1_1<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryAnnotatableValueWriter_1_1<'value, 'top> {
        BinaryAnnotatableValueWriter_1_1 {
            allocator,
            encoding_buffer,
        }
    }
}

impl<'value, 'top: 'value> AnnotatableValueWriter
    for BinaryAnnotatableValueWriter_1_1<'value, 'top>
{
    type ValueWriter = BinaryValueWriter_1_1<'value, 'top>;
    type AnnotatedValueWriter<'a, SymbolType: AsRawSymbolTokenRef + 'a> =
    BinaryAnnotationsWrapperWriter_1_1<'a, 'top, SymbolType> where Self: 'a;
    fn with_annotations<'a, SymbolType: AsRawSymbolTokenRef>(
        self,
        annotations: &'a [SymbolType],
    ) -> Self::AnnotatedValueWriter<'a, SymbolType>
    where
        Self: 'a,
    {
        BinaryAnnotationsWrapperWriter_1_1::new(self.allocator, annotations, self.encoding_buffer)
    }

    #[inline(always)]
    fn without_annotations(self) -> BinaryValueWriter_1_1<'value, 'top> {
        BinaryValueWriter_1_1::new(self.allocator, self.encoding_buffer)
    }
}

pub struct BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType: AsRawSymbolTokenRef> {
    annotations: &'value [SymbolType],
    allocator: &'top BumpAllocator,
    output_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef>
    BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    pub fn new(
        allocator: &'top BumpAllocator,
        annotations: &'value [SymbolType],
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType> {
        BinaryAnnotationsWrapperWriter_1_1 {
            annotations,
            allocator,
            output_buffer: encoding_buffer,
        }
    }
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef>
    BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    fn encode_annotated<F>(self, _encode_value_fn: F) -> IonResult<()>
    where
        F: for<'a> FnOnce(BinaryAnnotatedValueWriter_1_1<'a, 'top>) -> IonResult<()>,
    {
        todo!()
    }

    fn annotate_encoded_value(self, _encoded_value: &[u8]) -> IonResult<()> {
        todo!()
    }

    fn encode_annotations_sequence(&self, _buffer: &'_ mut BumpVec<'_, u8>) -> IonResult<()> {
        todo!()
    }

    fn todo_value_writer_impl(self) -> Self {
        todo!()
    }
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef> Sealed
    for BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    // No methods, precludes implementations outside the crate.
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef> ValueWriter
    for BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    type ListWriter<'a> = BinaryListValuesWriter_1_1<'a>;
    type SExpWriter<'a> = BinarySExpValuesWriter_1_1<'a>;
    type StructWriter<'a> = BinaryStructFieldsWriter_1_1<'a>;

    fn write_null(self, _ion_type: IonType) -> IonResult<()> {
        todo!()
    }

    fn write_bool(self, _value: bool) -> IonResult<()> {
        todo!()
    }

    fn write_i64(self, _value: i64) -> IonResult<()> {
        todo!()
    }

    fn write_int(self, _value: &Int) -> IonResult<()> {
        todo!()
    }

    fn write_f32(self, _value: f32) -> IonResult<()> {
        todo!()
    }

    fn write_f64(self, _value: f64) -> IonResult<()> {
        todo!()
    }

    fn write_decimal(self, _value: &Decimal) -> IonResult<()> {
        todo!()
    }

    fn write_timestamp(self, _value: &Timestamp) -> IonResult<()> {
        todo!()
    }

    fn write_string(self, _value: impl AsRef<str>) -> IonResult<()> {
        todo!()
    }

    fn write_symbol(self, _value: impl AsRawSymbolTokenRef) -> IonResult<()> {
        todo!()
    }

    fn write_clob(self, _value: impl AsRef<[u8]>) -> IonResult<()> {
        todo!()
    }

    fn write_blob(self, _value: impl AsRef<[u8]>) -> IonResult<()> {
        todo!()
    }

    fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
        self,
        _list_fn: F,
    ) -> IonResult<()> {
        todo!()
    }

    fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
        self,
        _sexp_fn: F,
    ) -> IonResult<()> {
        todo!()
    }

    fn write_struct<F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>>(
        self,
        _struct_fn: F,
    ) -> IonResult<()> {
        todo!()
    }
}

pub struct BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    pub fn new(allocator: &'top BumpAllocator, buffer: &'value mut BumpVec<'top, u8>) -> Self {
        Self { allocator, buffer }
    }
    pub(crate) fn value_writer(&mut self) -> BinaryValueWriter_1_1<'_, 'top> {
        BinaryValueWriter_1_1::new(self.allocator, self.buffer)
    }

    pub(crate) fn buffer(&self) -> &[u8] {
        self.buffer.as_slice()
    }
}

impl<'value, 'top> Sealed for BinaryAnnotatedValueWriter_1_1<'value, 'top> {}

impl<'value, 'top: 'value> ValueWriter for BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    type ListWriter<'a> = BinaryListValuesWriter_1_1<'a>;
    type SExpWriter<'a> = BinarySExpValuesWriter_1_1<'a>;
    type StructWriter<'a> = BinaryStructFieldsWriter_1_1<'a>;
    delegate! {
        to self.value_writer() {
            fn write_null(mut self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(mut self, value: bool) -> IonResult<()>;
            fn write_i64(mut self, value: i64) -> IonResult<()>;
            fn write_int(mut self, value: &Int) -> IonResult<()>;
            fn write_f32(mut self, value: f32) -> IonResult<()>;
            fn write_f64(mut self, value: f64) -> IonResult<()>;
            fn write_decimal(mut self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(mut self, value: &Timestamp) -> IonResult<()>;
            fn write_string(mut self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_symbol(mut self, value: impl AsRawSymbolTokenRef) -> IonResult<()>;
            fn write_clob(mut self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(mut self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
                mut self,
                list_fn: F,
            ) -> IonResult<()>;
            fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
                mut self,
                sexp_fn: F,
            ) -> IonResult<()>;
            fn write_struct<
                F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>,
            >(
                mut self,
                struct_fn: F,
            ) -> IonResult<()>;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigInt;

    use crate::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
    use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
    use crate::{Decimal, Element, Int, IonResult, IonType, Null, SymbolId, Timestamp};

    fn encoding_test(
        mut test: impl FnMut(&mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>) -> IonResult<()>,
        expected_encoding: &[u8],
    ) -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer)?;
        test(&mut writer)?;
        writer.flush()?;
        // Make a byte array that starts with an Ion 1.1 IVM.
        let mut expected = vec![0xE0, 0x01, 0x01, 0xEA];
        expected.extend_from_slice(expected_encoding);
        let expected = expected.as_slice();
        let actual = buffer.as_slice();
        assert_eq!(
            expected, actual,
            "Actual \n    {actual:x?}\nwas not equal to\n    {expected:x?}\n"
        );
        Ok(())
    }

    #[test]
    fn write_nulls() -> IonResult<()> {
        let test_cases: &[(IonType, &[u8])] = &[
            (IonType::Null, &[0xEA]),
            (IonType::Bool, &[0xEB, 0]),
            (IonType::Int, &[0xEB, 1]),
            (IonType::Float, &[0xEB, 2]),
            (IonType::Decimal, &[0xEB, 3]),
            (IonType::Timestamp, &[0xEB, 4]),
            (IonType::String, &[0xEB, 5]),
            (IonType::Symbol, &[0xEB, 6]),
            (IonType::Blob, &[0xEB, 7]),
            (IonType::Clob, &[0xEB, 8]),
            (IonType::List, &[0xEB, 9]),
            (IonType::SExp, &[0xEB, 10]),
            (IonType::Struct, &[0xEB, 11]),
        ];
        for (ion_type, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(Null(*ion_type))?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_bools() -> IonResult<()> {
        let test_cases: &[(bool, &[u8])] = &[(true, &[0x5E]), (false, &[0x5F])];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(*value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_ints() -> IonResult<()> {
        let test_cases: &[(i64, &[u8])] = &[
            (0, &[0x50]),
            (-1, &[0x51, 0xFF]),
            (1, &[0x51, 0x01]),
            (100, &[0x51, 0x64]),
            (-100, &[0x51, 0x9C]),
            (127, &[0x51, 0x7F]),
            (-127, &[0x51, 0x81]),
            (128, &[0x52, 0x80, 0x00]),
            (-128, &[0x51, 0x80]),
            (
                i64::MAX,
                &[0x58, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
            ),
            (
                i64::MIN,
                &[0x58, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(*value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_f32s() -> IonResult<()> {
        let test_f64s: &[f32] = &[
            1.0,
            1.5,
            -1.5,
            10.0,
            10.5,
            -10.5,
            f32::INFINITY,
            f32::NEG_INFINITY,
            f32::NAN,
        ];
        for value in test_f64s {
            let mut expected_encoding = vec![0x5C];
            expected_encoding.extend_from_slice(&value.to_le_bytes()[..]);
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value)?;
                    Ok(())
                },
                expected_encoding.as_slice(),
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_f64s() -> IonResult<()> {
        let test_f64s: &[f64] = &[
            1.0,
            1.5,
            -1.5,
            10.0,
            10.5,
            -10.5,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ];
        for value in test_f64s {
            let mut expected_encoding = vec![0x5D];
            expected_encoding.extend_from_slice(&value.to_le_bytes()[..]);
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value)?;
                    Ok(())
                },
                expected_encoding.as_slice(),
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_strings() -> IonResult<()> {
        let test_cases: &[(&str, &[u8])] = &[
            ("", &[0x80]),
            //                 f     o     o
            ("foo", &[0x83, 0x66, 0x6F, 0x6F]),
            (
                "foo bar baz quux quuz",
                &[
                    0xF8, // Opcode: string with variable-width length
                    0x2B, // FlexUInt length
                    0x66, // UTF-8 text bytes
                    0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72, 0x20, 0x62, 0x61, 0x7a, 0x20, 0x71, 0x75,
                    0x75, 0x78, 0x20, 0x71, 0x75, 0x75, 0x7a,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(*value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_symbols_with_inline_text() -> IonResult<()> {
        let test_cases: &[(&str, &[u8])] = &[
            ("", &[0x90]),
            //                 f     o     o
            ("foo", &[0x93, 0x66, 0x6F, 0x6F]),
            (
                "foo bar baz quux quuz",
                &[
                    0xF9, // Opcode: symbol with variable-width length
                    0x2B, // FlexUInt length
                    0x66, // UTF-8 text bytes
                    0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72, 0x20, 0x62, 0x61, 0x7a, 0x20, 0x71, 0x75,
                    0x75, 0x78, 0x20, 0x71, 0x75, 0x75, 0x7a,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value.as_raw_symbol_token_ref())?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_symbol_ids() -> IonResult<()> {
        let test_cases: &[(SymbolId, &[u8])] = &[
            (0, &[0xE1, 0x00]),
            (1, &[0xE1, 0x01]),
            (255, &[0xE1, 0xFF]),
            (256, &[0xE2, 0x00, 0x00]),
            (65_791, &[0xE2, 0xFF, 0xFF]),
            (65_792, &[0xE3, 0x01]),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value.as_raw_symbol_token_ref())?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_decimals() -> IonResult<()> {
        let test_cases: &[(Decimal, &[u8])] = &[
            (Decimal::new(0, 0), &[0x60]),
            (Decimal::new(0, 3), &[0x61, 0x07]),
            (Decimal::negative_zero(), &[0x62, 0x01, 0x00]),
            (Decimal::negative_zero_with_exponent(3), &[0x62, 0x07, 0x00]),
            (
                Decimal::negative_zero_with_exponent(-3),
                &[0x62, 0xFB, 0x00],
            ),
            (Decimal::new(7, 4), &[0x62, 0x09, 0x07]),
            (
                // ~Pi
                Decimal::new(3_1415926535i64, -10),
                &[0x66, 0xED, 0x07, 0xFF, 0x88, 0x50, 0x07],
            ),
            (
                // ~e
                Decimal::new(
                    Int::from(
                        BigInt::from_str("27182818284590452353602874713526624977572").unwrap(),
                    ),
                    -40,
                ),
                &[
                    0xF6, 0x25, 0xB1, 0xA4, 0x2, 0x7E, 0xFA, 0x42, 0x46, 0x53, 0x50, 0xEF, 0x56,
                    0x73, 0xB, 0xE7, 0x5E, 0x14, 0xE2, 0x4F,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_timestamps() -> IonResult<()> {
        let test_cases: &[(&str, &[u8])] = &[
            // === Year ===
            //                  .YYY_YYYY
            ("1970T", &[0x70, 0b0000_0000]),
            ("2097T", &[0x70, 0b0111_1111]),
            ("2024T", &[0x70, 0b0011_0110]),
            //
            // === Month ===
            //                     MYYY_YYYY    ...._.MMM
            ("2024-01T", &[0x71, 0b1011_0110, 0b0000_0000]),
            ("2024-10T", &[0x71, 0b0011_0110, 0b0000_0101]),
            ("2024-11T", &[0x71, 0b1011_0110, 0b0000_0101]),
            ("2024-12T", &[0x71, 0b0011_0110, 0b0000_0110]),
            //
            // === Day ===
            //                       MYYY_YYYY    DDDD_DMMM
            ("2024-06-01", &[0x72, 0b0011_0110, 0b0000_1011]),
            ("2024-06-15", &[0x72, 0b0011_0110, 0b0111_1011]),
            ("2024-06-30", &[0x72, 0b0011_0110, 0b1111_0011]),
            //
            // === Hour & Minute @ UTC ===
            //
            (
                "2024-06-01T08:00Z",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x73, 0b0011_0110, 0b0000_1011, 0b0000_1000, 0b0000_0000],
            ),
            (
                "2024-06-15T12:30Z",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x73, 0b0011_0110, 0b0111_1011, 0b1100_1100, 0b0000_0011],
            ),
            (
                "2024-06-30T16:45Z",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x73, 0b0011_0110, 0b1111_0011, 0b1011_0000, 0b0000_0101],
            ),
            //
            // === Hour & Minute @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00-00:00",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x73, 0b0011_0110, 0b0000_1011, 0b0000_1000, 0b0000_1000],
            ),
            (
                "2024-06-15T12:30-00:00",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x73, 0b0011_0110, 0b0111_1011, 0b1100_1100, 0b0000_1011],
            ),
            (
                "2024-06-30T16:45-00:00",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x73, 0b0011_0110, 0b1111_0011, 0b1011_0000, 0b0000_1101],
            ),
            //
            // === Second @ UTC ===
            //
            (
                "2024-06-01T08:00:00Z",
                &[
                    0x74,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_0000, // ssss_Ummm
                    0b0000_0000, // ...._..ss
                ],
            ),
            (
                "2024-06-15T12:30:30Z",
                &[
                    0x74,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_0011, // ssss_Ummm
                    0b0000_0001, // ...._..ss
                ],
            ),
            (
                "2024-06-30T16:45:45Z",
                &[
                    0x74,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_0101, // ssss_Ummm
                    0b0000_0010, // ...._..ss
                ],
            ),
            //
            // === Second @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00-00:00",
                &[
                    0x74,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_1000, // ssss_Ummm
                    0b0000_0000, // ...._..ss
                ],
            ),
            (
                "2024-06-15T12:30:30-00:00",
                &[
                    0x74,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_1011, // ssss_Ummm
                    0b0000_0001, // ...._..ss
                ],
            ),
            (
                "2024-06-30T16:45:45-00:00",
                &[
                    0x74,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_1101, // ssss_Ummm
                    0b0000_0010, // ...._..ss
                ],
            ),
            //
            // === Milliseconds @ UTC ===
            //
            (
                "2024-06-01T08:00:00.000Z",
                &[
                    0x75,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_0000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.030Z",
                &[
                    0x75,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_0011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.045Z",
                &[
                    0x75,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_0101, // ssss_Ummm
                    0b1011_0110, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            //
            // === Milliseconds @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00.000-00:00",
                &[
                    0x75,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_1000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.030-00:00",
                &[
                    0x75,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_1011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.045-00:00",
                &[
                    0x75,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_1101, // ssss_Ummm
                    0b1011_0110, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            //
            // === Microseconds @ UTC ===
            //
            (
                "2024-06-01T08:00:00.000000Z",
                &[
                    0x76,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_0000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.000030Z",
                &[
                    0x76,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_0011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.000045Z",
                &[
                    0x76,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_0101, // ssss_Ummm
                    0b1011_0110, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            //
            // === Microseconds @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00.000000-00:00",
                &[
                    0x76,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_1000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.000030-00:00",
                &[
                    0x76,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_1011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.000045-00:00",
                &[
                    0x76,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_1101, // ssss_Ummm
                    0b1011_0110, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            //
            // === Nanoseconds @ UTC ===
            //
            (
                "2024-06-01T08:00:00.000000000Z",
                &[
                    0x77,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_0000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.000000030Z",
                &[
                    0x77,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_0011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.000000045Z",
                &[
                    0x77,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_0101, // ssss_Ummm
                    0b1011_0110, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                ],
            ),
            //
            // === Nanoseconds @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00.000000000-00:00",
                &[
                    0x77,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_1000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.000000030-00:00",
                &[
                    0x77,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_1011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.000000045-00:00",
                &[
                    0x77,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_1101, // ssss_Ummm
                    0b1011_0110, // ffff_ffss
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                ],
            ),
            //
            // === Hour & Minute @ Known offset ===
            //
            // Offset `-05:00` is 36 quarter-hours beyond the short form's minimum `-14:00` offset.
            (
                "2024-06-01T08:00-05:00",
                &[
                    0x78,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0010_0000, // oooo_ommm
                    0b0000_0001, // ...._..oo
                ],
            ),
            (
                "2024-06-15T12:30-05:00",
                &[
                    0x78,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b0010_0011, // oooo_ommm
                    0b0000_0001, // ...._..oo
                ],
            ),
            (
                "2024-06-30T16:45-05:00",
                &[
                    0x78,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b0010_0101, // oooo_ommm
                    0b0000_0001, // ...._..oo
                ],
            ),
            //
            // === Second @ Known offset ===
            //
            (
                "2024-06-01T08:00:00-05:00",
                &[
                    0x79,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0010_0000, // oooo_ommm
                    0b0000_0001, // ssss_ssoo
                ],
            ),
            (
                "2024-06-15T12:30:30-05:00",
                &[
                    0x79,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b0010_0011, // oooo_ommm
                    0b0111_1001, // ssss_ssoo
                ],
            ),
            (
                "2024-06-30T16:45:45-05:00",
                &[
                    0x79,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b0010_0101, // oooo_ommm
                    0b1011_0101, // ssss_ssoo
                ],
            ),
            //
            // === Milliseconds @ Known offset ===
            //
            (
                "2024-06-01T08:00:00.000-05:00",
                &[
                    0x7A,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0010_0000, // oooo_ommm
                    0b0000_0001, // ssss_ssoo
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ...._..ff
                ],
            ),
            (
                "2024-06-15T12:30:30.030-05:00",
                &[
                    0x7A,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b0010_0011, // oooo_ommm
                    0b0111_1001, // ssss_ssoo
                    0b0001_1110, // ffff_ffff
                    0b0000_0000, // ...._..ff
                ],
            ),
            (
                "2024-06-30T16:45:45.045-05:00",
                &[
                    0x7A,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b0010_0101, // oooo_ommm
                    0b1011_0101, // ssss_ssoo
                    0b0010_1101, // ffff_ffff
                    0b0000_0000, // ...._..ff
                ],
            ),
            //
            // === Microseconds @ Known offset ===
            //
            (
                "2024-06-01T08:00:00.000000-05:00",
                &[
                    0x7B,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0010_0000, // oooo_ommm
                    0b0000_0001, // ssss_ssoo
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.000030-05:00",
                &[
                    0x7B,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b0010_0011, // oooo_ommm
                    0b0111_1001, // ssss_ssoo
                    0b0001_1110, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.000045-05:00",
                &[
                    0x7B,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b0010_0101, // oooo_ommm
                    0b1011_0101, // ssss_ssoo
                    0b0010_1101, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ...._ffff
                ],
            ),
            //
            // === Nanoseconds @ Known offset ===
            //
            (
                "2024-06-01T08:00:00.000000000-05:00",
                &[
                    0x7C,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0010_0000, // oooo_ommm
                    0b0000_0001, // ssss_ssoo
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.000000030-05:00",
                &[
                    0x7C,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b0010_0011, // oooo_ommm
                    0b0111_1001, // ssss_ssoo
                    0b0001_1110, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.000000045-05:00",
                &[
                    0x7C,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b0010_0101, // oooo_ommm
                    0b1011_0101, // ssss_ssoo
                    0b0010_1101, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ffff_ffff
                    0b0000_0000, // ..ff_ffff
                ],
            ),
        ];
        // Turn the &str timestamps into instances of Timestamp
        let test_cases: Vec<(Timestamp, &[u8])> = test_cases
            .iter()
            .map(|(text, expected_encoding)| {
                (
                    Element::read_one(text)
                        .unwrap()
                        .expect_timestamp()
                        .unwrap()
                        .clone(),
                    *expected_encoding,
                )
            })
            .collect();

        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(&value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }
}
