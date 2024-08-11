use arrayvec::ArrayVec;
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use ice_code::ice as cold_path;

use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::binary::v1_1::container_writers::{
    BinaryEExpWriter_1_1, BinaryListWriter_1_1, BinarySExpWriter_1_1, BinaryStructWriter_1_1,
};
use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
use crate::lazy::encoder::binary::v1_1::flex_sym::FlexSym;
use crate::lazy::encoder::binary::v1_1::{flex_int::FlexInt, flex_uint::FlexUInt};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::ValueWriter;
use crate::lazy::encoder::value_writer::{delegate_value_writer_to_self, AnnotatableWriter};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::types::float::{FloatRepr, SmallestFloatRepr};
use crate::{Decimal, Int, IonResult, IonType, RawSymbolRef, SymbolId, Timestamp};

/// The initial size of the bump-allocated buffer created to hold a container's child elements.
// This number was chosen somewhat arbitrarily and can be updated as needed.
// TODO: Writers could track the largest container size they've seen and use that as their initial
//       size to minimize reallocations.
const DEFAULT_CONTAINER_BUFFER_SIZE: usize = 512;

pub struct BinaryValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    encoding_buffer: &'value mut BumpVec<'top, u8>,
    delimited_containers: bool,
}

impl<'value, 'top> BinaryValueWriter_1_1<'value, 'top> {
    pub fn new<'a, 'b: 'a>(
        allocator: &'b BumpAllocator,
        encoding_buffer: &'a mut BumpVec<'b, u8>,
        delimited_containers: bool,
    ) -> BinaryValueWriter_1_1<'a, 'b> {
        BinaryValueWriter_1_1 {
            allocator,
            encoding_buffer,
            delimited_containers,
        }
    }

    pub fn with_delimited_containers(mut self) -> Self {
        self.delimited_containers = true;
        self
    }

    pub fn with_length_prefixed_containers(mut self) -> Self {
        self.delimited_containers = false;
        self
    }

    #[inline]
    fn push_byte(&mut self, byte: u8) {
        self.encoding_buffer.push(byte);
    }

    #[inline]
    fn push_bytes(&mut self, bytes: &[u8]) {
        self.encoding_buffer.extend_from_slice_copy(bytes)
    }

    pub(crate) fn buffer(&self) -> &[u8] {
        self.encoding_buffer.as_slice()
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
            true => 0x6E,
            false => 0x6F,
        };
        self.push_byte(encoding);
        Ok(())
    }

    #[inline]
    pub fn write_i64(mut self, value: i64) -> IonResult<()> {
        let mut opcode = 0x60;
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

    #[inline]
    pub fn write_int(mut self, value: &Int) -> IonResult<()> {
        if let Some(small_value) = value.as_i64() {
            return self.write_i64(small_value);
        }
        cold_path! {{
            let value: i128 = value.data;
            // Because we've ruled out numbers small enough to fit in an i64, its encoded length
            // must be greater than 8. Write the opcode for an integer with a FlexUInt length.
            self.push_byte(0xF6);
            let num_sign_bits = if value < 0 {
                value.leading_ones()
            } else {
                value.leading_zeros()
            };
            let num_magnitude_bits = 128 - num_sign_bits;
            let num_encoded_bytes = (num_magnitude_bits as usize / 8) + 1;
            let le_bytes = value.to_le_bytes();
            let encoded_bytes = &le_bytes[..num_encoded_bytes];
            // Write the length as a FlexUInt.
            FlexUInt::write(self.encoding_buffer, num_encoded_bytes as u64)?;
            // Write the little endian bytes of the integer.
            self.push_bytes(encoded_bytes);
            Ok(())
        }}
    }

    pub fn write_f32(mut self, value: f32) -> IonResult<()> {
        match value.smallest_repr() {
            FloatRepr::Zero => {
                self.push_byte(0x6A);
            }
            // TODO: FloatRepr::Half => ...0x6B...
            FloatRepr::Single(f) => {
                self.push_byte(0x6C);
                self.push_bytes(&f.to_le_bytes());
            }
            FloatRepr::Double(_) => unreachable!("smallest repr for f32 cannot be f64"),
        }
        Ok(())
    }

    pub fn write_f64(mut self, value: f64) -> IonResult<()> {
        match value.smallest_repr() {
            FloatRepr::Zero => {
                self.push_byte(0x6A);
            }
            // TODO: FloatRepr::Half => ...0x6B...
            FloatRepr::Single(f) => {
                self.push_byte(0x6C);
                self.push_bytes(&f.to_le_bytes());
            }
            FloatRepr::Double(f) => {
                self.push_byte(0x6D);
                self.push_bytes(&f.to_le_bytes());
            }
        }

        Ok(())
    }

    pub fn write_decimal(mut self, value: &Decimal) -> IonResult<()> {
        // Insert a placeholder opcode; we'll overwrite the length nibble with the appropriate value when the encoding
        // is complete.
        let opcode_index = self.encoding_buffer.len();
        self.push_byte(0x70);

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
            _ => {
                // If the encoded size ends up being unusually large, we will splice in a corrected header.
                // Start by overwriting our original opcode with 0xF6, which indicates a Decimal with a FlexUInt length.
                self.encoding_buffer[opcode_index] = 0xF7;
                // We'll use an `ArrayVec` as our encoding buffer because it's stack-allocated and implements `io::Write`.
                // It has a capacity of 16 bytes because it's the smallest power of two that is still large enough to
                // hold a FlexUInt encoding of usize::MAX on a 64-bit platform.
                let mut buffer: ArrayVec<u8, 16> = ArrayVec::new();
                FlexUInt::write(&mut buffer, encoded_body_size)?;
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

        const MIN_OFFSET: i32 = -14 * 60; // Western hemisphere, -14:00
        const MAX_OFFSET: i32 = 14 * 60; // Eastern hemisphere, 14:00
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
                None => (1, 0, 0, 0), // Unknown offset uses a single bit (0); opcode and length stay the same.
                Some(0) => (1, 1, 0, 0), // UTC uses a single bit (1); opcode and length stay the same.
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
                (Year, _) => (0x80, 7, 1, 0),
                (Month, _) => (0x81, 11, 2, 0),
                (Day, _) => (0x82, 16, 2, 0),
                (HourAndMinute, _) => (0x83, 27 + num_offset_bits, 4, 0),
                // Seconds
                (Second, 0) => (0x84, 33 + num_offset_bits, 5, 0),
                // Milliseconds
                (Second, 3) => (0x85, 43 + num_offset_bits, 6, value.milliseconds()),
                // Microseconds
                (Second, 6) => (0x86, 53 + num_offset_bits, 7, value.microseconds()),
                // Nanoseconds
                (Second, 9) => (0x87, 63 + num_offset_bits, 8, value.nanoseconds()),
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
            .wrapping_sub(1);
        encoding &= mask;

        self.push_byte(opcode);

        // If the timestamp is at a known offset and uses nanosecond precision...
        if opcode == 0x8C {
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

    fn write_long_form_timestamp(mut self, value: &Timestamp) -> IonResult<()> {
        use crate::TimestampPrecision::*;

        // The number of bits dedicated to each time unit in a long-form timestamp
        const NUM_YEAR_BITS: u32 = 14;
        const NUM_MONTH_BITS: u32 = 4;
        const NUM_DAY_BITS: u32 = 5;
        const NUM_HOUR_BITS: u32 = 5;
        const NUM_MINUTE_BITS: u32 = 6;
        const NUM_SECOND_BITS: u32 = 6;
        // The number of bits dedicated to representing the offset in a long-form timestamp
        const NUM_OFFSET_BITS: u32 = 12;
        // The bit offsets of each time unit within the encoding
        const MONTH_BIT_OFFSET: u32 = NUM_YEAR_BITS;
        const DAY_BIT_OFFSET: u32 = MONTH_BIT_OFFSET + NUM_MONTH_BITS;
        const HOUR_BIT_OFFSET: u32 = DAY_BIT_OFFSET + NUM_DAY_BITS;
        const MINUTE_BIT_OFFSET: u32 = HOUR_BIT_OFFSET + NUM_HOUR_BITS;
        const OFFSET_BIT_OFFSET: u32 = MINUTE_BIT_OFFSET + NUM_MINUTE_BITS;
        const SECOND_BIT_OFFSET: u32 = OFFSET_BIT_OFFSET + NUM_OFFSET_BITS;

        let mut encoding: u64 = value.year() as u64;
        encoding |= (value.month() as u64) << MONTH_BIT_OFFSET;
        encoding |= (value.day() as u64) << DAY_BIT_OFFSET;
        encoding |= (value.hour() as u64) << HOUR_BIT_OFFSET;
        encoding |= (value.minute() as u64) << MINUTE_BIT_OFFSET;

        const MIN_OFFSET: i32 = -24 * 60;
        const UNKNOWN_OFFSET: u64 = (1 << NUM_OFFSET_BITS) - 1;

        let offset_minutes = match value.offset() {
            Some(minutes) => (minutes - MIN_OFFSET) as u64,
            None => UNKNOWN_OFFSET,
        };
        encoding |= offset_minutes << OFFSET_BIT_OFFSET;
        encoding |= (value.second() as u64) << SECOND_BIT_OFFSET;

        let precision = value.precision();
        let scale = value.fractional_seconds_scale().unwrap_or(0);

        // The encoded bytelength of all components *except* subseconds.
        let (mut encoded_length, num_bits_in_use) = match precision {
            Year => (2, 14),
            Month => (3, MONTH_BIT_OFFSET + NUM_MONTH_BITS),
            Day => {
                let bits_in_use = DAY_BIT_OFFSET + NUM_DAY_BITS;
                // Set the "day-not-month" bit, just beyond the day bits.
                encoding |= 1 << bits_in_use;
                (3, bits_in_use + 1)
            }
            // (hour, minute, offset) are an atomic unit in the encoding--when one is present they must all be present.
            HourAndMinute => (6, OFFSET_BIT_OFFSET + NUM_OFFSET_BITS),
            Second => (7, SECOND_BIT_OFFSET + SECOND_BIT_OFFSET),
        };

        // Because we eagerly (and branchless-ly) encoded all of the time units, we may have populated bits that are
        // irrelevant to the final encoding. To simplify unit testing (and in the current absence of a binary 1.1
        // reader), we calculate a mask of which bits are relevant to the current opcode and set any bits not in use
        // to `0`.
        // TODO: Remove this logic pending resolution of https://github.com/amazon-ion/ion-docs/issues/295, which
        //       suggests requiring readers to ignore bits not used by the specified opcode
        let mask = 1u64
            .checked_shl(num_bits_in_use)
            .unwrap_or(0)
            .wrapping_sub(1);
        encoding &= mask;

        // Push 0xF8 (the opcode for a Timestamp w/FlexUInt length) and 0x01 (a placeholder 0 FlexUInt that we'll
        // overwrite when the final encoding size is known.
        self.push_bytes(&[0xF8, 0x01]);
        let length_byte_index = self.encoding_buffer.len() - 1;
        self.push_bytes(&encoding.to_le_bytes()[..encoded_length]);

        let subsecond_encoding_size = match scale {
            0 => 0,
            _ => {
                // We've confirmed that there are subseconds, so we can `unwrap()` this safely.
                let subseconds = value.fractional_seconds_as_decimal().unwrap();
                let encoded_coefficient_size =
                    FlexUInt::write(self.encoding_buffer, subseconds.coefficient().magnitude())?;
                let encoded_scale_size =
                    FixedUInt::write(self.encoding_buffer, u64::try_from(scale).unwrap())?;
                encoded_coefficient_size + encoded_scale_size
            }
        };
        encoded_length += subsecond_encoding_size;

        // 127 is the largest size that can be encoded in the single FlexUInt byte that we reserved at the outset
        // of this method. This limit can be lifted if an appropriate use case arises; for the time being, 127 is
        // a very high ceiling given that a long-form timestamp with nanosecond precision is ~12 bytes.
        if encoded_length > 127 {
            return IonResult::encoding_error(
                "maximum supported long-form timestamp encoding size is 127 bytes",
            );
        }
        // Now that we know the final length, overwrite the placeholder FlexUInt from earlier.
        self.encoding_buffer[length_byte_index] = ((encoded_length as u8) << 1) + 1; // FlexUInt encoding

        Ok(())
    }

    #[inline]
    pub fn write_string<A: AsRef<str>>(mut self, value: A) -> IonResult<()> {
        const STRING_OPCODE: u8 = 0x90;
        const STRING_FLEX_UINT_LEN_OPCODE: u8 = 0xF9;
        self.write_text(STRING_OPCODE, STRING_FLEX_UINT_LEN_OPCODE, value.as_ref());
        Ok(())
    }

    #[inline]
    pub fn write_symbol<A: AsRawSymbolRef>(mut self, value: A) -> IonResult<()> {
        const SYMBOL_OPCODE: u8 = 0xA0;
        const SYMBOL_FLEX_UINT_LEN_OPCODE: u8 = 0xFA;
        match value.as_raw_symbol_token_ref() {
            RawSymbolRef::SymbolId(sid) => self.write_symbol_id(sid),
            RawSymbolRef::Text(text) => {
                self.write_text(SYMBOL_OPCODE, SYMBOL_FLEX_UINT_LEN_OPCODE, text.as_ref());
                Ok(())
            }
        }
    }

    #[inline]
    fn write_symbol_id(&mut self, symbol_id: SymbolId) -> IonResult<()> {
        let mut buffer = [0u8; 4];
        let encoded_bytes = match symbol_id {
            0..=255 => {
                buffer[0] = 0xE1; // Symbol ID value opcode; one-byte FixedUInt follows
                buffer[1] = symbol_id as u8;
                &buffer[0..2]
            }
            // The u16::MAX range, but biased by 256.
            256..=65_791 => {
                let le_bytes = ((symbol_id - 256) as u16).to_le_bytes();
                buffer[0] = 0xE2; // Symbol ID value opcode; two-byte FixedUInt follows
                buffer[1] = le_bytes[0];
                buffer[2] = le_bytes[1];
                &buffer[0..3]
            }
            // 65,792 and higher
            _ => {
                cold_path! {
                    xl_symbol_id_value => {{
                        self.push_byte(0xE3); // Biased FlexUInt follows
                        let _ = FlexUInt::write(self.encoding_buffer, symbol_id - 65_792).unwrap();
                    }}
                };
                return Ok(());
            }
        };
        self.push_bytes(encoded_bytes);
        Ok(())
    }

    /// Helper method for writing strings and symbols with inline UTF8 bytes.
    #[inline]
    fn write_text(&mut self, opcode: u8, var_len_opcode: u8, text: &str) {
        if text.len() < 16 {
            self.encoding_buffer
                .extend_from_slice_copy(&[opcode | text.len() as u8]);
        } else {
            FlexUInt::encode_opcode_and_length(
                self.encoding_buffer,
                var_len_opcode,
                text.len() as u64,
            );
        }
        self.push_bytes(text.as_bytes());
    }

    pub fn write_clob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()> {
        self.write_lob(0xFF, value)
    }

    pub fn write_blob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()> {
        self.write_lob(0xFE, value)
    }

    fn write_lob<A: AsRef<[u8]>>(mut self, opcode: u8, value: A) -> IonResult<()> {
        let bytes = value.as_ref();
        self.push_byte(opcode);
        FlexUInt::write(self.encoding_buffer, bytes.len())?;
        self.push_bytes(bytes);
        Ok(())
    }

    fn list_writer(self) -> IonResult<<Self as ValueWriter>::ListWriter> {
        let writer = if self.delimited_containers {
            BinaryListWriter_1_1::new_delimited(self.allocator, self.encoding_buffer)
        } else {
            BinaryListWriter_1_1::new_length_prefixed(self.allocator, self.encoding_buffer)
        };
        Ok(writer)
    }

    fn sexp_writer(self) -> IonResult<<Self as ValueWriter>::SExpWriter> {
        let writer = if self.delimited_containers {
            BinarySExpWriter_1_1::new_delimited(self.allocator, self.encoding_buffer)
        } else {
            BinarySExpWriter_1_1::new_length_prefixed(self.allocator, self.encoding_buffer)
        };
        Ok(writer)
    }

    fn struct_writer(self) -> IonResult<<Self as ValueWriter>::StructWriter> {
        let writer = if self.delimited_containers {
            BinaryStructWriter_1_1::new_delimited(self.allocator, self.encoding_buffer)
        } else {
            BinaryStructWriter_1_1::new_length_prefixed(self.allocator, self.encoding_buffer)
        };
        Ok(writer)
    }

    fn eexp_writer<'a>(
        self,
        macro_id: impl Into<MacroIdRef<'a>>,
    ) -> IonResult<<Self as ValueWriter>::EExpWriter> {
        match macro_id.into() {
            MacroIdRef::LocalName(_name) => {
                // This would be handled by the system writer
                todo!("macro invocation by name");
            }
            MacroIdRef::LocalAddress(address) if address < 64 => {
                // Invoke this ID with a one-byte opcode
                self.encoding_buffer.push(address as u8);
            }
            MacroIdRef::LocalAddress(_address) => {
                todo!("macros with addresses higher than 64");
            }
        };
        Ok(BinaryEExpWriter_1_1::new(
            self.allocator,
            self.encoding_buffer,
            self.delimited_containers,
        ))
    }
}

impl<'value, 'top> Sealed for BinaryValueWriter_1_1<'value, 'top> {}

impl<'value, 'top> AnnotatableWriter for BinaryValueWriter_1_1<'value, 'top> {
    type AnnotatedValueWriter<'a> = BinaryAnnotatedValueWriter_1_1<'a, 'top> where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(BinaryAnnotatedValueWriter_1_1::new(
            self.allocator,
            self.encoding_buffer,
            annotations.into_annotations_vec(),
        ))
    }
}

impl<'value, 'top> ValueWriter for BinaryValueWriter_1_1<'value, 'top> {
    type ListWriter = BinaryListWriter_1_1<'value, 'top>;
    type SExpWriter = BinarySExpWriter_1_1<'value, 'top>;
    type StructWriter = BinaryStructWriter_1_1<'value, 'top>;

    type EExpWriter = BinaryEExpWriter_1_1<'value, 'top>;

    delegate_value_writer_to_self!();
}

/// Takes a series of `TYPE => METHOD` pairs, generating a function for each that encodes an
/// annotations sequence and then delegates encoding the value to the corresponding value writer
/// method.
macro_rules! annotate_and_delegate_1_1 {
    // End of iteration
    () => {};
    // Recurses one argument pair at a time
    ($value_type:ty => $method:ident, $($rest:tt)*) => {
        fn $method(mut self, value: $value_type) -> IonResult<()> {
            self.encode_annotations();
            // We've encoded the annotations, now create a no-annotations ValueWriter to encode the value itself.
            let value_writer = $crate::lazy::encoder::binary::v1_1::value_writer::BinaryValueWriter_1_1::new(self.allocator, self.buffer, self.delimited_containers);
            value_writer.$method(value)?;
            Ok(())
        }
        annotate_and_delegate_1_1!($($rest)*);
    };
}

pub struct BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    annotations: AnnotationsVec<'value>,
    allocator: &'top BumpAllocator,
    buffer: &'value mut BumpVec<'top, u8>,
    delimited_containers: bool,
}

impl<'value, 'top> BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    fn encode_annotations(&mut self) {
        match self.annotations.as_slice() {
            [] => {
                // There are no annotations; nothing to do.
            }
            [a] => {
                // Opcode 0xE7: A single FlexSym annotation follows
                self.buffer.push(0xE7);
                FlexSym::encode_symbol(self.buffer, a);
            }
            [a1, a2] => {
                // Opcode 0xE8: Two FlexSym annotations follow
                self.buffer.push(0xE8);
                FlexSym::encode_symbol(self.buffer, a1);
                FlexSym::encode_symbol(self.buffer, a2);
            }
            _ => {
                self.write_length_prefixed_flex_sym_annotation_sequence();
            }
        }
    }

    fn write_flex_sym_annotation(buffer: &mut BumpVec<'top, u8>, annotation: impl AsRawSymbolRef) {
        FlexSym::encode_symbol(buffer, annotation);
    }

    #[cold]
    fn write_length_prefixed_flex_sym_annotation_sequence(&mut self) {
        // A FlexUInt follows with the byte length of the FlexSym sequence that follows
        let mut annotations_buffer = BumpVec::new_in(self.allocator);
        for annotation in &self.annotations {
            FlexSym::encode_symbol(&mut annotations_buffer, annotation);
        }
        // A FlexUInt follows that represents the length of a sequence of FlexSym-encoded annotations
        self.buffer.push(0xE9);
        FlexUInt::write(self.buffer, annotations_buffer.len()).unwrap();
        self.buffer
            .extend_from_slice_copy(annotations_buffer.as_slice());
    }

    fn local_buffer(&mut self) -> &mut BumpVec<'top, u8> {
        &mut *self.buffer
    }
}

impl<'value, 'top> Sealed for BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    // No methods, precludes implementations outside the crate.
}

impl<'value, 'top> AnnotatableWriter for BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    type AnnotatedValueWriter<'a> = BinaryAnnotatedValueWriter_1_1<'a, 'top> where Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(BinaryAnnotatedValueWriter_1_1::new(
            self.allocator,
            self.buffer,
            annotations.into_annotations_vec(),
        ))
    }
}

impl<'value, 'top> ValueWriter for BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    type ListWriter = BinaryListWriter_1_1<'value, 'top>;
    type SExpWriter = BinarySExpWriter_1_1<'value, 'top>;
    type StructWriter = BinaryStructWriter_1_1<'value, 'top>;
    type EExpWriter = BinaryEExpWriter_1_1<'value, 'top>;

    annotate_and_delegate_1_1!(
        IonType => write_null,
        bool => write_bool,
        i64 => write_i64,
        &Int => write_int,
        f32 => write_f32,
        f64 => write_f64,
        &Decimal => write_decimal,
        &Timestamp => write_timestamp,
        impl AsRef<str> => write_string,
        impl AsRawSymbolRef => write_symbol,
        impl AsRef<[u8]> => write_clob,
        impl AsRef<[u8]> => write_blob,
    );

    fn list_writer(mut self) -> IonResult<Self::ListWriter> {
        self.encode_annotations();
        self.value_writer().list_writer()
    }

    fn sexp_writer(mut self) -> IonResult<Self::SExpWriter> {
        self.encode_annotations();
        self.value_writer().sexp_writer()
    }

    fn struct_writer(mut self) -> IonResult<Self::StructWriter> {
        self.encode_annotations();
        self.value_writer().struct_writer()
    }

    fn eexp_writer<'a>(self, macro_id: impl Into<MacroIdRef<'a>>) -> IonResult<Self::EExpWriter> {
        if !self.annotations.is_empty() {
            return IonResult::encoding_error("e-expressions cannot have annotations");
        }
        self.value_writer().eexp_writer(macro_id)
    }
}

impl<'value, 'top> BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        buffer: &'value mut BumpVec<'top, u8>,
        annotations: AnnotationsVec<'value>,
    ) -> Self {
        Self {
            allocator,
            buffer,
            annotations,
            delimited_containers: false,
        }
    }
    pub(crate) fn value_writer(self) -> BinaryValueWriter_1_1<'value, 'top> {
        let mut writer =
            BinaryValueWriter_1_1::new(self.allocator, self.buffer, self.delimited_containers);
        writer.delimited_containers = self.delimited_containers;
        writer
    }

    pub(crate) fn buffer(&self) -> &[u8] {
        self.buffer.as_slice()
    }
}

#[cfg(test)]
mod tests {
    use num_traits::FloatConst;
    use rstest::rstest;

    use crate::ion_data::IonEq;
    use crate::lazy::encoder::annotate::{Annotatable, Annotated};
    use crate::lazy::encoder::annotation_seq::AnnotationSeq;
    use crate::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
    use crate::lazy::encoder::value_writer::ValueWriter;
    use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
    use crate::lazy::encoder::write_as_ion::{WriteAsIon, WriteAsSExp};
    use crate::raw_symbol_ref::AsRawSymbolRef;
    use crate::types::float::{FloatRepr, SmallestFloatRepr};
    use crate::{
        v1_1, Decimal, Element, Int, IonResult, IonType, Null, RawSymbolRef, SymbolId, Timestamp,
        Writer,
    };

    fn encoding_test(
        test: impl FnOnce(&mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>) -> IonResult<()>,
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
        let test_cases: &[(bool, &[u8])] = &[(true, &[0x6E]), (false, &[0x6F])];
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
            (0, &[0x60]),
            (-1, &[0x61, 0xFF]),
            (1, &[0x61, 0x01]),
            (100, &[0x61, 0x64]),
            (-100, &[0x61, 0x9C]),
            (127, &[0x61, 0x7F]),
            (-127, &[0x61, 0x81]),
            (128, &[0x62, 0x80, 0x00]),
            (-128, &[0x61, 0x80]),
            (
                i64::MAX,
                &[0x68, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
            ),
            (
                i64::MIN,
                &[0x68, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80],
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
            let mut expected_encoding = vec![0x6C];
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
            f64::PI(),
            f64::E(),
            f64::EPSILON,
        ];
        for value in test_f64s {
            let mut expected_encoding = vec![];
            match value.smallest_repr() {
                FloatRepr::Zero => {
                    expected_encoding.push(0x6A);
                }
                FloatRepr::Single(f) => {
                    expected_encoding.push(0x6C);
                    expected_encoding.extend_from_slice(&f.to_le_bytes()[..]);
                }
                FloatRepr::Double(f) => {
                    expected_encoding.push(0x6D);
                    expected_encoding.extend_from_slice(&f.to_le_bytes()[..]);
                }
            }
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
            ("", &[0x90]),
            //                 f     o     o
            ("foo", &[0x93, 0x66, 0x6F, 0x6F]),
            (
                "foo bar baz quux quuz",
                &[
                    0xF9, // Opcode: string with variable-width length
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
            ("", &[0xA0]),
            //                 f     o     o
            ("foo", &[0xA3, 0x66, 0x6F, 0x6F]),
            (
                "foo bar baz quux quuz",
                &[
                    0xFA, // Opcode: symbol with variable-width length
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
            (Decimal::new(0, 0), &[0x70]),
            (Decimal::new(0, 3), &[0x71, 0x07]),
            (Decimal::negative_zero(), &[0x72, 0x01, 0x00]),
            (Decimal::negative_zero_with_exponent(3), &[0x72, 0x07, 0x00]),
            (
                Decimal::negative_zero_with_exponent(-3),
                &[0x72, 0xFB, 0x00],
            ),
            (Decimal::new(7, 4), &[0x72, 0x09, 0x07]),
            (
                // ~Pi
                Decimal::new(3_1415926535i64, -10),
                &[0x76, 0xED, 0x07, 0xFF, 0x88, 0x50, 0x07],
            ),
            (
                // ~e
                Decimal::new(Int::from(27182818284590452353602874713526624i128), -40),
                &[
                    0xF7, 0x21, 0xB1, 0x60, 0x51, 0x2B, 0xF8, 0xFE, 0x2B, 0xA4, 0x11, 0xAF, 0x90,
                    0xF7, 0x66, 0x37, 0x3C, 0x05,
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
            ("1970T", &[0x80, 0b0000_0000]),
            ("2097T", &[0x80, 0b0111_1111]),
            ("2024T", &[0x80, 0b0011_0110]),
            //
            // === Month ===
            //                     MYYY_YYYY    ...._.MMM
            ("2024-01T", &[0x81, 0b1011_0110, 0b0000_0000]),
            ("2024-10T", &[0x81, 0b0011_0110, 0b0000_0101]),
            ("2024-11T", &[0x81, 0b1011_0110, 0b0000_0101]),
            ("2024-12T", &[0x81, 0b0011_0110, 0b0000_0110]),
            //
            // === Day ===
            //                       MYYY_YYYY    DDDD_DMMM
            ("2024-06-01", &[0x82, 0b0011_0110, 0b0000_1011]),
            ("2024-06-15", &[0x82, 0b0011_0110, 0b0111_1011]),
            ("2024-06-30", &[0x82, 0b0011_0110, 0b1111_0011]),
            //
            // === Hour & Minute @ UTC ===
            //
            (
                "2024-06-01T08:00Z",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x83, 0b0011_0110, 0b0000_1011, 0b0000_1000, 0b0000_1000],
            ),
            (
                "2024-06-15T12:30Z",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x83, 0b0011_0110, 0b0111_1011, 0b1100_1100, 0b0000_1011],
            ),
            (
                "2024-06-30T16:45Z",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x83, 0b0011_0110, 0b1111_0011, 0b1011_0000, 0b0000_1101],
            ),
            //
            // === Hour & Minute @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00-00:00",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x83, 0b0011_0110, 0b0000_1011, 0b0000_1000, 0b0000_0000],
            ),
            (
                "2024-06-15T12:30-00:00",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x83, 0b0011_0110, 0b0111_1011, 0b1100_1100, 0b0000_0011],
            ),
            (
                "2024-06-30T16:45-00:00",
                //        MYYY_YYYY    DDDD_DMMM    mmmH_HHHH    ...._Ummm
                &[0x83, 0b0011_0110, 0b1111_0011, 0b1011_0000, 0b0000_0101],
            ),
            //
            // === Second @ UTC ===
            //
            (
                "2024-06-01T08:00:00Z",
                &[
                    0x84,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_1000, // ssss_Ummm
                    0b0000_0000, // ...._..ss
                ],
            ),
            (
                "2024-06-15T12:30:30Z",
                &[
                    0x84,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_1011, // ssss_Ummm
                    0b0000_0001, // ...._..ss
                ],
            ),
            (
                "2024-06-30T16:45:45Z",
                &[
                    0x84,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_1101, // ssss_Ummm
                    0b0000_0010, // ...._..ss
                ],
            ),
            //
            // === Second @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00-00:00",
                &[
                    0x84,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_0000, // ssss_Ummm
                    0b0000_0000, // ...._..ss
                ],
            ),
            (
                "2024-06-15T12:30:30-00:00",
                &[
                    0x84,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_0011, // ssss_Ummm
                    0b0000_0001, // ...._..ss
                ],
            ),
            (
                "2024-06-30T16:45:45-00:00",
                &[
                    0x84,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_0101, // ssss_Ummm
                    0b0000_0010, // ...._..ss
                ],
            ),
            //
            // === Milliseconds @ UTC ===
            //
            (
                "2024-06-01T08:00:00.000Z",
                &[
                    0x85,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_1000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.030Z",
                &[
                    0x85,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_1011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.045Z",
                &[
                    0x85,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_1101, // ssss_Ummm
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
                    0x85,
                    0b0011_0110, // MYYY_YYYY
                    0b0000_1011, // DDDD_DMMM
                    0b0000_1000, // mmmH_HHHH
                    0b0000_0000, // ssss_Ummm
                    0b0000_0000, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-15T12:30:30.030-00:00",
                &[
                    0x85,
                    0b0011_0110, // MYYY_YYYY
                    0b0111_1011, // DDDD_DMMM
                    0b1100_1100, // mmmH_HHHH
                    0b1110_0011, // ssss_Ummm
                    0b0111_1001, // ffff_ffss
                    0b0000_0000, // ...._ffff
                ],
            ),
            (
                "2024-06-30T16:45:45.045-00:00",
                &[
                    0x85,
                    0b0011_0110, // MYYY_YYYY
                    0b1111_0011, // DDDD_DMMM
                    0b1011_0000, // mmmH_HHHH
                    0b1101_0101, // ssss_Ummm
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
                    0x86,
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
                "2024-06-15T12:30:30.000030Z",
                &[
                    0x86,
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
                "2024-06-30T16:45:45.000045Z",
                &[
                    0x86,
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
            // === Microseconds @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00.000000-00:00",
                &[
                    0x86,
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
                "2024-06-15T12:30:30.000030-00:00",
                &[
                    0x86,
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
                "2024-06-30T16:45:45.000045-00:00",
                &[
                    0x86,
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
            // === Nanoseconds @ UTC ===
            //
            (
                "2024-06-01T08:00:00.000000000Z",
                &[
                    0x87,
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
                "2024-06-15T12:30:30.000000030Z",
                &[
                    0x87,
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
                "2024-06-30T16:45:45.000000045Z",
                &[
                    0x87,
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
            // === Nanoseconds @ Unknown Offset ===
            //
            (
                "2024-06-01T08:00:00.000000000-00:00",
                &[
                    0x87,
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
                "2024-06-15T12:30:30.000000030-00:00",
                &[
                    0x87,
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
                "2024-06-30T16:45:45.000000045-00:00",
                &[
                    0x87,
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
            // === Hour & Minute @ Known offset ===
            //
            // Offset `-05:00` is 36 quarter-hours beyond the short form's minimum `-14:00` offset.
            (
                "2024-06-01T08:00-05:00",
                &[
                    0x88,
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
                    0x88,
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
                    0x88,
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
                    0x89,
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
                    0x89,
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
                    0x89,
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
                    0x8A,
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
                    0x8A,
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
                    0x8A,
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
                    0x8B,
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
                    0x8B,
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
                    0x8B,
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
                    0x8C,
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
                    0x8C,
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
                    0x8C,
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
            //
            // === Long-form year ===
            //
            (
                "1969T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x05,        // FlexUInt length 2
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // ..YY_YYYY
                ],
            ),
            (
                "0001T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x05,        // FlexUInt length 2
                    0b0000_0001, // YYYY_YYYY
                    0b0000_0000, // ..YY_YYYY
                ],
            ),
            (
                "9999T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x05,        // FlexUInt length 2
                    0b0000_1111, // YYYY_YYYY
                    0b0010_0111, // ..YY_YYYY
                ],
            ),
            //
            // === Long-form month ===
            //
            (
                "1969-01T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x07,        // FlexUInt length 3
                    0b1011_0001, // YYYY_YYYY
                    0b0100_0111, // MMYY_YYYY
                    0b0000_0000, // h..._..MM
                ],
            ),
            (
                "1969-06T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x07,        // FlexUInt length 3
                    0b1011_0001, // YYYY_YYYY
                    0b1000_0111, // MMYY_YYYY
                    0b0000_0001, // h..._..MM
                ],
            ),
            (
                "1969-12T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x07,        // FlexUInt length 3
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0000_0011, // h..._..MM
                ],
            ),
            //
            // === Long-form day ===
            //
            (
                "1969-01-01T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x07,        // FlexUInt length 3
                    0b1011_0001, // YYYY_YYYY
                    0b0100_0111, // MMYY_YYYY
                    0b1000_0100, // hDDD_DDMM
                ],
            ),
            (
                "1969-06-15T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x07,        // FlexUInt length 3
                    0b1011_0001, // YYYY_YYYY
                    0b1000_0111, // MMYY_YYYY
                    0b1011_1101, // hDDD_DDMM
                ],
            ),
            (
                "1969-12-31T",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x07,        // FlexUInt length 3
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b1111_1111, // hDD_DDMM
                ],
            ),
            //
            // === Long-form hour & minute ===
            //
            (
                "1969-01-01T00:00Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0D,        // FlexUInt length 6
                    0b1011_0001, // YYYY_YYYY
                    0b0100_0111, // MMYY_YYYY
                    0b0000_0100, // hDDD_DDMM
                    0b0000_0000, // mmmm_HHHH
                    0b1000_0000, // oooo_oomm
                    0b0001_0110, // ..oo_oooo
                ],
            ),
            (
                "1969-06-15T12:30Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0D,        // FlexUInt length 6
                    0b1011_0001, // YYYY_YYYY
                    0b1000_0111, // MMYY_YYYY
                    0b0011_1101, // hDDD_DDMM
                    0b1110_0110, // mmmm_HHHH
                    0b1000_0001, // oooo_oomm
                    0b0001_0110, // ..oo_oooo
                ],
            ),
            (
                "1969-12-31T18:45Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0D,        // FlexUInt length 6
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0111_1111, // hDDD_DDMM
                    0b1101_1001, // mmmm_HHHH
                    0b1000_0010, // oooo_oomm
                    0b0001_0110, // ..oo_oooo
                ],
            ),
            (
                "1969-12-31T18:45-00:00", // Unknown offset
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0D,        // FlexUInt length 6
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0111_1111, // hDDD_DDMM
                    0b1101_1001, // mmmm_HHHH
                    0b1111_1110, // oooo_oomm
                    0b0011_1111, // ..oo_oooo
                ],
            ),
            //
            // === Long-form seconds ===
            //
            (
                "1969-01-01T00:00:00Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0F,        // FlexUInt length 7
                    0b1011_0001, // YYYY_YYYY
                    0b0100_0111, // MMYY_YYYY
                    0b0000_0100, // hDDD_DDMM
                    0b0000_0000, // mmmm_HHHH
                    0b1000_0000, // oooo_oomm
                    0b0001_0110, // ssoo_oooo
                    0b0000_0000, // ...._ssss
                ],
            ),
            (
                "1969-06-15T12:30:30Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0F,        // FlexUInt length 7
                    0b1011_0001, // YYYY_YYYY
                    0b1000_0111, // MMYY_YYYY
                    0b0011_1101, // hDDD_DDMM
                    0b1110_0110, // mmmm_HHHH
                    0b1000_0001, // oooo_oomm
                    0b1001_0110, // ssoo_oooo
                    0b0000_0111, // ...._ssss
                ],
            ),
            (
                "1969-12-31T18:45:45Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0F,        // FlexUInt length 7
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0111_1111, // hDDD_DDMM
                    0b1101_1001, // mmmm_HHHH
                    0b1000_0010, // oooo_oomm
                    0b0101_0110, // ssoo_oooo
                    0b0000_1011, // ...._ssss
                ],
            ),
            (
                "1969-12-31T18:45:45-00:00", // Unknown offset
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x0F,        // FlexUInt length 7
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0111_1111, // hDDD_DDMM
                    0b1101_1001, // mmmm_HHHH
                    0b1111_1110, // oooo_oomm
                    0b0111_1111, // ssoo_oooo
                    0b0000_1011, // ...._ssss
                ],
            ),
            //
            // === Long-form subseconds ===
            //
            (
                "1969-01-01T00:00:00.000Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x13,        // FlexUInt length 9
                    0b1011_0001, // YYYY_YYYY
                    0b0100_0111, // MMYY_YYYY
                    0b0000_0100, // hDDD_DDMM
                    0b0000_0000, // mmmm_HHHH
                    0b1000_0000, // oooo_oomm
                    0b0001_0110, // ssoo_oooo
                    0b0000_0000, // ...._ssss
                    0b0000_0001, // FlexUInt: 0 subseconds
                    0b0000_0011, // FixedUInt: scale of 3 (exp: -3)
                ],
            ),
            (
                "1969-06-15T12:30:30.000030Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x13,        // FlexUInt length 9
                    0b1011_0001, // YYYY_YYYY
                    0b1000_0111, // MMYY_YYYY
                    0b0011_1101, // hDDD_DDMM
                    0b1110_0110, // mmmm_HHHH
                    0b1000_0001, // oooo_oomm
                    0b1001_0110, // ssoo_oooo
                    0b0000_0111, // ...._ssss
                    0b0011_1101, // FlexUInt: 30 subseconds
                    0b0000_0110, // FixedUInt: scale of 6 (exp: -6)
                ],
            ),
            (
                "1969-12-31T18:45:45.000000045Z",
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x13,        // FlexUInt length 7
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0111_1111, // hDDD_DDMM
                    0b1101_1001, // mmmm_HHHH
                    0b1000_0010, // oooo_oomm
                    0b0101_0110, // ssoo_oooo
                    0b0000_1011, // ...._ssss
                    0b0101_1011, // FlexUInt: 45 subseconds
                    0b0000_1001, // FixedUInt: scale of 9 (exp: -9)
                ],
            ),
            (
                "1969-12-31T18:45:45.000000045-00:00", // Unknown offset
                &[
                    0xF8,        // Timestamp w/FlexUInt length
                    0x13,        // FlexUInt length 7
                    0b1011_0001, // YYYY_YYYY
                    0b0000_0111, // MMYY_YYYY
                    0b0111_1111, // hDDD_DDMM
                    0b1101_1001, // mmmm_HHHH
                    0b1111_1110, // oooo_oomm
                    0b0111_1111, // ssoo_oooo
                    0b0000_1011, // ...._ssss
                    0b0101_1011, // FlexUInt: 45 subseconds
                    0b0000_1001, // FixedUInt: scale of 9 (exp: -9)
                ],
            ),
        ];
        // Turn the &str timestamps into instances of Timestamp
        let test_cases: Vec<(Timestamp, &[u8])> = test_cases
            .iter()
            .map(|(text, expected_encoding)| {
                (
                    Element::read_one(text).unwrap().expect_timestamp().unwrap(),
                    *expected_encoding,
                )
            })
            .collect();

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
    fn write_blobs() -> IonResult<()> {
        let test_cases: &[(&[u8], &[u8])] = &[
            (
                b"",
                &[
                    0xFE, // Blob
                    0x01, // FlexUInt 0
                ],
            ),
            (
                b"foo",
                &[
                    0xFE, // Blob
                    0x07, // FlexUInt 3
                    // f     o     o
                    0x66, 0x6F, 0x6F,
                ],
            ),
            (
                b"foo bar",
                &[
                    0xFE, // Blob
                    0x0F, // FlexUInt 7
                    // f     o     o           b     a     r
                    0x66, 0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72,
                ],
            ),
            (
                b"foo bar baz",
                &[
                    0xFE, // Blob
                    0x17, // FlexUInt 11
                    // f     o     o           b     a     r           b     a     z
                    0x66, 0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72, 0x20, 0x62, 0x61, 0x7a,
                ],
            ),
            (
                b"foo bar baz quux quuz",
                &[
                    0xFE, // Blob
                    0x2B, // FlexUInt
                    // f     o     o           b     a     r           b     a     z           q
                    0x66, 0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72, 0x20, 0x62, 0x61, 0x7a, 0x20, 0x71,
                    // u     u     x           q     u     u     z
                    0x75, 0x75, 0x78, 0x20, 0x71, 0x75, 0x75, 0x7a,
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
    fn write_clobs() -> IonResult<()> {
        let test_cases: &[(&[u8], &[u8])] = &[
            (
                b"",
                &[
                    0xFF, // Clob
                    0x01, // FlexUInt 0
                ],
            ),
            (
                b"foo",
                &[
                    0xFF, // Clob
                    0x07, // FlexUInt 3
                    // f     o     o
                    0x66, 0x6F, 0x6F,
                ],
            ),
            (
                b"foo bar",
                &[
                    0xFF, // Clob
                    0x0F, // FlexUInt 7
                    // f     o     o           b     a     r
                    0x66, 0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72,
                ],
            ),
            (
                b"foo bar baz",
                &[
                    0xFF, // Clob
                    0x17, // FlexUInt 11
                    // f     o     o           b     a     r           b     a     z
                    0x66, 0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72, 0x20, 0x62, 0x61, 0x7a,
                ],
            ),
            (
                b"foo bar baz quux quuz",
                &[
                    0xFF, // Clob
                    0x2B, // FlexUInt
                    // f     o     o           b     a     r           b     a     z           q
                    0x66, 0x6F, 0x6F, 0x20, 0x62, 0x61, 0x72, 0x20, 0x62, 0x61, 0x7a, 0x20, 0x71,
                    // u     u     x           q     u     u     z
                    0x75, 0x75, 0x78, 0x20, 0x71, 0x75, 0x75, 0x7a,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.value_writer().write_clob(value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_length_prefixed_lists() -> IonResult<()> {
        let test_cases: &[(&[&str], &[u8])] = &[
            (&[], &[0xB0]),
            (
                &["foo"],
                &[
                    //             f     o     o
                    0xB4, 0x93, 0x66, 0x6F, 0x6F,
                ],
            ),
            (
                &["foo", "bar"],
                &[
                    //             f     o     o           b     a     r
                    0xB8, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72,
                ],
            ),
            (
                &["foo", "bar", "baz"],
                &[
                    //             f     o     o           b     a     r           b     a     z
                    0xBC, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61, 0x7a,
                ],
            ),
            (
                &["foo", "bar", "baz", "quux", "quuz"],
                &[
                    //                   f     o     o           b     a     r           b     a
                    0xFB, 0x2D, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61,
                    // r           q     u     u     x           q     u     u     z
                    0x7a, 0x94, 0x71, 0x75, 0x75, 0x78, 0x94, 0x71, 0x75, 0x75, 0x7a,
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
    fn write_delimited_lists() -> IonResult<()> {
        let test_cases: &[(&[&str], &[u8])] = &[
            (&[], &[0xF1, 0xF0]),
            (
                &["foo"],
                &[
                    //             f     o     o
                    0xF1, 0x93, 0x66, 0x6F, 0x6F, 0xF0,
                ],
            ),
            (
                &["foo", "bar"],
                &[
                    //             f     o     o           b     a     r
                    0xF1, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0xF0,
                ],
            ),
            (
                &["foo", "bar", "baz"],
                &[
                    //             f     o     o           b     a     r           b     a     z
                    0xF1, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61, 0x7a,
                    0xF0,
                ],
            ),
            (
                &["foo", "bar", "baz", "quux", "quuz"],
                &[
                    //             f     o     o           b     a     r           b     a
                    0xF1, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61,
                    // r           q     u     u     x           q     u     u     z
                    0x7a, 0x94, 0x71, 0x75, 0x75, 0x78, 0x94, 0x71, 0x75, 0x75, 0x7a, 0xF0,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    let mut list = writer
                        .value_writer()
                        .with_delimited_containers()
                        .list_writer()?;
                    list.write_all(*value)?;
                    list.close()
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_length_prefixed_sexps() -> IonResult<()> {
        let test_cases: &[(&[&str], &[u8])] = &[
            (&[], &[0xC0]),
            (
                &["foo"],
                &[
                    //             f     o     o
                    0xC4, 0x93, 0x66, 0x6F, 0x6F,
                ],
            ),
            (
                &["foo", "bar"],
                &[
                    //             f     o     o           b     a     r
                    0xC8, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72,
                ],
            ),
            (
                &["foo", "bar", "baz"],
                &[
                    //             f     o     o           b     a     r           b     a     z
                    0xCC, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61, 0x7a,
                ],
            ),
            (
                &["foo", "bar", "baz", "quux", "quuz"],
                &[
                    //                   f     o     o           b     a     r           b     a
                    0xFC, 0x2D, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61,
                    // r           q     u     u     x           q     u     u     z
                    0x7a, 0x94, 0x71, 0x75, 0x75, 0x78, 0x94, 0x71, 0x75, 0x75, 0x7a,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value.as_sexp())?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_delimited_sexps() -> IonResult<()> {
        let test_cases: &[(&[&str], &[u8])] = &[
            (&[], &[0xF2, 0xF0]),
            (
                &["foo"],
                &[
                    //             f     o     o
                    0xF2, 0x93, 0x66, 0x6F, 0x6F, 0xF0,
                ],
            ),
            (
                &["foo", "bar"],
                &[
                    //             f     o     o           b     a     r
                    0xF2, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0xF0,
                ],
            ),
            (
                &["foo", "bar", "baz"],
                &[
                    //             f     o     o           b     a     r           b     a     z
                    0xF2, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61, 0x7a,
                    0xF0,
                ],
            ),
            (
                &["foo", "bar", "baz", "quux", "quuz"],
                &[
                    //             f     o     o           b     a     r           b     a
                    0xF2, 0x93, 0x66, 0x6F, 0x6F, 0x93, 0x62, 0x61, 0x72, 0x93, 0x62, 0x61,
                    // r           q     u     u     x           q     u     u     z
                    0x7a, 0x94, 0x71, 0x75, 0x75, 0x78, 0x94, 0x71, 0x75, 0x75, 0x7a, 0xF0,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    let mut sexp = writer
                        .value_writer()
                        .with_delimited_containers()
                        .sexp_writer()?;
                    sexp.write_all(*value)?;
                    sexp.close()
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    /// A list of field name/value pairs that will be serialized as a struct in each test.
    type TestStruct<'a> = &'a [(RawSymbolRef<'a>, Element)];
    impl<'a> WriteAsIon for TestStruct<'a> {
        fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
            let mut struct_writer = writer.struct_writer()?;
            for (name, value) in self.iter() {
                struct_writer.write(name, value)?;
            }
            struct_writer.close()
        }
    }

    /// Constructs a field name/value pair out of a symbol token and a value written as Ion text.
    fn field<'a>(name: impl Into<RawSymbolRef<'a>>, value: &'a str) -> (RawSymbolRef<'a>, Element) {
        (
            name.into(),
            Element::read_one(value).expect("failed to read field value"),
        )
    }

    #[test]
    fn write_length_prefixed_structs() -> IonResult<()> {
        #[rustfmt::skip]
        let test_cases: &[(TestStruct, &[u8])] = &[
            // Empty struct
            (&[], &[0xD0]),
            // Struct with a single FlexUInt field name
            (
                &[field(4, "foo")],
                &[
                    // 5-byte struct
                    0xD5,
                    // FlexUInt symbol ID 4
                    0x09,
                    // 3-byte symbol
                    // ↓     f     o     o
                    0xA3, 0x66, 0x6F, 0x6F,
                ],
            ),
            // Struct with multiple FlexUInt field names
            (
                &[field(4, "foo"), field(5, "bar"), field(6, "baz")],
                &[
                    // 15-byte struct
                    0xDF,
                    // FlexUInt symbol ID 4
                    0x09,
                    // 3-byte symbol
                    // ↓     f     o     o
                    0xA3, 0x66, 0x6F, 0x6F,
                    // FlexUInt symbol ID 5
                    0x0B,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // --------------------
                    // FlexUInt symbol ID 6
                    0x0D,
                    // 3-byte symbol
                    // ↓     b     a     z
                    0xA3, 0x62, 0x61, 0x7A,
                ],
            ),
            // Struct with single FlexSym field name
            (
                &[field("foo", "bar")],
                &[
                    // 9-byte struct
                    0xD9,
                    // Enable FlexSym field name encoding
                    0x01,
                    // Inline 3-byte field name
                    // ↓     f     o     o
                    0xFB, 0x66, 0x6F, 0x6F,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                ],
            ),
            // Struct with multiple FlexSym field names
            (
                &[field("foo", "bar"), field("baz", "quux")],
                &[
                    // Struct with FlexUInt length
                    0xFD,
                    // FlexUInt 18
                    0x25,
                    // Enable FlexSym field name encoding
                    0x01,
                    // Inline 3-byte field name
                    // ↓     f     o     o
                    0xFB, 0x66, 0x6F, 0x6F,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // Inline 3-byte field name
                    // ↓     b     a     z
                    0xFB, 0x62, 0x61, 0x7A,
                    // 4-byte symbol
                    // ↓     q     u     u     x
                    0xA4, 0x71, 0x75, 0x75, 0x78
                ],
            ),
            // Struct with multiple FlexUInt field names followed by a FlexSym field name
            (
                &[field(4, "foo"), field(5, "bar"), field("quux", "quuz")],
                &[
                    // Struct with FlexUInt length
                    0xFD,
                    // FlexUInt length 21 
                    0x2B,
                    // FlexUInt symbol ID 4
                    0x09,
                    // 3-byte symbol
                    // ↓     f     o     o
                    0xA3, 0x66, 0x6F, 0x6F,
                    // FlexUInt symbol ID 5
                    0x0B,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // Enable FlexSym field name encoding
                    0x01,
                    // Inline 4-byte field name
                    // ↓     q     u     u     x
                    0xF9, 0x71, 0x75, 0x75, 0x78,
                    // 4-byte symbol
                    // ↓     q     u     u     z
                    0xA4, 0x71, 0x75, 0x75, 0x7A
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
    fn write_delimited_structs() -> IonResult<()> {
        #[rustfmt::skip]
            let test_cases: &[(TestStruct, &[u8])] = &[
            // Empty struct
            (&[], &[0xF3, 0x01, 0xF0]),
            // Struct with a single symbol ID field name
            (
                &[field(4, "foo")],
                &[
                    // Delimited struct
                    0xF3,
                    // FlexUInt symbol ID 4
                    0x09,
                    // 3-byte symbol
                    // ↓     f     o     o
                    0xA3, 0x66, 0x6F, 0x6F,
                    // End delimited struct
                    0x01, 0xF0,
                ],
            ),
            // Struct with multiple symbol ID field names
            (
                &[field(4, "foo"), field(5, "bar"), field(6, "baz")],
                &[
                    // Delimited struct
                    0xF3,
                    // FlexUInt symbol ID 4
                    0x09,
                    // 3-byte symbol
                    // ↓     f     o     o
                    0xA3, 0x66, 0x6F, 0x6F,
                    // FlexUInt symbol ID 5
                    0x0B,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // --------------------
                    // FlexUInt symbol ID 6
                    0x0D,
                    // 3-byte symbol
                    // ↓     b     a     z
                    0xA3, 0x62, 0x61, 0x7A,
                    // End delimited struct
                    0x01, 0xF0,
                ],
            ),
            // Struct with single inline-text field name
            (
                &[field("foo", "bar")],
                &[
                    // Delimited struct
                    0xF3,
                    // Inline 3-byte field name
                    // ↓     f     o     o
                    0xFB, 0x66, 0x6F, 0x6F,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // End delimited struct
                    0x01, 0xF0,
                ],
            ),
            // Struct with multiple inline-text field names
            (
                &[field("foo", "bar"), field("baz", "quux")],
                &[
                    // Delimited struct
                    0xF3,
                    // Inline 3-byte field name
                    // ↓     f     o     o
                    0xFB, 0x66, 0x6F, 0x6F,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // Inline 3-byte field name
                    // ↓     b     a     z
                    0xFB, 0x62, 0x61, 0x7A,
                    // 4-byte symbol
                    // ↓     q     u     u     x
                    0xA4, 0x71, 0x75, 0x75, 0x78,
                    // End delimited struct
                    0x01, 0xF0,
                ],
            ),
            // Struct with multiple symbol ID field names followed by an inline text field name
            (
                &[field(4, "foo"), field(5, "bar"), field("quux", "quuz")],
                &[
                    // Delimited struct
                    0xF3,
                    // FlexUInt symbol ID 4
                    0x09,
                    // 3-byte symbol
                    // ↓     f     o     o
                    0xA3, 0x66, 0x6F, 0x6F,
                    // FlexUInt symbol ID 5
                    0x0B,
                    // 3-byte symbol
                    // ↓     b     a     r
                    0xA3, 0x62, 0x61, 0x72,
                    // Inline 4-byte field name
                    // ↓     q     u     u     x
                    0xF9, 0x71, 0x75, 0x75, 0x78,
                    // 4-byte symbol
                    // ↓     q     u     u     z
                    0xA4, 0x71, 0x75, 0x75, 0x7A,
                    // End delimited struct
                    0x01, 0xF0,
                ],
            ),
        ];
        for (value, expected_encoding) in test_cases {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer
                        .value_writer()
                        .with_delimited_containers()
                        .write(*value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
        }
        Ok(())
    }

    #[test]
    fn write_annotated() -> IonResult<()> {
        fn case<'a, ValueType: WriteAsIon, SymbolType: 'a>(
            value: Annotated<'a, ValueType, SymbolType>,
            expected_encoding: &[u8],
        ) -> IonResult<()>
        where
            for<'x> &'x SymbolType: AnnotationSeq<'x>,
        {
            encoding_test(
                |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                    writer.write(value)?;
                    Ok(())
                },
                expected_encoding,
            )?;
            Ok(())
        }

        // Explicitly empty annotations set with a type hint the compiler can use in a generic context.
        const NO_ANNOTATIONS: [SymbolId; 0] = [];

        // === Symbol ID annotations ===
        case(
            0.annotated_with(NO_ANNOTATIONS),
            &[
                // Integer 0
                0x60,
            ],
        )?;
        case(
            0.annotated_with(4),
            &[
                0xE7, // One FlexSym annotation follows
                0x09, // FlexSym $4
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with([4, 5]),
            &[
                0xE8, // Two FlexSym annotations follow
                0x09, // FlexSym $4
                0x0B, // FlexSym $5
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with([4, 5, 6]),
            &[
                0xE9, // A FlexUInt follows that indicates the byte length of the FlexSym annotations sequence
                0x07, // FlexUInt length 3
                0x09, // FlexSym $4
                0x0B, // FlexSym $5
                0x0D, // FlexSym $6
                0x60, // Integer 0
            ],
        )?;

        // === Inline text annotations ===
        case(
            0.annotated_with(["foo"]),
            &[
                0xE7, // One FlexSym annotation follows
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with(["foo", "bar"]),
            &[
                0xE8, // Two FlexSym annotations follow
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x62, 0x61, 0x72, // bar
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with(["foo", "bar", "baz"]),
            &[
                0xE9, // A FlexUInt follows that indicates the byte length of the FlexSym annotations sequence
                0x19, // FlexUInt 12
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x62, 0x61, 0x72, // bar
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x62, 0x61, 0x7a, // baz
                0x60, // Integer 0
            ],
        )?;

        // === Mixed symbol IDs and inline text ===

        case(
            0.annotated_with([RawSymbolRef::SymbolId(4), RawSymbolRef::Text("foo")]),
            &[
                0xE8, // Two FlexSym annotations follow
                0x09, // FlexSym $4,
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with([RawSymbolRef::Text("foo"), RawSymbolRef::SymbolId(4)]),
            &[
                0xE8, // Two FlexSym annotations follow
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0x09, // FlexSym $4,
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with([
                RawSymbolRef::Text("foo"),
                RawSymbolRef::SymbolId(4),
                RawSymbolRef::Text("baz"),
            ]),
            &[
                0xE9, // A FlexUInt follows that indicates the byte length of the FlexSym annotations sequence
                0x13, // FlexUInt 9
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0x09, // FlexSym $4
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x62, 0x61, 0x7a, // baz
                0x60, // Integer 0
            ],
        )?;
        case(
            0.annotated_with([
                RawSymbolRef::SymbolId(4),
                RawSymbolRef::Text("foo"),
                RawSymbolRef::SymbolId(5),
            ]),
            &[
                0xE9, // A FlexUInt follows that indicates the byte length of the FlexSym annotations sequence
                0x0D, // FlexUInt 6
                0x09, // FlexSym $4
                0xFB, // FlexSym: 3 UTF-8 bytes
                0x66, 0x6F, 0x6F, // foo
                0x0B, // FlexSym $5
                0x60, // Integer 0
            ],
        )?;

        // === Special cases: "" and $0 ===
        case(
            0.annotated_with([RawSymbolRef::Text(""), RawSymbolRef::SymbolId(0)]),
            &[
                0xE8, // Two FlexSym annotations follow
                0x01, // Opcode follows
                0x90, // String of length 0
                0x01, // Opcode follows
                0xE1, // 1-byte FixedUInt symbol ID follows
                0x00, // Symbol ID 0
                0x60, // Integer 0
            ],
        )?;

        Ok(())
    }

    #[test]
    fn write_macro_invocations() -> IonResult<()> {
        encoding_test(
            |writer: &mut LazyRawBinaryWriter_1_1<&mut Vec<u8>>| {
                let mut args = writer.eexp_writer(0)?;
                args.write_symbol("foo")?
                    .write_symbol("bar")?
                    .write_symbol("baz")?;
                args.close()
            },
            &[
                0x00, // Invoke macro address 0
                0xA3, 0x66, 0x6f, 0x6f, // foo
                0xA3, 0x62, 0x61, 0x72, // bar
                0xA3, 0x62, 0x61, 0x7a, // baz
            ],
        )?;
        Ok(())
    }

    #[rstest]
    #[case::boolean("true false")]
    #[case::int("1 2 3 4 5")]
    #[case::annotated_int("foo::1 bar::baz::2 quux::quuz::waldo::3")]
    #[case::float("2.5e0 -2.5e0 100.2e0 -100.2e0")]
    #[case::annotated_float("foo::2.5e0 bar::baz::-2.5e0 quux::quuz::waldo::100.2e0")]
    #[case::float_special("+inf -inf nan")]
    #[case::decimal("2.5 -2.5 100.2 -100.2")]
    #[case::decimal_zero("0. 0d0 -0d0 -0.0")]
    #[case::annotated_decimal("foo::2.5 bar::baz::-2.5 quux::quuz::waldo::100.2")]
    #[case::timestamp_unknown_offset(
        r#"
            2024T
            2024-06T
            2024-06-07
            2024-06-07T10:06-00:00
            2024-06-07T10:06:30-00:00
            2024-06-07T10:06:30.333-00:00
        "#
    )]
    #[case::timestamp_utc(
        r#"
            2024-06-07T10:06Z
            2024-06-07T10:06+00:00
            2024-06-07T10:06:30Z
            2024-06-07T10:06:30+00:00
            2024-06-07T10:06:30.333Z
            2024-06-07T10:06:30.333+00:00
        "#
    )]
    #[case::timestamp_known_offset(
        r#"
            2024-06-07T10:06+02:00
            2024-06-07T10:06+01:00
            2024-06-07T10:06-05:00
            2024-06-07T10:06-08:00
            2024-06-07T10:06:30+02:00
            2024-06-07T10:06:30+01:00
            2024-06-07T10:06:30-05:00
            2024-06-07T10:06:30-08:00
            2024-06-07T10:06:30.333+02:00
            2024-06-07T10:06:30.333+01:00
            2024-06-07T10:06:30.333-05:00
            2024-06-07T10:06:30.333-08:00
        "#
    )]
    #[case::annotated_timestamp(
        r#"
            foo::2024T
            bar::baz::2024-06T
            quux::quuz::waldo::2024-06-07T
        "#
    )]
    #[case::string(
        r#"
            ""
            "hello"
            "안녕하세요"
            "⚛️"
        "#
    )]
    #[case::annotated_string(
        r#"
            foo::""
            bar::baz::"안녕하세요"
            quux::quuz::waldo::"⚛️"
        "#
    )]
    #[case::symbol(
        r#"
            foo
            'bar baz'
        "#
    )]
    #[case::annotated_symbol(
        r#"
        foo::Earth
        bar::baz::Mars
        quux::quuz::waldo::Jupiter
    "#
    )]
    #[case::symbol_unknown_text("$0")]
    #[case::blob("{{}} {{aGVsbG8=}}")]
    #[case::annotated_blob(
        r#"
            foo::{{}}
            bar::baz::{{aGVsbG8=}}
            quux::quuz::waldo::{{aGVsbG8=}}
        "#
    )]
    #[case::clob(r#"{{""}} {{"hello"}}"#)]
    #[case::annotated_clob(
        r#"
            foo::{{""}}
            bar::baz::{{"hello"}}
            quux::quuz::waldo::{{"world"}}
        "#
    )]
    #[case::list(
        r#"
            []
            [1, 2, 3]
            [1, [2, 3], 4]
        "#
    )]
    #[case::annotated_list(
        r#"
            foo::[]
            bar::baz::[1, 2, 3]
            quux::quuz::waldo::[1, nested::[2, 3], 4]
        "#
    )]
    #[case::sexp(
        r#"
            ()
            (1 2 3)
            (1 (2 3) 4)
        "#
    )]
    #[case::annotated_sexp(
        r#"
            foo::()
            bar::baz::(1 2 3)
            quux::quuz::waldo::(1 nested::(2 3) 4)
        "#
    )]
    #[case::struct_(
        r#"
            {}
            {a: 1, b: 2, c: 3}
            {a: 1, b: {c: 2, d: 3}, e: 4}
        "#
    )]
    #[case::annotated_struct(
        r#"
            foo::{}
            bar::baz::{a: 1, b: 2, c: 3}
            quux::quuz::waldo::{a: 1, b: nested::{c: 2, d: 3}, e: 4}
        "#
    )]
    fn roundtripping(#[case] ion_data_1_0: &str) -> IonResult<()> {
        // This test uses application-level readers and writers to do its roundtripping. This means
        // that tests involving annotations, symbol values, or struct field names will produce a
        // symbol table.
        let original_sequence = Element::read_all(ion_data_1_0)?;
        let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
        writer.write_all(&original_sequence)?;
        let binary_data_1_1 = writer.close()?;
        let output_sequence = Element::read_all(binary_data_1_1)?;
        assert!(
            original_sequence.ion_eq(&output_sequence),
            "(original, after roundtrip)\n{}",
            original_sequence.iter().zip(output_sequence.iter()).fold(
                String::new(),
                |mut text, (before, after)| {
                    use std::fmt::Write;
                    let is_eq = before.ion_eq(after);
                    let flag = if is_eq { "" } else { "<- not IonEq" };
                    writeln!(&mut text, "({}, {}) {}", before, after, flag).unwrap();
                    text
                }
            )
        );
        Ok(())
    }
}
