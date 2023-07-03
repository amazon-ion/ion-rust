use crate::result::IonResult;
use std::io::Write;
use std::mem;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarInt's magnitude and byte length in the future.
// See: https://github.com/amazon-ion/ion-rust/issues/7
type VarIntStorage = i64;
type VarIntSizeStorage = usize;

const BITS_PER_ENCODED_BYTE: usize = 7;
const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<VarIntStorage>() * 8;
const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

const LOWER_6_BITMASK: u8 = 0b0011_1111;
const LOWER_7_BITMASK: u8 = 0b0111_1111;
const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

const BITS_PER_BYTE: usize = 8;
const BITS_PER_U64: usize = mem::size_of::<u64>() * BITS_PER_BYTE;

const VARINT_NEGATIVE_ZERO: u8 = 0xC0;

#[derive(Debug)]
pub struct VarInt {
    size_in_bytes: usize,
    value: VarIntStorage,
    // [VarIntStorage] is not capable of natively representing negative zero. We track the sign
    // of the value separately so we can distinguish between 0 and -0.
    is_negative: bool,
}

const MAGNITUDE_BITS_IN_FINAL_BYTE: usize = 6;

/// Represents a variable-length signed integer. See the
/// [VarUInt and VarInt Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
impl VarInt {
    pub(crate) fn new(value: i64, is_negative: bool, size_in_bytes: usize) -> Self {
        VarInt {
            size_in_bytes,
            value,
            is_negative,
        }
    }

    /// Writes an `i64` to `sink`, returning the number of bytes written.
    pub fn write_i64<W: Write>(sink: &mut W, value: i64) -> IonResult<usize> {
        // An i64 is 8 bytes of data. The VarInt encoding will add one continuation bit per byte
        // as well as a sign bit, for a total of 9 extra bits. Therefore, the largest encoding
        // of an i64 will be just over 9 bytes.
        const VAR_INT_BUFFER_SIZE: usize = 10;

        // Create a buffer to store the encoded value.
        #[rustfmt::skip]
        let mut buffer: [u8; VAR_INT_BUFFER_SIZE] = [
            0, 0, 0, 0, 0,
            0, 0, 0, 0, 0b1000_0000
            //            ^-- Set the 'end' flag of the final byte to 1.
        ];

        // The absolute value of an i64 can be cast losslessly to a u64.
        let mut magnitude: u64 = value.unsigned_abs();

        // Calculate the number of bytes that the encoded version of our value will occupy.
        // We ignore any leading zeros in the value to minimize the encoded size.
        let occupied_bits = BITS_PER_U64 - magnitude.leading_zeros() as usize;
        // The smallest possible VarInt is a single byte.
        let mut bytes_required: usize = 1;
        // We can store up to 6 bits in a one-byte VarInt. If there are more than 6 bits of
        // magnitude to encode, we'll need to write additional bytes.
        // Saturating subtraction will return 0 instead of underflowing.
        let remaining_bits = occupied_bits.saturating_sub(MAGNITUDE_BITS_IN_FINAL_BYTE);
        // We can encode 7 bits of magnitude in every other byte.
        bytes_required += f64::ceil(remaining_bits as f64 / 7.0) as usize;

        // TODO: The above calculation could be cached for each number of occupied_bits from 0 to 64

        let mut bytes_remaining = bytes_required;
        // We're using right shifting to isolate the least significant bits in our magnitude
        // in each iteration of the loop, so we'll move from right to left in our encoding buffer.
        // The rightmost byte has already been flagged as the final byte.
        for buffer_byte in buffer[VAR_INT_BUFFER_SIZE - bytes_required..]
            .iter_mut()
            .rev()
        {
            bytes_remaining -= 1;
            if bytes_remaining > 0 {
                // This isn't the leftmost byte, so we can store 7 magnitude bits.
                *buffer_byte |= magnitude as u8 & LOWER_7_BITMASK;
                magnitude >>= 7;
            } else {
                // We're in the final byte, so we can only store 6 bits.
                *buffer_byte |= magnitude as u8 & LOWER_6_BITMASK;
                // If the value we're encoding is negative, flip the sign bit in the leftmost
                // encoded byte.
                if value < 0 {
                    *buffer_byte |= 0b0100_0000;
                }
            }
        }

        // Write the data from our encoding buffer to the provided sink in as few operations as
        // possible.
        let encoded_bytes = &buffer[VAR_INT_BUFFER_SIZE - bytes_required..];
        sink.write_all(encoded_bytes)?;
        Ok(encoded_bytes.len())
    }

    /// Encodes a negative zero as an `VarInt` and writes it to the provided `sink`.
    /// Returns the number of bytes written.
    ///
    /// This method is similar to [write_i64](crate::binary::var_int::VarInt::write_i64).
    /// However, because an i64 cannot represent a negative zero, a separate method is required.
    pub fn write_negative_zero<W: Write>(sink: &mut W) -> IonResult<usize> {
        sink.write_all(&[VARINT_NEGATIVE_ZERO])?;
        Ok(1)
    }

    /// Returns `true` if the VarInt is negative zero.
    pub fn is_negative_zero(&self) -> bool {
        // `self.value` can natively represent any negative integer _except_ -0.
        // To check for negative zero, we need to also look at the sign bit that was encoded
        // in the stream.
        self.value == 0 && self.is_negative
    }

    /// Returns the value of the signed integer. If the [VarInt] is negative zero, this method
    /// will return `0`. Use the [is_negative_zero](Self::is_negative_zero) method to check for
    /// negative zero explicitly.
    #[inline(always)]
    pub fn value(&self) -> VarIntStorage {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// signed integer
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::VarInt;
    use crate::result::IonResult;

    fn var_int_encoding_test(value: i64, expected_encoding: &[u8]) -> IonResult<()> {
        let mut buffer = vec![];
        VarInt::write_i64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_encoding);
        Ok(())
    }

    #[test]
    fn test_write_var_uint_zero() -> IonResult<()> {
        var_int_encoding_test(0, &[0b1000_0000])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_single_byte_values() -> IonResult<()> {
        var_int_encoding_test(17, &[0b1001_0001])?;
        var_int_encoding_test(-17, &[0b1101_0001])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_two_byte_values() -> IonResult<()> {
        var_int_encoding_test(555, &[0b0000_0100, 0b1010_1011])?;
        var_int_encoding_test(-555, &[0b0100_0100, 0b1010_1011])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_three_byte_values() -> IonResult<()> {
        var_int_encoding_test(400_600, &[0b0001_1000, 0b0011_1001, 0b1101_1000])?;
        var_int_encoding_test(-400_600, &[0b0101_1000, 0b0011_1001, 0b1101_1000])?;
        Ok(())
    }
}
