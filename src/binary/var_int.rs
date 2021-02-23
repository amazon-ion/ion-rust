use crate::data_source::IonDataSource;
use crate::result::{decoding_error, IonResult};
use std::io::Write;
use std::mem;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarInt's magnitude and byte length in the future.
// See: https://github.com/amzn/ion-rust/issues/7
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

#[derive(Debug)]
pub struct VarInt {
    size_in_bytes: usize,
    value: VarIntStorage,
}

const MAGNITUDE_BITS_IN_FINAL_BYTE: usize = 6;

/// Represents a variable-length signed integer. See the
/// [VarUInt and VarInt Fields](amzn.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
impl VarInt {
    /// Reads a VarInt from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R) -> IonResult<VarInt> {
        // Unlike VarUInt's encoding, the first byte in a VarInt is a special case because
        // bit #6 (0-indexed, from the right) indicates whether the value is positive (0) or
        // negative (1).

        let first_byte: u8 = data_source.next_byte()?.unwrap();
        let no_more_bytes: bool = first_byte >= 0b1000_0000; // If the first bit is 1, we're done.
        let is_positive: bool = (first_byte & 0b0100_0000) == 0;
        let sign: VarIntStorage = if is_positive { 1 } else { -1 };
        let mut magnitude = (first_byte & 0b0011_1111) as VarIntStorage;

        if no_more_bytes {
            return Ok(VarInt {
                size_in_bytes: 1,
                value: magnitude * sign,
            });
        }

        let mut byte_processor = |byte: u8| {
            let lower_seven = (0b0111_1111 & byte) as VarIntStorage;
            magnitude <<= 7;
            magnitude |= lower_seven;
            byte < 0b1000_0000
        };

        let encoded_size_in_bytes = 1 + data_source.read_next_byte_while(&mut byte_processor)?;

        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte VarInt. Max supported size is {} bytes.",
                encoded_size_in_bytes, MAX_ENCODED_SIZE_IN_BYTES
            ));
        }

        Ok(VarInt {
            size_in_bytes: encoded_size_in_bytes,
            value: magnitude * sign,
        })
    }

    #[rustfmt::skip]
    pub fn write_i64<W: Write>(sink: &mut W, value: i64) -> IonResult<()> {
        // An i64 is 8 bytes of data. The VarInt encoding will add one continuation bit per byte
        // as well as a sign bit, for a total of 9 extra bits. Therefore, the largest encoding
        // of an i64 will be just over 9 bytes.
        const VAR_INT_BUFFER_SIZE: usize = 10;

        // Create a buffer to store the encoded value.
        let mut buffer: [u8; VAR_INT_BUFFER_SIZE] = [
            0, 0, 0, 0, 0,
            0, 0, 0, 0, 0b1000_0000
            //            ^-- Set the 'end' flag of the final byte to 1.
        ];

        // The absolute value of an i64 can be cast losslessly to a u64.
        let mut magnitude: u64 = value.abs() as u64;

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
        for buffer_byte in buffer[VAR_INT_BUFFER_SIZE - bytes_required..].iter_mut().rev() {
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
        sink.write_all(&buffer[VAR_INT_BUFFER_SIZE - bytes_required..])?;
        Ok(())
    }

    /// Returns the value of the signed integer
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
    use std::io::{BufReader, Cursor};

    const ERROR_MESSAGE: &'static str = "Failed to read a VarUInt from the provided data.";

    #[test]
    fn test_read_negative_var_int() {
        let var_int = VarInt::read(&mut Cursor::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]))
            .expect(ERROR_MESSAGE);
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), -935_809);
    }

    #[test]
    fn test_read_positive_var_int() {
        let var_int = VarInt::read(&mut Cursor::new(&[0b0011_1001, 0b0000_1111, 0b1000_0001]))
            .expect(ERROR_MESSAGE);
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), 935_809);
    }

    #[test]
    fn test_read_var_uint_small_buffer() {
        let var_uint = VarInt::read(
            // Construct a BufReader whose input buffer cannot hold all of the data at once
            // to ensure that reads that span multiple I/O operations work as expected
            &mut BufReader::with_capacity(1, Cursor::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001])),
        )
        .expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 3);
        assert_eq!(var_uint.value(), -935_809);
    }

    #[test]
    fn test_read_var_int_zero() {
        let var_int = VarInt::read(&mut Cursor::new(&[0b1000_0000])).expect(ERROR_MESSAGE);
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), 0);
    }

    #[test]
    fn test_read_var_int_min_negative_two_byte_encoding() {
        let var_int =
            VarInt::read(&mut Cursor::new(&[0b0111_1111, 0b1111_1111])).expect(ERROR_MESSAGE);
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), -8_191);
    }

    #[test]
    fn test_read_var_int_max_positive_two_byte_encoding() {
        let var_int =
            VarInt::read(&mut Cursor::new(&[0b0011_1111, 0b1111_1111])).expect(ERROR_MESSAGE);
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), 8_191);
    }

    #[test]
    fn test_read_var_int_overflow_detection() {
        let _var_uint = VarInt::read(&mut Cursor::new(&[
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b1111_1111,
        ]))
        .expect_err("This should have failed due to overflow.");
    }

    fn var_int_encoding_test(value: i64, expected_encoding: &[u8]) -> IonResult<()> {
        let mut buffer = vec![];
        VarInt::write_i64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_encoding);
        return Ok(());
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
