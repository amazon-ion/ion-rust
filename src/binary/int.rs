use std::mem;

use crate::data_source::IonDataSource;
use crate::result::{decoding_error, IonResult};
use crate::types;
use crate::types::{Coefficient, Int};
use num_bigint::{BigInt, Sign};
use num_traits::Zero;
use std::io::Write;

type IntStorage = i64;
const INT_NEGATIVE_ZERO: u8 = 0x80;

// This limit is used for stack-allocating buffer space to encode/decode Ints.
const INT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_INT_SIZE_IN_BYTES: usize = 2048;

/// Represents a fixed-length signed integer. See the
/// [UInt and Int Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct DecodedInt {
    size_in_bytes: usize,
    value: Int,
    // [Integer] is not capable of natively representing negative zero. We track the sign
    // of the value separately so we can distinguish between 0 and -0.
    is_negative: bool,
}

impl DecodedInt {
    pub(crate) fn new(value: Int, is_negative: bool, size_in_bytes: usize) -> Self {
        DecodedInt {
            size_in_bytes,
            value,
            is_negative,
        }
    }

    /// Reads an Int with `length` bytes from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R, length: usize) -> IonResult<DecodedInt> {
        if length == 0 {
            return Ok(DecodedInt {
                size_in_bytes: 0,
                value: Int::I64(0),
                is_negative: false,
            });
        } else if length > MAX_INT_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {length}-byte Int. Max supported size is {MAX_INT_SIZE_IN_BYTES} bytes."
            ));
        }

        if length <= INT_STACK_BUFFER_SIZE {
            let buffer = &mut [0u8; INT_STACK_BUFFER_SIZE];
            DecodedInt::read_using_buffer(data_source, length, buffer)
        } else {
            // We're reading an enormous int. Heap-allocate a Vec to use as storage.
            let mut buffer = vec![0u8; length];
            DecodedInt::read_using_buffer(data_source, length, buffer.as_mut_slice())
        }
    }

    pub fn read_using_buffer<R: IonDataSource>(
        data_source: &mut R,
        length: usize,
        buffer: &mut [u8],
    ) -> IonResult<DecodedInt> {
        // Get a mutable reference to a portion of the buffer just big enough to fit
        // the requested number of bytes.
        let buffer = &mut buffer[0..length];

        data_source.read_exact(buffer)?;
        let mut byte_iter = buffer.iter();
        let mut is_negative: bool = false;

        let value = if length <= mem::size_of::<i64>() {
            // This Int will fit in an i64.
            let first_byte: i64 = i64::from(byte_iter.next().copied().unwrap());
            let sign: i64 = if first_byte & 0b1000_0000 == 0 {
                1
            } else {
                is_negative = true;
                -1
            };
            let mut magnitude: i64 = first_byte & 0b0111_1111;
            for &byte in byte_iter {
                let byte = i64::from(byte);
                magnitude <<= 8;
                magnitude |= byte;
            }
            Int::I64(sign * magnitude)
        } else {
            // This Int is too big for an i64, we'll need to use a BigInt
            let sign: num_bigint::Sign = if buffer[0] & 0b1000_0000 == 0 {
                Sign::Plus
            } else {
                is_negative = true;
                Sign::Minus
            };
            // We're going to treat the buffer's contents like the big-endian bytes of an
            // unsigned integer. Now that we've made a note of the sign, set the sign bit
            // in the buffer to zero.
            buffer[0] &= 0b0111_1111;
            let value = BigInt::from_bytes_be(sign, buffer);
            Int::BigInt(value)
        };

        Ok(DecodedInt {
            size_in_bytes: length,
            value,
            is_negative,
        })
    }

    /// Encodes the provided `value` as an Int and writes it to the provided `sink`.
    /// Returns the number of bytes written.
    pub fn write_i64<W: Write>(sink: &mut W, value: i64) -> IonResult<usize> {
        let magnitude = value.unsigned_abs();
        // Using leading_zeros() to determine how many empty bytes we can ignore.
        // We subtract one from the number of leading bits to leave space for a sign bit
        // and divide by 8 to get the number of bytes.
        let empty_leading_bytes: u32 = (magnitude.leading_zeros() - 1) >> 3;
        let first_occupied_byte = empty_leading_bytes as usize;

        let mut magnitude_bytes: [u8; mem::size_of::<u64>()] = magnitude.to_be_bytes();
        let bytes_to_write: &mut [u8] = &mut magnitude_bytes[first_occupied_byte..];
        if value < 0 {
            bytes_to_write[0] |= 0b1000_0000;
        }

        sink.write_all(bytes_to_write)?;
        Ok(bytes_to_write.len())
    }

    /// Encodes a negative zero as an `Int` and writes it to the privided `sink`.
    /// Returns the number of bytes written.
    ///
    /// This method is similar to [Self::write_i64]. However, because an i64 cannot represent a negative
    /// zero, a separate method is required.
    pub fn write_negative_zero<W: Write>(sink: &mut W) -> IonResult<usize> {
        sink.write_all(&[INT_NEGATIVE_ZERO])?;
        Ok(1)
    }

    /// Returns `true` if the Int is negative zero.
    pub fn is_negative_zero(&self) -> bool {
        // `self.value` can natively represent any negative integer _except_ -0.
        // To check for negative zero, we need to also look at the sign bit that was encoded
        // in the stream.
        self.value.is_zero() && self.is_negative
    }

    /// Returns the value of the signed integer.
    #[inline(always)]
    pub fn value(&self) -> &Int {
        &self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// signed integer.
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }

    /// Constructs a DecodedInt that represents zero. This is useful when reading from a stream
    /// where a zero-length Int is found, meaning that it is implicitly positive zero.
    pub fn zero() -> Self {
        DecodedInt {
            size_in_bytes: 0,
            value: Int::I64(0),
            is_negative: false,
        }
    }
}

impl From<DecodedInt> for Int {
    /// Note that if the DecodedInt represents -0, converting it to an Integer will result in a 0.
    /// If negative zero is significant to your use case, check it using [DecodedInt::is_negative_zero]
    /// before converting it to an Integer.
    fn from(uint: DecodedInt) -> Self {
        let DecodedInt {
            value,
            .. // Ignore 'size_in_bytes' and 'is_negative'
        } = uint;
        value
    }
}

impl From<DecodedInt> for Coefficient {
    fn from(int: DecodedInt) -> Self {
        let DecodedInt {
            value,
            is_negative,
            .. // ignore `size_in_bytes`
        } = int;
        use types::Sign::{Negative, Positive};
        let sign = if is_negative { Negative } else { Positive };
        Coefficient::new(sign, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::result::IonResult;
    use crate::types::Int;
    use std::io;
    use std::io::Cursor;

    const READ_ERROR_MESSAGE: &str = "Failed to read an Int from the provided cursor.";

    #[test]
    fn test_read_three_byte_positive_int() {
        let data = &[0b0011_1100, 0b1000_0111, 0b1000_0001];
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Int::I64(3_966_849));
    }

    #[test]
    fn test_read_three_byte_negative_int() {
        let data = &[0b1011_1100, 0b1000_0111, 0b1000_0001];
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Int::I64(-3_966_849));
    }

    #[test]
    fn test_read_int_negative_zero() {
        let data = &[0b1000_0000]; // Negative zero
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Int::I64(0));
        assert!(int.is_negative_zero());
    }

    #[test]
    fn test_read_int_positive_zero() {
        let data = &[0b0000_0000]; // Positive zero
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Int::I64(0));
        assert!(!int.is_negative_zero());
    }

    #[test]
    fn test_read_two_byte_positive_int() {
        let data = &[0b0111_1111, 0b1111_1111];
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Int::I64(32_767));
    }

    #[test]
    fn test_read_two_byte_negative_int() {
        let data = &[0b1111_1111, 0b1111_1111];
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Int::I64(-32_767));
    }

    #[test]
    fn test_read_int_length_zero() {
        let data = &[];
        let int = DecodedInt::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 0);
        assert_eq!(int.value(), &Int::I64(0));
    }

    #[test]
    fn test_read_int_overflow() {
        // A Vec of bytes that's one beyond the maximum allowable Int size. Each byte is a 1.
        let buffer = vec![1; MAX_INT_SIZE_IN_BYTES + 1];
        let data = buffer.as_slice();
        let _int = DecodedInt::read(&mut Cursor::new(data), data.len())
            .expect_err("This exceeded the configured max Int size.");
    }

    fn write_int_test(value: i64, expected_bytes: &[u8]) -> IonResult<()> {
        let mut buffer: Vec<u8> = vec![];
        DecodedInt::write_i64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_bytes);
        Ok(())
    }

    #[test]
    fn test_write_int_zero() -> IonResult<()> {
        write_int_test(0, &[0b0000_0000])
    }

    #[test]
    fn test_write_int_negative_zero() -> IonResult<()> {
        let mut buffer: Vec<u8> = vec![];
        DecodedInt::write_negative_zero(&mut buffer)?;
        assert_eq!(buffer.as_slice(), &[0b1000_0000]);
        Ok(())
    }

    #[test]
    fn test_write_int_single_byte_values() -> IonResult<()> {
        write_int_test(1, &[0b0000_0001])?;
        write_int_test(3, &[0b0000_0011])?;
        write_int_test(7, &[0b0000_0111])?;
        write_int_test(100, &[0b0110_0100])?;

        write_int_test(-1, &[0b1000_0001])?;
        write_int_test(-3, &[0b1000_0011])?;
        write_int_test(-7, &[0b1000_0111])?;
        write_int_test(-100, &[0b1110_0100])?;
        Ok(())
    }

    #[test]
    fn test_write_int_two_byte_values() -> IonResult<()> {
        write_int_test(201, &[0b0000_0000, 0b1100_1001])?;
        write_int_test(501, &[0b0000_0001, 0b1111_0101])?;
        write_int_test(16_000, &[0b0011_1110, 0b1000_0000])?;

        write_int_test(-201, &[0b1000_0000, 0b1100_1001])?;
        write_int_test(-501, &[0b1000_0001, 0b1111_0101])?;
        write_int_test(-16_000, &[0b1011_1110, 0b1000_0000])?;
        Ok(())
    }

    #[test]
    fn test_write_int_max_i64() -> IonResult<()> {
        let mut buffer: Vec<u8> = vec![];
        let length = DecodedInt::write_i64(&mut buffer, i64::MAX)?;
        let i = DecodedInt::read(&mut io::Cursor::new(buffer.as_slice()), length)?;
        assert_eq!(i.value, Int::I64(i64::MAX));
        Ok(())
    }
}
