use std::mem;

use crate::data_source::IonDataSource;
use crate::result::{decoding_error, IonResult};
use std::io::Write;

type IntStorage = i64;
const MAX_INT_SIZE_IN_BYTES: usize = mem::size_of::<IntStorage>();

/// Represents a fixed-length signed integer. See the
/// [UInt and Int Fields](http://amzn.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct Int {
    size_in_bytes: usize,
    value: IntStorage,
    // [IntStorage] is not capable of natively representing negative zero. We track the sign
    // of the value separately so we can distinguish between 0 and -0.
    is_negative: bool,
}

impl Int {
    /// Reads an Int with `length` bytes from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R, length: usize) -> IonResult<Int> {
        if length == 0 {
            return Ok(Int {
                size_in_bytes: 0,
                value: 0,
                is_negative: false,
            });
        } else if length > MAX_INT_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte Int. Max supported size is {} bytes.",
                length, MAX_INT_SIZE_IN_BYTES
            ));
        }

        // Create a stack-allocated buffer to hold the data we're going to read in.
        let mut buffer = [0u8; MAX_INT_SIZE_IN_BYTES];
        // Get a mutable reference to a portion of the buffer just big enough to fit
        // the requested number of bytes.
        let buffer = &mut buffer[0..length];

        data_source.read_exact(buffer)?;
        let mut byte_iter = buffer.iter();

        let first_byte: i64 = i64::from(byte_iter.next().copied().unwrap());
        let sign: IntStorage = if first_byte & 0b1000_0000 == 0 { 1 } else { -1 };
        let mut magnitude: IntStorage = first_byte & 0b0111_1111;

        for &byte in byte_iter {
            let byte = i64::from(byte);
            magnitude <<= 8;
            magnitude |= byte;
        }

        Ok(Int {
            size_in_bytes: length,
            value: magnitude * sign,
            is_negative: sign == -1,
        })
    }

    /// Encodes the provided `value` as an Int and writes it to the provided `sink`.
    /// Returns the number of bytes written.
    pub fn write_i64<W: Write>(sink: &mut W, value: i64) -> IonResult<usize> {
        let magnitude = value.abs() as u64;
        // Using leading_zeros() to determine how many empty bytes we can ignore.
        // We subtract one from the number of leading bits to leave space for a sign bit
        // and divide by 8 to get the number of bytes.
        let empty_leading_bytes: u32 = magnitude.leading_zeros() - 1 >> 3;
        let first_occupied_byte = empty_leading_bytes as usize;

        let mut magnitude_bytes: [u8; mem::size_of::<u64>()] = (magnitude as u64).to_be_bytes();
        let bytes_to_write: &mut [u8] = &mut magnitude_bytes[first_occupied_byte..];
        if value < 0 {
            bytes_to_write[0] |= 0b1000_0000;
        }

        sink.write_all(bytes_to_write)?;
        Ok(bytes_to_write.len())
    }

    /// Returns `true` if the Int is negative zero.
    pub fn is_negative_zero(&self) -> bool {
        // `self.value` can natively represent any negative integer _except_ -0.
        // To check for negative zero, we need to also look at the sign bit that was encoded
        // in the stream.
        self.value == 0 && self.is_negative
    }

    /// Returns the value of the signed integer.
    #[inline(always)]
    pub fn value(&self) -> IntStorage {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// signed integer.
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::Int;
    use crate::result::IonResult;
    use std::io;
    use std::io::Cursor;

    const READ_ERROR_MESSAGE: &str = "Failed to read an Int from the provided cursor.";

    #[test]
    fn test_read_three_byte_positive_int() {
        let data = &[0b0011_1100, 0b1000_0111, 0b1000_0001];
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), 3_966_849);
    }

    #[test]
    fn test_read_three_byte_negative_int() {
        let data = &[0b1011_1100, 0b1000_0111, 0b1000_0001];
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), -3_966_849);
    }

    #[test]
    fn test_read_int_negative_zero() {
        let data = &[0b1000_0000]; // Negative zero
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), 0);
    }

    #[test]
    fn test_read_int_positive_zero() {
        let data = &[0b0000_0000]; // Positive zero
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), 0);
    }

    #[test]
    fn test_read_two_byte_positive_int() {
        let data = &[0b0111_1111, 0b1111_1111];
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), 32_767);
    }

    #[test]
    fn test_read_two_byte_negative_int() {
        let data = &[0b1111_1111, 0b1111_1111];
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), -32_767);
    }

    #[test]
    fn test_read_int_length_zero() {
        let data = &[];
        let int = Int::read(&mut Cursor::new(data), data.len()).expect(READ_ERROR_MESSAGE);
        assert_eq!(int.size_in_bytes(), 0);
        assert_eq!(int.value(), 0);
    }

    #[test]
    fn test_read_int_overflow() {
        let data = &[0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF, 0x01];
        let _int = Int::read(&mut Cursor::new(data), data.len())
            .expect_err("This should have failed due to overflow.");
    }

    fn write_int_test(value: i64, expected_bytes: &[u8]) -> IonResult<()> {
        let mut buffer: Vec<u8> = vec![];
        Int::write_i64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_bytes);
        Ok(())
    }

    #[test]
    fn test_write_int_zero() -> IonResult<()> {
        write_int_test(0, &[0b0000_0000])
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
        let length = Int::write_i64(&mut buffer, i64::MAX)?;
        let i = Int::read(&mut io::Cursor::new(buffer.as_slice()), length)?;
        assert_eq!(i.value, i64::MAX);
        Ok(())
    }
}
