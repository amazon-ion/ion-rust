use std::mem;

use crate::data_source::IonDataSource;
use crate::result::{decoding_error_result, IonResult};

type IntStorage = i64;
const MAX_INT_SIZE_IN_BYTES: usize = mem::size_of::<IntStorage>();

/// Represents a fixed-length signed integer. See the
/// [UInt and Int Fields](http://amzn.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct Int {
    size_in_bytes: usize,
    value: IntStorage,
}

impl Int {
    /// Reads an Int with `length` bytes from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R, length: usize) -> IonResult<Int> {
        if length == 0 {
            return Ok(Int {
                size_in_bytes: 0,
                value: 0,
            });
        } else if length > MAX_INT_SIZE_IN_BYTES {
            return decoding_error_result(format!(
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
        })
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
}
