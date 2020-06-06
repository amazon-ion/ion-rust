use crate::data_source::IonDataSource;
use crate::result::{decoding_error_result, IonResult};
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

const LOWER_7_BITMASK: u8 = 0b0111_1111;
const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

#[derive(Debug)]
pub struct VarInt {
    size_in_bytes: usize,
    value: VarIntStorage,
}

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
            return decoding_error_result(format!(
                "Found a {}-byte VarInt. Max supported size is {} bytes.",
                encoded_size_in_bytes, MAX_ENCODED_SIZE_IN_BYTES
            ));
        }

        Ok(VarInt {
            size_in_bytes: encoded_size_in_bytes,
            value: magnitude * sign,
        })
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
}
