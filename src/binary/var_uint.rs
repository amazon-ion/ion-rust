use crate::result::IonResult;
use std::io::Write;
use std::mem;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarUInt's magnitude and byte length in the future.
// See: https://github.com/amazon-ion/ion-rust/issues/7

const BITS_PER_ENCODED_BYTE: usize = 7;
const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<usize>() * 8;
const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

const LOWER_7_BITMASK: u8 = 0b0111_1111;
const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

/// Represents a variable-length unsigned integer. See the
/// [VarUInt and VarInt Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct VarUInt {
    value: usize,
    size_in_bytes: usize,
}

impl VarUInt {
    pub(crate) fn new(value: usize, size_in_bytes: usize) -> Self {
        VarUInt {
            value,
            size_in_bytes,
        }
    }

    /// Encodes the given unsigned int value as a VarUInt and writes it to the
    /// sink, returning the number of bytes written.
    pub fn write_u64<W: Write>(sink: &mut W, mut magnitude: u64) -> IonResult<usize> {
        // A u64 is 8 bytes of data. The VarUInt encoding will add a continuation bit to every byte,
        // growing the data size by 8 more bits. Therefore, the largest encoded size of a u64 is
        // 9 bytes.
        const VAR_UINT_BUFFER_SIZE: usize = 9;

        // Create a buffer to store the encoded value.
        #[rustfmt::skip]
        let mut buffer: [u8; VAR_UINT_BUFFER_SIZE] = [
            0, 0, 0, 0, 0, 0, 0, 0, 0b1000_0000
            //                        ^-- Set the 'end' flag of the final byte to 1
        ];

        if magnitude == 0 {
            sink.write_all(&[0b1000_0000])?;
            return Ok(1);
        }

        // The encoding process moves right-to-left, from the last byte in the buffer to the first.
        // `first_byte` tracks the leftmost byte in the buffer that contains encoded data.
        // We will always write at least one byte.
        let mut first_byte = VAR_UINT_BUFFER_SIZE as u64;
        for buffer_byte in buffer.iter_mut().rev() {
            first_byte -= 1;
            *buffer_byte |= magnitude as u8 & LOWER_7_BITMASK;
            magnitude >>= BITS_PER_ENCODED_BYTE;
            if magnitude == 0 {
                break;
            }
        }

        let encoded_bytes = &buffer[(first_byte as usize)..];
        sink.write_all(encoded_bytes)?;
        Ok(encoded_bytes.len())
    }

    /// Returns the magnitude of the unsigned integer
    #[inline(always)]
    pub fn value(&self) -> usize {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// unsigned integer
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::VarUInt;
    use crate::result::IonResult;

    fn var_uint_encoding_test(value: u64, expected_encoding: &[u8]) -> IonResult<()> {
        let mut buffer = vec![];
        VarUInt::write_u64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_encoding);
        Ok(())
    }

    #[test]
    fn test_write_var_uint_zero() -> IonResult<()> {
        var_uint_encoding_test(0, &[0b1000_0000])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_single_byte_values() -> IonResult<()> {
        var_uint_encoding_test(6, &[0b1000_0110])?;
        var_uint_encoding_test(17, &[0b1001_0001])?;
        var_uint_encoding_test(41, &[0b1010_1001])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_two_byte_values() -> IonResult<()> {
        var_uint_encoding_test(279, &[0b0000_0010, 0b1001_0111])?;
        var_uint_encoding_test(555, &[0b0000_0100, 0b1010_1011])?;
        var_uint_encoding_test(999, &[0b0000_0111, 0b1110_0111])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_three_byte_values() -> IonResult<()> {
        var_uint_encoding_test(81_991, &[0b0000_0101, 0b0000_0000, 0b1100_0111])?;
        var_uint_encoding_test(400_600, &[0b0001_1000, 0b0011_1001, 0b1101_1000])?;
        Ok(())
    }
}
