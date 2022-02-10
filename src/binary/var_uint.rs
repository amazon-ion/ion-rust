use crate::data_source::IonDataSource;
use crate::result::{decoding_error, IonResult};
use std::io::{Read, Write};
use std::mem;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarUInt's magnitude and byte length in the future.
// See: https://github.com/amzn/ion-rust/issues/7
pub type VarUIntStorage = usize;
pub type VarUIntSizeStorage = usize;

const BITS_PER_ENCODED_BYTE: usize = 7;
const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<VarUIntStorage>() * 8;
const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

const LOWER_7_BITMASK: u8 = 0b0111_1111;
const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

/// Represents a variable-length unsigned integer. See the
/// [VarUInt and VarInt Fields](amzn.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug, Default)]
pub struct VarUInt {
    value: VarUIntStorage,
    size_in_bytes: VarUIntSizeStorage,
}

impl VarUInt {
    /// Reads a VarUInt from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R) -> IonResult<VarUInt> {
        let mut magnitude: VarUIntStorage = 0;

        let mut byte_processor = |byte: u8| {
            let lower_seven = (LOWER_7_BITMASK & byte) as VarUIntStorage;
            magnitude <<= 7; // Shifts 0 to 0 in the first iteration
            magnitude |= lower_seven;
            byte < HIGHEST_BIT_VALUE // If the highest bit is zero, continue reading
        };

        let encoded_size_in_bytes = data_source.read_next_byte_while(&mut byte_processor)?;

        // Prevent overflow by checking that the VarUInt was not too large to safely fit in the
        // data type being used to house the decoded value.
        //
        // This approach has two drawbacks:
        // * When using a u64, we only allow up to 63 bits of encoded magnitude data.
        // * It will return an error for inefficiently-encoded small values that use more bytes
        //   than required. (e.g. A 10-byte encoding of the number 0 will be rejected.)
        //
        // However, reading VarUInt values is a very hot code path for reading binary Ion. This
        // compromise allows us to prevent overflows for the cost of a single branch per VarUInt
        // rather than performing extra bookkeeping logic on a per-byte basis.
        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte VarUInt. Max supported size is {} bytes.",
                encoded_size_in_bytes, MAX_ENCODED_SIZE_IN_BYTES
            ));
        }

        Ok(VarUInt {
            size_in_bytes: encoded_size_in_bytes,
            value: magnitude,
        })
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
    pub fn value(&self) -> VarUIntStorage {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// unsigned integer
    #[inline(always)]
    pub fn size_in_bytes(&self) -> VarUIntSizeStorage {
        self.size_in_bytes
    }

    pub fn write_new_var_uint<W: Write>(sink: &mut W, value: u64) -> IonResult<usize> {
        const BITS_PER_BYTE: u32 = 8;
        // The header byte containing 'packed' continuation bits.
        const HEADER_MASKS: &[u64] = &[
            // A 1-byte value; the first bit is set to 1, indicating it is the last byte.
            0b1000_0000,
            // A 2-byte value; the second bit is set to 1, indicating the next byte is the last.
            0b0100_0000 << (BITS_PER_BYTE * 1),
            // A 3-byte value; the third bit is set to 1, indicating two more bytes follow.
            0b0010_0000 << (BITS_PER_BYTE * 2),
            // ... and so on.
            0b0001_0000 << (BITS_PER_BYTE * 3),
            0b0000_1000 << (BITS_PER_BYTE * 4),
            0b0000_0100 << (BITS_PER_BYTE * 5),
            0b0000_0010 << (BITS_PER_BYTE * 6),
            0b0000_0001 << (BITS_PER_BYTE * 7),
        ];
        const SIZE_OF_U64_IN_BYTES: u32 = 8;

        let leading_zeros = value.leading_zeros();
        let empty_bits_in_leading_byte = leading_zeros % BITS_PER_BYTE;
        let encoded_size_in_bytes = SIZE_OF_U64_IN_BYTES - (leading_zeros / BITS_PER_BYTE);

        if encoded_size_in_bytes < empty_bits_in_leading_byte {
            // The first byte of `value` has enough empty (zero) bits at the beginning to hold the
            // header. Do a bitwise `or` with the appropriate header from the table above.
            let encoded_value = value | HEADER_MASKS[encoded_size_in_bytes as usize - 1];
            // Turn the value into a &[u8] containing big endian bytes.
            let all_bytes = &encoded_value.to_be_bytes();
            // Take a subslice of the array to ignore any leading zero bytes.
            let occupied_bytes = &all_bytes[all_bytes.len() - (encoded_size_in_bytes as usize)..];
            sink.write_all(occupied_bytes)?;
            Ok(occupied_bytes.len())
        } else if encoded_size_in_bytes == SIZE_OF_U64_IN_BYTES {
            // The value is large enough that none of its leading bytes are zero.
            if empty_bits_in_leading_byte >= 1 {
                // The first bit is empty; write a 0-byte indicating 8 non-terminal bytes...
                sink.write_all(&[0])?;
                // ... then set the first bit of `value` to 1 to complete the header.
                sink.write_all(&((1 << 63) | value).to_be_bytes())?;
                Ok(9)
            } else {
                // The value is 8 bytes long AND the first bit is a 1. We can't squeeze any part of
                // the header into the value's in-memory representation. Write the header...
                sink.write_all(&[0, 0b1000_0000])?;
                // ... and then write the value itself as big endian bytes.
                sink.write_all(&value.to_be_bytes())?;
                Ok(10)
            }
        } else {
            // The value is shorter than 8 bytes, but there's no room for the header in the first
            // encoded byte. We need to write a header byte and then the body.
            let header_mask = HEADER_MASKS[encoded_size_in_bytes as usize];
            let encoded_value = value | header_mask;
            let all_bytes = &encoded_value.to_be_bytes();
            let occupied_bytes = &all_bytes[all_bytes.len() - (encoded_size_in_bytes as usize + 1)..];
            sink.write_all(occupied_bytes)?;
            Ok(occupied_bytes.len())
        }
    }
    pub fn read_new_var_uint<R: IonDataSource>(data_source: &mut R) -> IonResult<VarUInt> {
        const BITS_PER_BYTE: u32 = 8;
        const HEADER_MASKS: &[u8] = &[
            0b0111_1111,
            0b0011_1111,
            0b0001_1111,
            0b0000_1111,
            0b0000_0111,
            0b0000_0011,
            0b0000_0001,
        ];
        const SIZE_OF_U64_IN_BYTES: u32 = 8;

        // Read the first byte. (Technically the header could be multiple bytes, but not in this
        // implementation.)
        let header = data_source.next_byte()?.unwrap();
        // The number of leading zeros in the header byte is the number of bytes that follow it in
        // the input stream.
        let leading_zeros = header.leading_zeros();

        // This will hold our decoded value.
        let mut buffer = [0u8; 8];

        if leading_zeros >= 8 {
            // This is important for correctness but not for this performance test.
            todo!("Handle VarUInts with 8 or 9 bytes.");
        }

        // Place the header byte in the buffer using the number leading zeros we read to determine
        // how large the decoded u64 will be.
        let header_position = 8 - leading_zeros - 1;
        buffer[header_position as usize] = header & HEADER_MASKS[leading_zeros as usize];

        // Populate the rest of the buffer from the input stream.
        let mut read_buffer = &mut buffer[(header_position+1) as usize..];
        data_source.read_exact(read_buffer)?;
        let bytes_read = 1 + read_buffer.len();

        // Convert the buffer's contents into a u64
        let magnitude: u64 = u64::from_be_bytes(buffer);

        Ok(VarUInt { value: magnitude as usize, size_in_bytes: bytes_read})
    }
}

#[cfg(test)]
mod tests {
    use std::io;
    use super::VarUInt;
    use crate::result::IonResult;
    use std::io::{BufReader, Cursor};

    const ERROR_MESSAGE: &str = "Failed to read a VarUInt from the provided data.";

    #[test]
    fn test_read_var_uint() {
        let var_uint = VarUInt::read(&mut Cursor::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]))
            .expect(ERROR_MESSAGE);
        assert_eq!(3, var_uint.size_in_bytes());
        assert_eq!(1_984_385, var_uint.value());
    }

    #[test]
    fn test_read_var_uint_small_buffer() {
        let var_uint = VarUInt::read(
            // Construct a BufReader whose input buffer cannot hold all of the data at once
            // to ensure that reads that span multiple I/O operations work as expected
            &mut BufReader::with_capacity(1, Cursor::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001])),
        )
        .expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 3);
        assert_eq!(var_uint.value(), 1_984_385);
    }

    #[test]
    fn test_read_var_uint_zero() {
        let var_uint = VarUInt::read(&mut Cursor::new(&[0b1000_0000])).expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 1);
        assert_eq!(var_uint.value(), 0);
    }

    #[test]
    fn test_read_var_uint_two_bytes_max_value() {
        let var_uint =
            VarUInt::read(&mut Cursor::new(&[0b0111_1111, 0b1111_1111])).expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 2);
        assert_eq!(var_uint.value(), 16_383);
    }

    #[test]
    fn test_read_var_uint_overflow_detection() {
        let _var_uint = VarUInt::read(&mut Cursor::new(&[
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

    #[test]
    fn test_new_var_uint() -> IonResult<()> {
        let value: u64 = 202233312022;

        let mut buffer = Vec::with_capacity(64);
        let bytes_written = VarUInt::write_new_var_uint(&mut buffer, 202233312022).unwrap();
        println!("{buffer:x?}");
        assert_eq!(6, bytes_written);

        let read_buffer = &buffer[0..bytes_written];
        let var_uint = VarUInt::read_new_var_uint(&mut io::Cursor::new(read_buffer)).unwrap();
        assert_eq!(value, var_uint.value as u64);
        Ok(())
    }
}
