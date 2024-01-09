use crate::IonResult;
use std::io::Write;

const BITS_PER_U64: usize = 64;
const BITS_PER_ENCODED_BYTE: usize = 7;

// Compile-time mapping from number of leading zeros to the number of bytes needed to encode
const fn init_bytes_needed_cache() -> [u8; 65] {
    let mut cache = [0u8; 65];
    let mut leading_zeros = 0usize;
    while leading_zeros < BITS_PER_U64 {
        let magnitude_bits_needed = 64 - leading_zeros;
        cache[leading_zeros] =
            ((magnitude_bits_needed + BITS_PER_ENCODED_BYTE - 1) / BITS_PER_ENCODED_BYTE) as u8;
        leading_zeros += 1;
    }
    // Special case; 64 leading zeros means the value is zero. We need a byte to represent it.
    cache[64] = 1;
    cache
}

static BYTES_NEEDED_CACHE: [u8; 65] = init_bytes_needed_cache();

/// An Ion 1.1 encoding primitive that represents a variable-length unsigned integer.
#[derive(Debug)]
pub struct FlexUInt {
    value: u64,
    size_in_bytes: usize,
}

impl FlexUInt {
    pub fn new(size_in_bytes: usize, value: u64) -> Self {
        Self {
            value,
            size_in_bytes,
        }
    }

    #[inline]
    pub fn write_u64<W: Write>(output: &mut W, value: u64) -> IonResult<usize> {
        let leading_zeros = value.leading_zeros();
        let num_encoded_bytes = BYTES_NEEDED_CACHE[leading_zeros as usize] as usize;
        if num_encoded_bytes <= 8 {
            let flag_bits = 1u64 << (num_encoded_bytes - 1);
            // Left shift the value to accommodate the trailing flag bits and then OR them together
            let encoded_value = (value << num_encoded_bytes) | flag_bits;
            output.write_all(&encoded_value.to_le_bytes()[..num_encoded_bytes])?;
            return Ok(num_encoded_bytes);
        }
        Self::write_large_u64(output, value, num_encoded_bytes)
    }

    /// Helper method that encodes a signed values that require 9 or 10 bytes to represent.
    /// This code path is rarely used and requires more instructions than the common case.
    /// Keeping it in a separate method allows the common case to be inlined in more places.
    fn write_large_u64<W: Write>(
        output: &mut W,
        value: u64,
        encoded_size_in_bytes: usize,
    ) -> IonResult<usize> {
        match encoded_size_in_bytes {
            9 => {
                // When combined with the continuation flags, the value is too large to be encoded in
                // a u64. It will be nine bytes in all.
                //
                // Set up a stack-allocated buffer to hold our encoding. This allows us to call
                // `output.write_all()` a single time.
                let mut buffer: [u8; 9] = [0; 9];

                // The first byte will always be 0x00, indicating that 8 more bytes follow.
                //
                // We need to leave a `1` in the low bit of the second byte to be the End flag. Because
                // we need fewer than 64 bits for magnitude, we can encode the remainder of the data
                // in a u64.
                let encoded_value = (value << 1) + 1; // Leave a trailing `1` in the lowest bit
                buffer[1..].copy_from_slice(&encoded_value.to_le_bytes()[..]);
                output.write_all(buffer.as_slice())?;
                Ok(9)
            }
            10 => {
                // Set up a stack-allocated buffer to hold our encoding. This allows us to call
                // `output.write_all()` a single time.
                let mut buffer: [u8; 10] = [0; 10];
                // The first byte in the encoding is always 0x00, indicating that at least 8 more bytes
                // follow. The second byte has two more continuation flag bits (`10`), indicating that
                // the whole value is 10 bytes long. We can fit 6 bits of magnitude in this second byte.
                let second_byte = ((value & 0b111111) << 2) as u8 | 0b10u8;
                buffer[1] = second_byte;

                // The remaining 58 bits of magnitude can be encoded in a u64.
                let remaining_magnitude: u64 = value >> 6;
                buffer[2..].copy_from_slice(&remaining_magnitude.to_le_bytes()[..]);

                // Call `write_all()` once with our complete encoding.
                output.write_all(buffer.as_slice())?;
                Ok(10)
            }
            _ => unreachable!(
                "write_large_u64() is only called for values whose encoded size is 9 or 10 bytes"
            ),
        }
    }

    pub fn value(&self) -> u64 {
        self.value
    }

    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
    use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
    use crate::{IonError, IonResult};

    const FLEX_UINT_TEST_CASES: &[(u64, &[u8])] = &[
        (0, &[0b00000001]),
        (1, &[0b00000011]),
        (2, &[0b00000101]),
        (3, &[0b00000111]),
        (4, &[0b00001001]),
        (5, &[0b00001011]),
        (14, &[0b00011101]),
        (63, &[0b01111111]),
        (64, &[0b10000001]),
        (127, &[0b11111111]),
        (128, &[0b00000010, 0b00000010]),
        (729, &[0b01100110, 0b00001011]),
        (16383, &[0b11111110, 0b11111111]),
        (16384, &[0b00000100, 0b00000000, 0b00000010]),
        (2097151, &[0b11111100, 0b11111111, 0b11111111]),
        (2097152, &[0b00001000, 0b00000000, 0b00000000, 0b00000010]),
        (268435455, &[0b11111000, 0b11111111, 0b11111111, 0b11111111]),
        (
            268435456,
            &[0b00010000, 0b00000000, 0b00000000, 0b00000000, 0b00000010],
        ),
        (
            34359738368,
            &[
                0b00100000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000010,
            ],
        ),
        (
            4398046511104,
            &[
                0b01000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000010,
            ],
        ),
        (
            562949953421311,
            &[
                0b11000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
            ],
        ),
        (
            562949953421312,
            &[
                0b10000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000010,
            ],
        ),
        (
            72057594037927935,
            &[
                0b10000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111,
            ],
        ),
        (
            72057594037927936,
            &[
                0b00000000, 0b00000001, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000000, 0b00000010,
            ],
        ),
        (
            9223372036854775807,
            &[
                0b00000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b11111111,
            ],
        ),
    ];

    #[test]
    fn decode_flex_uint() -> IonResult<()> {
        let overpadded_test_cases: &[(u64, &[u8])] = &[
            // Over-padded 5
            (5, &[0b00010110, 0b00000000]),
            // Over-padded 128
            (128, &[0b00000100, 0b00000100, 0b00000000]),
        ];
        let mut flex_uint_tests = FLEX_UINT_TEST_CASES.to_vec();
        flex_uint_tests.extend_from_slice(overpadded_test_cases);
        for (expected_value, encoding) in flex_uint_tests {
            println!("-> {expected_value}");
            let (flex_uint, _remaining) = ImmutableBuffer::new(encoding).read_flex_uint()?;
            let actual_value = flex_uint.value();
            assert_eq!(actual_value, expected_value, "actual value {actual_value} was != expected value {expected_value} for encoding {encoding:x?}")
        }
        Ok(())
    }

    #[test]
    fn encode_flex_int() -> IonResult<()> {
        for (value, expected_encoding) in FLEX_UINT_TEST_CASES {
            let mut buffer = Vec::new();
            FlexUInt::write_u64(&mut buffer, *value)?;
            let encoding = buffer.as_slice();
            assert_eq!(encoding, *expected_encoding, "actual encoding {encoding:x?} was != expected encoding {expected_encoding:x?} for value {value}");
        }
        Ok(())
    }

    #[test]
    fn detect_incomplete_flex_uint() {
        for (_value, expected_encoding) in FLEX_UINT_TEST_CASES {
            // Exhaustively check incomplete input detection by trying to read all prefixes of a test
            // value's complete encoding.
            for end in 0..expected_encoding.len() - 1 {
                let partial_encoding = ImmutableBuffer::new(&expected_encoding[..end]);
                assert!(matches!(
                    partial_encoding.read_flex_uint(),
                    Err(IonError::Incomplete(_))
                ));
            }
        }
    }
}
