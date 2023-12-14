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

    /// Encodes `value` as a `FlexUInt` and writes the resulting bytes to `output`.
    #[inline]
    pub fn write_u64<W: Write>(output: &mut W, value: u64) -> IonResult<usize> {
        // This method is on the hot path for encoding Ion. As an optimization, this implementation
        // checks up front for the most common case in which `value` requires 1-2 bytes to encode.
        // If it will take more, the method delegates to `write_u64_slow`, a general-purpose
        // encoding method that can handle any size of value. This arrangement allows the compiler
        // to inline the logic for the 1- and 2-byte cases at most call sites while still accommodating
        // larger FlexUInts via delegation.

        if value < 0x80 {
            // The value to encode fits in a single byte
            output.write_all(&[(value * 2) as u8 + 1])?;
            return Ok(1);
        } else if value < 0x4000 {
            // The value to encode fits in two bytes
            output.write_all(&((value * 4) as u16 + 2u16).to_le_bytes())?;
            return Ok(2);
        }
        Self::write_u64_slow(output, value)
    }

    #[cold]
    fn write_u64_slow<W: Write>(output: &mut W, value: u64) -> IonResult<usize> {
        // The value requires 3 or more bytes, fall back to a general-purpose
        let leading_zeros = value.leading_zeros();
        let num_encoded_bytes = BYTES_NEEDED_CACHE[leading_zeros as usize] as usize;

        match num_encoded_bytes {
            0..=8 => {
                // When encoded, the continuation flags and the value all fit in 8 bytes. We can encode
                // everything in a u64 and then write it to output.
                //
                // There's one continuation flag bit for each encoded byte. To set the bits:
                // * Left shift a `1` by the number of bytes minus one.
                //
                // For example, if `num_encoded_bytes` is 5, then:
                //   1 << 4   =>   1 0000
                //      End flag --^ ^^^^-- Four more bytes follow
                let flag_bits = 1u64 << (num_encoded_bytes - 1);
                // Left shift the value to accommodate the trailing flag bits and then OR them together
                let encoded_value = (value << num_encoded_bytes) | flag_bits;
                output.write_all(&encoded_value.to_le_bytes()[..num_encoded_bytes])?;
                Ok(num_encoded_bytes)
            }
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
                output.write_all(buffer.as_slice()).unwrap();
                Ok(10)
            }
            _ => unreachable!("a u64 value cannot have more than 64 magnitude bits"),
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
        (0u64, &[0b00000001]),
        (1u64, &[0b00000011]),
        (2u64, &[0b00000101]),
        (3u64, &[0b00000111]),
        (4u64, &[0b00001001]),
        (5u64, &[0b00001011]),
        (14u64, &[0b00011101]),
        (63u64, &[0b01111111]),
        (64u64, &[0b10000001]),
        (127u64, &[0b11111111]),
        (128u64, &[0b00000010, 0b00000010]),
        (729u64, &[0b01100110, 0b00001011]),
        (16383u64, &[0b11111110, 0b11111111]),
        (16384u64, &[0b00000100, 0b00000000, 0b00000010]),
        (2097151u64, &[0b11111100, 0b11111111, 0b11111111]),
        (
            2097152u64,
            &[0b00001000, 0b00000000, 0b00000000, 0b00000010],
        ),
        (
            268435455u64,
            &[0b11111000, 0b11111111, 0b11111111, 0b11111111],
        ),
        (
            268435456u64,
            &[0b00010000, 0b00000000, 0b00000000, 0b00000000, 0b00000010],
        ),
        (
            34359738368u64,
            &[
                0b00100000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000010,
            ],
        ),
        (
            4398046511104u64,
            &[
                0b01000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000010,
            ],
        ),
        (
            562949953421311u64,
            &[
                0b11000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
            ],
        ),
        (
            562949953421312u64,
            &[
                0b10000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000010,
            ],
        ),
        (
            72057594037927935u64,
            &[
                0b10000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111,
            ],
        ),
        (
            72057594037927936u64,
            &[
                0b00000000, 0b00000001, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000000, 0b00000010,
            ],
        ),
        (
            9223372036854775807u64,
            &[
                0b00000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b11111111,
            ],
        ),
    ];

    #[test]
    fn decode_flex_uint() -> IonResult<()> {
        for (expected_value, encoding) in FLEX_UINT_TEST_CASES {
            let (flex_uint, _remaining) = ImmutableBuffer::new(encoding).read_flex_uint()?;
            let actual_value = flex_uint.value();
            assert_eq!(actual_value, *expected_value, "actual value {actual_value} was != expected value {expected_value} for encoding {encoding:x?}")
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
