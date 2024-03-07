use crate::{FlexUInt, IonResult};
use bumpalo::collections::Vec as BumpVec;
use ice_code::ice as cold_path;
use std::io::Write;

const BITS_PER_I64: usize = 64;
const BITS_PER_ENCODED_BYTE: usize = 7;

// Compile-time mapping from number of leading zeros to the number of bytes needed to encode
const fn init_bytes_needed_cache() -> [u8; 65] {
    let mut cache = [0u8; 65];
    let mut leading_zeros = 0usize;
    while leading_zeros <= BITS_PER_I64 {
        let magnitude_bits_needed = BITS_PER_I64 - leading_zeros;
        let encoded_size_in_bytes = (magnitude_bits_needed / BITS_PER_ENCODED_BYTE) + 1;
        cache[leading_zeros] = encoded_size_in_bytes as u8;
        leading_zeros += 1;
    }
    cache
}

// Indexes are the number of leading ones (for negative ints) or the number of leading zeros (for
// non-negative ints), values are the number of bytes needed to encode that value as a FlexInt.
static BYTES_NEEDED_CACHE: [u8; 65] = init_bytes_needed_cache();

/// An Ion 1.1 encoding primitive that represents a variable-length signed integer.
#[derive(Debug)]
pub struct FlexInt {
    value: i64,
    size_in_bytes: usize,
}

impl FlexInt {
    fn new(size_in_bytes: usize, value: i64) -> Self {
        Self {
            value,
            size_in_bytes,
        }
    }

    /// Reads a [`FlexInt`] from the buffer.
    ///
    /// `input` is the byte slice from which to read a `FlexInt`.
    /// `offset` is the position of the slice in some larger input stream. It is only used to populate
    ///          an appropriate error message if reading fails.
    #[inline]
    pub fn read(input: &[u8], offset: usize) -> IonResult<FlexInt> {
        // A FlexInt has the same structure as a FlexUInt. We can read a FlexUInt and then re-interpret
        // its unsigned bytes as two's complement bytes.
        let flex_uint =
            FlexUInt::read_flex_primitive_as_uint(input, offset, "reading a FlexInt", true)?;
        let unsigned_value = flex_uint.value();

        // If the encoded FlexInt required `N` bytes to encode where `N` is fewer than 8, then its
        // u64 value will have `8 - N` leading zero bytes. If the highest bit in the encoding was a
        // 1, then then number is negative and we need to flip all of those leading zeros to ones.
        // Look at the original input to see if the highest bit was a zero (positive) or one (negative).
        let last_explicit_byte = input[flex_uint.size_in_bytes() - 1];
        let sign_bit = 0b1000_0000 & last_explicit_byte;
        let signed_value = if sign_bit == 0 {
            unsigned_value as i64
        } else {
            // Flip all of the leading zeros in the unsigned value to ones and then re-interpret it
            // as a signed value.
            let mask = ((1u64 << 63) as i64) >> unsigned_value.leading_zeros();
            (unsigned_value as i64) | mask
        };
        Ok(FlexInt::new(flex_uint.size_in_bytes(), signed_value))
    }

    // This is equivalent to calling `write_i64(my_bump_vec).unwrap()`, but optimized for writing
    // to a `BumpVec` instead of a `W: Write`. Writing to a BumpVec cannot fail (barring out-of-
    // memory errors and the like), which eliminates some branching, a loop inside
    // `io::Write::write_all`, and the construction of a return value.
    #[inline]
    pub fn encode_i64(output: &mut BumpVec<u8>, value: i64) {
        let encoded_size_in_bytes = if value < 0 {
            BYTES_NEEDED_CACHE[value.leading_ones() as usize]
        } else {
            BYTES_NEEDED_CACHE[value.leading_zeros() as usize]
        } as usize;
        if encoded_size_in_bytes <= 8 {
            // The entire encoding (including continuation bits) will fit in a u64.
            // `encoded_size_in_bytes` is also the number of continuation bits we need to include
            let mut encoded = value << encoded_size_in_bytes;
            // Set the `end` flag to 1
            encoded += 1 << (encoded_size_in_bytes - 1);
            output.extend_from_slice_copy(&encoded.to_le_bytes()[..encoded_size_in_bytes]);
            return;
        }
        cold_path! {{
            let _ = Self::write_large_i64(output, value, encoded_size_in_bytes);
        }}
    }

    #[inline]
    pub fn write_i64<W: Write>(output: &mut W, value: i64) -> IonResult<usize> {
        let encoded_size_in_bytes = if value < 0 {
            BYTES_NEEDED_CACHE[value.leading_ones() as usize]
        } else {
            BYTES_NEEDED_CACHE[value.leading_zeros() as usize]
        } as usize;
        if encoded_size_in_bytes <= 8 {
            // The entire encoding (including continuation bits) will fit in a u64.
            // `encoded_size_in_bytes` is also the number of continuation bits we need to include
            let mut encoded = value << encoded_size_in_bytes;
            // Set the `end` flag to 1
            encoded += 1 << (encoded_size_in_bytes - 1);
            output.write_all(&encoded.to_le_bytes()[..encoded_size_in_bytes])?;
            return Ok(encoded_size_in_bytes);
        }
        cold_path! {
            Self::write_large_i64(output, value, encoded_size_in_bytes)
        }
    }

    /// Helper method that encodes a signed values that require 9 or 10 bytes to represent.
    /// This code path is rarely used and requires more instructions than the common case.
    /// Keeping it in a separate method allows the common case to be inlined in more places.
    fn write_large_i64<W: Write>(
        output: &mut W,
        value: i64,
        encoded_size_in_bytes: usize,
    ) -> IonResult<usize> {
        match encoded_size_in_bytes {
            9 => {
                // Write a byte that is only continuation bits--a zero.
                output.write_all(&[0x00])?;
                // Shift the value left by one and set the low bit to 1 as an end flag
                let encoded = (value << 1) + 1;
                // Write out the end flag and the value itself (which must be 8 bytes long)
                output.write_all(&encoded.to_le_bytes())?;
            }
            10 => {
                // Set up a stack-allocated buffer to hold our encoding. This allows us to call
                // `output.write_all()` a single time.
                let mut buffer: [u8; 10] = [0; 10];
                // The first byte in the encoding is always 0x00, indicating that at least 8 more bytes
                // follow. The second byte has two more continuation flag bits (`10`), indicating that
                // the whole value is 10 bytes long. We can fit 6 bits of magnitude in this second byte.
                buffer[1] = ((value & 0b111111) << 2) as u8 | 0b10u8;

                // The remaining 58 bits of magnitude can be encoded in a u64.
                // Because `value` is signed (i64), shifting it right will carry in sign bits from
                // the left, preserving the resulting value's sign.
                let remaining_magnitude: i64 = value >> 6;
                buffer[2..].copy_from_slice(&remaining_magnitude.to_le_bytes()[..]);

                // Call `write_all()` once with our complete encoding.
                output.write_all(buffer.as_slice())?;
            }
            _ => unreachable!(
                "write_large_i64() is only called for values whose encoded size is 9 or 10 bytes"
            ),
        };
        Ok(encoded_size_in_bytes)
    }

    pub fn value(&self) -> i64 {
        self.value
    }
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
    use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;
    use crate::{IonError, IonResult};
    const FLEX_INT_TEST_CASES: &[(i64, &[u8])] = &[
        (0i64, &[0b00000001u8]),
        (1, &[0b00000011]),
        (2, &[0b00000101]),
        (3, &[0b00000111]),
        (4, &[0b00001001]),
        (5, &[0b00001011]),
        (14, &[0b00011101]),
        (63, &[0b01111111]),
        (64, &[0b00000010, 0b00000001]),
        (729, &[0b01100110, 0b00001011]),
        (8191, &[0b11111110, 0b01111111]),
        (8192, &[0b00000100, 0b00000000, 0b00000001]),
        (1048575, &[0b11111100, 0b11111111, 0b01111111]),
        (1048576, &[0b00001000, 0b00000000, 0b00000000, 0b00000001]),
        (134217727, &[0b11111000, 0b11111111, 0b11111111, 0b01111111]),
        (
            134217728,
            &[0b00010000, 0b00000000, 0b00000000, 0b00000000, 0b00000001],
        ),
        (
            17179869184,
            &[
                0b00100000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000001,
            ],
        ),
        (
            2199023255552,
            &[
                0b01000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000001,
            ],
        ),
        (
            281474976710655,
            &[
                0b11000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111,
            ],
        ),
        (
            281474976710656,
            &[
                0b10000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000001,
            ],
        ),
        (
            36028797018963967,
            &[
                0b10000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b01111111,
            ],
        ),
        (
            36028797018963968,
            &[
                0b00000000, 0b00000001, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000000, 0b00000001,
            ],
        ),
        (
            4611686018427387903,
            &[
                0b00000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b01111111,
            ],
        ),
        (
            4611686018427387904,
            &[
                0b00000000, 0b00000010, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000000, 0b00000000, 0b00000001,
            ],
        ),
        (
            9223372036854775807,
            &[
                0b00000000, 0b11111110, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b11111111, 0b00000001,
            ],
        ),
        (-1, &[0b11111111]),
        (-2, &[0b11111101]),
        (-3, &[0b11111011]),
        (-14, &[0b11100101]),
        (-64, &[0b10000001]),
        (-65, &[0b11111110, 0b11111110]),
        (-729, &[0b10011110, 0b11110100]),
        (-8192, &[0b00000010, 0b10000000]),
        (-8193, &[0b11111100, 0b11111111, 0b11111110]),
        (-1048576, &[0b00000100, 0b00000000, 0b10000000]),
        (-1048577, &[0b11111000, 0b11111111, 0b11111111, 0b11111110]),
        (
            -134217728,
            &[0b00001000, 0b00000000, 0b00000000, 0b10000000],
        ),
        (
            -134217729,
            &[0b11110000, 0b11111111, 0b11111111, 0b11111111, 0b11111110],
        ),
        (
            -17179869184,
            &[0b00010000, 0b00000000, 0b00000000, 0b00000000, 0b10000000],
        ),
        (
            -17179869185,
            &[
                0b11100000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111110,
            ],
        ),
        (
            -281474976710656,
            &[
                0b01000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000,
            ],
        ),
        (
            -281474976710657,
            &[
                0b10000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111110,
            ],
        ),
        (
            -36028797018963968,
            &[
                0b10000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b10000000,
            ],
        ),
        (
            -36028797018963969,
            &[
                0b00000000, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b11111110,
            ],
        ),
        (
            -4611686018427387904,
            &[
                0b00000000, 0b00000001, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000000, 0b10000000,
            ],
        ),
        (
            -4611686018427387905,
            &[
                0b00000000, 0b11111110, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b11111111, 0b11111111, 0b11111110,
            ],
        ),
        (
            -9223372036854775808,
            &[
                0b00000000, 0b00000010, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000000, 0b00000000, 0b11111110,
            ],
        ),
    ];

    #[test]
    fn decode_flex_int() -> IonResult<()> {
        for (expected_value, encoding) in FLEX_INT_TEST_CASES {
            let (flex_int, _remaining) = ImmutableBuffer::new(encoding).read_flex_int()?;
            let actual_value = flex_int.value();
            assert_eq!(actual_value, *expected_value, "actual value {actual_value} was != expected value {expected_value} for encoding {encoding:x?}")
        }
        Ok(())
    }

    #[test]
    fn encode_flex_int() -> IonResult<()> {
        for (value, expected_encoding) in FLEX_INT_TEST_CASES {
            let mut buffer = Vec::new();
            FlexInt::write_i64(&mut buffer, *value)?;
            let encoding = buffer.as_slice();
            assert_eq!(encoding, *expected_encoding, "actual encoding {encoding:x?} was != expected encoding {expected_encoding:x?} for value {value}");
        }
        Ok(())
    }

    #[test]
    fn detect_incomplete_flex_int() {
        for (_value, expected_encoding) in FLEX_INT_TEST_CASES {
            // Exhaustively check incomplete input detection by trying to read all prefixes of a test
            // value's complete encoding.
            for end in 0..expected_encoding.len() - 1 {
                let partial_encoding = ImmutableBuffer::new(&expected_encoding[..end]);
                assert!(matches!(
                    partial_encoding.read_flex_int(),
                    Err(IonError::Incomplete(_))
                ));
            }
        }
    }
}
