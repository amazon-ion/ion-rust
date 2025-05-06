use crate::result::IonFailure;
use crate::{IonResult, UInt};
use bumpalo::collections::Vec as BumpVec;
use ice_code::ice as cold_path;
use std::io::Write;

const BITS_PER_U128: usize = 128;
const BITS_PER_ENCODED_BYTE: usize = 7;

// Compile-time mapping from number of leading zeros to the number of bytes needed to encode
const fn init_bytes_needed_cache() -> [u8; 129] {
    let mut cache = [0u8; 129];
    let mut leading_zeros = 0usize;
    while leading_zeros < BITS_PER_U128 {
        let magnitude_bits_needed = 128 - leading_zeros;
        cache[leading_zeros] = magnitude_bits_needed.div_ceil(BITS_PER_ENCODED_BYTE) as u8;
        leading_zeros += 1;
    }
    // Special case: 128 leading zeros means it's `0i128`, which requires one byte.
    cache[128] = 1;
    cache
}

static BYTES_NEEDED_CACHE: [u8; 129] = init_bytes_needed_cache();

/// An Ion 1.1 encoding primitive that represents a variable-length unsigned integer.
#[derive(Debug)]
pub struct FlexUInt {
    value: u64,
    size_in_bytes: usize,
}

impl FlexUInt {
    pub(crate) fn new(size_in_bytes: usize, value: u64) -> Self {
        Self {
            value,
            size_in_bytes,
        }
    }

    /// Reads a [`FlexUInt`] from the buffer.
    ///
    /// `input` is the byte slice from which to read a `FlexUInt`.
    /// `offset` is the position of the slice in some larger input stream. It is only used to populate
    ///          an appropriate error message if reading fails.
    #[inline(always)]
    pub fn read(input: &[u8], offset: usize) -> IonResult<FlexUInt> {
        const COMMON_CASE_INPUT_BYTES_NEEDED: usize = 4;
        // We want to minimize the number of branches that happen in the common case. To do this,
        // we perform a single length check, making sure that the buffer contains enough data to
        // represent a FlexUInt whose continuation bits fit in a single byte (i.e. one with 7 or
        // fewer bytes of magnitude). If the buffer doesn't have at least 4 bytes in it or the
        // FlexUInt we find requires more than 4 bytes to represent, we'll fall back to the general
        // case.
        if input.len() >= COMMON_CASE_INPUT_BYTES_NEEDED {
            'common_case: {
                let num_encoded_bytes = input[0].trailing_zeros() as usize + 1;
                // By branching on particular values, we make the value of `num_encoded_bytes` in their
                // corresponding arm `const`. This allows us to use `read_n_bytes` to optimize for those
                // sizes.
                let mut buffer = [0u8; size_of::<u64>()];
                match num_encoded_bytes {
                    1 => Self::read_n_bytes::<1>(input, &mut buffer),
                    2 => Self::read_n_bytes::<2>(input, &mut buffer),
                    3 => Self::read_n_bytes::<3>(input, &mut buffer),
                    4 => Self::read_n_bytes::<4>(input, &mut buffer),
                    // If the number of encoded bytes isn't 1-4, fall back to the general-purpose
                    // reading logic.
                    _ => break 'common_case,
                };
                let value = u64::from_le_bytes(buffer).wrapping_shr(num_encoded_bytes as u32);
                let flex_uint = FlexUInt::new(num_encoded_bytes, value);
                return Ok(flex_uint);
            }
        }
        // General-purpose FlexUInt reading logic. Checks for empty input and supports FlexUInts
        // up to U64::MAX.
        Self::read_flex_primitive_as_uint(input, offset, "reading a FlexUInt")
    }

    #[inline]
    pub fn read_n_bytes<const NUM_BYTES: usize>(bytes: &[u8], buffer: &mut [u8; size_of::<u64>()]) {
        let input: [u8; NUM_BYTES] = *(bytes.first_chunk::<NUM_BYTES>().unwrap());
        *buffer.first_chunk_mut::<NUM_BYTES>().unwrap() = input;
    }

    pub(crate) fn read_flex_primitive_as_uint(
        input: &[u8],
        offset: usize,
        label: &'static str,
    ) -> IonResult<FlexUInt> {
        // A closure that generates an incomplete data result at the current offset. This can be invoked
        // in a variety of early-return cases in this method.
        let incomplete = || IonResult::incomplete(label, offset);

        let bytes_available = input.len();
        if bytes_available == 0 {
            return incomplete();
        }

        let num_encoded_bytes = match input[0] {
            // If the first byte is zero, we're not done reading the length bits yet.
            // Confirm that we have more than just one byte remaining in input.
            0 if input.len() == 1 => return incomplete(),
            // The number of trailing zeros in the second byte plus the 8 trailing
            // zeros from the first byte.
            0 => (input[1].trailing_zeros() as usize + 1) + 8,
            // Otherwise, use the number of trailing zeros from the first byte.
            first_byte => first_byte.trailing_zeros() as usize + 1,
        };

        if num_encoded_bytes > 10 {
            return IonResult::decoding_error(
                "maximum supported serialized FlexUInt size is 10 bytes",
            );
        }
        if num_encoded_bytes > input.len() {
            return incomplete();
        }
        let mut buffer = [0u8; size_of::<u128>()];
        (&mut buffer[..num_encoded_bytes]).copy_from_slice(&input[..num_encoded_bytes]);
        let big_value = u128::from_le_bytes(buffer).wrapping_shr(num_encoded_bytes as u32);
        let value = big_value as u64;
        Ok(FlexUInt::new(num_encoded_bytes, value))
    }

    #[inline]
    pub(crate) fn encode_opcode_and_length(output: &mut BumpVec<'_, u8>, opcode: u8, length: u64) {
        // In the common case, the length fits in a single FlexUInt byte. We can perform a single
        // `reserve`/`memcopy` to get both the opcode and the length into the buffer.
        if length < 127 {
            let flex_uint_byte = (length << 1) as u8 + 1;
            return output.extend_from_slice_copy(&[opcode, flex_uint_byte]);
        }

        // If there's call for it, we could also do this for 2-byte FlexUInts. For now, we fall
        // back to the general-purpose.
        cold_path! { encode_opcode_and_length_general_case => {
            output.push(opcode);
            let _ = FlexUInt::write(output, length).unwrap();
        }}
    }

    // This is capped at 14 bytes to simplify encoding. FlexUInt values up to 14 bytes (2^112 - 1)
    // can be encoded entirely within a u128, which offers native shifting and masking operations.
    // FlexUInts are used to represent symbol/macro table addresses and byte lengths, so 112 bits of
    // magnitude should be sufficient for all but the most extreme use cases.
    const MAX_FLEX_UINT_ENCODED_SIZE_IN_BYTES: usize = size_of::<u128>();

    #[inline]
    pub fn write<W: Write>(output: &mut W, value: impl Into<UInt>) -> IonResult<usize> {
        let value = value.into().data;
        let leading_zeros = value.leading_zeros();
        let num_encoded_bytes = BYTES_NEEDED_CACHE[leading_zeros as usize] as usize;
        if num_encoded_bytes <= Self::MAX_FLEX_UINT_ENCODED_SIZE_IN_BYTES {
            let flag_bits = 1u128 << (num_encoded_bytes - 1);
            // Left shift the value to accommodate the trailing flag bits and then OR them together
            let encoded_value = (value << num_encoded_bytes) | flag_bits;
            output.write_all(&encoded_value.to_le_bytes()[..num_encoded_bytes])?;
            return Ok(num_encoded_bytes);
        }
        IonResult::encoding_error("found a FlexUInt that was larger than the current limit")
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
    use crate::lazy::binary::binary_buffer::BinaryBuffer;
    use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
    use crate::{EncodingContext, IonError, IonResult, IonVersion};

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
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
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
            let (flex_uint, _remaining) =
                BinaryBuffer::new(context.get_ref(), encoding).read_flex_uint()?;
            let actual_value = flex_uint.value();
            assert_eq!(actual_value, expected_value, "actual value {actual_value} was != expected value {expected_value} for encoding {encoding:x?}")
        }
        Ok(())
    }

    #[test]
    fn encode_flex_uint() -> IonResult<()> {
        for (value, expected_encoding) in FLEX_UINT_TEST_CASES {
            let mut buffer = Vec::new();
            FlexUInt::write(&mut buffer, *value)?;
            let encoding = buffer.as_slice();
            assert_eq!(encoding, *expected_encoding, "[u64] actual encoding {encoding:x?} was != expected encoding {expected_encoding:x?} for value {value}");
        }
        // Convert each of the u64s above to BigUints and confirm that the encodings are still correct
        for (value, expected_encoding) in FLEX_UINT_TEST_CASES {
            let mut buffer = Vec::new();
            FlexUInt::write(&mut buffer, *value)?;
            let encoding = buffer.as_slice();
            assert_eq!(encoding, *expected_encoding, "[BigUint] actual encoding {encoding:x?} was != expected encoding {expected_encoding:x?} for value {value}");
        }
        Ok(())
    }

    #[test]
    fn detect_incomplete_flex_uint() {
        let context = EncodingContext::for_ion_version(IonVersion::v1_0);
        for (_value, expected_encoding) in FLEX_UINT_TEST_CASES {
            // Exhaustively check incomplete input detection by trying to read all prefixes of a test
            // value's complete encoding.
            for end in 0..expected_encoding.len() - 1 {
                let partial_encoding =
                    BinaryBuffer::new(context.get_ref(), &expected_encoding[..end]);
                assert!(matches!(
                    partial_encoding.read_flex_uint(),
                    Err(IonError::Incomplete(_))
                ));
            }
        }
    }
}
