use crate::result::IonFailure;
use crate::{IonResult, UInt};
use bumpalo::collections::Vec as BumpVec;
use ice_code::ice as cold_path;
use std::io::Write;
use std::mem;

const BITS_PER_U128: usize = 128;
const BITS_PER_ENCODED_BYTE: usize = 7;

// Compile-time mapping from number of leading zeros to the number of bytes needed to encode
const fn init_bytes_needed_cache() -> [u8; 129] {
    let mut cache = [0u8; 129];
    let mut leading_zeros = 0usize;
    while leading_zeros < BITS_PER_U128 {
        let magnitude_bits_needed = 128 - leading_zeros;
        cache[leading_zeros] =
            ((magnitude_bits_needed + BITS_PER_ENCODED_BYTE - 1) / BITS_PER_ENCODED_BYTE) as u8;
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
    #[inline]
    pub fn read(input: &[u8], offset: usize) -> IonResult<FlexUInt> {
        const COMMON_CASE_INPUT_BYTES_NEEDED: usize = 8;

        // We want to minimize the number of branches that happen in the common case. To do this,
        // we perform a single length check, making sure that the buffer contains enough data to
        // represent a FlexUInt whose continuation bits fit in a single byte (i.e. one with 7 or
        // fewer bytes of magnitude). If the buffer doesn't have at least 8 bytes in it or the
        // FlexUInt we find requires more than 8 bytes to represent, we'll fall back to the general
        // case.
        if input.len() < COMMON_CASE_INPUT_BYTES_NEEDED || input[0] == 0 {
            // Calling `read_flex_primitive_as_uint_no_inline` keeps this method small enough that
            // the code for the common case can be inlined.
            return Self::read_flex_primitive_as_uint_no_inline(
                input,
                offset,
                "reading a FlexUInt",
                false,
            );
        }
        let flex_uint = Self::read_small_flex_uint(input);
        Ok(flex_uint)
    }

    /// Helper method that reads a [`FlexUInt`] with 7 or fewer bytes of magnitude from the buffer.
    // Caller must confirm that `bytes` has at least 8 bytes.
    #[inline]
    fn read_small_flex_uint(bytes: &[u8]) -> FlexUInt {
        debug_assert!(bytes.len() >= 8);
        let num_encoded_bytes = bytes[0].trailing_zeros() as usize + 1;
        let num_encoded_bits = 8 * num_encoded_bytes;
        // Get a mask with the low 'n' bits set
        // TODO: Should this be a const cache of num_encoded_bits -> mask?
        let mask = 1u64
            .checked_shl(num_encoded_bits as u32)
            .map(|v| v - 1)
            .unwrap_or(u64::MAX);
        // Convert our longer-than-8-bytes slice to a fixed sized 8-byte array that we can convert
        // to a u64 directly.
        let fixed_size_input: [u8; 8] = bytes[..8].try_into().unwrap();
        // This step will often read unrelated bytes from beyond the FlexUInt, but they are
        // discarded in the shift operation that follows.
        let encoded_value = u64::from_le_bytes(fixed_size_input);
        // Note that `num_encoded_bytes` is also the number of continuation flags that we need
        // to discard via right shifting.
        let value = (encoded_value & mask) >> num_encoded_bytes;
        FlexUInt::new(num_encoded_bytes, value)
    }

    #[inline(never)]
    pub(crate) fn read_flex_primitive_as_uint_no_inline(
        input: &[u8],
        offset: usize,
        label: &'static str,
        support_sign_extension: bool,
    ) -> IonResult<FlexUInt> {
        Self::read_flex_primitive_as_uint(input, offset, label, support_sign_extension)
    }

    /// Helper method that reads a flex-encoded primitive from the buffer, returning it as a `FlexUInt`.
    /// If an error occurs while reading, its description will include the supplied `label`.
    ///
    /// The current implementation supports flex primitives with up to 64 bits of representation
    /// beyond the leading header bits. Flex primitives requiring 10 bytes to encode have 70 magnitude
    /// bits. If this value is unsigned (`support_sign_extension=false`), the six bits beyond the
    /// supported 64 must all be `0`. If this value will later be re-interpreted as a signed value,
    /// (`support_sign_extension=true`), then the six bits beyond the supported 64 must all be the
    /// same as the 64th (highest supported) bit. This will allow encodings of up to 70 bits
    /// to be correctly interpreted as positive, negative, or beyond the bounds of the 64 bit
    /// limitation.
    pub(crate) fn read_flex_primitive_as_uint(
        input: &[u8],
        offset: usize,
        label: &'static str,
        support_sign_extension: bool,
    ) -> IonResult<FlexUInt> {
        // A closure that generates an incomplete data result at the current offset. This can be invoked
        // in a variety of early-return cases in this method.
        let incomplete = || IonResult::incomplete(label, offset);

        let bytes_available = input.len();
        if bytes_available == 0 {
            return incomplete();
        }

        // The `from_le_bytes` method we use to interpret data requires at least 8 bytes to be available.
        // There can be 1-2 bytes of header for a u64, leading to a maximum size of 10 bytes. If the input
        // buffer doesn't have at least 10 bytes, copy its contents into a temporary buffer that's
        // padded with 0 bytes. We round the size of the temp buffer to 16 as it produces slightly
        // nicer assembly than 10.
        let mut buffer = [0u8; 16];
        let bytes = if bytes_available >= 10 {
            input
        } else {
            buffer[0..bytes_available].copy_from_slice(input);
            &buffer[..]
        };

        let first_byte = bytes[0];
        // If the first byte is not zero, the FlexUInt is 7 or fewer bytes.
        if first_byte != 0 {
            let num_encoded_bytes = first_byte.trailing_zeros() as usize + 1;
            // Note that `bytes_available` is the number of bytes in the original unpadded input.
            // Our buffer may be 16 bytes long but only `bytes_available` of those are meaningful.
            if bytes_available < num_encoded_bytes {
                return incomplete();
            }
            // At this point, we know the original input contained all of the FlexUInt's bytes.
            // We can call `read_small_flex_uint` with the now-padded version of the buffer.
            // It will discard any bytes that are not part of the FlexUInt.
            let flex_uint = Self::read_small_flex_uint(bytes);
            return Ok(flex_uint);
        }

        cold_path! {{
            // If we reach this point, the first byte was a zero. The FlexUInt is at least 9 bytes in size.
            // We need to inspect the second byte to see how many more prefix bits there are.
            if bytes_available < 2 {
                return incomplete();
            }
            let second_byte = bytes[1];

            if second_byte & 0b11 == 0b00 {
                // The flag bits in the second byte indicate at least two more bytes, meaning the total
                // length is more than 10 bytes. We're not equipped to handle this.
                return IonResult::decoding_error(
                    "found a >10 byte Flex(U)Int too large to fit in 64 bits",
                );
            }

            if second_byte & 0b11 == 0b10 {
                // The lowest bit of the second byte is empty, the next lowest is not. The encoding
                // is 10 bytes.

                if bytes_available < 10 {
                    return incomplete();
                }

                let flex_uint = Self::read_10_byte_flex_primitive_as_uint(
                    support_sign_extension,
                    bytes,
                    second_byte,
                )?;
                return Ok(flex_uint);
            }

            // The lowest bit of the second byte is set. The encoding is 9 bytes.
            if bytes_available < 9 {
                return incomplete();
            }
            // There are 57-63 bits of magnitude. We can decode the remaining bytes in a u64.
            let remaining_data = &bytes[1..9];
            // We know that the slice is 8 bytes long, so we can unwrap() the conversion to [u8; 8]
            // Lop off the lowest bit to discard the `end` flag.
            let value = u64::from_le_bytes(remaining_data[..8].try_into().unwrap()) >> 1;
            let flex_uint = FlexUInt::new(9, value);
            Ok(flex_uint)
        }}
    }

    /// Helper method to handle flex primitives whose encoding requires 10 bytes. This case is
    /// complex because it requires evaluating data beyond the supported 64 bits of representation
    /// to detect overflow and support signed re-interpretation.
    fn read_10_byte_flex_primitive_as_uint(
        support_sign_extension: bool,
        input: &[u8],
        second_byte: u8,
    ) -> IonResult<FlexUInt> {
        // There are 10 prefix (continuation) bits, 64 bits of magnitude, and 6 bits of sign
        // extension (if enabled). We cannot store the highest 6 bits, so this method just checks
        // to make sure that they do not modify the meaning of the value in the lower 64 bits.
        // For signed values, this means the 6 extra bits must all be the same as the 64th bit.
        // For unsigned values, this means that the 6 extra bits must all be `0`.
        //
        // Little Endian byte diagram:
        //
        //      b0       b1       b2       b3
        //   PPPPPPPP MMMMMMPP MMMMMMMM MMMMMMMM
        //      b4       b5       b6       b7
        //   MMMMMMMM MMMMMMMM MMMMMMMM MMMMMMMM
        //      b8       b9
        //   MMMMMMMM XXXXXXMM
        //
        // P = Prefix bit
        // M = Magnitude bit
        // X = An 'extra' bit; if `support_sign_extension` is true, these are sign bits.

        // We've already processed the first byte, and we've looked at the lowest two bits of
        // the second byte. Isolate the highest six bits of the second byte (b1) which represent
        // the lowest six bits of the magnitude.
        let magnitude_low_six = second_byte >> 2;
        // Load the remaining 8 bytes into a u64 that we can easily shift/mask.
        let remaining_data = &input[2..10];
        // We know the slice is 8 bytes long, so we can `unwrap()` the conversion to [u8; 8]
        let remaining_magnitude = u64::from_le_bytes(remaining_data.try_into().unwrap());

        let sign_extension_bits = (remaining_magnitude & (0b111111 << 58)) >> 58;
        if support_sign_extension {
            // Something downstream intends to use this as a signed value; we need to make sure
            // that bits 65-70 match bit 64. `remaining_magnitude` is storing 58 bits of data,
            // so bit 64 of the value (bit index=63) is bit 58 (bit index=57) in `remaining_magnitude`.
            let high_bit_is_set = remaining_magnitude & (1 << 57) != 0;
            if (high_bit_is_set && sign_extension_bits != 0b111111)
                || (!high_bit_is_set && sign_extension_bits != 0)
            {
                // If the sign extension bits don't agree with the top bit, this value required
                // more than 64 bits to encode.
                return IonResult::decoding_error(
                    "found a 10-byte FlexInt too large to fit in a i64",
                );
            }
        } else {
            // This is an unsigned value; if any of the highest six bits are set, then this
            // value is beyond the magnitude we can store in a u64.
            if sign_extension_bits != 0 {
                return IonResult::decoding_error(
                    "found a 10-byte FlexUInt too large to fit in a u64",
                );
            }
        }

        // Shift the magnitude from the last 8 bytes over and combine it with the six bits we
        // carried over from the second byte.
        let value = (remaining_magnitude << 6) | magnitude_low_six as u64;
        let flex_uint = FlexUInt::new(10, value);
        Ok(flex_uint)
    }

    #[inline]
    pub(crate) fn encode_opcode_and_length(output: &mut BumpVec<u8>, opcode: u8, length: u64) {
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
    const MAX_FLEX_UINT_ENCODED_SIZE_IN_BYTES: usize = mem::size_of::<u128>();

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
