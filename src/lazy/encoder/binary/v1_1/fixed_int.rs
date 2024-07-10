use std::io::Write;

use crate::decimal::coefficient::Coefficient;
use crate::result::IonFailure;
use crate::{Int, IonResult};

/// An Ion 1.1 encoding primitive that represents a fixed-length signed integer.
#[derive(Debug)]
pub struct FixedInt {
    value: Int,
    size_in_bytes: usize,
}

pub(crate) const MAX_INT_SIZE_IN_BYTES: usize = std::mem::size_of::<i128>();
pub(crate) const MAX_UINT_SIZE_IN_BYTES: usize = std::mem::size_of::<u128>();

impl FixedInt {
    fn new(size_in_bytes: usize, value: impl Into<Int>) -> Self {
        Self::from_int(size_in_bytes, value.into())
    }

    pub(crate) const fn from_int(size_in_bytes: usize, value: Int) -> Self {
        Self {
            value,
            size_in_bytes,
        }
    }

    /// Reads a [`FixedInt`] from the beginning of `input`.
    ///
    /// `input` is the byte slice from which to read a [`FixedInt`].
    /// `size_in_bytes` is the number of bytes to interpret as an unsigned integer.
    /// `offset` is the position of the slice in some larger input stream. It is only used to populate
    ///          an appropriate error message if reading fails.
    #[inline]
    pub fn read(input: &[u8], size_in_bytes: usize, offset: usize) -> IonResult<FixedInt> {
        if input.len() < size_in_bytes {
            return IonResult::incomplete("reading a FixedInt", offset);
        }
        // By branching on particular values, we make the value of `size_in_bytes` in their
        // corresponding arm `const`. This allows us to use `read_const` to optimize for those
        // sizes.
        let fixed_int = match size_in_bytes {
            0 => FixedInt::from_int(0, Int::ZERO),
            1 => Self::read_const::<1>(input.try_into().unwrap()),
            2 => Self::read_const::<2>(input.try_into().unwrap()),
            n if n <= MAX_INT_SIZE_IN_BYTES => Self::read_general_case(input, n),
            _ => {
                return IonResult::decoding_error(
                    "found a FixedInt that was larger than the supported maximum",
                )
            }
        };
        Ok(fixed_int)
    }

    /// When the size of the FixedInt is known, the generated assembly for parsing it is more
    /// efficient. This `const` read method is useful for optimizing common cases.
    #[inline]
    pub(crate) fn read_const<const N: usize>(input: [u8; N]) -> FixedInt {
        let mut buffer = [0u8; MAX_INT_SIZE_IN_BYTES];
        *buffer.last_chunk_mut::<N>().unwrap() = input;
        let value = i128::from_le_bytes(buffer)
            .checked_shr(128 - (N as u32 * 8))
            .unwrap_or(0i128);
        FixedInt::new(N, value)
    }

    fn read_general_case(input: &[u8], size_in_bytes: usize) -> FixedInt {
        const BUFFER_SIZE: usize = MAX_INT_SIZE_IN_BYTES;
        let mut buffer = [0u8; BUFFER_SIZE];
        // Copy the input into the buffer as the _most_ significant bits, read as i128, and then
        // shift right to the correct position, extending the sign.
        let first_occupied_byte_index = BUFFER_SIZE - size_in_bytes;
        buffer[first_occupied_byte_index..].copy_from_slice(input);
        let value: Int = i128::from_le_bytes(buffer)
            .checked_shr(128 - (size_in_bytes as u32 * 8))
            .unwrap_or(0)
            .into();
        FixedInt::new(size_in_bytes, value)
    }

    #[inline]
    fn write_i128<W: Write>(output: &mut W, value: i128) -> IonResult<usize> {
        let num_encoded_bytes = Self::encoded_size(value);

        let le_bytes = value.to_le_bytes();
        let encoded_bytes = &le_bytes[..num_encoded_bytes];

        output.write_all(encoded_bytes)?;
        Ok(num_encoded_bytes)
    }

    pub fn write(output: &mut impl Write, value: &Int) -> IonResult<usize> {
        Self::write_i128(output, value.data)
    }

    #[inline]
    pub fn encoded_size(value: impl Into<Int>) -> usize {
        let value = value.into();
        let num_sign_bits = if value.is_negative() {
            value.data.leading_ones()
        } else {
            value.data.leading_zeros()
        };
        let num_magnitude_bits = 128 - num_sign_bits;
        (num_magnitude_bits as usize / 8) + 1
    }

    pub fn value(&self) -> &Int {
        &self.value
    }

    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

impl From<FixedInt> for Int {
    fn from(other: FixedInt) -> Self {
        other.value
    }
}

impl From<FixedInt> for Coefficient {
    fn from(other: FixedInt) -> Self {
        other.value.into()
    }
}

impl From<i64> for FixedInt {
    fn from(other: i64) -> Self {
        let encoded_size = FixedInt::encoded_size(other);
        FixedInt::new(encoded_size, other)
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
    use crate::{Int, IonResult};

    const FIXED_INT_TEST_CASES: &[(i64, &[u8])] = &[
        (0, &[0b00000000]),
        (1, &[0b00000001]),
        (2, &[0b00000010]),
        (14, &[0b00001110]),
        (127, &[0b01111111]),
        (128, &[0b10000000, 0b00000000]),
        (32767, &[0b11111111, 0b01111111]),
        (32768, &[0b00000000, 0b10000000, 0b00000000]),
        (3954261, &[0b01010101, 0b01010110, 0b00111100]),
        (8388607, &[0b11111111, 0b11111111, 0b01111111]),
        (8388608, &[0b00000000, 0b00000000, 0b10000000, 0b00000000]),
        (
            2147483647,
            &[0b11111111, 0b11111111, 0b11111111, 0b01111111],
        ),
        (
            2147483648,
            &[0b00000000, 0b00000000, 0b00000000, 0b10000000, 0b00000000],
        ),
        (
            549755813887,
            &[0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111],
        ),
        (
            549755813888,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000, 0b00000000,
            ],
        ),
        (
            140737488355327,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111,
            ],
        ),
        (
            140737488355328,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000, 0b00000000,
            ],
        ),
        (
            36028797018963967,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111,
            ],
        ),
        (
            36028797018963968,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000,
                0b00000000,
            ],
        ),
        (
            72624976668147840,
            &[
                0b10000000, 0b01000000, 0b00100000, 0b00010000, 0b00001000, 0b00000100, 0b00000010,
                0b00000001,
            ],
        ),
        (
            9223372036854775807,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
                0b01111111,
            ],
        ),
        (-1, &[0b11111111]),
        (-2, &[0b11111110]),
        (-14, &[0b11110010]),
        (-128, &[0b10000000]),
        (-129, &[0b01111111, 0b11111111]),
        (-32768, &[0b00000000, 0b10000000]),
        (-32769, &[0b11111111, 0b01111111, 0b11111111]),
        (-3954261, &[0b10101011, 0b10101001, 0b11000011]),
        (-8388608, &[0b00000000, 0b00000000, 0b10000000]),
        (-8388609, &[0b11111111, 0b11111111, 0b01111111, 0b11111111]),
        (
            -2147483648,
            &[0b00000000, 0b00000000, 0b00000000, 0b10000000],
        ),
        (
            -2147483649,
            &[0b11111111, 0b11111111, 0b11111111, 0b01111111, 0b11111111],
        ),
        (
            -549755813888,
            &[0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000],
        ),
        (
            -549755813889,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111, 0b11111111,
            ],
        ),
        (
            -140737488355328,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000,
            ],
        ),
        (
            -140737488355329,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111, 0b11111111,
            ],
        ),
        (
            -36028797018963968,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b10000000,
            ],
        ),
        (
            -36028797018963969,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b01111111,
                0b11111111,
            ],
        ),
        (
            -72624976668147841,
            &[
                0b01111111, 0b10111111, 0b11011111, 0b11101111, 0b11110111, 0b11111011, 0b11111101,
                0b11111110,
            ],
        ),
        (
            -9223372036854775808,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b10000000,
            ],
        ),
    ];

    #[test]
    fn decode_fixed_int() -> IonResult<()> {
        for (expected_value, encoding) in FIXED_INT_TEST_CASES {
            let fixed_int = FixedInt::read(encoding, encoding.len(), 0)?;
            let actual_value = fixed_int.value();
            let expected_value = &Int::from(*expected_value);
            assert_eq!(actual_value, expected_value, "actual value {actual_value} was != expected value {expected_value} for encoding {encoding:x?}")
        }
        Ok(())
    }

    #[test]
    fn decode_zero_length_fixed_int() -> IonResult<()> {
        let encoding = &[];
        let fixed_int = FixedInt::read(encoding, encoding.len(), 0)?;
        let actual_value = fixed_int.value().expect_i64()?;
        assert_eq!(
            actual_value, 0,
            "actual value {actual_value} was != expected value 0 for encoding {encoding:x?}"
        );
        Ok(())
    }

    #[test]
    fn encode_fixed_int() -> IonResult<()> {
        // Make two copies of each of our tests. In the first, each i64 is turned into a Int.
        let mut test_cases: Vec<_> = FIXED_INT_TEST_CASES
            .iter()
            .cloned()
            .map(|(value, encoding)| (Int::from(value), encoding))
            .collect();
        // In the second, each i64 is turned into a BigInt and then turned into an Int, exercising a different
        // serialization code path.
        let big_uint_test_cases = FIXED_INT_TEST_CASES
            .iter()
            .cloned()
            .map(|(value, encoding)| (Int::from(i128::from(value)), encoding));
        test_cases.extend(big_uint_test_cases);

        for (value, expected_encoding) in test_cases {
            let mut buffer = Vec::new();
            FixedInt::write(&mut buffer, &value)?;
            let encoding = buffer.as_slice();
            assert_eq!(encoding, expected_encoding, "actual encoding {encoding:x?} was != expected encoding {expected_encoding:x?} for value {value}");
        }
        Ok(())
    }
}
