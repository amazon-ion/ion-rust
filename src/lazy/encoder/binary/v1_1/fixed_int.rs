use std::io::Write;

use num_bigint::BigInt;

use crate::result::IonFailure;
use crate::types::integer::IntData;
use crate::{Int, IonResult};

/// An Ion 1.1 encoding primitive that represents a fixed-length signed integer.
#[derive(Debug)]
pub struct FixedInt {
    value: Int,
    size_in_bytes: usize,
}

impl FixedInt {
    fn new(size_in_bytes: usize, value: impl Into<Int>) -> Self {
        Self {
            value: value.into(),
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

        let value: Int = if input.len() <= 8 {
            // Look at the last byte in the input that is part of the FixedInt; this is the most significant byte.
            let most_significant_byte = input[size_in_bytes - 1];
            let sign_bit = most_significant_byte & 0b1000_0000;
            // Create a buffer that is filled with the sign bit that we can write into.
            // Any bytes not overwritten will be an extension of the sign bit.
            let mut buffer = if sign_bit == 0 { [0x0; 8] } else { [0xFF; 8] };
            buffer[..size_in_bytes].copy_from_slice(input);
            i64::from_le_bytes(buffer).into()
        } else {
            BigInt::from_signed_bytes_le(&input[..size_in_bytes]).into()
        };

        Ok(FixedInt::new(size_in_bytes, value))
    }

    #[inline]
    fn write_i64<W: Write>(output: &mut W, value: i64) -> IonResult<usize> {
        let num_encoded_bytes = Self::encoded_size_i64(value);

        let le_bytes = value.to_le_bytes();
        let encoded_bytes = &le_bytes[..num_encoded_bytes];

        output.write_all(encoded_bytes)?;
        Ok(num_encoded_bytes)
    }

    fn write_big_int<W: Write>(output: &mut W, value: &BigInt) -> IonResult<usize> {
        let encoded_bytes = value.to_signed_bytes_le();
        output.write_all(encoded_bytes.as_slice())?;
        Ok(encoded_bytes.len())
    }

    pub fn write(output: &mut impl Write, value: &Int) -> IonResult<usize> {
        match &value.data {
            IntData::I64(int) => Self::write_i64(output, *int),
            IntData::BigInt(int) => Self::write_big_int(output, int),
        }
    }

    #[inline]
    pub fn encoded_size_i64(value: i64) -> usize {
        let num_sign_bits = if value < 0 {
            value.leading_ones()
        } else {
            value.leading_zeros()
        };
        let num_magnitude_bits = 64 - num_sign_bits;
        (num_magnitude_bits as usize / 8) + 1
    }

    pub fn value(&self) -> &Int {
        &self.value
    }

    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

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
            .map(|(value, encoding)| (Int::from(BigInt::from(value)), encoding));
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
