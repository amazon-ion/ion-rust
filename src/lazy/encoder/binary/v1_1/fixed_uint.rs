use std::io::Write;

use num_bigint::BigUint;

use crate::result::IonFailure;
use crate::types::integer::UIntData;
use crate::{IonResult, UInt};

/// An Ion 1.1 encoding primitive that represents a fixed-length unsigned integer.
#[derive(Debug)]
pub struct FixedUInt {
    value: UInt,
    size_in_bytes: usize,
}

impl FixedUInt {
    fn new(size_in_bytes: usize, value: impl Into<UInt>) -> Self {
        Self {
            value: value.into(),
            size_in_bytes,
        }
    }

    /// Reads a [`FixedUInt`] from the beginning of `input`.
    ///
    /// `input` is the byte slice from which to read a [`FixedUInt`].
    /// `size_in_bytes` is the number of bytes to interpret as an unsigned integer.
    /// `offset` is the position of the slice in some larger input stream. It is only used to populate
    ///          an appropriate error message if reading fails.
    #[inline]
    pub fn read(input: &[u8], size_in_bytes: usize, offset: usize) -> IonResult<FixedUInt> {
        if input.len() < size_in_bytes {
            return IonResult::incomplete("reading a FixedUInt", offset);
        }

        let value: UInt = if input.len() <= 8 {
            let mut buffer = [0; 8];
            buffer[..size_in_bytes].copy_from_slice(input);
            u64::from_le_bytes(buffer).into()
        } else {
            BigUint::from_bytes_le(&input[..size_in_bytes]).into()
        };

        Ok(FixedUInt::new(size_in_bytes, value))
    }

    #[inline]
    pub(crate) fn write_u64<W: Write>(output: &mut W, value: u64) -> IonResult<usize> {
        let encoded_bytes = value.to_le_bytes();
        let leading_zeros = value.leading_zeros();
        let num_encoded_bytes = (8 - (leading_zeros as usize / 8)).max(1);

        output.write_all(&encoded_bytes[..num_encoded_bytes])?;
        Ok(num_encoded_bytes)
    }

    fn write_big_uint<W: Write>(output: &mut W, value: &BigUint) -> IonResult<usize> {
        let encoded_bytes = value.to_bytes_le();
        output.write_all(encoded_bytes.as_slice())?;
        Ok(encoded_bytes.len())
    }

    pub fn write(output: &mut impl Write, value: &UInt) -> IonResult<usize> {
        match &value.data {
            UIntData::U64(uint) => Self::write_u64(output, *uint),
            UIntData::BigUInt(uint) => Self::write_big_uint(output, uint),
        }
    }

    pub fn value(&self) -> &UInt {
        &self.value
    }

    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
    use crate::{IonResult, UInt};
    use num_bigint::BigUint;

    const FIXED_UINT_TEST_CASES: &[(u64, &[u8])] = &[
        (0, &[0b00000000]),
        (1, &[0b00000001]),
        (2, &[0b00000010]),
        (14, &[0b00001110]),
        (127, &[0b01111111]),
        (128, &[0b10000000]),
        (255, &[0b11111111]),
        (256, &[0b00000000, 0b00000001]),
        (65535, &[0b11111111, 0b11111111]),
        (65536, &[0b00000000, 0b00000000, 0b00000001]),
        (3954261, &[0b01010101, 0b01010110, 0b00111100]),
        (16777215, &[0b11111111, 0b11111111, 0b11111111]),
        (16777216, &[0b00000000, 0b00000000, 0b00000000, 0b00000001]),
        (
            4294967295,
            &[0b11111111, 0b11111111, 0b11111111, 0b11111111],
        ),
        (
            4294967296,
            &[0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000001],
        ),
        (
            1099511627775,
            &[0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111],
        ),
        (
            1099511627776,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000001,
            ],
        ),
        (
            281474976710655,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
            ],
        ),
        (
            281474976710656,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000001,
            ],
        ),
        (
            5023487023698435,
            &[
                0b00000011, 0b11010010, 0b10010100, 0b10110111, 0b11010101, 0b11011000, 0b00010001,
            ],
        ),
        (
            72057594037927935,
            &[
                0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
            ],
        ),
        (
            72057594037927936,
            &[
                0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000,
                0b00000001,
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
    ];

    #[test]
    fn decode_fixed_uint() -> IonResult<()> {
        for (expected_value, encoding) in FIXED_UINT_TEST_CASES {
            let fixed_uint = FixedUInt::read(encoding, encoding.len(), 0)?;
            let actual_value = fixed_uint.value();
            let expected_value = &UInt::from(*expected_value);
            assert_eq!(actual_value, expected_value, "actual value {actual_value} was != expected value {expected_value} for encoding {encoding:x?}")
        }
        Ok(())
    }

    #[test]
    fn decode_zero_length_fixed_uint() -> IonResult<()> {
        let encoding = &[];
        let fixed_uint = FixedUInt::read(encoding, encoding.len(), 0)?;
        let actual_value = fixed_uint.value().expect_u64()?;
        assert_eq!(
            actual_value, 0,
            "actual value {actual_value} was != expected value 0 for encoding {encoding:x?}"
        );
        Ok(())
    }

    #[test]
    fn encode_fixed_uint() -> IonResult<()> {
        // Make two copies of each of our tests. In the first, each u64 is turned into a UInt.
        let mut test_cases: Vec<_> = FIXED_UINT_TEST_CASES
            .iter()
            .cloned()
            .map(|(value, encoding)| (UInt::from(value), encoding))
            .collect();
        // In the second, each u64 is turned into a BigUint and then turned into a UInt, exercising a different
        // serialization code path.
        let big_uint_test_cases = FIXED_UINT_TEST_CASES
            .iter()
            .cloned()
            .map(|(value, encoding)| (UInt::from(BigUint::from(value)), encoding));
        test_cases.extend(big_uint_test_cases);

        for (value, expected_encoding) in test_cases {
            let mut buffer = Vec::new();
            FixedUInt::write(&mut buffer, &value)?;
            let encoding = buffer.as_slice();
            assert_eq!(encoding, expected_encoding, "actual encoding {encoding:x?} was != expected encoding {expected_encoding:x?} for value {value}");
        }
        Ok(())
    }
}
