// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;

use arrayvec::ArrayVec;
use bigdecimal::Zero;

use crate::binary::int::DecodedInt;
use crate::binary::raw_binary_writer::MAX_INLINE_LENGTH;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::ion_data::IonEq;
use crate::result::{IonFailure, IonResult};
use crate::types::integer::UIntData;
use crate::types::{Coefficient, Decimal, Sign, UInt};
use crate::IonError;

const DECIMAL_BUFFER_SIZE: usize = 32;
const DECIMAL_POSITIVE_ZERO: Decimal = Decimal {
    coefficient: Coefficient {
        sign: Sign::Positive,
        magnitude: UInt {
            data: UIntData::U64(0),
        },
    },
    exponent: 0,
};

/// Provides support to write [`Decimal`] into [Ion binary].
///
/// [Ion binary]: https://amazon-ion.github.io/ion-docs/docs/binary.html#5-decimal
pub trait DecimalBinaryEncoder {
    /// Encodes the content of a [`Decimal`] as per the Ion binary encoding.
    /// Returns the length of the encoded bytes.
    ///
    /// This does not encode the type descriptor nor the associated length.
    /// Prefer [`DecimalBinaryEncoder::encode_decimal_value`] for that.
    fn encode_decimal(&mut self, decimal: &Decimal) -> IonResult<usize>;

    /// Encodes a [`Decimal`] as an Ion value with the type descriptor and
    /// length. Returns the length of the encoded bytes.
    fn encode_decimal_value(&mut self, decimal: &Decimal) -> IonResult<usize>;
}

impl<W> DecimalBinaryEncoder for W
where
    W: Write,
{
    fn encode_decimal(&mut self, decimal: &Decimal) -> IonResult<usize> {
        // 0d0 has no representation, as per the spec.
        if decimal.ion_eq(&DECIMAL_POSITIVE_ZERO) {
            return Ok(0);
        }

        let mut bytes_written: usize = 0;

        bytes_written += VarInt::write_i64(self, decimal.exponent)?;

        if decimal.coefficient.is_negative_zero() {
            bytes_written += DecodedInt::write_negative_zero(self)?;
            return Ok(bytes_written);
        }

        // If the coefficient is small enough to safely fit in an i64, use that to avoid
        // allocating.
        if let Some(small_coefficient) = decimal.coefficient.as_i64() {
            // From the spec: "The subfield should not be present (that is, it
            // has zero length) when the coefficient’s value is (positive)
            // zero."
            if !small_coefficient.is_zero() {
                bytes_written += DecodedInt::write_i64(self, small_coefficient)?;
            }
        } else {
            // Otherwise, allocate a Vec<u8> with the necessary representation.
            let mut coefficient_bytes = match &decimal.coefficient.magnitude().data {
                UIntData::U64(unsigned) => unsigned.to_be_bytes().into(),
                UIntData::BigUInt(big) => big.to_bytes_be(),
            };

            let first_byte: &mut u8 = &mut coefficient_bytes[0];
            let first_bit_is_zero: bool = *first_byte & 0b1000_0000 == 0;
            if let Sign::Negative = decimal.coefficient.sign() {
                // If the first bit is unset, it's now the sign bit. Set it to 1.
                if first_bit_is_zero {
                    *first_byte |= 0b1000_0000;
                } else {
                    // Otherwise, we need to write out an extra leading byte with a sign bit set
                    self.write_all(&[0b1000_0000])?;
                    bytes_written += 1;
                }
            } else {
                // If the first bit is unset, it's now the sign bit.
                if first_bit_is_zero {
                    // Do nothing; zero is the correct sign bit for a non-negative coefficient.
                } else {
                    // Otherwise, we need to write out an extra leading byte with an unset sign bit
                    self.write_all(&[0b0000_0000])?;
                    bytes_written += 1;
                }
            }
            self.write_all(coefficient_bytes.as_slice())?;
            bytes_written += coefficient_bytes.len();
        }

        Ok(bytes_written)
    }

    fn encode_decimal_value(&mut self, decimal: &Decimal) -> IonResult<usize> {
        let mut bytes_written: usize = 0;
        // First encode the decimal value to a stack-allocated buffer.
        // We need to know its encoded length before we can write out
        // the preceding type descriptor.
        let mut encoded: ArrayVec<u8, DECIMAL_BUFFER_SIZE> = ArrayVec::new();
        encoded.encode_decimal(decimal).map_err(|_e| {
            IonError::encoding_error("found a decimal that was too large for the configured buffer")
        })?;

        // Now that we have the value's encoded bytes, we can encode its header
        // and write it to the output stream.
        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            // The value is small enough to encode its length in the type
            // descriptor byte.
            type_descriptor = 0x50 | encoded.len() as u8;
            self.write_all(&[type_descriptor])?;
            bytes_written += 1;
        } else {
            // The value is too large to encode its length in the type descriptor
            // byte; we'll encode it as a VarUInt that follows the type descriptor
            // byte instead.
            type_descriptor = 0x5E;
            self.write_all(&[type_descriptor])?;
            bytes_written += 1;
            bytes_written += VarUInt::write_u64(self, encoded.len() as u64)?;
        }

        // Now that we've written the header to the output stream, we can write
        // the value's encoded bytes.
        self.write_all(&encoded[..])?;
        bytes_written += encoded.len();

        Ok(bytes_written)
    }
}

#[cfg(test)]
mod binary_decimal_tests {
    use num_bigint::BigUint;
    use rstest::*;
    use std::str::FromStr;

    use super::*;

    /// This test ensures that we implement [PartialEq] and [IonEq] correctly for the special
    /// decimal value 0d0.
    #[test]
    fn decimal_0d0_is_a_special_zero_value() {
        assert_eq!(DECIMAL_POSITIVE_ZERO, Decimal::new(0, 0));
        assert!(DECIMAL_POSITIVE_ZERO.ion_eq(&Decimal::new(0, 0)));

        assert_eq!(DECIMAL_POSITIVE_ZERO, Decimal::new(0, 10));
        assert!(!DECIMAL_POSITIVE_ZERO.ion_eq(&Decimal::new(0, 10)));

        assert_eq!(DECIMAL_POSITIVE_ZERO, Decimal::new(0, 100));
        assert!(!DECIMAL_POSITIVE_ZERO.ion_eq(&Decimal::new(0, 100)));
    }

    #[rstest]
    #[case::exactly_zero(Decimal::new(0, 0), 1)]
    #[case::zero_with_nonzero_exp(Decimal::new(0, 10), 2)]
    #[case::meaning_of_life(Decimal::new(42, 0), 3)]
    fn bytes_written(#[case] input: Decimal, #[case] expected: usize) -> IonResult<()> {
        let mut buf = vec![];
        let written = buf.encode_decimal_value(&input)?;
        assert_eq!(buf.len(), expected);
        assert_eq!(written, expected);
        Ok(())
    }

    #[test]
    fn oversized_decimal() {
        let mut buf = vec![];
        // Even though our output stream is a growable Vec, the encoder uses a
        // fixed-size, stack-allocated buffer to encode the body of the decimal.
        // If it's asked to encode a decimal that won't fit (>32 bytes), it should
        // return an error.
        let precise_pi = Decimal::new(
            BigUint::from_str("31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679").unwrap(),
            -99
        );
        let result = buf.encode_decimal_value(&precise_pi);
        assert!(result.is_err());
    }
}
