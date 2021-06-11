// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;

use arrayvec::ArrayVec;
use bigdecimal::Zero;

use crate::{
    binary::{int::Int, var_int::VarInt, var_uint::VarUInt, writer::MAX_INLINE_LENGTH},
    result::IonResult,
    types::{
        coefficient::{Coefficient, Sign},
        decimal::Decimal,
        magnitude::Magnitude,
    },
};

const DECIMAL_BUFFER_SIZE: usize = 16;
const DECIMAL_POSITIVE_ZERO: Decimal = Decimal {
    coefficient: Coefficient {
        sign: Sign::Positive,
        magnitude: Magnitude::U64(0),
    },
    exponent: 0,
};

/// Provides support to write [`Decimal`] into [Ion binary].
///
/// [Ion binary]: https://amzn.github.io/ion-docs/docs/binary.html#5-decimal
// TODO: Change these methods to return the number of bytes written. #283
pub trait DecimalBinaryEncoder {
    /// Encodes the content of a [`Decimal`] as per the Ion binary encoding.
    /// Returns the length of the encoded bytes.
    ///
    /// This does not encode the type descriptor nor the associated length.
    /// Prefer [`DecimalBinaryEncoder::encode_decimal_value`] for that.
    fn encode_decimal(&mut self, decimal: &Decimal) -> IonResult<()>;

    /// Encodes a [`Decimal`] as an Ion value with the type descriptor and
    /// length. Returns the length of the encoded bytes.
    fn encode_decimal_value(&mut self, decimal: &Decimal) -> IonResult<()>;
}

impl<W> DecimalBinaryEncoder for W
where
    W: Write,
{
    fn encode_decimal(&mut self, decimal: &Decimal) -> IonResult<()> {
        if decimal == &DECIMAL_POSITIVE_ZERO {
            return Ok(());
        }

        VarInt::write_i64(self, decimal.exponent)?;

        // If the coefficient is small enough to safely fit in an i64, use that to avoid
        // allocating.
        if let Some(small_coefficient) = decimal.coefficient.as_i64() {
            // From the spec: "The subfield should not be present (that is, it
            // has zero length) when the coefficient’s value is (positive)
            // zero."
            if !small_coefficient.is_zero() {
                let _ = Int::write_i64(self, small_coefficient)?;
            }
        } else {
            // Otherwise, allocate a Vec<u8> with the necessary representation.
            let mut coefficient_bytes = match decimal.coefficient.magnitude() {
                Magnitude::U64(unsigned) => unsigned.to_be_bytes().into(),
                Magnitude::BigUInt(big) => big.to_bytes_be(),
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
                }
            } else {
                // If the first bit is unset, it's now the sign bit.
                if first_bit_is_zero {
                    // Do nothing; zero is the correct sign bit for a non-negative coefficient.
                } else {
                    // Otherwise, we need to write out an extra leading byte with an unset sign bit
                    self.write_all(&[0b0000_0000])?;
                }
            }
            self.write_all(coefficient_bytes.as_slice())?;
        }

        Ok(())
    }

    fn encode_decimal_value(&mut self, decimal: &Decimal) -> IonResult<()> {
        // First encode the decimal. We need to know the encoded length before
        // we can compute and write out the type descriptor.
        let mut encoded: ArrayVec<u8, DECIMAL_BUFFER_SIZE> = ArrayVec::new();
        encoded.encode_decimal(decimal)?;

        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            type_descriptor = 0x50 | encoded.len() as u8;
            self.write(&[type_descriptor])?;
        } else {
            type_descriptor = 0x5E;
            self.write(&[type_descriptor])?;
            VarUInt::write_u64(self, encoded.len() as u64)?;
        }

        // Now we can write out the encoded decimal!
        self.write(&encoded[..])?;

        Ok(())
    }
}
