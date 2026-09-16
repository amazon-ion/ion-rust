use crate::decimal::Coefficient;
use crate::result::IonResult;
use crate::types::integer::{AsBigOrSmallValue, UIntData};
use crate::Int;
use ice_code::ice as cold_path;
use std::io::Write;

const INT_NEGATIVE_ZERO: u8 = 0x80;

/// Represents a fixed-length signed integer. See the
/// [UInt and Int Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct DecodedInt {
    size_in_bytes: usize,
    value: Int,
    // [Int] is not capable of natively representing negative zero. We track the sign
    // of the value separately so we can distinguish between 0 and -0.
    is_negative: bool,
}

impl DecodedInt {
    pub(crate) fn new(value: impl Into<Int>, is_negative: bool, size_in_bytes: usize) -> Self {
        let value = value.into();
        DecodedInt {
            size_in_bytes,
            value,
            is_negative,
        }
    }

    // Note: read functionality lives in the `BinaryBuffer` type

    /// Encodes the provided `value` as an Int and writes it to the provided `sink`.
    /// Returns the number of bytes written.
    pub fn write<W: Write>(sink: &mut W, value: &Int) -> IonResult<usize> {
        let is_negative = value.is_negative();
        let magnitude = value.unsigned_abs();
        // Common case: the magnitude is stored inline, so its big-endian bytes can be encoded on
        // the stack with no heap allocation.
        if let Some(mag) = magnitude.data.as_small_value() {
            let (mut be, start) = UIntData::small_to_be_bytes(mag);
            return Self::write_sign_and_magnitude(sink, &mut be[start..], is_negative);
        }
        // Cold path: a BigUint magnitude, which has to be heap-allocated to be encoded.
        // `cold_path!` wraps its body in a closure, so `?` and `return` inside the block are scoped
        // to that closure rather than to `write`. This block is `write`'s tail expression, so its
        // value is the value of `write`.
        cold_path! {{
            let mut be = magnitude.data.to_be_bytes();
            Self::write_sign_and_magnitude(sink, &mut be, is_negative)
        }}
    }

    /// Writes the sign bit followed by the minimal big-endian magnitude in `be` to `sink`,
    /// returning the number of bytes written.
    ///
    /// Ion's `Int` field stores the sign in the high bit of the first byte. If that bit is already
    /// occupied by the magnitude, a leading sign-only byte is written instead. `be` is taken
    /// mutably so the sign bit can be set in place, avoiding a second write in the common case.
    ///
    /// `be` must be non-empty: it holds the minimal big-endian magnitude, which is at least one
    /// byte (zero encodes as `[0x00]`). Both callers derive `be` from [`UIntData::small_to_be_bytes`]
    /// or [`UIntData::to_be_bytes`], which guarantee this.
    fn write_sign_and_magnitude<W: Write>(
        sink: &mut W,
        be: &mut [u8],
        is_negative: bool,
    ) -> IonResult<usize> {
        debug_assert!(!be.is_empty(), "magnitude byte slice must be non-empty");
        let high_bit_set = be[0] & 0x80 != 0;
        if is_negative {
            if high_bit_set {
                sink.write_all(&[0b1000_0000])?;
            } else {
                be[0] |= 0b1000_0000;
            }
        } else if high_bit_set {
            sink.write_all(&[0x00])?;
        }
        sink.write_all(be)?;
        Ok(be.len() + high_bit_set as usize)
    }

    /// Encodes a negative zero as an `Int` and writes it to the provided `sink`.
    /// Returns the number of bytes written.
    ///
    /// This method is similar to [Self::write]. However, because Rust's native integer types cannot
    /// represent a negative zero, a separate method is required.
    pub fn write_negative_zero<W: Write>(sink: &mut W) -> IonResult<usize> {
        sink.write_all(&[INT_NEGATIVE_ZERO])?;
        Ok(1)
    }

    /// Returns `true` if the Int is negative zero.
    pub fn is_negative_zero(&self) -> bool {
        // `self.value` can natively represent any negative integer _except_ -0.
        // To check for negative zero, we need to also look at the sign bit that was encoded
        // in the stream.
        self.value.is_zero() && self.is_negative
    }

    /// Returns the value of the signed integer.
    #[inline(always)]
    pub fn value(&self) -> &Int {
        &self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// signed integer.
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }

    /// Constructs a DecodedInt that represents zero. This is useful when reading from a stream
    /// where a zero-length Int is found, meaning that it is implicitly positive zero.
    pub fn zero() -> Self {
        DecodedInt {
            size_in_bytes: 0,
            value: 0i64.into(),
            is_negative: false,
        }
    }
}

impl From<DecodedInt> for Int {
    // Note that if the DecodedInt represents -0, converting it to an Integer will result in a 0.
    // If negative zero is significant to your use case, check it using [DecodedInt::is_negative_zero]
    // before converting it to an Integer.
    fn from(uint: DecodedInt) -> Self {
        let DecodedInt {
            value,
            .. // Ignore 'size_in_bytes' and 'is_negative'
        } = uint;
        value
    }
}

impl From<DecodedInt> for Coefficient {
    fn from(decoded_int: DecodedInt) -> Self {
        if decoded_int.is_negative_zero() {
            return Coefficient::negative_zero();
        }
        Coefficient::new(decoded_int)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::result::IonResult;
    use crate::UInt;
    use rstest::rstest;

    /// Asserts that `value` encodes to exactly `expected_bytes` and that the byte count reported by
    /// [`DecodedInt::write`] agrees with the number of bytes that landed in the sink.
    fn write_int_test(value: Int, expected_bytes: &[u8]) -> IonResult<()> {
        let mut buffer: Vec<u8> = vec![];
        let length = DecodedInt::write(&mut buffer, &value)?;
        assert_eq!(buffer.as_slice(), expected_bytes);
        assert_eq!(length, expected_bytes.len());
        Ok(())
    }

    /// Returns `2^128`, the smallest magnitude that `Int` cannot store inline. Encoding it takes
    /// the `BigUint` cold path in [`DecodedInt::write`].
    fn two_pow_128() -> Int {
        let mut bytes = vec![0u8; 17];
        bytes[16] = 1;
        Int::from_le_signed_bytes(&bytes)
    }

    #[rstest]
    // Zero. The magnitude is trimmed to a single `0x00` byte rather than to nothing.
    #[case::zero(Int::from(0i64), &[0b0000_0000])]
    // Single-byte magnitudes whose high bit is clear, so the sign shares the magnitude's byte.
    #[case::one(Int::from(1i64), &[0b0000_0001])]
    #[case::three(Int::from(3i64), &[0b0000_0011])]
    #[case::seven(Int::from(7i64), &[0b0000_0111])]
    #[case::one_hundred(Int::from(100i64), &[0b0110_0100])]
    #[case::negative_one(Int::from(-1i64), &[0b1000_0001])]
    #[case::negative_three(Int::from(-3i64), &[0b1000_0011])]
    #[case::negative_seven(Int::from(-7i64), &[0b1000_0111])]
    #[case::negative_one_hundred(Int::from(-100i64), &[0b1110_0100])]
    // A single-byte magnitude whose high bit is set needs a leading sign-only byte.
    #[case::two_hundred_one(Int::from(201i64), &[0b0000_0000, 0b1100_1001])]
    #[case::negative_two_hundred_one(Int::from(-201i64), &[0b1000_0000, 0b1100_1001])]
    // Two-byte magnitudes with a clear leading high bit.
    #[case::five_hundred_one(Int::from(501i64), &[0b0000_0001, 0b1111_0101])]
    #[case::negative_five_hundred_one(Int::from(-501i64), &[0b1000_0001, 0b1111_0101])]
    #[case::sixteen_thousand(Int::from(16_000i64), &[0b0011_1110, 0b1000_0000])]
    #[case::negative_sixteen_thousand(Int::from(-16_000i64), &[0b1011_1110, 0b1000_0000])]
    // A *multi-byte* magnitude whose leading byte has its high bit set; the pad/sign byte must be
    // written even though the magnitude has room for a zero bit further down.
    #[case::two_to_the_fifteenth(Int::from(32_768i64), &[0x00, 0x80, 0x00])]
    #[case::negative_two_to_the_fifteenth(Int::from(-32_768i64), &[0x80, 0x80, 0x00])]
    // Eight-byte magnitudes.
    #[case::max_i64(Int::from(i64::MAX), &[0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])]
    #[case::min_i64(
        Int::from(i64::MIN),
        &[0x80, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    )]
    // Sixteen-byte magnitudes: the widest that `Int` stores inline.
    #[case::max_i128(
        Int::from(i128::MAX),
        &[
            0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        ]
    )]
    #[case::min_i128(
        Int::from(i128::MIN),
        &[
            0x80, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    // A 16-byte magnitude whose leading byte's high bit is clear (`start == 0`): the sign bit is set
    // in place in the first byte, with no leading sign-only byte. Guards the `be[0] |= 0x80` branch
    // at the widest inline width.
    #[case::negative_two_pow_120(
        Int::from(-(1i128 << 120)),
        &[
            0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    // `u128::MAX` is stored as a `BigInt` because it does not fit in an `i128`, but its *magnitude*
    // fits in a `u128`, so `Int::unsigned_abs` normalizes it back to inline storage and it takes
    // the stack-only path. This is the widest output that path can produce: 17 bytes.
    #[case::max_u128_magnitude(
        Int::from(UInt::from(u128::MAX)),
        &[
            0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        ]
    )]
    #[case::negative_max_u128_magnitude(
        Int::from(UInt::from(u128::MAX)).neg(),
        &[
            0x80, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        ]
    )]
    // Just past the seam: a magnitude that exceeds `u128` and so takes the heap-allocating path.
    #[case::two_pow_128(
        two_pow_128(),
        &[
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    #[case::negative_two_pow_128(
        two_pow_128().neg(),
        &[
            0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]
    )]
    fn test_write_int(#[case] value: Int, #[case] expected_bytes: &[u8]) -> IonResult<()> {
        write_int_test(value, expected_bytes)
    }

    #[test]
    fn test_write_int_negative_zero() -> IonResult<()> {
        let mut buffer: Vec<u8> = vec![];
        let length = DecodedInt::write_negative_zero(&mut buffer)?;
        assert_eq!(buffer.as_slice(), &[0b1000_0000]);
        assert_eq!(length, buffer.len());
        Ok(())
    }

    #[test]
    fn write_big_int_roundtrip() -> IonResult<()> {
        // 2^128 exceeds i128
        let big = two_pow_128();

        let mut buffer: Vec<u8> = vec![];
        let length = DecodedInt::write(&mut buffer, &big)?;
        assert_eq!(length, 17);
        assert_eq!(length, buffer.len());

        // Read it back
        let context =
            crate::lazy::expanded::EncodingContext::for_ion_version(crate::IonVersion::v1_0);
        let buf = crate::lazy::binary::binary_buffer::BinaryBuffer::new(context.get_ref(), &buffer);
        let (decoded, _) = buf.read_int(buffer.len())?;
        assert_eq!(*decoded.value(), big);
        Ok(())
    }
}
