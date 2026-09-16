use crate::result::IonResult;
use ice_code::ice as cold_path;
use std::io::Write;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarInt's magnitude and byte length in the future.
// See: https://github.com/amazon-ion/ion-rust/issues/7
type VarIntStorage = i64;

const LOWER_6_BITMASK: u8 = 0b0011_1111;
const LOWER_7_BITMASK: u8 = 0b0111_1111;

const VARINT_NEGATIVE_ZERO: u8 = 0xC0;

const END_FLAG: u8 = 0b1000_0000;

/// Builds a big-endian `VarInt` byte-array literal from magnitude `m`, sign bit `s` (`0` or `0x40`),
/// and the shift amounts of its groups (most-significant first). The leftmost byte holds the sign
/// plus 6 magnitude bits; the final group is shift `0` and carries the "end" flag, so callers list
/// only the leading shifts. For a single byte the leftmost and final byte coincide.
///
/// It's a macro, not a `fn var_int_bytes<const N>(m, s)`, because expanding to an array *literal*
/// keeps the encoding as straight-line stores at every optimization level: a `macro_rules!` can't
/// read a const generic's value to unroll, and LLVM's loop unroller is throttled at `-Os`/`-Oz`
/// (the wasm norm), so a generic loop body would compile to a real runtime loop there.
macro_rules! var_int {
    // Single byte: the leftmost (sign + 6 magnitude bits) and final (end flag) byte are one.
    ($m:expr, $s:expr) => {
        [END_FLAG | $s | ($m as u8 & LOWER_6_BITMASK)]
    };
    // Leftmost byte carries the sign plus 6 magnitude bits; the rest are 7-bit groups, the final
    // one (shift 0) carrying the end flag.
    ($m:expr, $s:expr, $first:literal $(, $mid:literal)*) => {
        [
            $s | (($m >> $first) as u8 & LOWER_6_BITMASK),
            $( ($m >> $mid) as u8 & LOWER_7_BITMASK, )*
            END_FLAG | ($m as u8 & LOWER_7_BITMASK),
        ]
    };
}

#[derive(Debug)]
pub struct VarInt {
    size_in_bytes: usize,
    value: VarIntStorage,
    // [VarIntStorage] is not capable of natively representing negative zero. We track the sign
    // of the value separately so we can distinguish between 0 and -0.
    is_negative: bool,
}

/// Represents a variable-length signed integer. See the
/// [VarUInt and VarInt Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
impl VarInt {
    pub(crate) fn new(value: i64, is_negative: bool, size_in_bytes: usize) -> Self {
        VarInt {
            size_in_bytes,
            value,
            is_negative,
        }
    }

    /// Writes an `i64` to `sink`, returning the number of bytes written.
    ///
    /// A `VarInt` is a big-endian sequence of 7-bit groups, except the leftmost byte holds only 6
    /// magnitude bits plus a sign bit (bit 6); the high bit of each byte is the "end" flag, set on
    /// the rightmost byte. So `n` bytes hold `6 + 7*(n - 1)` magnitude bits.
    ///
    /// The one- to four-byte values that dominate (decimal exponents, timestamp offsets, small
    /// coefficients) are handled by an inline if-ladder — sizes are locally stable so the branch
    /// predicts well, and each arm writes a compile-time-constant-length array (inline stores rather
    /// than a data-dependent `memcpy`, and no `f64::ceil` size calculation). Five-or-more-byte
    /// values (magnitudes `>= 2^27`) are rare and delegate to an out-of-line tail that picks the
    /// size in O(1). Each threshold `1 << (6 + 7 * (n - 1))` is an `n`-byte VarInt's upper bound;
    /// each arm's array is built by the `var_int!` macro from its leading group shift amounts. The
    /// five-or-more-byte case is a `cold_path!` fallback (out-of-line, never-inlined).
    #[inline]
    pub fn write_i64<W: Write>(sink: &mut W, value: i64) -> IonResult<usize> {
        const SIGN: u8 = 0b0100_0000;
        // The absolute value of an i64 can be cast losslessly to a u64.
        let m: u64 = value.unsigned_abs();
        // Sign bit lives in the leftmost byte only.
        let s: u8 = if value < 0 { SIGN } else { 0 };
        if m < 1 << 6 {
            sink.write_all(&var_int!(m, s))?;
            return Ok(1);
        }
        if m < 1 << 13 {
            sink.write_all(&var_int!(m, s, 7))?;
            return Ok(2);
        }
        if m < 1 << 20 {
            sink.write_all(&var_int!(m, s, 14, 7))?;
            return Ok(3);
        }
        if m < 1 << 27 {
            sink.write_all(&var_int!(m, s, 21, 14, 7))?;
            return Ok(4);
        }
        // Five or more bytes (`magnitude >= 2^27`): rare, so `cold_path!` moves this into an
        // out-of-line, never-inlined function. The byte count is `1 + bits/7` (O(1) via
        // `leading_zeros`, where `bits` counts magnitude bits). `s` is the leftmost byte's sign bit.
        cold_path! {{
            let n = 1 + ((u64::BITS - m.leading_zeros()) / 7) as usize;
            match n {
                5 => sink.write_all(&var_int!(m, s, 28, 21, 14, 7))?,
                6 => sink.write_all(&var_int!(m, s, 35, 28, 21, 14, 7))?,
                7 => sink.write_all(&var_int!(m, s, 42, 35, 28, 21, 14, 7))?,
                8 => sink.write_all(&var_int!(m, s, 49, 42, 35, 28, 21, 14, 7))?,
                9 => sink.write_all(&var_int!(m, s, 56, 49, 42, 35, 28, 21, 14, 7))?,
                _ => sink.write_all(&var_int!(m, s, 63, 56, 49, 42, 35, 28, 21, 14, 7))?,
            }
            Ok(n)
        }}
    }

    /// Encodes a negative zero as an `VarInt` and writes it to the provided `sink`.
    /// Returns the number of bytes written.
    ///
    /// This method is similar to [write_i64](crate::binary::var_int::VarInt::write_i64).
    /// However, because an i64 cannot represent a negative zero, a separate method is required.
    pub fn write_negative_zero<W: Write>(sink: &mut W) -> IonResult<usize> {
        sink.write_all(&[VARINT_NEGATIVE_ZERO])?;
        Ok(1)
    }

    /// Returns `true` if the VarInt is negative zero.
    pub fn is_negative_zero(&self) -> bool {
        // `self.value` can natively represent any negative integer _except_ -0.
        // To check for negative zero, we need to also look at the sign bit that was encoded
        // in the stream.
        self.value == 0 && self.is_negative
    }

    /// Returns the value of the signed integer. If the [VarInt] is negative zero, this method
    /// will return `0`. Use the [is_negative_zero](Self::is_negative_zero) method to check for
    /// negative zero explicitly.
    #[inline(always)]
    pub fn value(&self) -> VarIntStorage {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// signed integer
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{VarInt, END_FLAG, LOWER_6_BITMASK, LOWER_7_BITMASK};
    use crate::result::IonResult;

    fn var_int_encoding_test(value: i64, expected_encoding: &[u8]) -> IonResult<()> {
        let mut buffer = vec![];
        VarInt::write_i64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_encoding);
        Ok(())
    }

    #[test]
    fn test_write_var_uint_zero() -> IonResult<()> {
        var_int_encoding_test(0, &[0b1000_0000])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_single_byte_values() -> IonResult<()> {
        var_int_encoding_test(17, &[0b1001_0001])?;
        var_int_encoding_test(-17, &[0b1101_0001])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_two_byte_values() -> IonResult<()> {
        var_int_encoding_test(555, &[0b0000_0100, 0b1010_1011])?;
        var_int_encoding_test(-555, &[0b0100_0100, 0b1010_1011])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_three_byte_values() -> IonResult<()> {
        var_int_encoding_test(400_600, &[0b0001_1000, 0b0011_1001, 0b1101_1000])?;
        var_int_encoding_test(-400_600, &[0b0101_1000, 0b0011_1001, 0b1101_1000])?;
        Ok(())
    }

    #[test]
    fn test_write_var_int_large_values() -> IonResult<()> {
        // 5-byte: 2^30 sets bit 30, which lands in the leftmost (6-bit) group of a 5-byte VarInt.
        var_int_encoding_test(1 << 30, &[0x04, 0x00, 0x00, 0x00, 0x80])?;
        // 10-byte extremes.
        var_int_encoding_test(
            i64::MAX,
            &[0x00, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0xff],
        )?;
        var_int_encoding_test(
            i64::MIN,
            &[0x41, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80],
        )?;
        Ok(())
    }

    /// Independent reference encoder: the original reversed big-endian loop (leftmost byte holds 6
    /// magnitude bits plus the sign, others hold 7, end flag on the rightmost). Used as an oracle to
    /// byte-check `write_i64` across every arm (`N = 1..=10`) and both signs.
    fn reference_var_int(value: i64) -> Vec<u8> {
        const N: usize = 10;
        let mut buffer = [0u8; N];
        buffer[N - 1] = END_FLAG; // end flag on the rightmost byte
        let mut magnitude: u64 = value.unsigned_abs();
        let occupied_bits = 64 - magnitude.leading_zeros() as usize;
        // Leftmost byte holds 6 magnitude bits; each additional byte holds 7.
        let bytes_required = 1 + occupied_bits.saturating_sub(6).div_ceil(7);
        let mut bytes_remaining = bytes_required;
        for byte in buffer[N - bytes_required..].iter_mut().rev() {
            bytes_remaining -= 1;
            if bytes_remaining > 0 {
                *byte |= (magnitude as u8) & LOWER_7_BITMASK;
                magnitude >>= 7;
            } else {
                *byte |= (magnitude as u8) & LOWER_6_BITMASK;
                if value < 0 {
                    *byte |= 0b0100_0000;
                }
            }
        }
        buffer[N - bytes_required..].to_vec()
    }

    #[test]
    fn test_write_var_int_matches_reference_all_arms() -> IonResult<()> {
        // Values spanning every byte-count arm, both signs: each power-of-two boundary (and one
        // below it) and a midpoint within the arm. `1 << 62` is the largest power of two an i64
        // holds; the extremes exercise the 10-byte arm.
        let mut values: Vec<i64> = vec![0, i64::MAX, i64::MIN];
        for b in 0..63u32 {
            let p = 1i64 << b;
            for v in [p, -p, p - 1, -(p - 1), p + (p >> 1)] {
                values.push(v);
            }
        }
        let mut buffer = vec![];
        for value in values {
            buffer.clear();
            let written = VarInt::write_i64(&mut buffer, value)?;
            let expected = reference_var_int(value);
            assert_eq!(
                buffer.as_slice(),
                expected.as_slice(),
                "encoding mismatch for value {value}"
            );
            assert_eq!(
                written,
                expected.len(),
                "byte count mismatch for value {value}"
            );
        }
        Ok(())
    }
}
