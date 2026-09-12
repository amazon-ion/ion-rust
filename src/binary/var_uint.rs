use crate::result::IonResult;
use ice_code::ice as cold_path;
use num_integer::Integer;
use std::io::Write;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarUInt's magnitude and byte length in the future.
// See: https://github.com/amazon-ion/ion-rust/issues/7

const BITS_PER_ENCODED_BYTE: usize = 7;

const LOWER_7_BITMASK: u8 = 0b0111_1111;

const END_FLAG: u8 = 0b1000_0000;

/// Builds a big-endian `VarUInt` byte-array literal from magnitude `m` and the shift amounts of its
/// leading 7-bit groups (most-significant first). The final group is shift `0` and carries the
/// "end" flag, so callers list only the leading shifts.
///
/// It's a macro, not a `fn var_uint_bytes<const N>(m)`, because expanding to an array *literal*
/// keeps the encoding as straight-line stores at every optimization level: a `macro_rules!` can't
/// read a const generic's value to unroll, and LLVM's loop unroller is throttled at `-Os`/`-Oz`
/// (the wasm norm), so a generic loop body would compile to a real runtime loop there.
macro_rules! var_uint {
    ($m:expr $(, $lead:literal)*) => {
        [
            $( (($m >> $lead) as u8) & LOWER_7_BITMASK, )*
            END_FLAG | ($m as u8 & LOWER_7_BITMASK),
        ]
    };
}

/// Represents a variable-length unsigned integer. See the
/// [VarUInt and VarInt Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct VarUInt {
    value: usize,
    size_in_bytes: usize,
}

impl VarUInt {
    pub(crate) fn new(value: usize, size_in_bytes: usize) -> Self {
        VarUInt {
            value,
            size_in_bytes,
        }
    }

    /// Returns the number of bytes needed to encode `value` as a `VarUInt`.
    #[inline]
    pub fn encoded_size_of(value: u64) -> usize {
        let leading_zeros = value.leading_zeros() as usize;
        let bits_used = u64::BITS as usize - leading_zeros;
        let (full_bytes, remaining_bits) = bits_used.div_rem(&BITS_PER_ENCODED_BYTE);
        match (full_bytes, remaining_bits) {
            (0, 0) => 1,
            (_, 0) => full_bytes,
            _ => full_bytes + 1,
        }
    }

    /// Encodes the given unsigned int value as a VarUInt and writes it to the
    /// sink, returning the number of bytes written.
    ///
    /// A `VarUInt` is a big-endian sequence of 7-bit groups; the high bit of each byte is the
    /// "end" flag, set only on the final byte. The one- to four-byte values that dominate real
    /// data (symbol IDs, field SIDs, small lengths and magnitudes) are handled by an inline
    /// if-ladder — sizes are locally stable so the branch predicts well, and each arm writes a
    /// compile-time-constant-length array (inline stores rather than a data-dependent `memcpy`).
    /// Values needing five or more bytes (lengths/magnitudes `>= 2^28`, e.g. multi-hundred-MB
    /// containers) are rare and handled by a `cold_path!` fallback (an out-of-line, never-inlined
    /// function) that picks the size in O(1) via `encoded_size_of` instead of continuing the
    /// comparison chain, so large containers don't hit a branch-walk cliff. Each arm's array is
    /// built by the `var_uint!` macro from its leading 7-bit-group shift amounts.
    #[inline]
    pub fn write_u64<W: Write>(sink: &mut W, magnitude: u64) -> IonResult<usize> {
        let m = magnitude;
        if m < 1 << 7 {
            sink.write_all(&var_uint!(m))?;
            return Ok(1);
        }
        if m < 1 << 14 {
            sink.write_all(&var_uint!(m, 7))?;
            return Ok(2);
        }
        if m < 1 << 21 {
            sink.write_all(&var_uint!(m, 14, 7))?;
            return Ok(3);
        }
        if m < 1 << 28 {
            sink.write_all(&var_uint!(m, 21, 14, 7))?;
            return Ok(4);
        }
        // Five or more bytes (`magnitude >= 2^28`): rare, so `cold_path!` moves this into an
        // out-of-line, never-inlined function and keeps the small-value path above tiny.
        cold_path! {{
            let n = Self::encoded_size_of(m);
            match n {
                5 => sink.write_all(&var_uint!(m, 28, 21, 14, 7))?,
                6 => sink.write_all(&var_uint!(m, 35, 28, 21, 14, 7))?,
                7 => sink.write_all(&var_uint!(m, 42, 35, 28, 21, 14, 7))?,
                8 => sink.write_all(&var_uint!(m, 49, 42, 35, 28, 21, 14, 7))?,
                9 => sink.write_all(&var_uint!(m, 56, 49, 42, 35, 28, 21, 14, 7))?,
                _ => sink.write_all(&var_uint!(m, 63, 56, 49, 42, 35, 28, 21, 14, 7))?,
            }
            Ok(n)
        }}
    }

    /// Returns the magnitude of the unsigned integer
    #[inline(always)]
    pub fn value(&self) -> usize {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// unsigned integer
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{VarUInt, END_FLAG, LOWER_7_BITMASK};
    use crate::result::IonResult;

    fn var_uint_encoding_test(value: u64, expected_encoding: &[u8]) -> IonResult<()> {
        let mut buffer = vec![];
        VarUInt::write_u64(&mut buffer, value)?;
        assert_eq!(buffer.as_slice(), expected_encoding);
        Ok(())
    }

    #[test]
    fn test_write_var_uint_zero() -> IonResult<()> {
        var_uint_encoding_test(0, &[0b1000_0000])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_single_byte_values() -> IonResult<()> {
        var_uint_encoding_test(6, &[0b1000_0110])?;
        var_uint_encoding_test(17, &[0b1001_0001])?;
        var_uint_encoding_test(41, &[0b1010_1001])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_two_byte_values() -> IonResult<()> {
        var_uint_encoding_test(279, &[0b0000_0010, 0b1001_0111])?;
        var_uint_encoding_test(555, &[0b0000_0100, 0b1010_1011])?;
        var_uint_encoding_test(999, &[0b0000_0111, 0b1110_0111])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_three_byte_values() -> IonResult<()> {
        var_uint_encoding_test(81_991, &[0b0000_0101, 0b0000_0000, 0b1100_0111])?;
        var_uint_encoding_test(400_600, &[0b0001_1000, 0b0011_1001, 0b1101_1000])?;
        Ok(())
    }

    #[test]
    fn test_write_var_uint_for_u64_max() -> IonResult<()> {
        var_uint_encoding_test(
            u64::MAX,
            &[0x01, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0xFF],
        )?;
        Ok(())
    }

    #[test]
    fn encoded_size_calculation() -> IonResult<()> {
        let mut values: Vec<u64> = Vec::new();
        for num_bytes in 0..=63u32 {
            values.push(2u64.pow(num_bytes) - 1);
            values.push(2u64.pow(num_bytes))
        }
        values.push(u64::MAX);

        let mut buffer = vec![];
        for value in values {
            buffer.clear();
            VarUInt::write_u64(&mut buffer, value)?;
            let encoded_length = buffer.len();
            let calculated_length = VarUInt::encoded_size_of(value);
            assert_eq!(
                encoded_length, calculated_length,
                "encoded length {encoded_length} != calculated length {calculated_length} for value {value}"
            );
        }
        Ok(())
    }

    /// Independent reference encoder: a straightforward reversed big-endian loop, used as an oracle
    /// to byte-check `write_u64` across every arm (`N = 1..=10`), including the wider arms that have
    /// no hand-written expected-bytes case.
    fn reference_var_uint(mut m: u64) -> Vec<u8> {
        if m == 0 {
            return vec![END_FLAG];
        }
        let mut groups = Vec::new();
        while m > 0 {
            groups.push((m as u8) & LOWER_7_BITMASK);
            m >>= 7;
        }
        groups.reverse();
        *groups.last_mut().unwrap() |= END_FLAG;
        groups
    }

    #[test]
    fn test_write_var_uint_matches_reference_all_arms() -> IonResult<()> {
        // Values spanning every byte-count arm: each power-of-two boundary (and one below it), a
        // midpoint within each arm, plus the extremes. Byte 63 lands in the 10-byte arm.
        let mut values: Vec<u64> = vec![0, u64::MAX];
        for b in 0..64u32 {
            values.push(1u64 << b);
            values.push((1u64 << b).saturating_sub(1));
            values.push((1u64 << b) | ((1u64 << b) / 3));
        }
        let mut buffer = vec![];
        for value in values {
            buffer.clear();
            let written = VarUInt::write_u64(&mut buffer, value)?;
            let expected = reference_var_uint(value);
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
