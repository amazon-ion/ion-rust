use crate::result::IonResult;
use crate::types::int_data::UIntData;
use crate::{Int, UInt};
use std::io::Write;

/// Represents a fixed-length unsigned integer. See the
/// [UInt and Int Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct DecodedUInt {
    size_in_bytes: usize,
    value: UInt,
}

impl DecodedUInt {
    /// Interprets all of the bytes in the provided slice as big-endian unsigned integer bytes.
    #[inline]
    pub(crate) fn uint_from_slice(uint_bytes: &[u8]) -> UInt {
        // The `from_be_bytes` method will work for a uint of any size. However, because the slice
        // is of an unknown length, the `memcpy` performed by that method does not get inlined by
        // the compiler. Here we check for some common int sizes and construct the int manually to
        // allow the hot path to be inlined.
        match uint_bytes.len() {
            // If the slice is empty, it's a zero.
            0 => 0u128.into(),
            // If the slice has 1-3 bytes, perform the conversion manually to avoid the `memcpy`
            // call made by the general-purpose conversion logic.
            // The aim is to allow the most common cases to be inlined by the caller. If we try
            // to special case too many integer sizes, then code generated for `uint_from_slice`
            // itself gets too large, and neither `uint_from_slice` nor `memcpy` get inlined.
            1 => uint_bytes[0].into(),
            2 => u16::from_le_bytes([uint_bytes[1], uint_bytes[0]]).into(),
            3 => u32::from_le_bytes([uint_bytes[2], uint_bytes[1], uint_bytes[0], 0u8]).into(),
            // General-purpose conversion from bytes to UInt.
            _ => UIntData::from_be_bytes(uint_bytes).into(),
        }
    }

    /// Encodes the provided `magnitude` as a UInt and writes it to the provided `sink`.
    pub fn write_u64<W: Write>(sink: &mut W, magnitude: u64) -> IonResult<usize> {
        let encoded = encode(magnitude);
        let bytes_to_write = encoded.as_ref();

        sink.write_all(bytes_to_write)?;
        Ok(bytes_to_write.len())
    }

    /// Returns the magnitude of the unsigned integer.
    #[inline(always)]
    pub fn value(&self) -> &UInt {
        &self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// unsigned integer.
    #[inline(always)]
    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}

impl From<DecodedUInt> for Int {
    fn from(uint: DecodedUInt) -> Self {
        let DecodedUInt {
            value,
            .. // Ignore 'size_in_bytes'
        } = uint;
        value.into()
    }
}

/// A buffer for storing a UInt's Big Endian bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UIntBeBytes {
    bytes: [u8; size_of::<u128>()],
}

impl UIntBeBytes {
    pub fn new(bytes: [u8; size_of::<u128>()]) -> Self {
        Self { bytes }
    }
}

/// The big-endian, compact slice of bytes for a UInt (`u64`). Leading zero
/// octets are not part of the representation. See the [spec] for more
/// information.
///
/// [spec]: https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodedUInt {
    be_bytes: UIntBeBytes,
    first_occupied_byte: usize,
}

impl EncodedUInt {
    /// Returns the slice view of the encoded UInt.
    pub fn as_bytes(&self) -> &[u8] {
        &self.be_bytes.bytes[self.first_occupied_byte..]
    }
}

impl AsRef<[u8]> for EncodedUInt {
    /// The same as [EncodedUInt::as_bytes].
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

/// Returns the magnitude as big-endian bytes.
pub fn encode(magnitude: impl Into<u128>) -> EncodedUInt {
    let magnitude: u128 = magnitude.into();
    // We can divide the number of leading zero bits by 8
    // to get the number of leading zero bytes.
    let empty_leading_bytes: u32 = magnitude.leading_zeros() / 8;
    let first_occupied_byte = empty_leading_bytes as usize;

    EncodedUInt {
        be_bytes: UIntBeBytes::new(magnitude.to_be_bytes()),
        first_occupied_byte,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const WRITE_ERROR_MESSAGE: &str = "Writing a UInt to the provided sink failed.";

    #[test]
    fn test_write_ten_byte_uint() {
        let value = u128::from_str_radix("ffffffffffffffffffff", 16).unwrap();
        let mut buffer: Vec<u8> = vec![];
        let encoded = super::encode(value);
        buffer.write_all(encoded.as_bytes()).unwrap();
        let expected_bytes = vec![0xFFu8; 10];
        assert_eq!(expected_bytes.as_slice(), buffer.as_slice());
    }

    #[test]
    fn test_write_eight_byte_uint() {
        let value = 0x01_23_45_67_89_AB_CD_EF;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes = &[0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
        assert_eq!(expected_bytes, buffer.as_slice());
    }

    #[test]
    fn test_write_five_byte_uint() {
        let value = 0x01_23_45_67_89;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes = &[0x01, 0x23, 0x45, 0x67, 0x89];
        assert_eq!(expected_bytes, buffer.as_slice());
    }

    #[test]
    fn test_write_three_byte_uint() {
        let value = 0x01_23_45;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes: &[u8] = &[0x01, 0x23, 0x45];
        assert_eq!(expected_bytes, buffer.as_slice());
    }

    #[test]
    fn test_write_uint_zero() {
        let value = 0x00;
        let mut buffer: Vec<u8> = vec![];
        DecodedUInt::write_u64(&mut buffer, value).expect(WRITE_ERROR_MESSAGE);
        let expected_bytes: &[u8] = &[];
        assert_eq!(expected_bytes, buffer.as_slice());
    }
}
