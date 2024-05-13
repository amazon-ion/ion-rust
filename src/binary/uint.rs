use std::io::Write;
use std::mem;

use crate::result::IonResult;
use crate::{Int, IonError, UInt};

// This limit is used for stack-allocating buffer space to encode/decode UInts.
const UINT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_UINT_SIZE_IN_BYTES: usize = 2048;

/// Represents a fixed-length unsigned integer. See the
/// [UInt and Int Fields](https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct DecodedUInt {
    size_in_bytes: usize,
    value: UInt,
}

impl DecodedUInt {
    pub(crate) fn new(value: UInt, size_in_bytes: usize) -> Self {
        DecodedUInt {
            size_in_bytes,
            value,
        }
    }

    /// Interprets all of the bytes in the provided slice as big-endian unsigned integer bytes.
    /// The caller must confirm that `uint_bytes` is no longer than 8 bytes long; otherwise,
    /// overflow may quietly occur.
    pub(crate) fn small_uint_from_slice(uint_bytes: &[u8]) -> u64 {
        // TODO: copy from the slice and use from_be_bytes
        let mut magnitude: u64 = 0;
        for &byte in uint_bytes {
            let byte = u64::from(byte);
            magnitude <<= 8;
            magnitude |= byte;
        }
        magnitude
    }

    /// Interprets all of the bytes in the provided slice as big-endian unsigned integer bytes.
    pub(crate) fn big_uint_from_slice(uint_bytes: &[u8]) -> u128 {
        // TODO: copy from the slice and use from_be_bytes
        let mut magnitude: u128 = 0;
        for &byte in uint_bytes {
            let byte = u128::from(byte);
            magnitude <<= 8;
            magnitude |= byte;
        }
        magnitude
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

impl TryFrom<DecodedUInt> for Int {
    type Error = IonError;

    fn try_from(uint: DecodedUInt) -> Result<Self, Self::Error> {
        let DecodedUInt {
            value,
            .. // Ignore 'size_in_bytes'
        } = uint;
        value.try_into()
    }
}

/// A buffer for storing a UInt's Big Endian bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UIntBeBytes {
    bytes: [u8; mem::size_of::<u128>()],
}

impl UIntBeBytes {
    pub fn new(bytes: [u8; mem::size_of::<u128>()]) -> Self {
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

    const READ_ERROR_MESSAGE: &str = "Failed to read a UInt from the provided cursor.";
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
