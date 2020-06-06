use crate::data_source::IonDataSource;
use crate::result::{decoding_error_result, IonResult};
use std::mem;

// ion_rust does not currently support reading variable length integers of truly arbitrary size.
// These type aliases will simplify the process of changing the data types used to represent each
// VarUInt's magnitude and byte length in the future.
// See: https://github.com/amzn/ion-rust/issues/7
pub type VarUIntStorage = usize;
pub type VarUIntSizeStorage = usize;

const BITS_PER_ENCODED_BYTE: usize = 7;
const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<VarUIntStorage>() * 8;
const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

const LOWER_7_BITMASK: u8 = 0b0111_1111;
const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

/// Represents a variable-length unsigned integer. See the
/// [VarUInt and VarInt Fields](amzn.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields)
/// section of the binary Ion spec for more details.
#[derive(Debug)]
pub struct VarUInt {
    value: VarUIntStorage,
    size_in_bytes: VarUIntSizeStorage,
}

impl VarUInt {
    /// Reads a VarUInt from the provided data source.
    pub fn read<R: IonDataSource>(data_source: &mut R) -> IonResult<VarUInt> {
        let mut magnitude: VarUIntStorage = 0;

        let mut byte_processor = |byte: u8| {
            let lower_seven = (LOWER_7_BITMASK & byte) as VarUIntStorage;
            magnitude <<= 7; // Shifts 0 to 0 in the first iteration
            magnitude |= lower_seven;
            byte < HIGHEST_BIT_VALUE // If the highest bit is zero, continue reading
        };

        let encoded_size_in_bytes = data_source.read_next_byte_while(&mut byte_processor)?;

        // Prevent overflow by checking that the VarUInt was not too large to safely fit in the
        // data type being used to house the decoded value.
        //
        // This approach has two drawbacks:
        // * When using a u64, we only allow up to 63 bits of encoded magnitude data.
        // * It will return an error for inefficiently-encoded small values that use more bytes
        //   than required. (e.g. A 10-byte encoding of the number 0 will be rejected.)
        //
        // However, reading VarUInt values is a very hot code path for reading binary Ion. This
        // compromise allows us to prevent overflows for the cost of a single branch per VarUInt
        // rather than performing extra bookkeeping logic on a per-byte basis.
        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return decoding_error_result(format!(
                "Found a {}-byte VarUInt. Max supported size is {} bytes.",
                encoded_size_in_bytes, MAX_ENCODED_SIZE_IN_BYTES
            ));
        }

        Ok(VarUInt {
            size_in_bytes: encoded_size_in_bytes,
            value: magnitude,
        })
    }

    /// Returns the magnitude of the unsigned integer
    pub fn value(&self) -> VarUIntStorage {
        self.value
    }

    /// Returns the number of bytes that were read from the data source to construct this
    /// unsigned integer
    pub fn size_in_bytes(&self) -> VarUIntSizeStorage {
        self.size_in_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::VarUInt;
    use std::io::{BufReader, Cursor};

    const ERROR_MESSAGE: &'static str = "Failed to read a VarUInt from the provided data.";

    #[test]
    fn test_read_var_uint() {
        let var_uint = VarUInt::read(&mut Cursor::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]))
            .expect(ERROR_MESSAGE);
        assert_eq!(3, var_uint.size_in_bytes());
        assert_eq!(1_984_385, var_uint.value());
    }

    #[test]
    fn test_read_var_uint_small_buffer() {
        let var_uint = VarUInt::read(
            // Construct a BufReader whose input buffer cannot hold all of the data at once
            // to ensure that reads that span multiple I/O operations work as expected
            &mut BufReader::with_capacity(1, Cursor::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001])),
        )
        .expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 3);
        assert_eq!(var_uint.value(), 1_984_385);
    }

    #[test]
    fn test_read_var_uint_zero() {
        let var_uint = VarUInt::read(&mut Cursor::new(&[0b1000_0000])).expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 1);
        assert_eq!(var_uint.value(), 0);
    }

    #[test]
    fn test_read_var_uint_two_bytes_max_value() {
        let var_uint =
            VarUInt::read(&mut Cursor::new(&[0b0111_1111, 0b1111_1111])).expect(ERROR_MESSAGE);
        assert_eq!(var_uint.size_in_bytes(), 2);
        assert_eq!(var_uint.value(), 16_383);
    }

    #[test]
    fn test_read_var_uint_overflow_detection() {
        let _var_uint = VarUInt::read(&mut Cursor::new(&[
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b1111_1111,
        ]))
        .expect_err("This should have failed due to overflow.");
    }
}
