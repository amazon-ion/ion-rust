use crate::binary::constants::v1_0::{length_codes, IVM};
use crate::binary::int::DecodedInt;
use crate::binary::non_blocking::type_descriptor::{
    Header, TypeDescriptor, ION_1_0_TYPE_DESCRIPTORS,
};
use crate::binary::uint::DecodedUInt;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::result::{decoding_error, incomplete_data_error, incomplete_data_error_raw};
use crate::types::{Int, UInt};
use crate::{IonResult, IonType};
use num_bigint::{BigInt, BigUint, Sign};
use std::io::Read;
use std::mem;

// This limit is used for stack-allocating buffer space to encode/decode UInts.
const UINT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_UINT_SIZE_IN_BYTES: usize = 2048;

// This limit is used for stack-allocating buffer space to encode/decode Ints.
const INT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_INT_SIZE_IN_BYTES: usize = 2048;

/// A stack-allocated wrapper around an `AsRef<[u8]>` that provides methods to read Ion's
/// encoding primitives.
///
/// When the wrapped type is a `Vec<u8>`, data can be appended to the buffer between read
/// operations.
#[derive(Debug, PartialEq)]
pub(crate) struct BinaryBuffer<A: AsRef<[u8]>> {
    data: A,
    start: usize,
    end: usize,
    total_consumed: usize,
}

impl<A: AsRef<[u8]>> BinaryBuffer<A> {
    /// Constructs a new BinaryBuffer that wraps `data`.
    #[inline]
    pub fn new(data: A) -> BinaryBuffer<A> {
        let end = data.as_ref().len();
        BinaryBuffer {
            data,
            start: 0,
            end,
            total_consumed: 0,
        }
    }

    /// Creates an independent view of the `BinaryBuffer`'s data. The `BinaryBuffer` that is
    /// returned tracks its own position and consumption without affecting the original.
    pub fn slice(&self) -> BinaryBuffer<&A> {
        BinaryBuffer {
            data: &self.data,
            start: self.start,
            end: self.end,
            total_consumed: self.total_consumed,
        }
    }

    /// Returns a slice containing all of the buffer's remaining bytes.
    pub fn bytes(&self) -> &[u8] {
        &self.data.as_ref()[self.start..self.end]
    }

    /// Returns a slice containing all of the buffer's bytes. This includes all of the consumed
    /// bytes, and remaining unconsumed bytes.
    pub(crate) fn raw_bytes(&self) -> &[u8] {
        self.data.as_ref()
    }

    /// Gets a slice from the buffer starting at `offset` and ending at `offset + length`.
    /// The caller must check that the buffer contains `length + offset` bytes prior
    /// to calling this method.
    pub fn bytes_range(&self, offset: usize, length: usize) -> &[u8] {
        let from = self.start + offset;
        let to = from + length;
        &self.data.as_ref()[from..to]
    }

    /// Returns the number of bytes that have been marked as read either via the
    /// [`consume`](Self::consume) method or one of the `read_*` methods.
    pub fn total_consumed(&self) -> usize {
        self.total_consumed
    }

    /// Returns the number of unread bytes left in the buffer.
    pub fn remaining(&self) -> usize {
        self.end - self.start
    }

    /// Returns `true` if there are no bytes remaining in the buffer. Otherwise, returns `false`.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// If the buffer is not empty, returns `Some(_)` containing the next byte in the buffer.
    /// Otherwise, returns `None`.
    pub fn peek_next_byte(&self) -> Option<u8> {
        self.data.as_ref().get(self.start).copied()
    }

    /// If there are at least `n` bytes left in the buffer, returns `Some(_)` containing a slice
    /// with the first `n` bytes. Otherwise, returns `None`.
    pub fn peek_n_bytes(&self, n: usize) -> Option<&[u8]> {
        self.data.as_ref().get(self.start..self.start + n)
    }

    /// Marks the first `num_bytes_to_consume` bytes in the buffer as having been read.
    ///
    /// After data has been inspected using the `peek` methods, those bytes can be marked as read
    /// by calling the `consume` method.
    ///
    /// Note that the various `read_*` methods to parse Ion encoding primitives automatically
    /// consume the bytes they read if they are successful.
    #[inline]
    pub fn consume(&mut self, num_bytes_to_consume: usize) {
        // This assertion is always run during testing but is removed in the release build.
        debug_assert!(num_bytes_to_consume <= self.remaining());
        self.start += num_bytes_to_consume;
        self.total_consumed += num_bytes_to_consume;
    }

    /// Reads (but does not consume) the first byte in the buffer and returns it as a
    /// [TypeDescriptor].
    pub fn peek_type_descriptor(&self) -> IonResult<TypeDescriptor> {
        if self.is_empty() {
            return incomplete_data_error("a type descriptor", self.total_consumed());
        }
        let next_byte = self.data.as_ref()[self.start];
        Ok(ION_1_0_TYPE_DESCRIPTORS[next_byte as usize])
    }

    /// Reads the first four bytes in the buffer as an Ion version marker. If it is successful,
    /// returns an `Ok(_)` containing a `(major, minor)` version tuple and consumes the
    /// source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#value-streams>
    pub fn read_ivm(&mut self) -> IonResult<(u8, u8)> {
        let bytes = self
            .peek_n_bytes(IVM.len())
            .ok_or_else(|| incomplete_data_error_raw("an IVM", self.total_consumed()))?;

        match bytes {
            [0xE0, major, minor, 0xEA] => {
                let version = (*major, *minor);
                self.consume(IVM.len());
                Ok(version)
            }
            invalid_ivm => decoding_error(format!("invalid IVM: {invalid_ivm:?}")),
        }
    }

    /// Reads a `VarUInt` encoding primitive from the beginning of the buffer. If it is successful,
    /// returns an `Ok(_)` containing its [VarUInt] representation and consumes the source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields>
    pub fn read_var_uint(&mut self) -> IonResult<VarUInt> {
        const BITS_PER_ENCODED_BYTE: usize = 7;
        const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<usize>() * 8;
        const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

        const LOWER_7_BITMASK: u8 = 0b0111_1111;
        const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

        let mut magnitude: usize = 0;
        let mut encoded_size_in_bytes = 0;

        for byte in self.bytes().iter().copied() {
            encoded_size_in_bytes += 1;
            magnitude <<= 7; // Shifts 0 to 0 in the first iteration
            let lower_seven = (LOWER_7_BITMASK & byte) as usize;
            magnitude |= lower_seven;
            if byte >= HIGHEST_BIT_VALUE {
                // This is the final byte.
                // Make sure we haven't exceeded the configured maximum size
                if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
                    return Self::value_too_large(
                        "a VarUInt",
                        encoded_size_in_bytes,
                        MAX_ENCODED_SIZE_IN_BYTES,
                    );
                }
                self.consume(encoded_size_in_bytes);
                return Ok(VarUInt::new(magnitude, encoded_size_in_bytes));
            }
        }

        incomplete_data_error("a VarUInt", self.total_consumed() + encoded_size_in_bytes)
    }

    /// Reads a `VarInt` encoding primitive from the beginning of the buffer. If it is successful,
    /// returns an `Ok(_)` containing its [VarInt] representation and consumes the source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields>
    pub fn read_var_int(&mut self) -> IonResult<VarInt> {
        const BITS_PER_ENCODED_BYTE: usize = 7;
        const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<i64>() * 8;
        const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

        const LOWER_6_BITMASK: u8 = 0b0011_1111;
        const LOWER_7_BITMASK: u8 = 0b0111_1111;
        const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

        const BITS_PER_BYTE: usize = 8;
        const BITS_PER_U64: usize = mem::size_of::<u64>() * BITS_PER_BYTE;

        // Unlike VarUInt's encoding, the first byte in a VarInt is a special case because
        // bit #6 (0-indexed, from the right) indicates whether the value is positive (0) or
        // negative (1).

        if self.is_empty() {
            return incomplete_data_error("a VarInt", self.total_consumed());
        }
        let first_byte: u8 = self.peek_next_byte().unwrap();
        let no_more_bytes: bool = first_byte >= 0b1000_0000; // If the first bit is 1, we're done.
        let is_negative: bool = (first_byte & 0b0100_0000) == 0b0100_0000;
        let sign: i64 = if is_negative { -1 } else { 1 };
        let mut magnitude = (first_byte & 0b0011_1111) as i64;

        if no_more_bytes {
            self.consume(1);
            return Ok(VarInt::new(magnitude * sign, is_negative, 1));
        }

        let mut encoded_size_in_bytes = 1;
        // Whether we found the terminating byte in this buffer.
        let mut terminated = false;

        for byte in self.bytes()[1..].iter().copied() {
            let lower_seven = (0b0111_1111 & byte) as i64;
            magnitude <<= 7;
            magnitude |= lower_seven;
            encoded_size_in_bytes += 1;
            if byte >= 0b1000_0000 {
                terminated = true;
                break;
            }
        }

        if !terminated {
            return incomplete_data_error(
                "a VarInt",
                self.total_consumed() + encoded_size_in_bytes,
            );
        }

        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {encoded_size_in_bytes}-byte VarInt. Max supported size is {MAX_ENCODED_SIZE_IN_BYTES} bytes."
            ));
        }

        self.consume(encoded_size_in_bytes);
        Ok(VarInt::new(
            magnitude * sign,
            is_negative,
            encoded_size_in_bytes,
        ))
    }

    /// Reads the first `length` bytes from the buffer as a `UInt` encoding primitive. If it is
    /// successful, returns an `Ok(_)` containing its [DecodedUInt] representation and consumes the
    /// source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields>
    pub fn read_uint(&mut self, length: usize) -> IonResult<DecodedUInt> {
        if length <= mem::size_of::<u64>() {
            return self.read_small_uint(length);
        }

        // The UInt is too large to fit in a u64; read it as a BigUInt instead.
        self.read_big_uint(length)
    }

    /// Reads the first `length` bytes from the buffer as a `UInt`. The caller must confirm that
    /// `length` is small enough to fit in a `u64`.
    #[inline]
    fn read_small_uint(&mut self, length: usize) -> IonResult<DecodedUInt> {
        let uint_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| incomplete_data_error_raw("a UInt", self.total_consumed()))?;
        let magnitude = DecodedUInt::small_uint_from_slice(uint_bytes);
        self.consume(length);
        Ok(DecodedUInt::new(UInt::U64(magnitude), length))
    }

    /// Reads the first `length` bytes from the buffer as a `UInt`. If `length` is small enough
    /// that the value can fit in a `usize`, it is strongly recommended that you use
    /// `read_small_uint` instead as it will be much faster.
    #[inline(never)]
    // This method performs allocations and its generated assembly is rather large. Isolating its
    // logic in a separate method that is never inlined keeps `read_uint` (its caller) small enough
    // to inline. This is important as `read_uint` is on the hot path for most Ion streams.
    fn read_big_uint(&mut self, length: usize) -> IonResult<DecodedUInt> {
        if length > MAX_UINT_SIZE_IN_BYTES {
            return Self::value_too_large("a Uint", length, MAX_UINT_SIZE_IN_BYTES);
        }

        let uint_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| incomplete_data_error_raw("a UInt", self.total_consumed()))?;

        let magnitude = BigUint::from_bytes_be(uint_bytes);
        self.consume(length);
        Ok(DecodedUInt::new(UInt::BigUInt(magnitude), length))
    }

    #[inline(never)]
    // This method is inline(never) because it is rarely invoked and its allocations/formatting
    // compile to a non-trivial number of instructions.
    fn value_too_large<T>(label: &str, length: usize, max_length: usize) -> IonResult<T> {
        decoding_error(format!(
            "found {label} that was too large; size = {length}, max size = {max_length}"
        ))
    }

    /// Reads the first `length` bytes from the buffer as an `Int` encoding primitive. If it is
    /// successful, returns an `Ok(_)` containing its [DecodedInt] representation and consumes the
    /// source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields>
    pub fn read_int(&mut self, length: usize) -> IonResult<DecodedInt> {
        if length == 0 {
            return Ok(DecodedInt::new(Int::I64(0), false, 0));
        } else if length > MAX_INT_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {length}-byte Int. Max supported size is {MAX_INT_SIZE_IN_BYTES} bytes."
            ));
        }

        let int_bytes = self.peek_n_bytes(length).ok_or_else(|| {
            incomplete_data_error_raw("an Int encoding primitive", self.total_consumed())
        })?;

        let mut is_negative: bool = false;

        let value = if length <= mem::size_of::<i64>() {
            // This Int will fit in an i64.
            let first_byte: i64 = i64::from(int_bytes[0]);
            let sign: i64 = if first_byte & 0b1000_0000 == 0 {
                1
            } else {
                is_negative = true;
                -1
            };
            let mut magnitude: i64 = first_byte & 0b0111_1111;
            for &byte in &int_bytes[1..] {
                let byte = i64::from(byte);
                magnitude <<= 8;
                magnitude |= byte;
            }
            Int::I64(sign * magnitude)
        } else {
            // This Int is too big for an i64, we'll need to use a BigInt
            let value = if int_bytes[0] & 0b1000_0000 == 0 {
                BigInt::from_bytes_be(Sign::Plus, int_bytes)
            } else {
                is_negative = true;
                // The leading sign bit is the only part of the input that can't be considered
                // unsigned, big-endian integer bytes. We need to make our own copy of the input
                // so we can flip that bit back to a zero before calling `from_bytes_be`.
                let mut owned_int_bytes = Vec::from(int_bytes);
                owned_int_bytes[0] &= 0b0111_1111;
                BigInt::from_bytes_be(Sign::Minus, owned_int_bytes.as_slice())
            };

            Int::BigInt(value)
        };
        self.consume(length);
        Ok(DecodedInt::new(value, is_negative, length))
    }

    /// Reads a `NOP` encoding primitive from the buffer. If it is successful, returns an `Ok(_)`
    /// containing the number of bytes that were consumed.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#nop-pad>
    #[inline(never)]
    // NOP padding is not widely used in Ion 1.0, in part because many writer implementations do not
    // expose the ability to write them. As such, this method has been marked `inline(never)` to
    // allow the hot path to be better optimized.
    pub fn read_nop_pad(&mut self) -> IonResult<usize> {
        let type_descriptor = self.peek_type_descriptor()?;
        // Advance beyond the type descriptor
        self.consume(1);
        // If the type descriptor says we should skip more bytes, skip them.
        let length = self.read_length(type_descriptor.length_code)?;
        if self.remaining() < length.value() {
            return incomplete_data_error("a NOP", self.total_consumed());
        }
        self.consume(length.value());
        Ok(1 + length.size_in_bytes() + length.value())
    }

    /// Interprets the length code in the provided [Header]; if necessary, will read more bytes
    /// from the buffer to interpret as the value's length. If it is successful, returns an `Ok(_)`
    /// containing a [VarUInt] representation of the value's length and consumes any additional
    /// bytes read. If no additional bytes were read, the returned `VarUInt`'s `size_in_bytes()`
    /// method will return `0`.
    pub fn read_value_length(&mut self, header: Header) -> IonResult<VarUInt> {
        use IonType::*;
        // Some type-specific `length` field overrides
        let length_code = match header.ion_type {
            // Null (0x0F) and Boolean (0x10, 0x11) are the only types that don't have/use a `length`
            // field; the header contains the complete value.
            Null | Bool => 0,
            // If a struct has length = 1, its fields are ordered and the actual length follows.
            // For the time being, this reader does not have any special handling for this case.
            // Use `0xE` (14) as the length code instead so the call to `read_length` below
            // consumes a VarUInt.
            Struct if header.length_code == 1 => length_codes::VAR_UINT,
            // For any other type, use the header's declared length code.
            _ => header.length_code,
        };

        // Read the length, potentially consuming a VarUInt in the process.
        let length = self.read_length(length_code)?;

        // After we get the length, perform some type-specific validation.
        match header.ion_type {
            Float => match header.length_code {
                0 | 4 | 8 | 15 => {}
                _ => return decoding_error("found a float with an illegal length code"),
            },
            Timestamp if !header.is_null() && length.value() <= 1 => {
                return decoding_error("found a timestamp with length <= 1")
            }
            Struct if header.length_code == 1 && length.value() == 0 => {
                return decoding_error("found an empty ordered struct")
            }
            _ => {}
        };

        Ok(length)
    }

    /// Interprets a type descriptor's `L` nibble (length) in the way used by most Ion types.
    ///
    /// If `L` is...
    ///   * `f`: the value is a typed `null` and its length is `0`.
    ///   * `e`: the length is encoded as a `VarUInt` that follows the type descriptor.
    ///   * anything else: the `L` represents the actual length.
    ///
    /// If successful, returns an `Ok(_)` that contains the [VarUInt] representation
    /// of the value's length and consumes any additional bytes read.
    pub fn read_length(&mut self, length_code: u8) -> IonResult<VarUInt> {
        let length = match length_code {
            length_codes::NULL => VarUInt::new(0, 0),
            length_codes::VAR_UINT => self.read_var_uint()?,
            magnitude => VarUInt::new(magnitude as usize, 0),
        };

        Ok(length)
    }
}

/// These methods are only available to `BinaryBuffer`s that wrap a `Vec<u8>`. That is: buffers
/// that own a growable array into which more data can be appended.
// TODO: Instead of pinning this to Vec<u8>, we should define a trait that allows any owned/growable
//       byte buffer type to be used.
impl BinaryBuffer<Vec<u8>> {
    /// Moves any unread bytes to the front of the `Vec<u8>`, making room for more data at the tail.
    /// This method should only be called when the bytes remaining in the buffer represent an
    /// incomplete value; as such, the required `memcpy` should typically be quite small.
    fn restack(&mut self) {
        let remaining = self.remaining();
        self.data.copy_within(self.start..self.end, 0);
        self.start = 0;
        self.end = remaining;
        self.data.truncate(remaining);
    }

    /// Copies the provided bytes to end of the input buffer.
    pub fn append_bytes(&mut self, bytes: &[u8]) {
        self.restack();
        self.data.extend_from_slice(bytes);
        self.end += bytes.len();
    }

    /// Tries to read `length` bytes from `source`. Unlike [`append_bytes`](Self::append_bytes),
    /// this method does not do any copying. A slice of the reader's buffer is handed to `source`
    /// so it can be populated directly.
    ///
    /// If successful, returns an `Ok(_)` containing the number of bytes that were actually read.
    pub fn read_from<R: Read>(&mut self, mut source: R, length: usize) -> IonResult<usize> {
        self.restack();
        // Make sure that there are `length` bytes in the `Vec` beyond `self.end`.
        self.reserve_capacity(length);
        // Get a mutable slice to the first `length` bytes starting at `self.end`.
        let read_buffer = &mut self.data.as_mut_slice()[self.end..length];
        // Use that slice as our input buffer to read from the source.
        let bytes_read = source.read(read_buffer)?;
        // Update `self.end` to reflect that we have more data available to read.
        self.end += bytes_read;

        Ok(bytes_read)
    }

    /// Pushes `0u8` onto the end of the `Vec<u8>` until there are `length` bytes available beyond
    /// `self.end`. This block of zeroed out bytes can then be used as an input I/O buffer for calls
    /// to `read_from`. Applications should only use `read_from` when the buffer has been depleted,
    /// which means that calls to this method should usually be no-ops.
    fn reserve_capacity(&mut self, length: usize) {
        // TODO: More sophisticated logic to avoid potentially reallocating multiple times per call.
        //       For now, it is unlikely that this would happen often.
        let capacity = self.data.len() - self.end;
        if capacity < length {
            for _ in 0..(length - capacity) {
                self.data.push(0);
            }
        }
    }
}

/// Constructs a [BinaryBuffer] from anything that can be viewed as a slice of bytes, including
/// `&[u8]`, `Vec<u8>`, `Buf`, etc.
impl<A: AsRef<[u8]>> From<A> for BinaryBuffer<A> {
    fn from(data: A) -> Self {
        let end = data.as_ref().len();
        BinaryBuffer {
            data,
            start: 0,
            end,
            total_consumed: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::IonError;
    use num_traits::Num;

    fn input_test<I: AsRef<[u8]> + Into<BinaryBuffer<I>>>(input: I) {
        let mut input = input.into();
        // We can peek at the first byte...
        assert_eq!(input.peek_next_byte(), Some(b'f'));
        // ...without modifying the input. Looking at the next 3 bytes still includes 'f'.
        assert_eq!(input.peek_n_bytes(3), Some("foo".as_bytes()));
        // Advancing the cursor by 1...
        input.consume(1);
        // ...causes next_byte() to return 'o'.
        assert_eq!(input.peek_next_byte(), Some(b'o'));
        input.consume(1);
        assert_eq!(input.peek_next_byte(), Some(b'o'));
        input.consume(1);
        assert_eq!(input.peek_n_bytes(2), Some(" b".as_bytes()));
        assert_eq!(input.peek_n_bytes(6), Some(" bar b".as_bytes()));
    }

    #[test]
    fn string_test() {
        input_test(String::from("foo bar baz"));
    }

    #[test]
    fn slice_test() {
        input_test("foo bar baz".as_bytes());
    }

    #[test]
    fn vec_test() {
        input_test(Vec::from("foo bar baz".as_bytes()));
    }

    #[test]
    fn read_var_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]);
        let var_uint = buffer.read_var_uint()?;
        assert_eq!(3, var_uint.size_in_bytes());
        assert_eq!(1_984_385, var_uint.value());
        Ok(())
    }

    #[test]
    fn read_var_uint_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]);
        let var_uint = buffer.read_var_uint()?;
        assert_eq!(var_uint.size_in_bytes(), 1);
        assert_eq!(var_uint.value(), 0);
        Ok(())
    }

    #[test]
    fn read_var_uint_two_bytes_max_value() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_uint = buffer.read_var_uint()?;
        assert_eq!(var_uint.size_in_bytes(), 2);
        assert_eq!(var_uint.value(), 16_383);
        Ok(())
    }

    #[test]
    fn read_incomplete_var_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1001, 0b0000_1111]);
        match buffer.read_var_uint() {
            Err(IonError::Incomplete { .. }) => Ok(()),
            other => panic!("expected IonError::Incomplete, but found: {other:?}"),
        }
    }

    #[test]
    fn read_var_uint_overflow_detection() {
        let mut buffer = BinaryBuffer::new(&[
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
        ]);
        buffer
            .read_var_uint()
            .expect_err("This should have failed due to overflow.");
    }

    #[test]
    fn read_var_int_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), 0);
        Ok(())
    }

    #[test]
    fn read_negative_var_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), -935_809);
        Ok(())
    }

    #[test]
    fn read_positive_var_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1001, 0b0000_1111, 0b1000_0001]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), 935_809);
        Ok(())
    }

    #[test]
    fn read_var_int_two_byte_min() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), -8_191);
        Ok(())
    }

    #[test]
    fn read_var_int_two_byte_max() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1111, 0b1111_1111]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), 8_191);
        Ok(())
    }

    #[test]
    fn read_var_int_overflow_detection() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[
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
        ]);
        buffer
            .read_var_int()
            .expect_err("This should have failed due to overflow.");
        Ok(())
    }

    #[test]
    fn read_one_byte_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]);
        let var_int = buffer.read_uint(buffer.remaining())?;
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), &UInt::U64(128));
        Ok(())
    }

    #[test]
    fn read_two_byte_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_int = buffer.read_uint(buffer.remaining())?;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), &UInt::U64(32_767));
        Ok(())
    }

    #[test]
    fn read_three_byte_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1100, 0b1000_0111, 0b1000_0001]);
        let var_int = buffer.read_uint(buffer.remaining())?;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), &UInt::U64(3_966_849));
        Ok(())
    }

    #[test]
    fn test_read_ten_byte_uint() -> IonResult<()> {
        let data = vec![0xFFu8; 10];
        let mut buffer = BinaryBuffer::new(data);
        let uint = buffer.read_uint(buffer.remaining())?;
        assert_eq!(uint.size_in_bytes(), 10);
        assert_eq!(
            uint.value(),
            &UInt::BigUInt(BigUint::from_str_radix("ffffffffffffffffffff", 16).unwrap())
        );
        Ok(())
    }

    #[test]
    fn test_read_uint_too_large() {
        let mut buffer = Vec::with_capacity(MAX_UINT_SIZE_IN_BYTES + 1);
        buffer.resize(MAX_UINT_SIZE_IN_BYTES + 1, 1);
        let mut buffer = BinaryBuffer::new(buffer);
        let _uint = buffer
            .read_uint(buffer.remaining())
            .expect_err("This exceeded the configured max UInt size.");
    }

    #[test]
    fn read_int_negative_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]); // Negative zero
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Int::I64(0));
        assert!(int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_int_positive_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0000_0000]); // Negative zero
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Int::I64(0));
        assert!(!int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_int_length_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[]); // Negative zero
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 0);
        assert_eq!(int.value(), &Int::I64(0));
        assert!(!int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_two_byte_negative_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1111_1111, 0b1111_1111]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Int::I64(-32_767));
        Ok(())
    }

    #[test]
    fn read_two_byte_positive_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Int::I64(32_767));
        Ok(())
    }

    #[test]
    fn read_three_byte_negative_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1011_1100, 0b1000_0111, 0b1000_0001]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Int::I64(-3_966_849));
        Ok(())
    }

    #[test]
    fn read_three_byte_positive_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1100, 0b1000_0111, 0b1000_0001]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Int::I64(3_966_849));
        Ok(())
    }

    #[test]
    fn read_int_overflow() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(vec![1; MAX_INT_SIZE_IN_BYTES + 1]); // Negative zero
        buffer
            .read_int(buffer.remaining())
            .expect_err("This exceeded the configured max Int size.");
        Ok(())
    }
}
