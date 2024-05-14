use crate::binary::constants::v1_1::IVM;
use crate::binary::var_uint::VarUInt;
use crate::lazy::binary::encoded_value::EncodedValue;
use crate::lazy::binary::raw::v1_1::value::{
    LazyRawBinaryValue_1_1, LazyRawBinaryVersionMarker_1_1,
};
use crate::lazy::binary::raw::v1_1::{Header, LengthType, Opcode, ION_1_1_OPCODES};
use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;
use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
use crate::result::IonFailure;
use crate::{IonError, IonResult};
use std::fmt::{Debug, Formatter};
use std::ops::Range;

// This limit is used for stack-allocating buffer space to encode/decode UInts.
const UINT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_UINT_SIZE_IN_BYTES: usize = 2048;

// This limit is used for stack-allocating buffer space to encode/decode Ints.
const INT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_INT_SIZE_IN_BYTES: usize = 2048;

/// A buffer of unsigned bytes that can be cheaply copied and which defines methods for parsing
/// the various encoding elements of a binary Ion stream.
///
/// Upon success, each parsing method on the `ImmutableBuffer` will return the value that was read
/// and a copy of the `ImmutableBuffer` that starts _after_ the bytes that were parsed.
///
/// Methods that `peek` at the input stream do not return a copy of the buffer.
#[derive(PartialEq, Clone, Copy)]
pub struct ImmutableBuffer<'a> {
    // `data` is a slice of remaining data in the larger input stream.
    // `offset` is the position in the overall input stream where that slice begins.
    //
    // input: 00 01 02 03 04 05 06 07 08 09
    //                          └────┬────┘
    //                          data: &[u8]
    //                          offset: 6
    data: &'a [u8],
    offset: usize,
}

impl<'a> Debug for ImmutableBuffer<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "ImmutableBuffer {{")?;
        for byte in self.bytes().iter().take(16) {
            write!(f, "{:x?} ", *byte)?;
        }
        write!(f, "}}")
    }
}

pub(crate) type ParseResult<'a, T> = IonResult<(T, ImmutableBuffer<'a>)>;

impl<'a> ImmutableBuffer<'a> {
    /// Constructs a new `ImmutableBuffer` that wraps `data`.
    #[inline]
    pub fn new(data: &[u8]) -> ImmutableBuffer {
        Self::new_with_offset(data, 0)
    }

    pub fn new_with_offset(data: &[u8], offset: usize) -> ImmutableBuffer {
        ImmutableBuffer { data, offset }
    }

    /// Returns a slice containing all of the buffer's bytes.
    pub fn bytes(&self) -> &'a [u8] {
        self.data
    }

    /// Gets a slice from the buffer starting at `offset` and ending at `offset + length`.
    /// The caller must check that the buffer contains `length + offset` bytes prior
    /// to calling this method.
    pub fn bytes_range(&self, offset: usize, length: usize) -> &'a [u8] {
        &self.data[offset..offset + length]
    }

    /// Like [`Self::bytes_range`] above, but returns an updated copy of the [`ImmutableBuffer`]
    /// instead of a `&[u8]`.
    pub fn slice(&self, offset: usize, length: usize) -> ImmutableBuffer<'a> {
        ImmutableBuffer {
            data: self.bytes_range(offset, length),
            offset: self.offset + offset,
        }
    }

    /// Returns the number of bytes between the start of the original input byte array and the
    /// subslice of that byte array that this `ImmutableBuffer` represents.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the number of bytes in the buffer.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn range(&self) -> Range<usize> {
        self.offset..self.offset + self.len()
    }

    /// Returns `true` if there are no bytes in the buffer. Otherwise, returns `false`.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// If the buffer is not empty, returns `Some(_)` containing the next byte in the buffer.
    /// Otherwise, returns `None`.
    pub fn peek_next_byte(&self) -> Option<u8> {
        self.data.first().copied()
    }

    /// If there are at least `n` bytes left in the buffer, returns `Some(_)` containing a slice
    /// with the first `n` bytes. Otherwise, returns `None`.
    pub fn peek_n_bytes(&self, n: usize) -> Option<&'a [u8]> {
        self.data.get(..n)
    }

    /// Creates a copy of this `ImmutableBuffer` that begins `num_bytes_to_consume` further into the
    /// slice.
    #[inline]
    pub fn consume(&self, num_bytes_to_consume: usize) -> Self {
        // This assertion is always run during testing but is removed in the release build.
        debug_assert!(num_bytes_to_consume <= self.len());
        Self {
            data: &self.data[num_bytes_to_consume..],
            offset: self.offset + num_bytes_to_consume,
        }
    }

    /// Reads the first byte in the buffer and returns it as an [Opcode].
    #[inline]
    pub(crate) fn peek_opcode(&self) -> IonResult<Opcode> {
        if self.is_empty() {
            return IonResult::incomplete("an opcode", self.offset());
        }
        let next_byte = self.data[0];
        Ok(ION_1_1_OPCODES[next_byte as usize])
    }

    /// Reads the first four bytes in the buffer as an Ion version marker. If it is successful,
    /// returns an `Ok(_)` containing a `(major, minor)` version tuple.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#value-streams>
    pub fn read_ivm(self) -> ParseResult<'a, LazyRawBinaryVersionMarker_1_1<'a>> {
        let bytes = self
            .peek_n_bytes(IVM.len())
            .ok_or_else(|| IonError::incomplete("an IVM", self.offset()))?;

        match bytes {
            [0xE0, major, minor, 0xEA] => {
                let matched = ImmutableBuffer::new_with_offset(bytes, self.offset);
                let marker = LazyRawBinaryVersionMarker_1_1::new(matched, *major, *minor);
                Ok((marker, self.consume(IVM.len())))
            }
            invalid_ivm => IonResult::decoding_error(format!("invalid IVM: {invalid_ivm:?}")),
        }
    }

    /// Reads a [`FlexInt`] from the buffer.
    pub fn read_flex_int(self) -> ParseResult<'a, FlexInt> {
        let flex_int = FlexInt::read(self.bytes(), self.offset())?;
        let remaining = self.consume(flex_int.size_in_bytes());
        Ok((flex_int, remaining))
    }

    /// Reads a [`FlexUInt`] from the buffer.
    #[inline]
    pub fn read_flex_uint(self) -> ParseResult<'a, FlexUInt> {
        let flex_uint = FlexUInt::read(self.bytes(), self.offset())?;
        let remaining = self.consume(flex_uint.size_in_bytes());
        Ok((flex_uint, remaining))
    }

    /// Attempts to decode an annotations wrapper at the beginning of the buffer and returning
    /// its subfields in an [`AnnotationsWrapper`].
    pub fn read_annotations_wrapper(&self, _opcode: Opcode) -> ParseResult<'a, AnnotationsWrapper> {
        todo!();
    }

    /// Reads a `NOP` encoding primitive from the buffer. If it is successful, returns an `Ok(_)`
    /// containing the number of bytes that were consumed.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#nop-pad>
    #[inline(never)]
    // NOP padding is not widely used in Ion 1.0, in part because many writer implementations do not
    // expose the ability to write them. As such, this method has been marked `inline(never)` to
    // allow the hot path to be better optimized.
    pub fn read_nop_pad(self) -> ParseResult<'a, usize> {
        let opcode = self.peek_opcode()?;

        // We need to determine the size of the nop..
        let (size, remaining) = if opcode.length_code == 0xC {
            // Size 0; the nop is contained entirely within the OpCode.
            (0, self.consume(1))
        } else if opcode.length_code == 0xD {
            // We have a flexuint telling us how long our nop is.
            let after_header = self.consume(1);
            let (len, rest) = after_header.read_flex_uint()?;
            (
                len.value() as usize + len.size_in_bytes(),
                rest.consume(len.value() as usize),
            )
        } else {
            return IonResult::decoding_error("Invalid NOP sub-type");
        };

        let total_nop_pad_size = 1 + size; // 1 for OpCode, plus any additional NOP bytes.
        Ok((total_nop_pad_size, remaining))
    }

    /// Calls [`Self::read_nop_pad`] in a loop until the buffer is empty or an opcode
    /// is encountered that is not a NOP.
    #[inline(never)]
    // NOP padding is not widely used in Ion 1.0. This method is annotated with `inline(never)`
    // to avoid the compiler bloating other methods on the hot path with its rarely used
    // instructions.
    pub fn consume_nop_padding(self, mut opcode: Opcode) -> ParseResult<'a, ()> {
        let mut buffer = self;
        // Skip over any number of NOP regions
        while opcode.is_nop() {
            let (_, buffer_after_nop) = buffer.read_nop_pad()?;
            buffer = buffer_after_nop;
            if buffer.is_empty() {
                break;
            }
            opcode = buffer.peek_opcode()?
        }
        Ok(((), buffer))
    }

    /// Interprets the length code in the provided [Header]; if necessary, will read more bytes
    /// from the buffer to interpret as the value's length. If it is successful, returns an `Ok(_)`
    /// containing a [FlexUInt] representation of the value's length. If no additional bytes were
    /// read, the returned `FlexUInt`'s `size_in_bytes()` method will return `0`.
    pub fn read_value_length(self, header: Header) -> ParseResult<'a, FlexUInt> {
        let length = match header.length_type() {
            LengthType::InOpcode(n) => {
                // FlexUInt represents the length, but is not physically present, hence the 0 size.
                FlexUInt::new(0, n as u64)
            }
            LengthType::FlexUIntFollows => {
                let (flexuint, _) = self.read_flex_uint()?;
                flexuint
            }
        };

        let remaining = self;

        // TODO: Validate length to ensure it is a reasonable value.

        Ok((length, remaining))
    }

    /// Reads a field ID and a value from the buffer.
    pub(crate) fn peek_field(self) -> IonResult<Option<LazyRawBinaryValue_1_1<'a>>> {
        todo!();
    }

    #[cold]
    /// Consumes (field ID, NOP pad) pairs until a non-NOP value is encountered in field position or
    /// the buffer is empty. Returns a buffer starting at the field ID before the non-NOP value.
    fn read_struct_field_nop_pad(self) -> IonResult<Option<(usize, VarUInt, ImmutableBuffer<'a>)>> {
        todo!();
    }

    /// Reads a value without a field name from the buffer. This is applicable in lists, s-expressions,
    /// and at the top level.
    pub(crate) fn peek_sequence_value(self) -> IonResult<Option<LazyRawBinaryValue_1_1<'a>>> {
        if self.is_empty() {
            return Ok(None);
        }
        let mut input = self;
        let mut type_descriptor = input.peek_opcode()?;
        // If we find a NOP...
        if type_descriptor.is_nop() {
            // ...skip through NOPs until we found the next non-NOP byte.
            (_, input) = self.consume_nop_padding(type_descriptor)?;
            // If there is no next byte, we're out of values.
            if input.is_empty() {
                return Ok(None);
            }
            // Otherwise, there's a value.
            type_descriptor = input.peek_opcode()?;
        }
        Ok(Some(input.read_value(type_descriptor)?))
    }

    /// Reads a value from the buffer. The caller must confirm that the buffer is not empty and that
    /// the next byte (`type_descriptor`) is not a NOP.
    fn read_value(self, type_descriptor: Opcode) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        if type_descriptor.is_annotation_wrapper() {
            self.read_annotated_value(type_descriptor)
        } else {
            self.read_value_without_annotations(type_descriptor)
        }
    }

    /// Reads a value from the buffer. The caller must confirm that the buffer is not empty and that
    /// the next byte (`type_descriptor`) is neither a NOP nor an annotations wrapper.
    fn read_value_without_annotations(
        self,
        type_descriptor: Opcode,
    ) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        let input = self;
        let header = type_descriptor
            .to_header()
            .ok_or_else(|| IonError::decoding_error("found a non-value in value position"))?;

        let header_offset = input.offset();
        let (length, _) = input.consume(1).read_value_length(header)?;
        let length_length = length.size_in_bytes() as u8;
        let value_length = length.value() as usize; // ha
        let total_length = 1 // Header byte
                + length_length as usize
                + value_length;

        let encoded_value = EncodedValue {
            header,
            // If applicable, these are populated by the caller: `read_annotated_value()`
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            header_offset,
            length_length,
            value_body_length: value_length,
            total_length,
        };
        let lazy_value = LazyRawBinaryValue_1_1 {
            encoded_value,
            // If this value has a field ID or annotations, this will be replaced by the caller.
            input: self,
        };
        Ok(lazy_value)
    }

    pub fn read_fixed_int(self, length: usize) -> ParseResult<'a, FixedInt> {
        let int_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("a FixedInt", self.offset()))?;
        let fixed_int = FixedInt::read(int_bytes, length, 0)?;
        Ok((fixed_int, self.consume(length)))
    }

    pub fn read_fixed_uint(self, length: usize) -> ParseResult<'a, FixedUInt> {
        let uint_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("a FixedUInt", self.offset()))?;
        let fixed_uint = FixedUInt::read(uint_bytes, length, 0)?;
        Ok((fixed_uint, self.consume(length)))
    }

    /// Reads an annotations wrapper and its associated value from the buffer. The caller must confirm
    /// that the next byte in the buffer (`type_descriptor`) begins an annotations wrapper.
    fn read_annotated_value(
        self,
        mut _type_descriptor: Opcode,
    ) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        todo!();
    }

}

/// Represents the data found in an Ion 1.0 annotations wrapper.
pub struct AnnotationsWrapper {
    pub header_length: u8,
    pub sequence_length: u8,
    pub expected_value_length: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn input_test<A: AsRef<[u8]>>(input: A) {
        let input = ImmutableBuffer::new(input.as_ref());
        // We can peek at the first byte...
        assert_eq!(input.peek_next_byte(), Some(b'f'));
        // ...without modifying the input. Looking at the next 3 bytes still includes 'f'.
        assert_eq!(input.peek_n_bytes(3), Some("foo".as_bytes()));
        // Advancing the cursor by 1...
        let input = input.consume(1);
        // ...causes next_byte() to return 'o'.
        assert_eq!(input.peek_next_byte(), Some(b'o'));
        let input = input.consume(1);
        assert_eq!(input.peek_next_byte(), Some(b'o'));
        let input = input.consume(1);
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
    fn validate_nop_length() {
        // read_nop_pad reads a single NOP value, this test ensures that we're tracking the right
        // size for these values.

        let buffer = ImmutableBuffer::new(&[0xECu8]);
        let (pad_size, _) = buffer.read_nop_pad().expect("unable to read NOP pad");
        assert_eq!(pad_size, 1);

        let buffer = ImmutableBuffer::new(&[0xEDu8, 0x05, 0x00, 0x00]);
        let (pad_size, _) = buffer.read_nop_pad().expect("unable to read NOP pad");
        assert_eq!(pad_size, 4);
    }
}
