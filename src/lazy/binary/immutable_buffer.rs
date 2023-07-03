use crate::binary::constants::v1_0::{length_codes, IVM};
use crate::binary::int::DecodedInt;
use crate::binary::non_blocking::type_descriptor::{
    Header, TypeDescriptor, ION_1_0_TYPE_DESCRIPTORS,
};
use crate::binary::uint::DecodedUInt;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::lazy::binary::encoded_value::EncodedValue;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::result::IonFailure;
use crate::types::UInt;
use crate::{Int, IonError, IonResult, IonType};
use num_bigint::{BigInt, BigUint, Sign};
use std::fmt::{Debug, Formatter};
use std::mem;

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
pub(crate) struct ImmutableBuffer<'a> {
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
    pub fn bytes(&self) -> &[u8] {
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

    /// Reads the first byte in the buffer and returns it as a [TypeDescriptor].
    #[inline]
    pub fn peek_type_descriptor(&self) -> IonResult<TypeDescriptor> {
        if self.is_empty() {
            return IonResult::incomplete("a type descriptor", self.offset());
        }
        let next_byte = self.data[0];
        Ok(ION_1_0_TYPE_DESCRIPTORS[next_byte as usize])
    }

    /// Reads the first four bytes in the buffer as an Ion version marker. If it is successful,
    /// returns an `Ok(_)` containing a `(major, minor)` version tuple.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#value-streams>
    pub fn read_ivm(self) -> ParseResult<'a, (u8, u8)> {
        let bytes = self
            .peek_n_bytes(IVM.len())
            .ok_or_else(|| IonError::incomplete("an IVM", self.offset()))?;

        match bytes {
            [0xE0, major, minor, 0xEA] => {
                let version = (*major, *minor);
                Ok((version, self.consume(IVM.len())))
            }
            invalid_ivm => IonResult::decoding_error(format!("invalid IVM: {invalid_ivm:?}")),
        }
    }

    /// Reads a `VarUInt` encoding primitive from the beginning of the buffer. If it is successful,
    /// returns an `Ok(_)` containing its [VarUInt] representation.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields>
    pub fn read_var_uint(self) -> ParseResult<'a, VarUInt> {
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
                return Ok((
                    VarUInt::new(magnitude, encoded_size_in_bytes),
                    self.consume(encoded_size_in_bytes),
                ));
            }
        }

        IonResult::incomplete("a VarUInt", self.offset() + encoded_size_in_bytes)
    }

    /// Reads a `VarInt` encoding primitive from the beginning of the buffer. If it is successful,
    /// returns an `Ok(_)` containing its [VarInt] representation.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields>
    pub fn read_var_int(self) -> ParseResult<'a, VarInt> {
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
            return IonResult::incomplete("a VarInt", self.offset());
        }
        let first_byte: u8 = self.peek_next_byte().unwrap();
        let no_more_bytes: bool = first_byte >= 0b1000_0000; // If the first bit is 1, we're done.
        let is_negative: bool = (first_byte & 0b0100_0000) == 0b0100_0000;
        let sign: i64 = if is_negative { -1 } else { 1 };
        let mut magnitude = (first_byte & 0b0011_1111) as i64;

        if no_more_bytes {
            return Ok((
                VarInt::new(magnitude * sign, is_negative, 1),
                self.consume(1),
            ));
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
            return IonResult::incomplete("a VarInt", self.offset() + encoded_size_in_bytes);
        }

        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return IonResult::decoding_error(format!(
                "Found a {encoded_size_in_bytes}-byte VarInt. Max supported size is {MAX_ENCODED_SIZE_IN_BYTES} bytes."
            ));
        }

        Ok((
            VarInt::new(magnitude * sign, is_negative, encoded_size_in_bytes),
            self.consume(encoded_size_in_bytes),
        ))
    }

    /// Reads the first `length` bytes from the buffer as a `UInt` encoding primitive. If it is
    /// successful, returns an `Ok(_)` containing its [DecodedUInt] representation.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields>
    pub fn read_uint(self, length: usize) -> ParseResult<'a, DecodedUInt> {
        if length <= mem::size_of::<u64>() {
            return self.read_small_uint(length);
        }

        // The UInt is too large to fit in a u64; read it as a BigUInt instead.
        self.read_big_uint(length)
    }

    /// Reads the first `length` bytes from the buffer as a `UInt`. The caller must confirm that
    /// `length` is small enough to fit in a `u64`.
    #[inline]
    fn read_small_uint(self, length: usize) -> ParseResult<'a, DecodedUInt> {
        let uint_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("a UInt", self.offset()))?;
        let magnitude = DecodedUInt::small_uint_from_slice(uint_bytes);
        Ok((
            DecodedUInt::new(UInt::from(magnitude), length),
            self.consume(length),
        ))
    }

    /// Reads the first `length` bytes from the buffer as a `UInt`. If `length` is small enough
    /// that the value can fit in a `usize`, it is strongly recommended that you use
    /// `read_small_uint` instead as it will be much faster.
    #[inline(never)]
    // This method performs allocations and its generated assembly is rather large. Isolating its
    // logic in a separate method that is never inlined keeps `read_uint` (its caller) small enough
    // to inline. This is important as `read_uint` is on the hot path for most Ion streams.
    fn read_big_uint(self, length: usize) -> ParseResult<'a, DecodedUInt> {
        if length > MAX_UINT_SIZE_IN_BYTES {
            return Self::value_too_large("a Uint", length, MAX_UINT_SIZE_IN_BYTES);
        }

        let uint_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("a UInt", self.offset()))?;

        let magnitude = BigUint::from_bytes_be(uint_bytes);
        Ok((
            DecodedUInt::new(UInt::from(magnitude), length),
            self.consume(length),
        ))
    }

    #[inline(never)]
    // This method is inline(never) because it is rarely invoked and its allocations/formatting
    // compile to a non-trivial number of instructions.
    fn value_too_large<T>(label: &str, length: usize, max_length: usize) -> IonResult<T> {
        IonResult::decoding_error(format!(
            "found {label} that was too large; size = {length}, max size = {max_length}"
        ))
    }

    /// Reads the first `length` bytes from the buffer as an `Int` encoding primitive. If it is
    /// successful, returns an `Ok(_)` containing its [DecodedInt] representation and consumes the
    /// source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields>
    pub fn read_int(self, length: usize) -> ParseResult<'a, DecodedInt> {
        if length == 0 {
            return Ok((DecodedInt::new(0, false, 0), self.consume(0)));
        } else if length > MAX_INT_SIZE_IN_BYTES {
            return IonResult::decoding_error(format!(
                "Found a {length}-byte Int. Max supported size is {MAX_INT_SIZE_IN_BYTES} bytes."
            ));
        }

        let int_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("an Int encoding primitive", self.offset()))?;

        let mut is_negative: bool = false;

        let value: Int = if length <= mem::size_of::<i64>() {
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
            (sign * magnitude).into()
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

            value.into()
        };
        Ok((
            DecodedInt::new(value, is_negative, length),
            self.consume(length),
        ))
    }

    /// Attempts to decode an annotations wrapper at the beginning of the buffer and returning
    /// its subfields in an [`AnnotationsWrapper`].
    pub fn read_annotations_wrapper(
        &self,
        type_descriptor: TypeDescriptor,
    ) -> ParseResult<'a, AnnotationsWrapper> {
        // Consume the first byte; its contents are already in the `type_descriptor` parameter.
        let input_after_type_descriptor = self.consume(1);

        // Read the combined length of the annotations sequence and the value that follows it
        let (annotations_and_value_length, input_after_combined_length) =
            match type_descriptor.length_code {
                length_codes::NULL => (0, input_after_type_descriptor),
                length_codes::VAR_UINT => {
                    let (var_uint, input) = input_after_type_descriptor.read_var_uint()?;
                    (var_uint.value(), input)
                }
                length => (length as usize, input_after_type_descriptor),
            };

        // Read the length of the annotations sequence
        let (annotations_length, input_after_annotations_length) =
            input_after_combined_length.read_var_uint()?;

        // Validate that the annotations sequence is not empty.
        if annotations_length.value() == 0 {
            return IonResult::decoding_error("found an annotations wrapper with no annotations");
        }

        // Validate that the annotated value is not missing.
        let expected_value_length = annotations_and_value_length
            - annotations_length.size_in_bytes()
            - annotations_length.value();

        if expected_value_length == 0 {
            return IonResult::decoding_error("found an annotation wrapper with no value");
        }

        // Skip over the annotations sequence itself; the reader will return to it if/when the
        // reader asks to iterate over those symbol IDs.
        let final_input = input_after_annotations_length.consume(annotations_length.value());

        // Here, `self` is the (immutable) buffer we started with. Comparing it with `input`
        // gets us the before-and-after we need to calculate the size of the header.
        let annotations_header_length = final_input.offset() - self.offset();
        let annotations_header_length = u8::try_from(annotations_header_length).map_err(|_e| {
            IonError::decoding_error("found an annotations header greater than 255 bytes long")
        })?;

        let annotations_sequence_length =
            u8::try_from(annotations_length.value()).map_err(|_e| {
                IonError::decoding_error(
                    "found an annotations sequence greater than 255 bytes long",
                )
            })?;

        let wrapper = AnnotationsWrapper {
            header_length: annotations_header_length,
            sequence_length: annotations_sequence_length,
            expected_value_length,
        };

        Ok((wrapper, final_input))
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
        let type_descriptor = self.peek_type_descriptor()?;
        // Advance beyond the type descriptor
        let remaining = self.consume(1);
        // If the type descriptor says we should skip more bytes, skip them.
        let (length, remaining) = remaining.read_length(type_descriptor.length_code)?;
        if remaining.len() < length.value() {
            return IonResult::incomplete("a NOP", remaining.offset());
        }
        let remaining = remaining.consume(length.value());
        let total_nop_pad_size = 1 + length.size_in_bytes() + length.value();
        Ok((total_nop_pad_size, remaining))
    }

    /// Calls [`Self::read_nop_pad`] in a loop until the buffer is empty or a type descriptor
    /// is encountered that is not a NOP.
    #[inline(never)]
    // NOP padding is not widely used in Ion 1.0. This method is annotated with `inline(never)`
    // to avoid the compiler bloating other methods on the hot path with its rarely used
    // instructions.
    pub fn consume_nop_padding(self, mut type_descriptor: TypeDescriptor) -> ParseResult<'a, ()> {
        let mut buffer = self;
        // Skip over any number of NOP regions
        while type_descriptor.is_nop() {
            let (_, buffer_after_nop) = buffer.read_nop_pad()?;
            buffer = buffer_after_nop;
            if buffer.is_empty() {
                break;
            }
            type_descriptor = buffer.peek_type_descriptor()?
        }
        Ok(((), buffer))
    }

    /// Interprets the length code in the provided [Header]; if necessary, will read more bytes
    /// from the buffer to interpret as the value's length. If it is successful, returns an `Ok(_)`
    /// containing a [VarUInt] representation of the value's length. If no additional bytes were
    /// read, the returned `VarUInt`'s `size_in_bytes()` method will return `0`.
    pub fn read_value_length(self, header: Header) -> ParseResult<'a, VarUInt> {
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
        let (length, remaining) = self.read_length(length_code)?;

        // After we get the length, perform some type-specific validation.
        match header.ion_type {
            Float => match header.length_code {
                0 | 4 | 8 | 15 => {}
                _ => return IonResult::decoding_error("found a float with an illegal length code"),
            },
            Timestamp if !header.is_null() && length.value() <= 1 => {
                return IonResult::decoding_error("found a timestamp with length <= 1")
            }
            Struct if header.length_code == 1 && length.value() == 0 => {
                return IonResult::decoding_error("found an empty ordered struct")
            }
            _ => {}
        };

        Ok((length, remaining))
    }

    /// Interprets a type descriptor's `L` nibble (length) in the way used by most Ion types.
    ///
    /// If `L` is...
    ///   * `f`: the value is a typed `null` and its length is `0`.
    ///   * `e`: the length is encoded as a `VarUInt` that follows the type descriptor.
    ///   * anything else: the `L` represents the actual length.
    ///
    /// If successful, returns an `Ok(_)` that contains the [VarUInt] representation
    /// of the value's length.
    pub fn read_length(self, length_code: u8) -> ParseResult<'a, VarUInt> {
        let length = match length_code {
            length_codes::NULL => VarUInt::new(0, 0),
            length_codes::VAR_UINT => return self.read_var_uint(),
            magnitude => VarUInt::new(magnitude as usize, 0),
        };

        // If we reach this point, the length was in the header byte and no additional bytes were
        // consumed
        Ok((length, self))
    }

    /// Reads a field ID and a value from the buffer.
    pub(crate) fn peek_field(self) -> IonResult<Option<LazyRawValue<'a>>> {
        self.peek_value(true)
    }

    /// Reads a value from the buffer.
    pub(crate) fn peek_value_without_field_id(self) -> IonResult<Option<LazyRawValue<'a>>> {
        self.peek_value(false)
    }

    /// Reads a value from the buffer. If `has_field` is true, it will read a field ID first.
    // This method consumes leading NOP bytes, but leaves the header representation in the buffer.
    // The resulting LazyRawValue's buffer slice always starts with the first non-NOP byte in the
    // header, which can be either a field ID, an annotations wrapper, or a type descriptor.
    fn peek_value(self, has_field: bool) -> IonResult<Option<LazyRawValue<'a>>> {
        let initial_input = self;
        if initial_input.is_empty() {
            return Ok(None);
        }
        let (field_id, field_id_length, mut input) = if has_field {
            let (field_id_var_uint, input_after_field_id) = initial_input.read_var_uint()?;
            if input_after_field_id.is_empty() {
                return IonResult::incomplete(
                    "found field name but no value",
                    input_after_field_id.offset(),
                );
            }
            let field_id_length =
                u8::try_from(field_id_var_uint.size_in_bytes()).map_err(|_| {
                    IonError::decoding_error("found a field id with length over 255 bytes")
                })?;
            (
                Some(field_id_var_uint.value()),
                field_id_length,
                input_after_field_id,
            )
        } else {
            (None, 0, initial_input)
        };

        let mut annotations_header_length = 0u8;
        let mut annotations_sequence_length = 0u8;
        let mut expected_value_length = None;

        let mut type_descriptor = input.peek_type_descriptor()?;
        if type_descriptor.is_annotation_wrapper() {
            let (wrapper, input_after_annotations) =
                input.read_annotations_wrapper(type_descriptor)?;
            annotations_header_length = wrapper.header_length;
            annotations_sequence_length = wrapper.sequence_length;
            expected_value_length = Some(wrapper.expected_value_length);
            input = input_after_annotations;
            type_descriptor = input.peek_type_descriptor()?;
            if type_descriptor.is_annotation_wrapper() {
                return IonResult::decoding_error("found an annotations wrapper ");
            }
        } else if type_descriptor.is_nop() {
            (_, input) = input.consume_nop_padding(type_descriptor)?;
        }

        let header = type_descriptor
            .to_header()
            .ok_or_else(|| IonError::decoding_error("found a non-value in value position"))?;

        let header_offset = input.offset();
        let (length, _) = input.consume(1).read_value_length(header)?;
        let length_length = u8::try_from(length.size_in_bytes()).map_err(|_e| {
            IonError::decoding_error("found a value with a header length field over 255 bytes long")
        })?;
        let value_length = length.value(); // ha
        let total_length = field_id_length as usize
            + annotations_header_length as usize
            + 1 // Header byte
            + length_length as usize
            + value_length;

        if let Some(expected_value_length) = expected_value_length {
            let actual_value_length = 1 + length_length as usize + value_length;
            if expected_value_length != actual_value_length {
                println!("{} != {}", expected_value_length, actual_value_length);
                return IonResult::decoding_error(
                    "value length did not match length declared by annotations wrapper",
                );
            }
        }

        let encoded_value = EncodedValue {
            header,
            field_id_length,
            field_id,
            annotations_header_length,
            annotations_sequence_length,
            header_offset,
            length_length,
            value_length,
            total_length,
        };
        let lazy_value = LazyRawValue {
            encoded_value,
            input: initial_input,
        };
        Ok(Some(lazy_value))
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
    use crate::IonError;
    use num_traits::Num;

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
    fn read_var_uint() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]);
        let var_uint = buffer.read_var_uint()?.0;
        assert_eq!(3, var_uint.size_in_bytes());
        assert_eq!(1_984_385, var_uint.value());
        Ok(())
    }

    #[test]
    fn read_var_uint_zero() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b1000_0000]);
        let var_uint = buffer.read_var_uint()?.0;
        assert_eq!(var_uint.size_in_bytes(), 1);
        assert_eq!(var_uint.value(), 0);
        Ok(())
    }

    #[test]
    fn read_var_uint_two_bytes_max_value() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_uint = buffer.read_var_uint()?.0;
        assert_eq!(var_uint.size_in_bytes(), 2);
        assert_eq!(var_uint.value(), 16_383);
        Ok(())
    }

    #[test]
    fn read_incomplete_var_uint() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1001, 0b0000_1111]);
        match buffer.read_var_uint() {
            Err(IonError::Incomplete { .. }) => Ok(()),
            other => panic!("expected IonError::Incomplete, but found: {other:?}"),
        }
    }

    #[test]
    fn read_var_uint_overflow_detection() {
        let buffer = ImmutableBuffer::new(&[
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
        let buffer = ImmutableBuffer::new(&[0b1000_0000]);
        let var_int = buffer.read_var_int()?.0;
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), 0);
        Ok(())
    }

    #[test]
    fn read_negative_var_int() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]);
        let var_int = buffer.read_var_int()?.0;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), -935_809);
        Ok(())
    }

    #[test]
    fn read_positive_var_int() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0011_1001, 0b0000_1111, 0b1000_0001]);
        let var_int = buffer.read_var_int()?.0;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), 935_809);
        Ok(())
    }

    #[test]
    fn read_var_int_two_byte_min() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_int = buffer.read_var_int()?.0;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), -8_191);
        Ok(())
    }

    #[test]
    fn read_var_int_two_byte_max() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0011_1111, 0b1111_1111]);
        let var_int = buffer.read_var_int()?.0;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), 8_191);
        Ok(())
    }

    #[test]
    fn read_var_int_overflow_detection() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[
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
        let buffer = ImmutableBuffer::new(&[0b1000_0000]);
        let var_int = buffer.read_uint(buffer.len())?.0;
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), &UInt::from(128u64));
        Ok(())
    }

    #[test]
    fn read_two_byte_uint() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_int = buffer.read_uint(buffer.len())?.0;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), &UInt::from(32_767u64));
        Ok(())
    }

    #[test]
    fn read_three_byte_uint() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0011_1100, 0b1000_0111, 0b1000_0001]);
        let var_int = buffer.read_uint(buffer.len())?.0;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), &UInt::from(3_966_849u64));
        Ok(())
    }

    #[test]
    fn test_read_ten_byte_uint() -> IonResult<()> {
        let data = vec![0xFFu8; 10];
        let buffer = ImmutableBuffer::new(&data);
        let uint = buffer.read_uint(buffer.len())?.0;
        assert_eq!(uint.size_in_bytes(), 10);
        assert_eq!(
            uint.value(),
            &UInt::from(BigUint::from_str_radix("ffffffffffffffffffff", 16).unwrap())
        );
        Ok(())
    }

    #[test]
    fn test_read_uint_too_large() {
        let mut buffer = Vec::with_capacity(MAX_UINT_SIZE_IN_BYTES + 1);
        buffer.resize(MAX_UINT_SIZE_IN_BYTES + 1, 1);
        let buffer = ImmutableBuffer::new(&buffer);
        let _uint = buffer
            .read_uint(buffer.len())
            .expect_err("This exceeded the configured max UInt size.");
    }

    #[test]
    fn read_int_negative_zero() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b1000_0000]); // Negative zero
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Int::from(0));
        assert!(int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_int_positive_zero() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0000_0000]); // Negative zero
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Int::from(0));
        assert!(!int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_int_length_zero() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[]); // Negative zero
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 0);
        assert_eq!(int.value(), &Int::from(0));
        assert!(!int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_two_byte_negative_int() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b1111_1111, 0b1111_1111]);
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Int::from(-32_767i64));
        Ok(())
    }

    #[test]
    fn read_two_byte_positive_int() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Int::from(32_767i64));
        Ok(())
    }

    #[test]
    fn read_three_byte_negative_int() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b1011_1100, 0b1000_0111, 0b1000_0001]);
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Int::from(-3_966_849i64));
        Ok(())
    }

    #[test]
    fn read_three_byte_positive_int() -> IonResult<()> {
        let buffer = ImmutableBuffer::new(&[0b0011_1100, 0b1000_0111, 0b1000_0001]);
        let int = buffer.read_int(buffer.len())?.0;
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Int::from(3_966_849i64));
        Ok(())
    }

    #[test]
    fn read_int_overflow() -> IonResult<()> {
        let data = vec![1; MAX_INT_SIZE_IN_BYTES + 1];
        let buffer = ImmutableBuffer::new(&data); // Negative zero
        buffer
            .read_int(buffer.len())
            .expect_err("This exceeded the configured max Int size.");
        Ok(())
    }
}
