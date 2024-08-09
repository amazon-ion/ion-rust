use ice_code::ice as cold_path;
use std::fmt::{Debug, Formatter};
use std::mem;
use std::ops::{Neg, Range};

use crate::binary::constants::v1_0::{length_codes, IVM};
use crate::binary::int::DecodedInt;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::lazy::binary::encoded_value::EncodedValue;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryFieldName_1_0;
use crate::lazy::binary::raw::type_descriptor::{Header, TypeDescriptor, ION_1_0_TYPE_DESCRIPTORS};
use crate::lazy::binary::raw::v1_1::immutable_buffer::AnnotationsEncoding;
use crate::lazy::binary::raw::value::{LazyRawBinaryValue_1_0, LazyRawBinaryVersionMarker_1_0};
use crate::lazy::decoder::LazyRawFieldExpr;
use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;
use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::lazy::expanded::template::ParameterEncoding;
use crate::result::IonFailure;
use crate::{Int, IonError, IonResult, IonType};

const MAX_INT_SIZE_IN_BYTES: usize = mem::size_of::<i128>();

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

    /// Reads the first byte in the buffer and returns it as a [TypeDescriptor].
    #[inline]
    pub(crate) fn peek_type_descriptor(&self) -> IonResult<TypeDescriptor> {
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
    pub fn read_ivm(self) -> ParseResult<'a, LazyRawBinaryVersionMarker_1_0<'a>> {
        let bytes = self
            .peek_n_bytes(IVM.len())
            .ok_or_else(|| IonError::incomplete("an IVM", self.offset()))?;

        match bytes {
            [0xE0, major, minor, 0xEA] => {
                let matched = ImmutableBuffer::new_with_offset(bytes, self.offset);
                let marker = LazyRawBinaryVersionMarker_1_0::new(matched, *major, *minor);
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

    /// Reads a `VarUInt` encoding primitive from the beginning of the buffer. If it is successful,
    /// returns an `Ok(_)` containing its [VarUInt] representation.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#varuint-and-varint-fields>
    #[inline]
    pub fn read_var_uint(self) -> ParseResult<'a, VarUInt> {
        const LOWER_7_BITMASK: u8 = 0b0111_1111;
        const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

        // Reading a `VarUInt` is one of the hottest paths in the binary 1.0 reader.
        // Because `VarUInt`s represent struct field names, annotations, and value lengths,
        // smaller values are more common than larger values. As an optimization, we have a
        // dedicated code path for the decoding of 1- and 2-byte VarUInts. This allows the logic
        // for the most common cases to be inlined and the logic for the less common cases
        // (including errors) to be a function call.

        let data = self.bytes();
        // The 'fast path' first checks whether we have at least two bytes available. This allows us
        // to do a single length check on the fast path. If there's one byte in the buffer that
        // happens to be a complete VarUInt (a very rare occurrence), it will still be handled by
        // `read_var_uint_slow()`.
        if data.len() >= 2 {
            let first_byte = data[0];
            let mut magnitude = (LOWER_7_BITMASK & first_byte) as usize;
            let num_bytes = if first_byte >= HIGHEST_BIT_VALUE {
                1
            } else {
                let second_byte = data[1];
                if second_byte < HIGHEST_BIT_VALUE {
                    return self.read_var_uint_slow();
                }
                let lower_seven = (LOWER_7_BITMASK & second_byte) as usize;
                magnitude <<= 7;
                magnitude |= lower_seven;
                2
            };
            return Ok((VarUInt::new(magnitude, num_bytes), self.consume(num_bytes)));
        }

        // All other VarUInt sizes and error cases (incomplete data, oversized, etc) are handled by
        // this more general decoding loop.
        self.read_var_uint_slow()
    }

    #[cold]
    pub fn read_var_uint_slow(self) -> ParseResult<'a, VarUInt> {
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

    #[inline(never)]
    // This method is inline(never) because it is rarely invoked and its allocations/formatting
    // compile to a non-trivial number of instructions.
    fn value_too_large<T>(label: &str, length: usize, max_length: usize) -> IonResult<T> {
        IonResult::decoding_error(format!(
            "found {label} that was too large; size = {length}, max size = {max_length}"
        ))
    }

    /// Reads the first `length` bytes from the buffer as an `Int` encoding primitive. If it is
    /// successful, returns an `Ok(_)` containing its `DecodedInt` representation and consumes the
    /// source bytes.
    ///
    /// See: <https://amazon-ion.github.io/ion-docs/docs/binary.html#uint-and-int-fields>
    pub fn read_int(self, length: usize) -> ParseResult<'a, DecodedInt> {
        const BUFFER_SIZE: usize = MAX_INT_SIZE_IN_BYTES;
        if length == 0 {
            return Ok((DecodedInt::new(0, false, 0), self.consume(0)));
        } else if length > BUFFER_SIZE + 1 {
            //                         ^^^
            // We support reading i128::MIN, which requires 17 bytes to encode. We reject anything
            // 18 bytes or larger here; later on, we reject 17-byte encodings of values other than
            // i128::MIN.
            return cold_path! {
            IonResult::decoding_error(format!(
                "Found a {length}-byte Int. Max supported size is {MAX_INT_SIZE_IN_BYTES} bytes."
            ))};
        }

        let int_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("an Int encoding primitive", self.offset()))?;

        // i128::MIN is a special case; it's the only 17-byte encoding we accept.
        const INT_MIN_ENCODING: &[u8] = &[0x80, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        if length == INT_MIN_ENCODING.len() {
            return cold_path! {{
                if int_bytes != INT_MIN_ENCODING {
                    IonResult::decoding_error("Found an int encoding primitive outside the supported range")
                } else {
                    Ok((
                        DecodedInt::new(Int::from(i128::MIN), true, length),
                        self.consume(length),
                    ))
                }
            }};
        }

        // Copy the 'n' bytes into a buffer known to be the exact size of a u128
        let mut buffer = [0u8; mem::size_of::<u128>()];
        let first_occupied_byte_index = buffer.len() - int_bytes.len();
        buffer[first_occupied_byte_index..].copy_from_slice(int_bytes);

        let is_negative: bool = int_bytes[0] & 0b1000_0000 != 0;
        // Unset the sign bit in the buffer
        buffer[first_occupied_byte_index] &= 0b0111_1111;

        // Now our sign-and-magnitude encoding is just a magnitude.
        let magnitude = u128::from_be_bytes(buffer);
        let mut value = i128::try_from(magnitude).unwrap();
        if is_negative {
            value = value.neg();
        }
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
        if input_after_annotations_length.len() < annotations_length.value() {
            return IonResult::incomplete(
                "an annotations sequence",
                input_after_annotations_length.offset(),
            );
        }
        // Here, `self` is the (immutable) buffer we started with. Comparing it with `input_after_annotations_length`
        // gets us the before-and-after comparison we need to calculate the size of the header.
        // "Header" here refers to the annotations opcode, wrapper length, and sequence length. It does
        // not include the length of the sequence itself.
        let annotations_header_length = input_after_annotations_length.offset() - self.offset();
        let annotations_header_length = u8::try_from(annotations_header_length).map_err(|_e| {
            IonError::decoding_error("found an annotations header greater than 255 bytes long")
        })?;

        let final_input = input_after_annotations_length.consume(annotations_length.value());

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
    #[inline]
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
    pub(crate) fn peek_field(self) -> IonResult<Option<LazyRawFieldExpr<'a, BinaryEncoding_1_0>>> {
        let mut input = self;
        if self.is_empty() {
            // We're at the end of the struct
            return Ok(None);
        }
        // Read the field ID
        let (mut field_id_var_uint, mut input_after_field_id) = input.read_var_uint()?;
        if input_after_field_id.is_empty() {
            return IonResult::incomplete(
                "found field name but no value",
                input_after_field_id.offset(),
            );
        }

        let mut type_descriptor = input_after_field_id.peek_type_descriptor()?;
        if type_descriptor.is_nop() {
            // Read past NOP fields until we find the first one that's an actual value
            // or we run out of struct bytes. Note that we read the NOP field(s) from `input` (the
            // initial input) rather than `input_after_field_id` because it simplifies
            // the logic of `read_struct_field_nop_pad()`, which is very rarely called.
            (field_id_var_uint, input_after_field_id) = match input.read_struct_field_nop_pad()? {
                None => {
                    // There are no more fields, we're at the end of the struct.
                    return Ok(None);
                }
                Some((nop_length, field_id_var_uint, input_after_field_id)) => {
                    // Advance `input` beyond the NOP so that when we store it in the value it begins
                    // with the field ID.
                    input = input.consume(nop_length);
                    type_descriptor = input_after_field_id.peek_type_descriptor()?;
                    (field_id_var_uint, input_after_field_id)
                }
            };
        }

        let field_id = field_id_var_uint.value();
        let matched_field_id = input.slice(0, field_id_var_uint.size_in_bytes());
        let field_name = LazyRawBinaryFieldName_1_0::new(field_id, matched_field_id);

        let field_value = input_after_field_id.read_value(type_descriptor)?;
        Ok(Some(LazyRawFieldExpr::NameValue(field_name, field_value)))
    }

    #[cold]
    /// Consumes (field ID, NOP pad) pairs until a non-NOP value is encountered in field position or
    /// the buffer is empty. Returns a buffer starting at the field ID before the non-NOP value.
    fn read_struct_field_nop_pad(self) -> IonResult<Option<(usize, VarUInt, ImmutableBuffer<'a>)>> {
        let mut input_before_field_id = self;
        loop {
            if input_before_field_id.is_empty() {
                return Ok(None);
            }
            let (field_id_var_uint, input_after_field_id) =
                input_before_field_id.read_var_uint()?;
            // If we're out of data (i.e. there's no field value) the struct is incomplete.
            if input_after_field_id.is_empty() {
                return IonResult::incomplete(
                    "found a field name but no value",
                    input_after_field_id.offset(),
                );
            }
            // Peek at the next value header. If it's a NOP, we need to repeat the process.
            if input_after_field_id.peek_type_descriptor()?.is_nop() {
                // Consume the NOP to position the buffer at the beginning of the next field ID.
                (_, input_before_field_id) = input_after_field_id.read_nop_pad()?;
            } else {
                // If it isn't a NOP, return the field ID and the buffer slice containing the field
                // value.
                let nop_length = input_before_field_id.offset() - self.offset();
                return Ok(Some((nop_length, field_id_var_uint, input_after_field_id)));
            }
        }
    }

    /// Reads a value without a field name from the buffer. This is applicable in lists, s-expressions,
    /// and at the top level.
    pub(crate) fn peek_sequence_value(self) -> IonResult<Option<LazyRawBinaryValue_1_0<'a>>> {
        if self.is_empty() {
            return Ok(None);
        }
        let mut input = self;
        let mut type_descriptor = input.peek_type_descriptor()?;
        // If we find a NOP...
        if type_descriptor.is_nop() {
            // ...skip through NOPs until we found the next non-NOP byte.
            (_, input) = self.consume_nop_padding(type_descriptor)?;
            // If there is no next byte, we're out of values.
            if input.is_empty() {
                return Ok(None);
            }
            // Otherwise, there's a value.
            type_descriptor = input.peek_type_descriptor()?;
        }
        Ok(Some(input.read_value(type_descriptor)?))
    }

    /// Reads a value from the buffer. The caller must confirm that the buffer is not empty and that
    /// the next byte (`type_descriptor`) is not a NOP.
    fn read_value(self, type_descriptor: TypeDescriptor) -> IonResult<LazyRawBinaryValue_1_0<'a>> {
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
        type_descriptor: TypeDescriptor,
    ) -> IonResult<LazyRawBinaryValue_1_0<'a>> {
        let input = self;
        let header = type_descriptor
            .to_header()
            .ok_or_else(|| IonError::decoding_error("found a non-value in value position"))?;

        let header_offset = input.offset();
        let (length, _) = input.consume(1).read_value_length(header)?;
        let length_length = length.size_in_bytes() as u8;
        let value_length = length.value(); // ha
        let total_length = 1 // Header byte
                + length_length as usize
                + value_length;

        if total_length > input.len() {
            return IonResult::incomplete(
                "the stream ended unexpectedly in the middle of a value",
                header_offset,
            );
        }

        let encoded_value = EncodedValue {
            encoding: ParameterEncoding::Tagged,
            header,
            // If applicable, these are populated by the caller: `read_annotated_value()`
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            annotations_encoding: AnnotationsEncoding::SymbolAddress,
            header_offset,
            opcode_length: 1,
            length_length,
            value_body_length: value_length,
            total_length,
        };
        let lazy_value = LazyRawBinaryValue_1_0 {
            encoded_value,
            // If this value has a field ID or annotations, this will be replaced by the caller.
            input: self,
        };
        Ok(lazy_value)
    }

    /// Reads an annotations wrapper and its associated value from the buffer. The caller must confirm
    /// that the next byte in the buffer (`type_descriptor`) begins an annotations wrapper.
    fn read_annotated_value(
        self,
        mut type_descriptor: TypeDescriptor,
    ) -> IonResult<LazyRawBinaryValue_1_0<'a>> {
        let input = self;
        let (wrapper, input_after_annotations) = input.read_annotations_wrapper(type_descriptor)?;
        type_descriptor = input_after_annotations.peek_type_descriptor()?;

        // Confirm that the next byte begins a value, not a NOP or another annotations wrapper.
        if type_descriptor.is_annotation_wrapper() {
            return IonResult::decoding_error(
                "found an annotations wrapper inside an annotations wrapper",
            );
        } else if type_descriptor.is_nop() {
            return IonResult::decoding_error("found a NOP inside an annotations wrapper");
        }

        let mut lazy_value =
            input_after_annotations.read_value_without_annotations(type_descriptor)?;
        if wrapper.expected_value_length != lazy_value.encoded_value.total_length() {
            return IonResult::decoding_error(
                "value length did not match length declared by annotations wrapper",
            );
        }

        lazy_value.encoded_value.annotations_header_length = wrapper.header_length;
        lazy_value.encoded_value.annotations_sequence_length = wrapper.sequence_length as u16;
        lazy_value.encoded_value.total_length +=
            lazy_value.encoded_value.annotations_total_length();
        // Modify the input to include the annotations
        lazy_value.input = input;

        Ok(lazy_value)
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
    use crate::{Int, IonError};

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
        let buffer = ImmutableBuffer::new(&[0b0000_0000]); // Positive zero
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
