use std::fmt::{Debug, Formatter};
use std::ops::Range;

use bumpalo::collections::Vec as BumpVec;

use crate::binary::constants::v1_1::IVM;
use crate::lazy::binary::encoded_value::EncodedValue;
use crate::lazy::binary::raw::v1_1::e_expression::{EncodedBinaryEExp, RawBinaryEExpression_1_1};
use crate::lazy::binary::raw::v1_1::value::{
    LazyRawBinaryValue_1_1, LazyRawBinaryVersionMarker_1_1,
};
use crate::lazy::binary::raw::v1_1::{Header, LengthType, Opcode, OpcodeType, ION_1_1_OPCODES};
use crate::lazy::decoder::{LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;
use crate::lazy::encoder::binary::v1_1::flex_sym::{FlexSym, FlexSymValue};
use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
use crate::lazy::expanded::macro_table::MacroKind;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::result::IonFailure;
use crate::{v1_1, HasRange, IonError, IonResult};


/// A buffer of unsigned bytes that can be cheaply copied and which defines methods for parsing
/// the various encoding elements of a binary Ion stream.
///
/// Upon success, each parsing method on the `ImmutableBuffer` will return the value that was read
/// and a copy of the `ImmutableBuffer` that starts _after_ the bytes that were parsed.
///
/// Methods that `peek` at the input stream do not return a copy of the buffer.
#[derive(Clone, Copy)]
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
    context: EncodingContextRef<'a>,
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
    pub fn new(context: EncodingContextRef<'a>, data: &'a [u8]) -> ImmutableBuffer<'a> {
        Self::new_with_offset(context, data, 0)
    }

    pub fn new_with_offset(
        context: EncodingContextRef<'a>,
        data: &'a [u8],
        offset: usize,
    ) -> ImmutableBuffer<'a> {
        ImmutableBuffer {
            data,
            offset,
            context,
        }
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
            context: self.context,
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
            context: self.context,
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
                let matched = ImmutableBuffer::new_with_offset(self.context, bytes, self.offset);
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

    #[inline]
    pub fn read_flex_sym(self) -> ParseResult<'a, FlexSym<'a>> {
        let flex_sym = FlexSym::read(self.bytes(), self.offset())?;
        let remaining = self.consume(flex_sym.size_in_bytes());
        Ok((flex_sym, remaining))
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
        let (size, remaining) = if opcode.low_nibble() == 0xC {
            // Size 0; the nop is contained entirely within the OpCode.
            (0, self.consume(1))
        } else if opcode.low_nibble() == 0xD {
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
    pub fn read_value_length(self, header: Header) -> ParseResult<'a, Option<FlexUInt>> {
        let length = match header.length_type() {
            LengthType::InOpcode(n) => {
                // FlexUInt represents the length, but is not physically present, hence the 0 size.
                FlexUInt::new(0, n as u64)
            }
            LengthType::FlexUIntFollows => {
                let (flexuint, _) = self.read_flex_uint()?;
                flexuint
            }
            LengthType::Unknown => return Ok((None, self)),
        };

        let remaining = self;

        // TODO: Validate length to ensure it is a reasonable value.

        Ok((Some(length), remaining))
    }

    /// Reads a value without a field name from the buffer. This is applicable in lists, s-expressions,
    /// and at the top level.
    pub(crate) fn peek_sequence_value_expr(
        self,
    ) -> IonResult<Option<LazyRawValueExpr<'a, v1_1::Binary>>> {
        if self.is_empty() {
            return Ok(None);
        }
        let mut input = self;
        let mut opcode = input.peek_opcode()?;
        // If we find a NOP...
        if opcode.is_nop() {
            // ...skip through NOPs until we found the next non-NOP byte.
            (_, input) = self.consume_nop_padding(opcode)?;
            // If there is no next byte, we're out of values.
            if input.is_empty() {
                return Ok(None);
            }
            // Otherwise, there's a value.
            opcode = input.peek_opcode()?;
        }
        if opcode.is_e_expression() {
            return Ok(Some(RawValueExpr::EExp(
                self.read_e_expression(opcode)?,
            )));
        }
        Ok(Some(RawValueExpr::ValueLiteral(
            input.read_value(opcode)?,
        )))
    }

    pub(crate) fn peek_delimited_container(
        self,
        opcode: Opcode,
    ) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        use crate::IonType;

        if let Some(IonType::Struct) = opcode.ion_type {
            self.peek_delimited_struct()
        } else {
            self.peek_delimited_sequence()
        }
    }

    pub(crate) fn peek_delimited_sequence(self) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        let head_opcode = self.peek_opcode()?;

        let mut input = self.consume(1);
        let header_offset = input.offset();
        let mut offsets = BumpVec::<usize>::new_in(self.context.allocator());

        loop {
            let opcode = input.peek_opcode()?;
            if opcode.opcode_type == OpcodeType::DelimitedContainerClose {
                offsets.push(input.offset());
                break;
            } else if opcode.opcode_type == OpcodeType::Nop {
                let res = input.consume_nop_padding(opcode)?;
                input = res.1;
            } else if let Some(value) = ImmutableBuffer::peek_sequence_value_expr(input)? {
                offsets.push(input.offset());
                input = input.consume(value.range().len());
            }
        }

        let header = head_opcode
            .to_header()
            .ok_or_else(|| IonError::decoding_error("found a non-value in value position"))?;

        let value_body_length = *offsets.last().unwrap() - header_offset;
        let total_length = 2 + value_body_length; // Opcode + Delimiter + Length

        let encoded_value = EncodedValue {
            header,
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            annotations_encoding: AnnotationsEncoding::SymbolAddress,
            header_offset,
            length_length: 0,
            total_length,
            value_body_length,
        };
        let lazy_value = LazyRawBinaryValue_1_1 {
            encoded_value,
            input: self,
            delimited_offsets: Some(offsets.into_bump_slice()),
        };
        Ok(lazy_value)
    }

    pub(crate) fn peek_delimited_struct(self) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        use crate::lazy::binary::raw::v1_1::OpcodeType;

        let head_opcode = self.peek_opcode()?;
        let mut input = self.consume(1);
        let mut offsets = BumpVec::<usize>::new_in(self.context.allocator());
        let header_offset = input.offset();

        loop {
            let (flexsym, after) = input.read_flex_sym()?;
            let field_offset = match flexsym.value() {
                FlexSymValue::SymbolRef(_sym) => input.offset(),
                FlexSymValue::Opcode(Opcode { opcode_type: OpcodeType::DelimitedContainerClose, ..}) => {
                    offsets.push(after.offset() - 1);
                    break
                }
                _ => unreachable!(),
            };
            input = after;

            let mut opcode = input.peek_opcode()?;
            if opcode.opcode_type == OpcodeType::Nop {
                let res = input.consume_nop_padding(opcode)?;
                input = res.1;
                opcode = input.peek_opcode()?;
            }
            let value = input.read_value(opcode)?;
            input = input.consume(value.encoded_value.total_length());
            offsets.push(field_offset);
        }

        let header = head_opcode
            .to_header()
            .ok_or_else(|| IonError::decoding_error("found a non-value in value position"))?;
        let value_body_length = *offsets.last().unwrap() - header_offset;
        let total_length = 2 + value_body_length;

        let encoded_value = EncodedValue {
            header,
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            annotations_encoding: AnnotationsEncoding::SymbolAddress,
            header_offset,
            length_length: 0,
            total_length,
            value_body_length,
        };

        let lazy_value = LazyRawBinaryValue_1_1 {
            encoded_value,
            input: self,
            delimited_offsets: Some(offsets.into_bump_slice()),
        };

        Ok(lazy_value)
    }

    /// Reads a value from the buffer. The caller must confirm that the buffer is not empty and that
    /// the next byte (`type_descriptor`) is not a NOP.
    pub fn read_value(self, opcode: Opcode) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        if opcode.is_annotations_sequence() {
            self.read_annotated_value(opcode)
        } else {
            self.read_value_without_annotations(opcode)
        }
    }

    /// Reads a value from the buffer. The caller must confirm that the buffer is not empty and that
    /// the next byte (`type_descriptor`) is neither a NOP nor an annotations wrapper.
    fn read_value_without_annotations(
        self,
        opcode: Opcode,
    ) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        let input = self;
        let header = opcode
            .to_header()
            .ok_or_else(|| IonError::decoding_error("found a non-value in value position .."))?;

        if opcode.is_delimited() {
            self.peek_delimited_container(opcode)
        } else {
            let header_offset = input.offset();
            let length = match input.consume(1).read_value_length(header)? {
                (None, _) => FlexUInt::new(0, 0), // Delimited value, we do not know the size.
                (Some(length), _) => length,
            };
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
                annotations_encoding: AnnotationsEncoding::SymbolAddress,
                header_offset,
                length_length,
                value_body_length: value_length,
                total_length,
            };
            let lazy_value = LazyRawBinaryValue_1_1 {
                encoded_value,
                // If this value has a field ID or annotations, this will be replaced by the caller.
                input: self,
                delimited_offsets: None,
            };
            Ok(lazy_value)
        }
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
    fn read_annotated_value(self, opcode: Opcode) -> IonResult<LazyRawBinaryValue_1_1<'a>> {
        let (annotations_seq, input_after_annotations) = self.read_annotations_sequence(opcode)?;
        let opcode = input_after_annotations.peek_opcode()?;
        let mut value = input_after_annotations.read_value_without_annotations(opcode)?;
        let total_annotations_length =
            annotations_seq.header_length as usize + annotations_seq.sequence_length as usize;
        value.encoded_value.annotations_header_length = total_annotations_length as u16;
        value.encoded_value.annotations_sequence_length = annotations_seq.sequence_length;
        value.encoded_value.annotations_encoding = annotations_seq.encoding;
        value.encoded_value.total_length += total_annotations_length;
        // Rewind the input to include the annotations sequence
        value.input = self;
        Ok(value)
    }

    fn read_annotations_sequence(self, opcode: Opcode) -> ParseResult<'a, EncodedAnnotations> {
        match opcode.opcode_type {
            OpcodeType::AnnotationFlexSym => self.read_flex_sym_annotations_sequence(opcode),
            OpcodeType::SymbolAddress => self.read_symbol_address_annotations_sequence(opcode),
            _ => unreachable!("read_annotations_sequence called for non-annotations opcode"),
        }
    }

    fn read_flex_sym_annotations_sequence(
        self,
        opcode: Opcode,
    ) -> ParseResult<'a, EncodedAnnotations> {
        let input_after_opcode = self.consume(1);
        // TODO: This implementation actively reads the annotations, which isn't necessary.
        //       At this phase of parsing we can just identify the buffer slice that contains
        //       the annotations and remember their encoding; later on, the annotations iterator
        //       can actually do the reading. That optimization would be impactful for FlexSyms
        //       that represent inline text.
        let (sequence, remaining_input) = match opcode.low_nibble() {
            7 => {
                let (flex_sym, remaining_input) = input_after_opcode.read_flex_sym()?;
                let sequence = EncodedAnnotations {
                    encoding: AnnotationsEncoding::FlexSym,
                    header_length: 1, // 0xE7
                    sequence_length: u16::try_from(flex_sym.size_in_bytes()).map_err(|_| {
                        IonError::decoding_error(
                            "the maximum supported annotations sequence length is 65KB.",
                        )
                    })?,
                };
                (sequence, remaining_input)
            }
            8 => {
                let (flex_sym1, input_after_sym1) = input_after_opcode.read_flex_sym()?;
                let (flex_sym2, input_after_sym2) = input_after_sym1.read_flex_sym()?;
                let combined_length = flex_sym1.size_in_bytes() + flex_sym2.size_in_bytes();
                let sequence = EncodedAnnotations {
                    encoding: AnnotationsEncoding::FlexSym,
                    header_length: 1, // 0xE8
                    sequence_length: u16::try_from(combined_length).map_err(|_| {
                        IonError::decoding_error(
                            "the maximum supported annotations sequence length is 65KB.",
                        )
                    })?,
                };
                (sequence, input_after_sym2)
            }
            9 => {
                let (flex_uint, remaining_input) = input_after_opcode.read_flex_uint()?;
                let sequence = EncodedAnnotations {
                    encoding: AnnotationsEncoding::FlexSym,
                    header_length: u8::try_from(1 + flex_uint.size_in_bytes()).map_err(|_| {
                        IonError::decoding_error("found a 256+ byte annotations header")
                    })?,
                    sequence_length: u16::try_from(flex_uint.value()).map_err(|_| {
                        IonError::decoding_error(
                            "the maximum supported annotations sequence length is 65KB.",
                        )
                    })?,
                };
                (
                    sequence,
                    remaining_input.consume(sequence.sequence_length as usize),
                )
            }
            _ => unreachable!("reading flexsym annotations sequence with invalid length code"),
        };
        Ok((sequence, remaining_input))
    }

    fn read_symbol_address_annotations_sequence(
        self,
        _opcode: Opcode,
    ) -> ParseResult<'a, EncodedAnnotations> {
        todo!()
    }

    fn read_e_expression(self, opcode: Opcode) -> IonResult<RawBinaryEExpression_1_1<'a>> {
        use OpcodeType::*;
        let (macro_id, buffer_after_id) = match opcode.opcode_type {
            EExpressionWithAddress => (
                MacroIdRef::LocalAddress(opcode.byte as usize),
                self.consume(1),
            ),
            EExpressionAddressFollows => todo!("e-expr with trailing address; {opcode:#0x?}",),
            _ => unreachable!("read_e_expression called with invalid opcode"),
        };

        // TODO: When we support untagged parameter encodings, we need to use the signature's
        //       parameter encodings to drive this process. For now--while everything is tagged
        //       and cardinality is always required--we just loop `num_parameters` times.
        let macro_def = self
            .context
            .macro_table
            .macro_with_id(macro_id)
            .ok_or_else(|| {
                IonError::decoding_error(format!("invocation of unknown macro '{macro_id:?}'"))
            })?;
        use MacroKind::*;
        let num_parameters = match macro_def.kind() {
            Template(t) => t.signature().parameters().len(),
            // Many system macros like `values`, `make_string`, etc take a variadic number of args.
            _ => todo!("system macros require support for argument group encoding"),
        };

        let args_cache = self
            .context
            .allocator()
            .alloc_with(|| BumpVec::with_capacity_in(num_parameters, self.context.allocator()));
        // `args_buffer` will be partially consumed in each iteration of the loop below.
        let mut args_buffer = buffer_after_id;
        for _ in 0..num_parameters {
            let value_expr = match args_buffer.peek_sequence_value_expr()? {
                Some(expr) => expr,
                None => {
                    return IonResult::incomplete(
                        "found an incomplete e-expression",
                        buffer_after_id.offset(),
                    )
                }
            };
            args_buffer = args_buffer.consume(value_expr.range().len());
            args_cache.push(value_expr);
        }
        let macro_id_encoded_length = buffer_after_id.offset() - self.offset();
        let args_length = args_buffer.offset() + args_buffer.len() - buffer_after_id.offset();
        let e_expression_buffer = self.slice(0, macro_id_encoded_length + args_length);

        let e_expression = RawBinaryEExpression_1_1::new(
            macro_id,
            EncodedBinaryEExp::new(macro_id_encoded_length as u16),
            e_expression_buffer,
            args_cache,
        );
        Ok(e_expression)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AnnotationsEncoding {
    SymbolAddress,
    FlexSym,
}

/// Represents the data found in an Ion 1.1 annotations sequence
#[derive(Clone, Copy, Debug)]
pub struct EncodedAnnotations {
    pub encoding: AnnotationsEncoding,
    // The number of bytes used to represent the annotations opcode and the byte length prefix
    // (in the case of 0xE9). As a result, this will almost always be 1 or 2.
    pub header_length: u8,
    // The number of bytes used to represent the annotations sequence itself. Because these
    // can be encoded with inline text, it's possible for the length to be non-trivial.
    pub sequence_length: u16,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::macro_evaluator::RawEExpression;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::raw::v1_1::reader::MacroAddress;

    fn input_test<A: AsRef<[u8]>>(input: A) {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let input = ImmutableBuffer::new(context, input.as_ref());
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
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let buffer = ImmutableBuffer::new(context, &[0xECu8]);
        let (pad_size, _) = buffer.read_nop_pad().expect("unable to read NOP pad");
        assert_eq!(pad_size, 1);

        let buffer = ImmutableBuffer::new(context, &[0xEDu8, 0x05, 0x00, 0x00]);
        let (pad_size, _) = buffer.read_nop_pad().expect("unable to read NOP pad");
        assert_eq!(pad_size, 4);
    }

    fn eexp_test(
        macro_source: &str,
        encode_macro_fn: impl FnOnce(MacroAddress) -> Vec<u8>,
        test_fn: impl FnOnce(RawBinaryEExpression_1_1) -> IonResult<()>,
    ) -> IonResult<()> {
        let mut context = EncodingContext::empty();
        let template_macro = TemplateCompiler::compile_from_text(context.get_ref(), macro_source)?;
        let macro_address = context.macro_table.add_macro(template_macro)?;
        let opcode_byte = u8::try_from(macro_address).unwrap();
        let binary_ion = encode_macro_fn(opcode_byte as usize);
        let buffer = ImmutableBuffer::new(context.get_ref(), &binary_ion);
        let eexp = buffer.read_e_expression(Opcode::from_byte(opcode_byte))?;
        assert_eq!(eexp.id(), MacroIdRef::LocalAddress(macro_address));
        println!("{:?}", eexp);
        assert_eq!(eexp.id, MacroIdRef::LocalAddress(opcode_byte as usize));
        test_fn(eexp)
    }

    #[test]
    fn read_eexp_without_args() -> IonResult<()> {
        let macro_source = r#"
            (macro seventeen () 17)
        "#;
        let encode_eexp_fn = |address: MacroAddress| vec![address as u8];
        eexp_test(
            macro_source,
            encode_eexp_fn,
            |eexp: RawBinaryEExpression_1_1| {
                let mut args = eexp.raw_arguments();
                assert!(args.next().is_none());
                Ok(())
            },
        )
    }

    #[test]
    fn read_eexp_with_one_arg() -> IonResult<()> {
        let macro_source = r#"
            (macro greet (name)
                (make_string "Hello, " name "!")
            )
        "#;

        #[rustfmt::skip]
            let encode_eexp_fn = |address: MacroAddress| vec![
            address as u8,
            // === 8-byte string ====
            0x98,
            // M     i     c     h     e     l     l     e
            0x4D, 0x69, 0x63, 0x68, 0x65, 0x6C, 0x6C, 0x65,
        ];

        let args_test = |eexp: RawBinaryEExpression_1_1| {
            let mut args = eexp.raw_arguments();
            assert_eq!(
                args.next()
                    .unwrap()?
                    .expect_value()?
                    .read()?
                    .expect_string()?,
                "Michelle"
            );
            Ok(())
        };

        eexp_test(macro_source, encode_eexp_fn, args_test)
    }

    #[test]
    fn read_eexp_with_two_args() -> IonResult<()> {
        let macro_source = r#"
            (macro greet (name day)
                (make_string "Hello, " name "! Have a pleasant " day ".")
            )
        "#;

        #[rustfmt::skip]
        let encode_eexp_fn = |address: MacroAddress| vec![
            address as u8,
            // === 8-byte string ====
            0x98,
            // M     i     c     h     e     l     l     e
            0x4D, 0x69, 0x63, 0x68, 0x65, 0x6C, 0x6C, 0x65,
            // === 7-byte string ===
            0x97,
            // T     u     e     s     d     a     y
            0x54, 0x75, 0x65, 0x73, 0x64, 0x61, 0x79,
        ];

        let args_test = |eexp: RawBinaryEExpression_1_1| {
            let mut args = eexp.raw_arguments();
            assert_eq!(
                args.next()
                    .unwrap()?
                    .expect_value()?
                    .read()?
                    .expect_string()?,
                "Michelle"
            );
            assert_eq!(
                args.next()
                    .unwrap()?
                    .expect_value()?
                    .read()?
                    .expect_string()?,
                "Tuesday"
            );
            Ok(())
        };

        eexp_test(macro_source, encode_eexp_fn, args_test)
    }
}
