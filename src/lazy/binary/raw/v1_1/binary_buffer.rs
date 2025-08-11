use arrayvec::ArrayVec;
use bumpalo::collections::Vec as BumpVec;
use std::fmt::{Debug, Formatter};
use std::mem::size_of;
use std::ops::Range;

use crate::binary::constants::v1_1::IVM;
use crate::lazy::binary::encoded_value::EncodedBinaryValue;
use crate::lazy::binary::raw::v1_1::e_expression::{
    BinaryEExpArgsIterator_1_1, BinaryEExpression_1_1,
};
use crate::lazy::binary::raw::v1_1::r#struct::LazyRawBinaryFieldName_1_1;
use crate::lazy::binary::raw::v1_1::type_code::OpcodeKind;
use crate::lazy::binary::raw::v1_1::value::{
    BinaryValueEncoding, DelimitedContents, LazyRawBinaryValue_1_1, LazyRawBinaryVersionMarker_1_1,
};
use crate::lazy::binary::raw::v1_1::{Header, LengthType, Opcode, OpcodeType, ION_1_1_OPCODES};
use crate::lazy::decoder::{LazyRawFieldExpr, LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoder::binary::v1_1::fixed_int::FixedInt;
use crate::lazy::encoder::binary::v1_1::fixed_uint::FixedUInt;
use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;
use crate::lazy::encoder::binary::v1_1::flex_sym::{FlexSym, FlexSymValue};
use crate::lazy::encoder::binary::v1_1::flex_uint::FlexUInt;
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::raw::v1_1::arg_group::EExpArgExpr;
use crate::lazy::text::raw::v1_1::reader::{
    MacroIdLike, MacroIdRef, ModuleKind, QualifiedAddress, SystemMacroAddress,
};
use crate::result::IonFailure;
use crate::{v1_1, IonError, IonResult, ValueExpr};

/// A buffer of unsigned bytes that can be cheaply copied and which defines methods for parsing
/// the various encoding elements of a binary Ion stream.
///
/// Upon success, each parsing method on the `BinaryBuffer` will return the value that was read
/// and a copy of the `BinaryBuffer` that starts _after_ the bytes that were parsed.
///
/// Methods that `peek` at the input stream do not return a copy of the buffer.
#[derive(Clone, Copy)]
pub struct BinaryBuffer<'a> {
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

impl Debug for BinaryBuffer<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "BinaryBuffer @ offset={} {{", self.offset)?;
        for byte in self.bytes().iter().take(16) {
            write!(f, "{:x?} ", *byte)?;
        }
        write!(f, "}}")
    }
}

impl PartialEq for BinaryBuffer<'_> {
    fn eq(&self, other: &Self) -> bool {
        // A definition of equality that ignores the `context` field.
        self.offset == other.offset && self.data == other.data
        // An argument could be made that two buffers are not equal if they're holding references to
        // different contexts, but this is a very low-level, feature-gated construct so it's probably
        // fine if the implementation is arguably imperfect.
    }
}

/// When `Ok`, contains the value that was matched/parsed and the remainder of the input buffer.
pub(crate) type ParseResult<'a, T> = IonResult<(T, BinaryBuffer<'a>)>;

impl<'a> BinaryBuffer<'a> {
    /// Constructs a new `BinaryBuffer` that wraps `data`.
    #[inline]
    pub fn new(context: EncodingContextRef<'a>, data: &'a [u8]) -> BinaryBuffer<'a> {
        Self::new_with_offset(context, data, 0)
    }

    #[inline]
    pub fn new_with_offset(
        context: EncodingContextRef<'a>,
        data: &'a [u8],
        offset: usize,
    ) -> BinaryBuffer<'a> {
        BinaryBuffer {
            data,
            offset,
            context,
        }
    }

    pub fn context(&self) -> EncodingContextRef<'a> {
        self.context
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

    /// Like [`Self::bytes_range`] above, but returns an updated copy of the [`BinaryBuffer`]
    /// instead of a `&[u8]`.
    pub fn slice(&self, offset: usize, length: usize) -> BinaryBuffer<'a> {
        BinaryBuffer {
            data: self.bytes_range(offset, length),
            offset: self.offset + offset,
            context: self.context,
        }
    }

    /// Returns the number of bytes between the start of the original input byte array and the
    /// subslice of that byte array that this `BinaryBuffer` represents.
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

    /// Creates a copy of this `BinaryBuffer` that begins `num_bytes_to_consume` further into the
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

    /// Reads the first byte in the buffer and returns it as an [Opcode]. If the buffer is empty,
    /// returns an `IonError::Incomplete`.
    #[inline]
    pub(crate) fn expect_opcode(&self) -> IonResult<Opcode> {
        if self.is_empty() {
            return IonResult::incomplete("an opcode", self.offset());
        }
        Ok(self.peek_opcode_unchecked())
    }

    /// Reads the first byte in the buffer and returns it as an [Opcode]. If the buffer is empty,
    /// returns `None`.
    #[inline]
    pub(crate) fn peek_opcode(&self) -> Option<Opcode> {
        if let Some(&byte) = self.data.first() {
            Some(ION_1_1_OPCODES[byte as usize])
        } else {
            None
        }
    }

    /// Reads the first byte in the buffer *without confirming one is available* and returns it
    /// as an [Opcode].
    #[inline]
    pub(crate) fn peek_opcode_unchecked(&self) -> Opcode {
        let next_byte = self.data[0];
        ION_1_1_OPCODES[next_byte as usize]
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
                let matched = BinaryBuffer::new_with_offset(self.context, bytes, self.offset);
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

    #[inline(always)]
    pub fn read_flex_uint_must_inline(self) -> ParseResult<'a, FlexUInt> {
        let flex_uint = FlexUInt::read(self.bytes(), self.offset())?;
        let remaining = self.consume(flex_uint.size_in_bytes());
        Ok((flex_uint, remaining))
    }

    pub fn read_flex_uint_as_lazy_value(self) -> ParseResult<'a, LazyRawBinaryValue_1_1<'a>> {
        let Some(first_byte) = self.peek_next_byte() else {
            return IonResult::incomplete("a flex_uint", self.offset());
        };
        let size_in_bytes = match first_byte {
            // If the first byte is zero, this flex_uint is encoded using 9+ bytes. That's pretty
            // uncommon, so we'll just use the existing logic in the `read` method and discard the
            // value. If this shows up in profiles, it can be optimized further.
            0 => FlexUInt::read(self.bytes(), self.offset())?.size_in_bytes(),
            _ => first_byte.trailing_zeros() as usize + 1,
        };

        if self.len() < size_in_bytes {
            return IonResult::incomplete("a flex_uint value", self.offset());
        }
        // XXX: This *doesn't* slice `self` because FlexUInt::read() is faster if the input
        //      is at least the size of a u64.
        let matched_input = self.slice(0, size_in_bytes);
        let remaining_input = self.slice_to_end(size_in_bytes);
        let value = LazyRawBinaryValue_1_1::for_flex_uint(matched_input);
        Ok((value, remaining_input))
    }

    pub fn read_fixed_uint_as_lazy_value(self, size_in_bytes: usize) -> ParseResult<'a, LazyRawBinaryValue_1_1<'a>> {
        if self.len() < size_in_bytes {
            return IonResult::incomplete("a uint", self.offset());
        }

        let encoding = match size_in_bytes {
            1 => BinaryValueEncoding::UInt8,
            2 => BinaryValueEncoding::UInt16,
            4 => BinaryValueEncoding::UInt32,
            8 => BinaryValueEncoding::UInt64,
            _ => return IonResult::decoding_error(format!("Invalid byte size for fixed uint: {size_in_bytes}")),
        };

        let matched_input = self.slice(0, size_in_bytes);
        let remaining_input = self.slice_to_end(size_in_bytes);
        let value = LazyRawBinaryValue_1_1::for_fixed_uint(matched_input, encoding);
        Ok((value, remaining_input))
    }

    pub fn slice_to_end(&self, offset: usize) -> BinaryBuffer<'a> {
        BinaryBuffer {
            data: &self.data[offset..],
            // stream offset + local offset
            offset: self.offset + offset,
            context: self.context,
        }
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
        let opcode = self.expect_opcode()?;

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
    pub fn consume_nop_padding(self, mut opcode: Opcode) -> ParseResult<'a, ()> {
        let mut buffer = self;
        // Skip over any number of NOP regions
        while opcode.is_nop() {
            let (_, buffer_after_nop) = buffer.read_nop_pad()?;
            buffer = buffer_after_nop;
            if buffer.is_empty() {
                break;
            }
            opcode = buffer.expect_opcode()?
        }
        Ok(((), buffer))
    }

    /// Interprets the length code in the provided [Header]; if necessary, will read more bytes
    /// from the buffer to interpret as the value's length. If it is successful, returns an `Ok(_)`
    /// containing a [FlexUInt] representation of the value's length. If no additional bytes were
    /// read, the returned `FlexUInt`'s `size_in_bytes()` method will return `0`.
    #[inline]
    pub fn read_value_length(self, header: Header) -> ParseResult<'a, Option<FlexUInt>> {
        match header.length_type() {
            LengthType::InOpcode(n) => {
                // FlexUInt represents the length, but is not physically present, hence the 0 size.
                Ok((Some(FlexUInt::new(0, n as u64)), self))
            }
            LengthType::Unknown => Ok((None, self)),
            LengthType::FlexUIntFollows => {
                let (flex, after) = self.read_flex_uint()?;
                Ok((Some(flex), after))
            }
        }
    }

    /// Reads a single expression (value literal or e-expression) as an argument to an e-expression.
    #[inline]
    pub(crate) fn expect_eexp_arg_expr(
        self,
        label: &'static str,
    ) -> ParseResult<'a, EExpArgExpr<'a, v1_1::Binary>> {
        let (raw_value_expr, remaining_input) = self.expect_sequence_value_expr(label)?;
        let arg_expr = match raw_value_expr {
            RawValueExpr::ValueLiteral(v) => EExpArgExpr::ValueLiteral(v),
            RawValueExpr::EExp(e) => EExpArgExpr::EExp(e),
        };
        Ok((arg_expr, remaining_input))
    }

    pub(crate) fn expect_sequence_value_expr(
        self,
        label: &'static str,
    ) -> ParseResult<'a, LazyRawValueExpr<'a, v1_1::Binary>> {
        match self.read_sequence_value_expr() {
            Ok((Some(expr), remaining)) => Ok((expr, remaining)),
            Ok((None, _)) => IonResult::incomplete(label, self.offset),
            Err(e) => Err(e),
        }
    }

    /// Returns `true` if the opcode was updated to one that follows the NOP.
    /// Returns `false` if there was no more data following the NOP.
    #[inline(never)]
    pub(crate) fn opcode_after_nop(&mut self, opcode: &mut Opcode) -> IonResult<bool> {
        let (_matched, input_after_nop) = self.consume_nop_padding(*opcode)?;
        if let Some(new_opcode) = input_after_nop
            .peek_next_byte()
            .map(|b| ION_1_1_OPCODES[b as usize])
        {
            *opcode = new_opcode;
            *self = input_after_nop;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Reads a value without a field name from the buffer. This is applicable in lists, s-expressions,
    /// and at the top level.
    #[inline]
    pub(crate) fn read_sequence_value_expr(
        self,
    ) -> ParseResult<'a, Option<LazyRawValueExpr<'a, v1_1::Binary>>> {
        let opcode = match self.peek_opcode() {
            Some(opcode) => opcode,
            None => return Ok((None, self)),
        };

        match opcode.kind {
            OpcodeKind::EExp => {
                let (eexp, remaining) = self.read_e_expression(opcode)?;
                Ok((
                    Some(LazyRawValueExpr::<'a, v1_1::Binary>::EExp(eexp)),
                    remaining,
                ))
            }
            OpcodeKind::Annotations => {
                let (value, remaining) = self.read_annotated_value(opcode)?;
                Ok((
                    Some(LazyRawValueExpr::<'a, v1_1::Binary>::ValueLiteral(value)),
                    remaining,
                ))
            }
            OpcodeKind::Value(_ion_type) => {
                let (value, remaining) = self.read_value_without_annotations(opcode)?;
                Ok((
                    Some(LazyRawValueExpr::<'a, v1_1::Binary>::ValueLiteral(value)),
                    remaining,
                ))
            }
            _other => self.read_nop_then_sequence_value(),
        }
    }

    #[inline(never)]
    fn read_nop_then_sequence_value(
        self,
    ) -> ParseResult<'a, Option<LazyRawValueExpr<'a, v1_1::Binary>>> {
        let mut opcode = self.expect_opcode()?;
        if !opcode.is_nop() {
            return IonResult::decoding_error("found a non-value, non-eexp, non-nop in a sequence");
        }
        let mut input = self;
        // This test updates input and opcode.
        if !input.opcode_after_nop(&mut opcode)? {
            return Ok((None, input));
        }
        if opcode.is_e_expression()
            || opcode.ion_type().is_some()
            || opcode.is_annotations_sequence()
        {
            return input.read_sequence_value_expr();
        }
        IonResult::decoding_error("found a non-value, non-eexp after a nop pad")
    }

    pub(crate) fn peek_delimited_container(
        self,
        opcode: Opcode,
    ) -> IonResult<(DelimitedContents<'a>, BinaryBuffer<'a>)> {
        use crate::IonType;

        if let Some(IonType::Struct) = opcode.ion_type() {
            self.peek_delimited_struct()
        } else {
            self.peek_delimited_sequence()
        }
    }

    pub(crate) fn peek_delimited_sequence(
        self,
    ) -> IonResult<(DelimitedContents<'a>, BinaryBuffer<'a>)> {
        self.consume(1).peek_delimited_sequence_body()
    }

    pub(crate) fn peek_delimited_sequence_body(
        self,
    ) -> IonResult<(DelimitedContents<'a>, BinaryBuffer<'a>)> {
        let mut input = self;
        let mut values =
            BumpVec::<LazyRawValueExpr<'a, v1_1::Binary>>::new_in(self.context.allocator());

        loop {
            let opcode = input.expect_opcode()?;
            if opcode.is_delimited_end() {
                input = input.consume(1);
                break;
            } else if opcode.opcode_type == OpcodeType::Nop {
                let res = input.consume_nop_padding(opcode)?;
                input = res.1;
            } else if let (Some(value), after) = BinaryBuffer::read_sequence_value_expr(input)? {
                values.push(value);
                input = after;
                // input = input.consume(value.range().len());
            }
        }

        Ok((DelimitedContents::Values(values.into_bump_slice()), input))
    }

    /// Reads the value for a delimited struct field, consuming NOPs if present.
    fn peek_delimited_struct_value(
        &self,
    ) -> IonResult<(Option<LazyRawValueExpr<'a, v1_1::Binary>>, BinaryBuffer<'a>)> {
        let opcode = self.expect_opcode()?;
        if opcode.is_nop() {
            let after_nops = self.consume_nop_padding(opcode)?.1;
            if after_nops.is_empty() {
                // Non-NOP field wasn't found, nothing remaining.
                return Ok((None, after_nops));
            }
            Ok((None, after_nops))
        } else {
            self.read_sequence_value_expr()
        }
    }

    /// Reads the field name, as a flexsym, for the current delimited struct field.
    fn peek_delimited_field_flexsym(
        &self,
    ) -> IonResult<(Option<LazyRawBinaryFieldName_1_1<'a>>, BinaryBuffer<'a>)> {
        if self.is_empty() {
            return Ok((None, *self));
        }

        let (flex_sym, after) = self.read_flex_sym()?;
        let (sym, after) = match flex_sym.value() {
            FlexSymValue::SymbolRef(sym_ref) => (sym_ref, after),
            FlexSymValue::Opcode(o) if o.is_delimited_end() => return Ok((None, after)),
            _ => unreachable!(),
        };

        let matched_field_id = self.slice(0, after.offset() - self.offset());
        let field_name = LazyRawBinaryFieldName_1_1::new(sym, matched_field_id);
        Ok((Some(field_name), after))
    }

    /// Reads a field within a delimited struct and returns the LazyRawFieldExpr for that field.
    pub(crate) fn peek_delimited_field(
        &self,
    ) -> IonResult<(Option<LazyRawFieldExpr<'a, v1_1::Binary>>, BinaryBuffer<'a>)> {
        let mut buffer = *self;
        loop {
            // Peek at our field name.
            let (field_name, after_name) = match buffer.peek_delimited_field_flexsym()? {
                (Some(field_name), after_name) => (field_name, after_name),
                (None, after_name) => return Ok((None, after_name)),
            };

            if after_name.is_empty() {
                return IonResult::incomplete("a struct field value", after_name.offset());
            }

            let (field, after_value) = match after_name.peek_delimited_struct_value()? {
                (None, after) => {
                    if after.is_empty() {
                        return IonResult::incomplete("a struct field value", after.offset());
                    }
                    buffer = after;
                    continue; // No value for this field, loop to try next field.
                }
                (Some(RawValueExpr::ValueLiteral(value)), after) => {
                    (LazyRawFieldExpr::NameValue(field_name, value), after)
                }
                (Some(RawValueExpr::EExp(eexp)), after) => {
                    (LazyRawFieldExpr::NameEExp(field_name, eexp), after)
                }
            };

            return Ok((Some(field), after_value));
        }
    }

    /// Reads a delimited struct from the buffer and returns a collection of LazyRawValueExprs
    /// that can be used with a struct iterator.
    pub(crate) fn peek_delimited_struct(
        self,
    ) -> IonResult<(DelimitedContents<'a>, BinaryBuffer<'a>)> {
        let mut input = self.consume(1);
        let mut values =
            BumpVec::<LazyRawFieldExpr<'a, v1_1::Binary>>::new_in(self.context.allocator());

        loop {
            match input.expect_opcode()? {
                o if o.is_delimited_end() => break,
                _ => match input.peek_delimited_field()? {
                    (Some(field), after) => {
                        values.push(field);
                        input = after;
                    }
                    (None, after) => {
                        input = after;
                        break;
                    }
                },
            }
        }

        Ok((DelimitedContents::Fields(values.into_bump_slice()), input))
    }

    /// Reads a value from the buffer. The caller must confirm that the buffer is not empty and that
    /// the next byte (`type_descriptor`) is neither a NOP nor an annotations wrapper.
    #[inline(always)]
    fn read_value_without_annotations(
        self,
        opcode: Opcode,
    ) -> ParseResult<'a, &'a mut LazyRawBinaryValue_1_1<'a>> {
        let input = self;
        let header = opcode.to_header().ok_or_else(|| {
            IonError::decoding_error(format!(
                "found a non-value in value position; buffer=<{:02X?}>",
                input.bytes_range(0, 16.min(input.bytes().len()))
            ))
        })?;

        let header_offset = input.offset();
        let (total_length, length_length, value_body_length, delimited_contents) =
            if opcode.is_delimited_start() {
                let (contents, after) = input.peek_delimited_container(opcode)?;
                let total_length = after.offset() - self.offset();
                let value_body_length = total_length - 1; // Total length - sizeof(opcode)
                (total_length, 0, value_body_length, contents)
            } else {
                let length = match header.length_type() {
                    LengthType::InOpcode(n) => FlexUInt::new(0, n as u64),
                    LengthType::Unknown => FlexUInt::new(0, 0), // Delimited value, we do not know the size.
                    LengthType::FlexUIntFollows => input.consume(1).read_flex_uint_must_inline()?.0,
                };

                let length_length = length.size_in_bytes() as u8;
                let value_length = length.value() as usize; // ha
                let total_length = 1 // Header byte
                + length_length as usize
                + value_length;
                (
                    total_length,
                    length_length,
                    value_length,
                    DelimitedContents::None,
                )
            };

        if total_length > input.len() {
            return IonResult::incomplete("a value", header_offset);
        }

        let encoded_value = EncodedBinaryValue {
            encoding: BinaryValueEncoding::Tagged,
            header,
            // If applicable, these are populated by the caller: `read_annotated_value()`
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            annotations_encoding: AnnotationsEncoding::SymbolAddress,
            header_offset,
            length_length,
            value_body_length,
            total_length,
        };

        let lazy_value_ref = self
            .context()
            .allocator()
            .alloc_with(|| LazyRawBinaryValue_1_1 {
                encoded_value,
                // If this value has a field ID or annotations, this will be replaced by the caller.
                input: self,
                delimited_contents,
            });
        Ok((lazy_value_ref, self.consume(total_length)))
    }

    pub fn read_fixed_int(self, length: usize) -> ParseResult<'a, FixedInt> {
        let int_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| IonError::incomplete("a FixedInt", self.offset()))?;
        let fixed_int = FixedInt::read(int_bytes, length, self.offset())?;
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
        opcode: Opcode,
    ) -> ParseResult<'a, &'a LazyRawBinaryValue_1_1<'a>> {
        let (annotations_seq, input_after_annotations) = self.read_annotations_sequence(opcode)?;
        let opcode = input_after_annotations.expect_opcode()?;
        let (value, input_after_value) =
            input_after_annotations.read_value_without_annotations(opcode)?;
        let total_annotations_length =
            annotations_seq.header_length as usize + annotations_seq.sequence_length as usize;
        value.encoded_value.annotations_header_length = annotations_seq.header_length;
        value.encoded_value.annotations_sequence_length = annotations_seq.sequence_length;
        value.encoded_value.annotations_encoding = annotations_seq.encoding;
        value.encoded_value.total_length += total_annotations_length;
        // Rewind the input to include the annotations sequence
        value.input = self;
        Ok((value, input_after_value))
    }

    fn read_annotations_sequence(self, opcode: Opcode) -> ParseResult<'a, EncodedAnnotations> {
        match opcode.opcode_type {
            OpcodeType::AnnotationFlexSym => self.read_flex_sym_annotations_sequence(opcode),
            OpcodeType::AnnotationSymAddress => {
                self.read_symbol_address_annotations_sequence(opcode)
            }
            opcode => unreachable!(
                "read_annotations_sequence called for non-annotations opcode {opcode:?}"
            ),
        }
    }

    fn read_flex_sym_annotations_sequence(
        self,
        opcode: Opcode,
    ) -> ParseResult<'a, EncodedAnnotations> {
        let input_after_opcode = self.consume(1);
        let (header_length, remaining_input) = match opcode.low_nibble() {
            7 => {
                let header_length = 1;
                let remaining_input = input_after_opcode.consume_flex_sym()?;
                (header_length, remaining_input)
            }
            8 => {
                let header_length = 1;
                let remaining_input = input_after_opcode.consume_flex_sym()?.consume_flex_sym()?;
                (header_length, remaining_input)
            }
            9 => {
                let (flex_uint, input_after_header) = input_after_opcode.read_flex_uint()?;
                let sequence_length = flex_uint.value() as usize;
                if input_after_header.len() < sequence_length {
                    return IonResult::incomplete(
                        "an annotations sequence",
                        input_after_header.offset(),
                    );
                }
                // Header = 0xE6, followed by FlexUInt size in bytes
                let header_length = u8::try_from(1 + flex_uint.size_in_bytes()).map_err(|_| {
                    IonError::decoding_error("found a 256+ byte annotations header")
                })?;
                let remaining = input_after_header.consume(sequence_length);
                (header_length, remaining)
            }
            _ => unreachable!("reading flexsym annotations sequence with invalid length code"),
        };

        let sequence_length =
            u16::try_from(remaining_input.offset() - (self.offset() + header_length as usize))
                .map_err(|_| {
                    IonError::decoding_error(
                        "the maximum supported annotations sequence length is 65KB",
                    )
                })?;

        let sequence = EncodedAnnotations {
            encoding: AnnotationsEncoding::FlexSym,
            header_length,
            sequence_length,
        };

        Ok((sequence, remaining_input))
    }

    /// Skips beyond a `FlexSym` at the head of the buffer, returning the remaining slice.
    fn consume_flex_sym(self) -> IonResult<Self> {
        // TODO: As an optimization, see if we can avoid actually reading the flex_sym.
        let (flex_sym, remaining) = self.read_flex_sym()?;
        if let FlexSymValue::Opcode(opcode) = flex_sym.value() {
            todo!("FlexSym escapes in annotation sequences; opcode: {opcode:?}");
        }

        Ok(remaining)
    }

    /// Skips beyond a `FlexUInt` at the head of the buffer, returning the remaining slice.
    fn consume_flex_uint(self) -> IonResult<Self> {
        match self.peek_next_byte() {
            Some(0) => {
                // This is a big FlexUInt; for now, fall back to the read impl.
                let (_flex_uint, remaining) = self.read_flex_uint()?;
                return Ok(remaining);
            }
            Some(byte) => {
                let num_bytes = (byte.trailing_zeros() + 1) as usize;
                // If we have enough data in the buffer, skip over the FlexUInt and return the tail.
                if self.len() >= num_bytes {
                    return Ok(self.consume(num_bytes));
                }
                // Otherwise, it's incomplete.
            }
            None => {
                // If there's no data in the buffer, it's incomplete.
            }
        }

        IonResult::incomplete("skipping a FlexUInt", self.offset())
    }

    fn read_symbol_address_annotations_sequence(
        self,
        opcode: Opcode,
    ) -> ParseResult<'a, EncodedAnnotations> {
        let input_after_opcode = self.consume(1);
        let (header_length, remaining_input) = match opcode.low_nibble() {
            4 => {
                let remaining = input_after_opcode.consume_flex_uint()?;
                (/* Header=0xE4, Length=*/ 1, remaining)
            }
            5 => {
                let remaining = input_after_opcode
                    .consume_flex_uint()?
                    .consume_flex_uint()?;
                (/* Header=0xE5, Length=*/ 1, remaining)
            }
            6 => {
                let (flex_uint, input_after_header) = input_after_opcode.read_flex_uint()?;
                let sequence_length = flex_uint.value() as usize;
                if input_after_header.len() < sequence_length {
                    return IonResult::incomplete(
                        "an annotations sequence",
                        input_after_header.offset(),
                    );
                }
                // Header = 0xE6, followed by FlexUInt size in bytes
                let header_length = u8::try_from(1 + flex_uint.size_in_bytes()).map_err(|_| {
                    IonError::decoding_error("found a 256+ byte annotations header")
                })?;
                let remaining = input_after_header.consume(sequence_length);
                (header_length, remaining)
            }
            _ => unreachable!("reading flexsym annotations sequence with invalid length code"),
        };

        let sequence_length =
            u16::try_from(remaining_input.offset() - (self.offset() + header_length as usize))
                .map_err(|_| {
                    IonError::decoding_error(
                        "the maximum supported annotations sequence length is 65KB",
                    )
                })?;

        let sequence = EncodedAnnotations {
            encoding: AnnotationsEncoding::SymbolAddress,
            header_length,
            sequence_length,
        };
        Ok((sequence, remaining_input))
    }

    #[inline]
    pub fn read_e_expression(
        self,
        opcode: Opcode,
    ) -> ParseResult<'a, &'a BinaryEExpression_1_1<'a>> {
        use OpcodeType::*;
        let (macro_id, input_after_address) = match opcode.opcode_type {
            EExpressionWith6BitAddress => (
                MacroIdRef::LocalAddress(opcode.byte as usize),
                self.consume(1),
            ),
            EExpressionWith12BitAddress => {
                if self.len() < 2 {
                    return IonResult::incomplete("a 12-bit e-exp address", self.offset);
                }

                let bias = ((opcode.byte as usize & 0x0F) << 8) + 64;
                let fixed_uint = self.bytes()[1] as usize;
                let address = fixed_uint + bias;
                (MacroIdRef::LocalAddress(address), self.consume(2))
            }
            EExpressionWith20BitAddress => {
                if self.len() < 3 {
                    return IonResult::incomplete("a 20-bit e-exp address", self.offset);
                }
                let bias = ((opcode.byte as usize & 0x0F) << 16) + 4160;
                let (fixed_uint, input_after_opcode) = self.consume(1).read_fixed_uint(2)?;
                let address = fixed_uint.value().expect_usize()? + bias;
                (MacroIdRef::LocalAddress(address), input_after_opcode)
            }
            // Length-prefixed is a special case.
            EExpressionWithLengthPrefix => return self.read_eexp_with_length_prefix(opcode),
            SystemEExpression => {
                // The next byte is the system macro address; make sure we have another byte available
                if self.len() < 2 {
                    return IonResult::incomplete("a system macro address", self.offset);
                }
                let address = self.bytes()[1] as usize;
                let system_macro_address = SystemMacroAddress::new(address).ok_or_else(|| {
                    IonError::decoding_error(format!(
                        "found invalid system macro address {address}"
                    ))
                })?;

                (
                    MacroIdRef::SystemAddress(system_macro_address),
                    self.consume(2), // 0xEF and address byte
                )
            }
            _ => unreachable!("read_e_expression called with invalid opcode"),
        };

        self.read_eexp_with_id(input_after_address, macro_id)
    }

    /// Reads a complete e-expression whose address is provided.
    ///
    /// `self` begins at the opcode, `input_after_address` begins after the opcode and any address
    /// bytes, and `macro_address` is the address of the invoked macro.
    fn read_eexp_with_id(
        self,
        input_after_address: BinaryBuffer<'a>,
        macro_id: MacroIdRef<'a>,
    ) -> ParseResult<'a, &'a BinaryEExpression_1_1<'a>> {
        // Get a reference to the macro that lives at that address
        let macro_ref = macro_id.resolve(self.context.macro_table()).map_err(
            #[inline(never)]
            |_| {
                IonError::decoding_error(format!(
                    "invocation of macro at unknown ID '{macro_id:?}', buffer: {self:?}"
                ))
            },
        )?;

        let signature = macro_ref.signature();
        let bitmap_size_in_bytes = signature.bitmap_size_in_bytes();

        let (bitmap_bits, input_after_bitmap) = if signature.num_variadic_params() == 0 {
            (0, input_after_address)
        } else {
            input_after_address.read_eexp_bitmap(bitmap_size_in_bytes)?
        };

        let bitmap = ArgGroupingBitmap::new(signature.num_variadic_params(), bitmap_bits);
        let mut args_iter =
            BinaryEExpArgsIterator_1_1::for_input(bitmap.iter(), input_after_bitmap, signature);
        let mut cache =
            BumpVec::with_capacity_in(args_iter.size_hint().0, self.context.allocator());

        // XXX: This is on the hot path for e-expression-heavy streams. Pushing args into the
        // BumpVec one at a time is surprisingly slow, presumably because each value is copied to
        // a remote buffer individually. Here we create a stack-allocated array that we fill,
        // emptying into the BumpVec as needed. This allows us to do the `memcpy`s in bulk.
        // At the time of this writing, a `ValueExpr<v1_1::Binary>` is 96 bytes. I chose `4` as
        // the batch size because it is a power of two and ~400 bytes seemed like a reasonable
        // chunk of stack space. This can be changed as needed.
        const ARG_BATCH_SIZE: usize = 4;
        let mut args_array: ArrayVec<ValueExpr<'_, v1_1::Binary>, ARG_BATCH_SIZE> = ArrayVec::new();
        for arg in &mut args_iter {
            let arg = arg?;
            let value_expr = arg.resolve(self.context)?;
            args_array.push(value_expr);
            if args_array.is_full() {
                cache.extend_from_slice_copy(args_array.as_slice());
                args_array.clear();
            }
        }
        // Copy over anything left in the args_array
        cache.extend_from_slice_copy(args_array.as_slice());

        let eexp_total_length = args_iter.offset() - self.offset();
        let matched_eexp_bytes = self.slice(0, eexp_total_length);
        let remaining_input = self.consume(matched_eexp_bytes.len());

        let bitmap_offset = input_after_address.offset() - self.offset();
        let args_offset = input_after_bitmap.offset() - self.offset();

        let eexp_ref = self.context.allocator().alloc_with(|| {
            BinaryEExpression_1_1::new(
                macro_ref,
                bitmap_bits,
                matched_eexp_bytes,
                // There is no length prefix, so we re-use the bitmap_offset as the first position
                // beyond the opcode and address subfields.
                bitmap_offset as u8,
                bitmap_offset as u8,
                args_offset as u8,
            )
            .with_arg_expr_cache(cache.into_bump_slice())
        });
        Ok((eexp_ref, remaining_input))
    }

    fn read_eexp_with_length_prefix(
        self,
        _opcode: Opcode,
    ) -> ParseResult<'a, &'a BinaryEExpression_1_1<'a>> {
        let input_after_opcode = self.consume(1);
        let (macro_address_flex_uint, input_after_address) = input_after_opcode.read_flex_uint()?;
        let (args_length_flex_uint, input_after_length) = input_after_address.read_flex_uint()?;
        let header_length = input_after_length.offset() - self.offset();
        let macro_address = macro_address_flex_uint.value() as usize;
        let args_length = args_length_flex_uint.value() as usize;

        let total_length = header_length + args_length;
        if self.len() < total_length {
            return IonResult::incomplete("a length-prefixed e-expression", self.offset);
        }
        let matched_bytes = self.slice(0, total_length);

        // Get a reference to the macro that lives at that address
        let macro_def = self
            .context
            .macro_table()
            .macro_at_address(macro_address)
            .ok_or_else(|| {
                IonError::decoding_error(format!(
                    "invocation of macro at unknown address '{macro_address:?}'"
                ))
            })?;
        let macro_ref = MacroRef::new(
            QualifiedAddress::new(ModuleKind::Default, macro_address),
            macro_def,
        );

        // Offset from `self`, not offset from the beginning of the stream.
        let length_offset = (input_after_address.offset() - self.offset()) as u8;
        let bitmap_offset = (input_after_length.offset() - self.offset()) as u8;
        let (bitmap_bits, _input_after_bitmap) =
            input_after_length.read_eexp_bitmap(macro_ref.signature().bitmap_size_in_bytes())?;
        let args_offset = bitmap_offset + macro_ref.signature().bitmap_size_in_bytes() as u8;
        let remaining_input = self.consume(total_length);
        let eexp_ref = self.context.allocator().alloc_with(|| {
            BinaryEExpression_1_1::new(
                macro_ref,
                bitmap_bits,
                matched_bytes,
                length_offset,
                bitmap_offset,
                args_offset,
            )
        });
        Ok((eexp_ref, remaining_input))
    }

    fn read_eexp_bitmap(self, bitmap_size_in_bytes: usize) -> ParseResult<'a, u64> {
        let bitmap_bytes = self
            .peek_n_bytes(bitmap_size_in_bytes)
            .ok_or_else(|| IonError::incomplete("an e-exp arg grouping bitmap", self.offset))?;
        if bitmap_size_in_bytes == 1 {
            return Ok((bitmap_bytes[0] as u64, self.consume(1)));
        }
        let mut buffer = [0u8; size_of::<u64>()];
        let bitmap_bytes = self
            .peek_n_bytes(bitmap_size_in_bytes)
            .ok_or_else(|| IonError::incomplete("an e-exp arg grouping bitmap", self.offset))?;
        buffer[..bitmap_size_in_bytes].copy_from_slice(bitmap_bytes);
        let bitmap_u64 = u64::from_le_bytes(buffer);
        Ok((bitmap_u64, self.consume(bitmap_size_in_bytes)))
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ArgGroupingBitmap {
    num_args: usize,
    bits: u64,
}

impl ArgGroupingBitmap {
    const BITS_PER_VARIADIC_PARAM: usize = 2;
    pub(crate) const MAX_VARIADIC_PARAMS: usize =
        u64::BITS as usize / Self::BITS_PER_VARIADIC_PARAM;
    pub(crate) fn new(num_args: usize, bits: u64) -> Self {
        Self { num_args, bits }
    }
    #[inline]
    pub fn iter(&self) -> ArgGroupingBitmapIterator {
        ArgGroupingBitmapIterator {
            remaining_args: self.num_args,
            bits: self.bits,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ArgGrouping {
    Empty,            // 00
    ValueExprLiteral, // 01
    ArgGroup,         // 10
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ArgGroupingBitmapIterator {
    remaining_args: usize,
    bits: u64,
}

impl ArgGroupingBitmapIterator {
    pub fn new(remaining_args: usize, bits: u64) -> Self {
        Self {
            remaining_args,
            bits,
        }
    }
}

impl Iterator for ArgGroupingBitmapIterator {
    type Item = IonResult<ArgGrouping>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_args == 0 {
            None
        } else {
            use ArgGrouping::*;
            // Read the last two bits
            let encoding = match self.bits & 0b11 {
                0b00 => Empty,
                0b01 => ValueExprLiteral,
                0b10 => ArgGroup,
                _ => {
                    return Some(IonResult::decoding_error(
                        "found e-expression argument using reserved bitmap entry",
                    ))
                }
            };
            // Discard the last two bits and decrement the number of remaining entries
            self.bits >>= 2;
            self.remaining_args -= 1;
            Some(Ok(encoding))
        }
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

#[cfg(feature = "experimental-ion-1-1")]
#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;
    use crate::ion_data::IonEq;
    use crate::lazy::any_encoding::IonVersion;
    use crate::lazy::binary::raw::v1_1::e_expression::BinaryEExpArgsIterator_1_1;
    use crate::lazy::binary::raw::v1_1::RawBinaryAnnotationsIterator_1_1;
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::macro_evaluator::{EExpressionArgGroup, RawEExpression};
    use crate::lazy::expanded::macro_table::MacroTable;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
    use crate::v1_0::RawValueRef;
    use crate::RawSymbolRef;
    use crate::{AnyEncoding, Element, ElementReader, Reader, SequenceWriter, Writer};

    #[rstest]
    #[case::no_args(0, &[0b00u8], &[])]
    #[case::one_empty_arg(1, &[0b00u8], &[ArgGrouping::Empty])]
    #[case::one_literal_arg(1, &[0b01u8], &[ArgGrouping::ValueExprLiteral])]
    #[case::one_group_arg(1, &[0b10u8], &[ArgGrouping::ArgGroup])]
    #[case::two_empty_args(2, &[0b0000u8], &[ArgGrouping::Empty, ArgGrouping::Empty])]
    #[case::one_literal_one_group_arg(2, &[0b1001u8], &[ArgGrouping::ValueExprLiteral, ArgGrouping::ArgGroup])]
    fn read_bitmaps(
        #[case] num_args: usize,
        #[case] bitmap_bytes: &[u8],
        #[case] expected_entries: &[ArgGrouping],
    ) -> IonResult<()> {
        let context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let buffer = BinaryBuffer::new(context.get_ref(), bitmap_bytes);
        let bitmap =
            ArgGroupingBitmap::new(num_args, buffer.read_eexp_bitmap(bitmap_bytes.len())?.0);

        // Sanity test for inputs
        assert_eq!(num_args, expected_entries.len());

        for (actual, expected) in bitmap.iter().zip(expected_entries.iter()) {
            assert_eq!(&actual?, expected);
        }
        Ok(())
    }

    fn input_test<A: AsRef<[u8]>>(input: A) {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let input = BinaryBuffer::new(context, input.as_ref());
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
        let buffer = BinaryBuffer::new(context, &[0xECu8]);
        let (pad_size, _) = buffer.read_nop_pad().expect("unable to read NOP pad");
        assert_eq!(pad_size, 1);

        let buffer = BinaryBuffer::new(context, &[0xEDu8, 0x05, 0x00, 0x00]);
        let (pad_size, _) = buffer.read_nop_pad().expect("unable to read NOP pad");
        assert_eq!(pad_size, 4);
    }

    #[rstest]
    #[case::single_address(AnnotationsEncoding::SymbolAddress, &[0xE4, 0x07], 1, 1, &[
        RawSymbolRef::SymbolId(3)
    ])]
    #[case::two_addresses(AnnotationsEncoding::SymbolAddress, &[0xE5, 0x07, 0x09], 1, 2, &[
        RawSymbolRef::SymbolId(3),
        RawSymbolRef::SymbolId(4)
    ])]
    #[case::three_addresses(AnnotationsEncoding::SymbolAddress, &[0xE6, 0x07, 0x07, 0x09, 0x0B], 2, 3, &[
        RawSymbolRef::SymbolId(3),
        RawSymbolRef::SymbolId(4),
        RawSymbolRef::SymbolId(5)
    ])]
    #[case::single_flex_sym(AnnotationsEncoding::FlexSym, &[0xE7, 0x07], 1, 1, &[
        RawSymbolRef::SymbolId(3)
    ])]
    #[case::two_flex_syms(AnnotationsEncoding::FlexSym, &[0xE8, 0x07, 0x09], 1, 2, &[
        RawSymbolRef::SymbolId(3),
        RawSymbolRef::SymbolId(4),
    ])]
    #[case::three_flex_syms(AnnotationsEncoding::FlexSym, &[0xE9, 0x07, 0x07, 0x09, 0x0B], 2, 3, &[
        RawSymbolRef::SymbolId(3),
        RawSymbolRef::SymbolId(4),
        RawSymbolRef::SymbolId(5)
    ])]
    #[case::one_flex_syms_with_system_symbol(AnnotationsEncoding::FlexSym, &[0xE7, 0x01, 0x6A], 1, 2, &[
        RawSymbolRef::Text("encoding"),
    ])]
    #[case::two_flex_syms_with_system_symbols(AnnotationsEncoding::FlexSym, &[0xE8, 0x01, 0x60, 0x01, 0x6A], 1, 4, &[
        RawSymbolRef::SymbolId(0),
        RawSymbolRef::Text("encoding"),
    ])]
    #[case::three_flex_syms_with_system_symbols(AnnotationsEncoding::FlexSym, &[0xE9, 0x0D, 0x01, 0x60, 0x01, 0x6A, 0x01, 0x98], 2, 6, &[
        RawSymbolRef::SymbolId(0),
        RawSymbolRef::Text("encoding"),
        RawSymbolRef::Text("make_field"),
    ])]
    fn read_annotations_sequence(
        #[case] encoding: AnnotationsEncoding,
        #[case] input: &[u8],
        #[case] expected_header_length: usize,
        #[case] expected_sequence_length: usize,
        #[case] expected_annotations: &[RawSymbolRef<'_>],
    ) -> IonResult<()> {
        let context = EncodingContext::empty();
        let buffer = BinaryBuffer::new(context.get_ref(), input);
        let (sequence, remaining) =
            buffer.read_annotations_sequence(Opcode::from_byte(buffer.data[0]))?;
        assert_eq!(
            sequence.header_length as usize, expected_header_length,
            "header length actual {} != expected {}",
            sequence.header_length as usize, expected_header_length
        );
        assert_eq!(
            sequence.sequence_length as usize, expected_sequence_length,
            "sequence length actual {} != expected {}",
            sequence.sequence_length as usize, expected_sequence_length
        );
        // Read the actual sequence
        let annotations_iter = RawBinaryAnnotationsIterator_1_1::new(
            buffer.consume(sequence.header_length as usize),
            encoding,
        );
        let actual_annotations = annotations_iter.collect::<IonResult<Vec<_>>>()?;
        assert_eq!(actual_annotations, expected_annotations);
        assert!(remaining.is_empty(), "remaining input was not empty");
        Ok(())
    }

    fn eexp_test(
        macro_source: &str,
        encode_macro_fn: impl FnOnce(MacroAddress) -> Vec<u8>,
        test_fn: impl FnOnce(BinaryEExpArgsIterator_1_1<'_>) -> IonResult<()>,
    ) -> IonResult<()> {
        let mut context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let template_macro =
            TemplateCompiler::compile_from_source(context.macro_table(), macro_source)?;
        let macro_address = context
            .macro_table_mut()
            .add_template_macro(template_macro)?;
        let opcode_byte = u8::try_from(macro_address).unwrap();
        let binary_ion = encode_macro_fn(opcode_byte as usize);
        let buffer = BinaryBuffer::new(context.get_ref(), &binary_ion);
        let eexp = buffer.read_e_expression(Opcode::from_byte(opcode_byte))?.0;
        let eexp_ref = &*context.allocator.alloc_with(|| eexp);
        assert_eq!(eexp.id(), MacroIdRef::LocalAddress(macro_address));
        println!("{:?}", &eexp);
        assert_eq!(eexp.id(), MacroIdRef::LocalAddress(opcode_byte as usize));
        test_fn(eexp_ref.raw_arguments())
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
            |mut args: BinaryEExpArgsIterator_1_1<'_>| {
                assert!(args.next().is_none());
                Ok(())
            },
        )
    }

    #[test]
    fn read_eexp_with_one_arg() -> IonResult<()> {
        let macro_source = r#"
            (macro greet (name)
                (.make_string "Hello, " name "!")
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

        let args_test = |mut args: BinaryEExpArgsIterator_1_1<'_>| {
            assert_eq!(
                args.next()
                    .unwrap()?
                    .expr()
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
                (.make_string "Hello, " name "! Have a pleasant " day ".")
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

        let args_test = |mut args: BinaryEExpArgsIterator_1_1<'_>| {
            assert_eq!(
                args.next()
                    .unwrap()?
                    .expr()
                    .expect_value()?
                    .read()?
                    .expect_string()?,
                "Michelle"
            );
            assert_eq!(
                args.next()
                    .unwrap()?
                    .expr()
                    .expect_value()?
                    .read()?
                    .expect_string()?,
                "Tuesday"
            );
            Ok(())
        };

        eexp_test(macro_source, encode_eexp_fn, args_test)
    }

    #[test]
    fn read_eexp_with_star_parameter_empty() -> IonResult<()> {
        let macro_source = r#"
            (macro wrap_in_list (values*) ["first", values, "last"])
        "#;

        #[rustfmt::skip]
        let encode_eexp_fn = |address: MacroAddress| vec![
            // === Invoke macro ====
            address as u8,
            // === Argument grouping bitmap: empty ===
            0b00,
        ];

        let args_test = |mut args: BinaryEExpArgsIterator_1_1<'_>| {
            let arg_group = args.next().unwrap()?.expr().expect_arg_group()?;
            let mut group_args = arg_group.iter();
            assert!(group_args.next().is_none());
            Ok(())
        };

        eexp_test(macro_source, encode_eexp_fn, args_test)
    }

    #[test]
    fn read_eexp_with_star_parameter_value_literal() -> IonResult<()> {
        let macro_source = r#"
            (macro wrap_in_list (values*) ["first", values, "last"])
        "#;

        #[rustfmt::skip]
        let encode_eexp_fn = |address: MacroAddress| vec![
            // === Invoke macro ====
            address as u8,
            // === Argument grouping bitmap: value literal ===
            0b01,
            // === Value Literal ===
            0x61, 0x01
        ];

        let args_test = |mut args: BinaryEExpArgsIterator_1_1<'_>| {
            let arg1 = args.next().unwrap()?.expr().expect_value()?;
            assert_eq!(arg1.read()?, RawValueRef::Int(1.into()));
            Ok(())
        };

        eexp_test(macro_source, encode_eexp_fn, args_test)
    }

    #[test]
    fn read_eexp_with_star_parameter_arg_group() -> IonResult<()> {
        let macro_source = r#"
            (macro wrap_in_list (values*) ["first", values, "last"])
        "#;

        #[rustfmt::skip]
        let encode_eexp_fn = |address: MacroAddress| vec![
            // === Invoke macro ====
            address as u8,
            // === Argument group header: arg group ===
            0b10,
            // === Arg group ===
            0x0D,       // FlexUInt: Byte length 6
            0x61, 0x01, // Int 1
            0x61, 0x02, // Int 2
            0x61, 0x03, // Int 3
        ];

        let args_test = |mut args: BinaryEExpArgsIterator_1_1<'_>| {
            let arg_group = args.next().unwrap()?.expr().expect_arg_group()?;
            let mut group_exprs = arg_group.iter();
            let group_arg1 = group_exprs.next().unwrap()?;
            let group_arg2 = group_exprs.next().unwrap()?;
            let group_arg3 = group_exprs.next().unwrap()?;
            assert_eq!(
                group_arg1.expect_value()?.read()?,
                RawValueRef::Int(1.into())
            );
            assert_eq!(
                group_arg2.expect_value()?.read()?,
                RawValueRef::Int(2.into())
            );
            assert_eq!(
                group_arg3.expect_value()?.read()?,
                RawValueRef::Int(3.into())
            );
            assert!(group_exprs.next().is_none());
            Ok(())
        };

        eexp_test(macro_source, encode_eexp_fn, args_test)
    }

    #[test]
    fn read_eexp_with_star_parameter_arg_group_nested_eexp() -> IonResult<()> {
        let macro_source = r#"
            (macro wrap_in_list (values*) ["first", (%values), "last"])
        "#;

        let expected_text = r#"
            [
                "first",
                1,
                ["first", "last"],
                3,
                "last",
            ]
        "#;

        let expected = Element::read_all(expected_text)?;

        let macro_address = MacroTable::FIRST_USER_MACRO_ID as u8;
        #[rustfmt::skip]
        let data = vec![
            // === Invoke macro ====
            macro_address,
            // === Argument group header: arg group ===
            0b10,
            // === Arg group ===
            0x0D,          // FlexUInt: Byte length 6
            0x61, 0x01,    // Int 1
            macro_address, // Nested invocation of same macro
            0b00,          // Empty group
            0x61, 0x03,    // Int 3
        ];

        let mut reader = Reader::new(v1_1::Binary, data)?;
        reader.register_template_src(macro_source)?;
        let actual = reader.read_all_elements()?;
        assert!(
            actual.ion_eq(&expected),
            "Actual sequence\n{actual:?}\nwas not IonEq to expected sequence\n{expected:?}"
        );
        Ok(())
    }

    #[test]
    fn read_length_prefixed_eexp_with_star_parameter_arg_group_nested_eexp() -> IonResult<()> {
        let macro_source = r#"
            (macro wrap_in_list (values*) ["first", (%values), "last"])
        "#;

        let expected_text = r#"
            [
                "first",
                1,
                ["first", "last"],
                3,
                "last",
            ]
        "#;

        let expected = Element::read_all(expected_text)?;

        let macro_address = MacroTable::FIRST_USER_MACRO_ID as u8;
        let flex_uint_macro_address = (macro_address * 2) + 1;
        #[rustfmt::skip]
        let data = vec![
            // === Invoke length prefixed macro ===
            0xF5,
            // === Macro address ===
            flex_uint_macro_address,
            // === Length prefix ===
            0x11, // FlexUInt 8
            // === Argument bitmap: arg group ===
            0b10,
            // === Arg group ===
            0x0D,          // FlexUInt: Byte length 6
            0x61, 0x01,    // Int 1
            macro_address, // Nested invocation of same macro (not length prefixed)
            0b00,          // Bitmap: Empty group
            0x61, 0x03,    // Int 3
        ];

        let mut reader = Reader::new(v1_1::Binary, data)?;
        reader.register_template_src(macro_source)?;
        let actual = reader.read_all_elements()?;
        assert!(
            actual.ion_eq(&expected),
            "Actual sequence\n{actual:?}\nwas not IonEq to expected sequence\n{expected:?}"
        );
        Ok(())
    }

    #[test]
    fn roundtrip_macro_addresses_up_to_20_bits() -> IonResult<()> {
        // This is a large enough value that many macros will be encoded using 20 bits.
        // However, it is not large enough to fully exercise the 20-bit encoding space. To do that,
        // we would need approximately 1 million macros, which takes too much time to execute in a
        // debug build.
        const MAX_TEST_MACRO_ADDRESS: usize = 6_000;

        let mut writer = Writer::new(v1_1::Binary, Vec::new())?;
        // Invoke each of the macros we just defined in order.
        for address in MacroTable::FIRST_USER_MACRO_ID..MAX_TEST_MACRO_ADDRESS {
            let macro_n = writer.compile_macro(format!("(macro m{address} () {address})"))?;
            writer.eexp_writer(&macro_n)?.close()?;
        }
        let data = writer.close()?;

        // Read from the resulting stream and confirm that we get each value back in the expected order.
        let mut reader = Reader::new(AnyEncoding, data)?;
        for expected in MacroTable::FIRST_USER_MACRO_ID..MAX_TEST_MACRO_ADDRESS {
            let actual = reader.expect_next()?.read()?.expect_int()?.expect_usize()?;
            assert_eq!(actual, expected, "actual {actual} != expected {expected}");
        }
        Ok(())
    }

    #[test]
    fn read_length_prefixed_eexp_with_star_parameter_empty() -> IonResult<()> {
        let macro_source = r#"
            (macro wrap_in_list (values*) ["first", (%values), "last"])
        "#;

        let expected_text = r#"
            [
                "first",
                "last",
            ]
        "#;

        let expected = Element::read_all(expected_text)?;

        let macro_address = MacroTable::FIRST_USER_MACRO_ID as u8;
        let flex_uint_macro_address = (macro_address * 2) + 1;
        #[rustfmt::skip]
        let data = vec![
            // === Invoke length prefixed macro ===
            0xF5,
            // === Macro address ===
            flex_uint_macro_address,
            // === Length prefix ===
            0x03, // FlexUInt 1
            // === Argument bitmap ===
            0b00, // empty group
        ];

        let mut reader = Reader::new(v1_1::Binary, data)?;
        reader.register_template_src(macro_source)?;
        let actual = reader.read_all_elements()?;
        assert!(
            actual.ion_eq(&expected),
            "Actual sequence\n{actual:?}\nwas not IonEq to expected sequence\n{expected:?}"
        );
        Ok(())
    }
}
