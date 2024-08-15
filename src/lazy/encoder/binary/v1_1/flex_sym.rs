use core::cmp::Ordering;

use bumpalo::collections::Vec as BumpVec;
use ice_code::ice as cold_path;

use crate::lazy::binary::raw::v1_1::type_descriptor::Opcode;
use crate::lazy::encoder::binary::v1_1::flex_int::FlexInt;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::IonResult;
use crate::RawSymbolRef::{self, SymbolId, Text};

#[derive(Debug, Clone, Copy)]
pub enum FlexSymValue<'top> {
    SymbolRef(RawSymbolRef<'top>),
    Opcode(Opcode),
}

/// An Ion 1.1 encoding primitive that can compactly represent a symbol ID or inline text.
#[derive(Debug)]
pub struct FlexSym<'top> {
    value: FlexSymValue<'top>,
    size_in_bytes: usize,
}

impl<'top> FlexSym<'top> {
    /// A FlexSym-encoded logical zero: the byte `0x01u8`
    pub const ZERO: u8 = 0x01;

    /// Encode the provided `symbol` as a FlexSym and write it to the provided [`BumpVec`].
    pub fn encode_symbol(output: &mut BumpVec<u8>, symbol: impl AsRawSymbolRef) {
        let symbol_token = symbol.as_raw_symbol_token_ref();
        // Write the field name
        match symbol_token {
            SymbolId(sid) if sid != 0 => {
                FlexInt::encode_i64(output, sid as i64);
            }
            Text(text) if !text.is_empty() => {
                let negated_num_bytes = -(text.len() as i64);
                FlexInt::encode_i64(output, negated_num_bytes);
                output.extend_from_slice_copy(text.as_bytes());
            }
            _ => cold_path! {
                Self::encode_special_case(output, symbol_token)
            },
        };
    }

    /// Encodes the empty string or symbol ID zero as a FlexSym. The caller is responsible for
    /// confirming that `symbol` is one of those two cases before calling.
    fn encode_special_case(output: &mut BumpVec<u8>, symbol: RawSymbolRef) {
        let encoding: &[u8] = match symbol {
            SymbolId(_) => &[FlexSym::ZERO, 0xE1, 0x00],
            Text(_) => &[FlexSym::ZERO, 0x90],
        };
        output.extend_from_slice_copy(encoding);
    }

    /// Reads a [`FlexSym`] from the beginning of `input`.
    ///
    /// `input` is the byte slice from which to read a [`FlexSym`].
    /// `offset` is the position of the slice in some larger input stream. It is only used to
    ///          populate an appropriate error message if reading fails.
    pub fn read(input: &'top [u8], offset: usize) -> IonResult<FlexSym<'top>> {
        use crate::{result::IonFailure, IonError};

        let value = FlexInt::read(input, offset)?;
        let sym_value = value.value();
        let (flex_sym_value, size_in_bytes) = match sym_value.cmp(&0) {
            Ordering::Greater => (
                FlexSymValue::SymbolRef(SymbolId(sym_value as usize)),
                value.size_in_bytes(),
            ),
            Ordering::Less => {
                let flex_int_len = value.size_in_bytes();
                let len = sym_value.unsigned_abs() as usize;
                let flex_sym_end = flex_int_len + len;
                if input.len() < flex_sym_end {
                    return IonResult::incomplete("reading a FlexSym", offset);
                }
                let text =
                    std::str::from_utf8(&input[flex_int_len..flex_sym_end]).map_err(|_| {
                        IonError::decoding_error("found FlexSym with invalid UTF-8 data")
                    })?;
                let symbol_ref = Text(text);
                (FlexSymValue::SymbolRef(symbol_ref), flex_int_len + len)
            }
            Ordering::Equal => (
                FlexSymValue::Opcode(Opcode::from_byte(input[value.size_in_bytes()])),
                value.size_in_bytes() + 1,
            ),
        };

        Ok(Self {
            value: flex_sym_value,
            size_in_bytes,
        })
    }

    pub fn value(&self) -> FlexSymValue<'top> {
        self.value
    }

    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bytes
    }
}
