#![allow(non_camel_case_types)]
use crate::lazy::binary::raw::v1_1::binary_buffer::{AnnotationsEncoding, BinaryBuffer};
use crate::lazy::encoder::binary::v1_1::flex_sym::FlexSymValue;
use crate::{IonResult, RawSymbolRef, SymbolId};

/// Iterates over a slice of bytes, lazily reading them as a sequence of FlexUInt- or
/// FlexSym-encoded symbol IDs.
pub struct RawBinaryAnnotationsIterator_1_1<'a> {
    buffer: BinaryBuffer<'a>,
    encoding: AnnotationsEncoding,
}

impl<'a> RawBinaryAnnotationsIterator_1_1<'a> {
    pub(crate) fn new(
        buffer: BinaryBuffer<'a>,
        encoding: AnnotationsEncoding,
    ) -> RawBinaryAnnotationsIterator_1_1<'a> {
        Self { buffer, encoding }
    }
}

impl<'a> Iterator for RawBinaryAnnotationsIterator_1_1<'a> {
    type Item = IonResult<RawSymbolRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            return None;
        }
        use AnnotationsEncoding::*;
        let (raw_symbol, remaining_input) = match self.encoding {
            SymbolAddress => match self.buffer.read_flex_uint() {
                Ok((flex_uint, remaining_input)) => (
                    RawSymbolRef::SymbolId(flex_uint.value() as SymbolId),
                    remaining_input,
                ),
                Err(error) => return Some(Err(error)),
            },
            FlexSym => {
                let (flex_sym, remaining_input) = match self.buffer.read_flex_sym() {
                    Ok((flex_sym, remaining_input)) => (flex_sym, remaining_input),
                    Err(error) => return Some(Err(error)),
                };
                let raw_symbol = match flex_sym.value() {
                    FlexSymValue::SymbolRef(raw_symbol) => raw_symbol,
                    FlexSymValue::Opcode(_opcode) => {
                        todo!("FlexSym escapes in annotation sequences")
                    }
                };
                (raw_symbol, remaining_input)
            }
        };
        self.buffer = remaining_input;
        Some(Ok(raw_symbol))
    }
}
