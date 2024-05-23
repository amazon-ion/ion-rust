#![allow(non_camel_case_types)]
use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::{IonResult, RawSymbolRef};

/// Iterates over a slice of bytes, lazily reading them as a sequence of FlexUInt- or
/// FlexSym-encoded symbol IDs.
pub struct RawBinaryAnnotationsIterator_1_1<'a> {
    buffer: ImmutableBuffer<'a>,
}

impl<'a> RawBinaryAnnotationsIterator_1_1<'a> {
    pub(crate) fn new(buffer: ImmutableBuffer<'a>) -> RawBinaryAnnotationsIterator_1_1<'a> {
        Self { buffer }
    }
}

impl<'a> Iterator for RawBinaryAnnotationsIterator_1_1<'a> {
    type Item = IonResult<RawSymbolRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
