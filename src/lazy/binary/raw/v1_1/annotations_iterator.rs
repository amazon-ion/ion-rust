use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::{IonResult, RawSymbolTokenRef};

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct RawBinaryAnnotationsIterator<'a> {
    buffer: ImmutableBuffer<'a>,
}

impl<'a> RawBinaryAnnotationsIterator<'a> {
    pub(crate) fn new(buffer: ImmutableBuffer<'a>) -> RawBinaryAnnotationsIterator<'a> {
        RawBinaryAnnotationsIterator { buffer }
    }
}

impl<'a> Iterator for RawBinaryAnnotationsIterator<'a> {
    type Item = IonResult<RawSymbolTokenRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}
