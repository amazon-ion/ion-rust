use crate::lazy::binary::immutable_buffer::BinaryBuffer;
use crate::{IonResult, RawSymbolRef};

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct RawBinaryAnnotationsIterator<'a> {
    buffer: BinaryBuffer<'a>,
}

impl<'a> RawBinaryAnnotationsIterator<'a> {
    pub(crate) fn new(buffer: BinaryBuffer<'a>) -> RawBinaryAnnotationsIterator<'a> {
        RawBinaryAnnotationsIterator { buffer }
    }
}

impl<'a> Iterator for RawBinaryAnnotationsIterator<'a> {
    type Item = IonResult<RawSymbolRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            return None;
        }
        // TODO: If the VarUInt doesn't end before the annotations sequence does (i.e. the stream is
        //       malformed, this will surface an `Incomplete` instead of a more descriptive error.
        let (var_uint, buffer_after_var_uint) = match self.buffer.read_var_uint() {
            Ok(output) => output,
            Err(error) => return Some(Err(error)),
        };
        let symbol_id = RawSymbolRef::SymbolId(var_uint.value());
        self.buffer = buffer_after_var_uint;
        Some(Ok(symbol_id))
    }
}
