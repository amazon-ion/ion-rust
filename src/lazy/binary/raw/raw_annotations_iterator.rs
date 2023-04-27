use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::{IonResult, RawSymbolTokenRef};

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct RawAnnotationsIterator<'a> {
    buffer: ImmutableBuffer<'a>,
}

impl<'a> RawAnnotationsIterator<'a> {
    pub(crate) fn new(buffer: ImmutableBuffer<'a>) -> RawAnnotationsIterator<'a> {
        RawAnnotationsIterator { buffer }
    }
}

impl<'a> Iterator for RawAnnotationsIterator<'a> {
    type Item = IonResult<RawSymbolTokenRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            return None;
        }
        let (var_uint, buffer_after_var_uint) = match self.buffer.read_var_uint() {
            Ok(output) => output,
            Err(error) => return Some(Err(error)),
        };
        // If this var_uint was longer than the declared annotations wrapper length, return an error.
        let symbol_id = RawSymbolTokenRef::SymbolId(var_uint.value());
        self.buffer = buffer_after_var_uint;
        Some(Ok(symbol_id))
    }
}
