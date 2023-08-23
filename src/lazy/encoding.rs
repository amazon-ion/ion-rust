use std::marker::PhantomData;

use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::LazyRawBinarySequence;
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::text::raw::r#struct::LazyRawTextStruct;
use crate::lazy::text::raw::reader::LazyRawTextReader;
use crate::lazy::text::raw::sequence::LazyRawTextSequence;
use crate::lazy::text::value::LazyRawTextValue;
use crate::{IonResult, RawSymbolTokenRef};

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// The Ion 1.0 binary encoding.
#[derive(Clone, Debug)]
pub struct BinaryEncoding;

/// The Ion 1.0 text encoding.
#[derive(Clone, Debug)]
pub struct TextEncoding;

impl<'data> LazyDecoder<'data> for BinaryEncoding {
    type Reader = LazyRawBinaryReader<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type Sequence = LazyRawBinarySequence<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
}

// === Placeholders ===
// The types below will need to be properly defined in order for the lazy text reader to be complete.
// The exist to satisfy various trait definitions.

#[derive(Debug, Clone)]
pub struct ToDoTextAnnotationsIterator<'data> {
    spooky: &'data PhantomData<()>,
}

impl<'data> Iterator for ToDoTextAnnotationsIterator<'data> {
    type Item = IonResult<RawSymbolTokenRef<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'data> LazyDecoder<'data> for TextEncoding {
    type Reader = LazyRawTextReader<'data>;
    type Value = LazyRawTextValue<'data>;
    type Sequence = LazyRawTextSequence<'data>;
    type Struct = LazyRawTextStruct<'data>;
    type AnnotationsIterator = ToDoTextAnnotationsIterator<'data>;
}
