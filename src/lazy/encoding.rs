use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList, LazyRawBinarySExp};
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::text::raw::r#struct::LazyRawTextStruct;
use crate::lazy::text::raw::reader::LazyRawTextReader;
use crate::lazy::text::raw::sequence::{LazyRawTextList, LazyRawTextSExp};
use crate::lazy::text::value::{LazyRawTextValue, RawTextAnnotationsIterator};

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
    type SExp = LazyRawBinarySExp<'data>;
    type List = LazyRawBinaryList<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
}

impl<'data> LazyDecoder<'data> for TextEncoding {
    type Reader = LazyRawTextReader<'data>;
    type Value = LazyRawTextValue<'data>;
    type SExp = LazyRawTextSExp<'data>;
    type List = LazyRawTextList<'data>;
    type Struct = LazyRawTextStruct<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
}
