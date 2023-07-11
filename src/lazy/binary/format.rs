use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::lazy_raw_sequence::LazyRawBinarySequence;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::format::LazyFormat;

// This type derives trait implementations in order to allow types that contain it to also derive
// trait implementations.
#[derive(Clone, Debug)]
pub struct BinaryFormat;

impl<'data> LazyFormat<'data> for BinaryFormat {
    type Reader = LazyRawBinaryReader<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type Sequence = LazyRawBinarySequence<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
}
