use crate::lazy::binary::raw::lazy_raw_reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::lazy_raw_sequence::LazyRawBinarySequence;
use crate::lazy::binary::raw::lazy_raw_struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawBinaryValue;
use crate::lazy::binary::raw::raw_annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::{IonResult, IonType, RawSymbolTokenRef};
use std::fmt::Debug;

pub trait LazyFormat<'data>: Sized + Debug + Clone {
    type Reader: LazyRawReader<'data, Self>;
    type Sequence: LazyRawSequence<'data, Self>;
    type Struct: LazyRawStruct<'data, Self>;
    type Value: LazyRawValue<'data, Self>;
    type AnnotationsIterator: Iterator<Item = IonResult<RawSymbolTokenRef<'data>>>;
}

pub trait LazyRawReader<'data, F: LazyFormat<'data>> {
    fn new(data: &'data [u8]) -> Self;
    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, F>>;
}

pub trait LazyRawValue<'data, F: LazyFormat<'data>>:
    private::LazyRawValuePrivate<'data> + Clone + Debug
{
    fn ion_type(&self) -> IonType;
    fn annotations(&self) -> F::AnnotationsIterator;
    fn read(&self) -> IonResult<RawValueRef<'data, F>>;
}

pub trait LazyRawSequence<'data, F: LazyFormat<'data>>:
    private::LazyContainerPrivate<'data, F> + Debug
{
    type Iterator: Iterator<Item = IonResult<F::Value>>;
    fn annotations(&self) -> F::AnnotationsIterator;
    fn ion_type(&self) -> IonType;
    fn iter(&self) -> Self::Iterator;
    fn as_value(&self) -> &F::Value;
}

pub trait LazyRawStruct<'data, F: LazyFormat<'data>>:
    private::LazyContainerPrivate<'data, F> + Debug
{
    type Field: LazyRawField<'data, F>;
    type Iterator: Iterator<Item = IonResult<Self::Field>>;

    fn annotations(&self) -> F::AnnotationsIterator;
    fn find(&self, name: &str) -> IonResult<Option<F::Value>>;
    fn get(&self, name: &str) -> IonResult<Option<RawValueRef<'data, F>>>;
    fn iter(&self) -> Self::Iterator;
}

pub trait LazyRawField<'data, F: LazyFormat<'data>>:
    private::LazyRawFieldPrivate<'data, F> + Debug
{
    fn name(&self) -> RawSymbolTokenRef<'data>;
    fn value(&self) -> &F::Value;
}

// This private module houses public traits. This allows the traits above to depend on them,
// but keeps users from being able to use them.
pub(crate) mod private {
    use super::LazyFormat;
    use crate::RawSymbolTokenRef;

    pub trait LazyRawFieldPrivate<'data, F: LazyFormat<'data>> {
        fn into_value(self) -> F::Value;
    }

    pub trait LazyContainerPrivate<'data, F: LazyFormat<'data>> {
        fn from_value(value: F::Value) -> Self;
    }

    // TODO: Doc
    pub trait LazyRawValuePrivate<'data> {
        fn field_name(&self) -> Option<RawSymbolTokenRef<'data>>;
    }
}

// == Impl for binary ==

#[derive(Clone, Debug)]
pub struct BinaryFormat;

impl<'data> LazyFormat<'data> for BinaryFormat {
    type Reader = LazyRawBinaryReader<'data>;
    type Sequence = LazyRawBinarySequence<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
}
