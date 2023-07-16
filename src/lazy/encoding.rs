use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::LazyRawBinaryStruct;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::LazyRawBinarySequence;
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawFieldPrivate};
use crate::lazy::decoder::{LazyDecoder, LazyRawField, LazyRawSequence, LazyRawStruct};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::raw::reader::LazyRawTextReader;
use crate::lazy::text::value::LazyRawTextValue;
use crate::{IonResult, IonType, RawSymbolTokenRef};
use std::marker::PhantomData;

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
pub struct ToDoTextSequence;

impl<'data> LazyContainerPrivate<'data, TextEncoding> for ToDoTextSequence {
    fn from_value(_value: LazyRawTextValue<'data>) -> Self {
        todo!()
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding> for ToDoTextSequence {
    type Iterator = Box<dyn Iterator<Item = IonResult<LazyRawTextValue<'data>>>>;

    fn annotations(&self) -> ToDoTextAnnotationsIterator<'data> {
        todo!()
    }

    fn ion_type(&self) -> IonType {
        todo!()
    }

    fn iter(&self) -> Self::Iterator {
        todo!()
    }

    fn as_value(&self) -> &<TextEncoding as LazyDecoder<'data>>::Value {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct ToDoTextStruct;

#[derive(Debug, Clone)]
pub struct ToDoTextField;

impl<'data> LazyRawFieldPrivate<'data, TextEncoding> for ToDoTextField {
    fn into_value(self) -> LazyRawTextValue<'data> {
        todo!()
    }
}

impl<'data> LazyRawField<'data, TextEncoding> for ToDoTextField {
    fn name(&self) -> RawSymbolTokenRef<'data> {
        todo!()
    }

    fn value(&self) -> &LazyRawTextValue<'data> {
        todo!()
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding> for ToDoTextStruct {
    fn from_value(_value: <TextEncoding as LazyDecoder>::Value) -> Self {
        todo!()
    }
}

impl<'data> LazyRawStruct<'data, TextEncoding> for ToDoTextStruct {
    type Field = ToDoTextField;
    type Iterator = Box<dyn Iterator<Item = IonResult<ToDoTextField>>>;

    fn annotations(&self) -> ToDoTextAnnotationsIterator<'data> {
        todo!()
    }

    fn find(&self, _name: &str) -> IonResult<Option<LazyRawTextValue<'data>>> {
        todo!()
    }

    fn get(&self, _name: &str) -> IonResult<Option<RawValueRef<'data, TextEncoding>>> {
        todo!()
    }

    fn iter(&self) -> Self::Iterator {
        todo!()
    }
}

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
    type Sequence = ToDoTextSequence;
    type Struct = ToDoTextStruct;
    type AnnotationsIterator = ToDoTextAnnotationsIterator<'data>;
}
