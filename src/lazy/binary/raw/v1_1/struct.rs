#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator_1_1;
use crate::lazy::binary::raw::v1_1::{
    immutable_buffer::ImmutableBuffer, value::LazyRawBinaryValue_1_1,
};
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName, LazyRawStruct,
};
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::span::Span;
use crate::{IonResult, RawSymbolRef};

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryFieldName_1_1<'top> {
    // The field name has to be read in order to discover its length, so we store it here to avoid
    // needing to re-read it.
    field_name: RawSymbolRef<'top>,
    // For viewing the span/range of the field name
    matched: ImmutableBuffer<'top>,
}

impl<'top> LazyRawBinaryFieldName_1_1<'top> {
    pub fn new(field_name: RawSymbolRef<'top>, matched: ImmutableBuffer<'top>) -> Self {
        Self {
            field_name,
            matched,
        }
    }
}

impl<'top> HasSpan<'top> for LazyRawBinaryFieldName_1_1<'top> {
    fn span(&self) -> Span<'top> {
        todo!()
    }
}

impl<'top> HasRange for LazyRawBinaryFieldName_1_1<'top> {
    fn range(&self) -> Range<usize> {
        todo!()
    }
}

impl<'top> LazyRawFieldName<'top> for LazyRawBinaryFieldName_1_1<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        todo!()
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawBinaryStruct_1_1<'top> {
    pub(crate) value: LazyRawBinaryValue_1_1<'top>,
}

impl<'a, 'top> IntoIterator for &'a LazyRawBinaryStruct_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = RawBinaryStructIterator_1_1<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top> Debug for LazyRawBinaryStruct_1_1<'top> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field in self {
            let (name, lazy_value) = field?.expect_name_value()?;
            let value = lazy_value.read()?;
            write!(f, "{:?}:{:?},", name, value)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<'top> LazyRawBinaryStruct_1_1<'top> {
    fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        self.value.annotations()
    }

    pub fn iter(&self) -> RawBinaryStructIterator_1_1<'top> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinaryStructIterator_1_1::new(buffer_slice)
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    fn from_value(value: LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawBinaryStruct_1_1 { value }
    }
}

impl<'top> LazyRawContainer<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    fn as_value(&self) -> <BinaryEncoding_1_1 as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top> LazyRawStruct<'top, BinaryEncoding_1_1> for LazyRawBinaryStruct_1_1<'top> {
    type Iterator = RawBinaryStructIterator_1_1<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        self.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        self.iter()
    }
}

pub struct RawBinaryStructIterator_1_1<'top> {
    source: ImmutableBuffer<'top>,
}

impl<'top> RawBinaryStructIterator_1_1<'top> {
    pub(crate) fn new(input: ImmutableBuffer<'top>) -> RawBinaryStructIterator_1_1<'top> {
        RawBinaryStructIterator_1_1 { source: input }
    }
}

impl<'top> Iterator for RawBinaryStructIterator_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
