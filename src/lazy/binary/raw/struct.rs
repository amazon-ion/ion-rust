#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::reader::DataSource;
use crate::lazy::binary::raw::value::LazyRawBinaryValue_1_0;
use crate::lazy::decoder::private::{
    LazyContainerPrivate, LazyRawFieldPrivate, LazyRawValuePrivate,
};
use crate::lazy::decoder::{
    LazyRawField, LazyRawFieldExpr, LazyRawStruct, RawFieldExpr, RawValueExpr,
};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::{IonResult, RawSymbolTokenRef};

#[derive(Copy, Clone)]
pub struct LazyRawBinaryStruct_1_0<'top> {
    pub(crate) value: LazyRawBinaryValue_1_0<'top>,
}

impl<'a, 'top> IntoIterator for &'a LazyRawBinaryStruct_1_0<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_0>>;
    type IntoIter = RawBinaryStructIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top> Debug for LazyRawBinaryStruct_1_0<'top> {
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

impl<'top> LazyRawBinaryStruct_1_0<'top> {
    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.value.annotations()
    }

    pub fn iter(&self) -> RawBinaryStructIterator<'top> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinaryStructIterator::new(buffer_slice)
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_0> for LazyRawBinaryStruct_1_0<'top> {
    fn from_value(value: LazyRawBinaryValue_1_0<'top>) -> Self {
        LazyRawBinaryStruct_1_0 { value }
    }
}

impl<'top> LazyRawStruct<'top, BinaryEncoding_1_0> for LazyRawBinaryStruct_1_0<'top> {
    type Iterator = RawBinaryStructIterator<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        self.iter()
    }
}

pub struct RawBinaryStructIterator<'top> {
    source: DataSource<'top>,
}

impl<'top> RawBinaryStructIterator<'top> {
    pub(crate) fn new(input: ImmutableBuffer<'top>) -> RawBinaryStructIterator<'top> {
        RawBinaryStructIterator {
            source: DataSource::new(input),
        }
    }
}

impl<'top> Iterator for RawBinaryStructIterator<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, BinaryEncoding_1_0>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.source.try_parse_next(ImmutableBuffer::peek_field) {
            Ok(Some(lazy_raw_value)) => Some(Ok(RawFieldExpr::NameValuePair(
                lazy_raw_value.field_name().unwrap(),
                RawValueExpr::ValueLiteral(lazy_raw_value),
            ))),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawBinaryField<'top> {
    pub(crate) value: LazyRawBinaryValue_1_0<'top>,
}

impl<'top> LazyRawBinaryField<'top> {
    pub(crate) fn new(value: LazyRawBinaryValue_1_0<'top>) -> Self {
        LazyRawBinaryField { value }
    }

    pub fn name(&self) -> RawSymbolTokenRef<'top> {
        // We're in a struct field, the field ID must be populated.
        let field_id = self.value.encoded_value.field_id.unwrap();
        RawSymbolTokenRef::SymbolId(field_id)
    }

    pub fn value(&self) -> LazyRawBinaryValue_1_0<'top> {
        self.value
    }

    pub(crate) fn into_value(self) -> LazyRawBinaryValue_1_0<'top> {
        self.value
    }
}

impl<'top> LazyRawFieldPrivate<'top, BinaryEncoding_1_0> for LazyRawBinaryField<'top> {
    fn into_value(self) -> LazyRawBinaryValue_1_0<'top> {
        self.value
    }
}

impl<'top> LazyRawField<'top, BinaryEncoding_1_0> for LazyRawBinaryField<'top> {
    fn name(&self) -> RawSymbolTokenRef<'top> {
        LazyRawBinaryField::name(self)
    }

    fn value(&self) -> LazyRawBinaryValue_1_0<'top> {
        self.value()
    }
}

impl<'top> Debug for LazyRawBinaryField<'top> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "${}: {:?}",
            self.value.encoded_value.field_id.unwrap(),
            self.value()
        )
    }
}
