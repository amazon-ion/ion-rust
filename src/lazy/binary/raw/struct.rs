use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::reader::DataSource;
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::private::{
    LazyContainerPrivate, LazyRawFieldPrivate, LazyRawValuePrivate,
};
use crate::lazy::decoder::{LazyRawField, LazyRawFieldExpr, LazyRawStruct, LazyRawValueExpr};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::{IonResult, RawSymbolTokenRef};

#[derive(Copy, Clone)]
pub struct LazyRawBinaryStruct<'data> {
    pub(crate) value: LazyRawBinaryValue<'data>,
}

impl<'a, 'data> IntoIterator for &'a LazyRawBinaryStruct<'data> {
    type Item = IonResult<LazyRawFieldExpr<'data, BinaryEncoding_1_0>>;
    type IntoIter = RawBinaryStructIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawBinaryStruct<'a> {
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

impl<'data> LazyRawBinaryStruct<'data> {
    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.value.annotations()
    }

    pub fn iter(&self) -> RawBinaryStructIterator<'data> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinaryStructIterator::new(buffer_slice)
    }
}

impl<'data> LazyContainerPrivate<'data, BinaryEncoding_1_0> for LazyRawBinaryStruct<'data> {
    fn from_value(value: LazyRawBinaryValue<'data>) -> Self {
        LazyRawBinaryStruct { value }
    }
}

impl<'data> LazyRawStruct<'data, BinaryEncoding_1_0> for LazyRawBinaryStruct<'data> {
    type Iterator = RawBinaryStructIterator<'data>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        self.iter()
    }
}

pub struct RawBinaryStructIterator<'data> {
    source: DataSource<'data>,
}

impl<'data> RawBinaryStructIterator<'data> {
    pub(crate) fn new(input: ImmutableBuffer<'data>) -> RawBinaryStructIterator<'data> {
        RawBinaryStructIterator {
            source: DataSource::new(input),
        }
    }
}

impl<'data> Iterator for RawBinaryStructIterator<'data> {
    type Item = IonResult<LazyRawFieldExpr<'data, BinaryEncoding_1_0>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.source.try_parse_next(ImmutableBuffer::peek_field) {
            Ok(Some(lazy_raw_value)) => Some(Ok(LazyRawFieldExpr::NameValuePair(
                lazy_raw_value.field_name().unwrap(),
                LazyRawValueExpr::ValueLiteral(lazy_raw_value),
            ))),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawBinaryField<'data> {
    pub(crate) value: LazyRawBinaryValue<'data>,
}

impl<'data> LazyRawBinaryField<'data> {
    pub(crate) fn new(value: LazyRawBinaryValue<'data>) -> Self {
        LazyRawBinaryField { value }
    }

    pub fn name(&self) -> RawSymbolTokenRef<'data> {
        // We're in a struct field, the field ID must be populated.
        let field_id = self.value.encoded_value.field_id.unwrap();
        RawSymbolTokenRef::SymbolId(field_id)
    }

    pub fn value(&self) -> LazyRawBinaryValue<'data> {
        self.value
    }

    pub(crate) fn into_value(self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'data> LazyRawFieldPrivate<'data, BinaryEncoding_1_0> for LazyRawBinaryField<'data> {
    fn into_value(self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'data> LazyRawField<'data, BinaryEncoding_1_0> for LazyRawBinaryField<'data> {
    fn name(&self) -> RawSymbolTokenRef<'data> {
        LazyRawBinaryField::name(self)
    }

    fn value(&self) -> LazyRawBinaryValue<'data> {
        self.value()
    }
}

impl<'a> Debug for LazyRawBinaryField<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "${}: {:?}",
            self.value.encoded_value.field_id.unwrap(),
            self.value()
        )
    }
}
