use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::lazy_raw_reader::DataSource;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawBinaryValue;
use crate::lazy::binary::raw::raw_annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::format::private::{LazyContainerPrivate, LazyRawFieldPrivate};
use crate::lazy::format::{BinaryFormat, LazyRawField, LazyRawStruct};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{IonResult, RawSymbolTokenRef};
use std::fmt;
use std::fmt::{Debug, Formatter};

pub struct LazyRawBinaryStruct<'data> {
    pub(crate) value: LazyRawBinaryValue<'data>,
}

impl<'a, 'data> IntoIterator for &'a LazyRawBinaryStruct<'data> {
    type Item = IonResult<LazyRawBinaryField<'data>>;
    type IntoIter = RawBinaryStructIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawBinaryStruct<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field in self {
            let field = field.map_err(|_| fmt::Error)?;
            let name = field.name();
            let lazy_value = field.value();
            let value = lazy_value.read().map_err(|_| fmt::Error)?;
            write!(f, "{:?}:{:?},", name, value).unwrap();
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<'data> LazyRawBinaryStruct<'data> {
    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn find(&self, name: &str) -> IonResult<Option<LazyRawBinaryValue<'data>>> {
        let name: RawSymbolTokenRef = name.as_raw_symbol_token_ref();
        for field in self {
            let field = field?;
            if field.name() == name {
                let value = field.value;
                return Ok(Some(value));
            }
        }
        Ok(None)
    }

    fn get(&self, name: &str) -> IonResult<Option<RawValueRef<'data, BinaryFormat>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    pub fn iter(&self) -> RawBinaryStructIterator<'data> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinaryStructIterator::new(buffer_slice)
    }
}

impl<'data> LazyContainerPrivate<'data, BinaryFormat> for LazyRawBinaryStruct<'data> {
    fn from_value(value: LazyRawBinaryValue<'data>) -> Self {
        LazyRawBinaryStruct { value }
    }
}

impl<'data> LazyRawStruct<'data, BinaryFormat> for LazyRawBinaryStruct<'data> {
    type Field = LazyRawBinaryField<'data>;
    type Iterator = RawBinaryStructIterator<'data>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.annotations()
    }

    fn find(&self, name: &str) -> IonResult<Option<LazyRawBinaryValue<'data>>> {
        self.find(name)
    }

    fn get(&self, name: &str) -> IonResult<Option<RawValueRef<'data, BinaryFormat>>> {
        self.get(name)
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
    type Item = IonResult<LazyRawBinaryField<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.source.try_parse_next(ImmutableBuffer::peek_field) {
            Ok(Some(lazy_raw_value)) => Some(Ok(LazyRawBinaryField::new(lazy_raw_value))),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

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

    pub fn value(&self) -> &LazyRawBinaryValue<'data> {
        &self.value
    }

    pub(crate) fn into_value(self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'data> LazyRawFieldPrivate<'data, BinaryFormat> for LazyRawBinaryField<'data> {
    fn into_value(self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'data> LazyRawField<'data, BinaryFormat> for LazyRawBinaryField<'data> {
    fn name(&self) -> RawSymbolTokenRef<'data> {
        LazyRawBinaryField::name(self)
    }

    fn value(&self) -> &LazyRawBinaryValue<'data> {
        LazyRawBinaryField::value(self)
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
