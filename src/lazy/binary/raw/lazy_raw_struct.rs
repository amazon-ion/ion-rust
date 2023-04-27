use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::lazy_raw_reader::{DataSource, LazyRawField};
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::IonResult;
use std::fmt;
use std::fmt::{Debug, Formatter};

pub struct LazyRawStruct<'data> {
    pub(crate) value: LazyRawValue<'data>,
}

impl<'a> Debug for LazyRawStruct<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut reader = self.iter();
        write!(f, "{{")?;
        while let Some(field) = reader.next().unwrap() {
            let name = field.name();
            let lazy_value = field.value();
            let value = lazy_value.read().unwrap();
            write!(f, "{:?}:{:?},", name, value).unwrap();
        }
        write!(f, "}}").unwrap();
        Ok(())
    }
}

impl<'data> LazyRawStruct<'data> {
    pub fn iter(&self) -> RawStructIterator<'data> {
        // Get as much of the struct's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawStructIterator::new(buffer_slice)
    }
}

pub struct RawStructIterator<'data> {
    source: DataSource<'data>,
}

impl<'data> RawStructIterator<'data> {
    pub(crate) fn new(input: ImmutableBuffer<'data>) -> RawStructIterator<'data> {
        RawStructIterator {
            source: DataSource::new(input),
        }
    }

    pub fn next(&mut self) -> IonResult<Option<LazyRawField<'data>>> {
        if let Some(lazy_field) = self.source.try_parse_next(ImmutableBuffer::peek_field)? {
            Ok(Some(LazyRawField::new(lazy_field)))
        } else {
            Ok(None)
        }
    }
}
