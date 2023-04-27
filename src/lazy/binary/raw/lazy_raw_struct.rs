use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::lazy_raw_reader::{DataSource, LazyRawField};
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::IonResult;
use std::fmt;
use std::fmt::{Debug, Formatter};

pub struct LazyRawStruct<'data> {
    pub(crate) value: LazyRawValue<'data>,
}

impl<'a, 'data> IntoIterator for &'a LazyRawStruct<'data> {
    type Item = IonResult<LazyRawField<'data>>;
    type IntoIter = RawStructIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawStruct<'a> {
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
}

impl<'data> Iterator for RawStructIterator<'data> {
    type Item = IonResult<LazyRawField<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.source.try_parse_next(ImmutableBuffer::peek_field) {
            Ok(Some(lazy_raw_value)) => Some(Ok(LazyRawField::new(lazy_raw_value))),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}
