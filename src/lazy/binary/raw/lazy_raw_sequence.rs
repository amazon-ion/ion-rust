use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::lazy_raw_reader::DataSource;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::{IonResult, IonType};
use std::fmt::{Debug, Formatter};

pub struct LazyRawSequence<'data> {
    pub(crate) value: LazyRawValue<'data>,
}

impl<'data> LazyRawSequence<'data> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawSequenceIterator<'data> {
        // Get as much of the sequence's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawSequenceIterator::new(buffer_slice)
    }
}

impl<'a> Debug for LazyRawSequence<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut reader = self.iter();
        match self.value.encoded_value.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                while let Some(value) = reader.next().unwrap() {
                    write!(f, "{:?} ", value.read().unwrap()).unwrap();
                }
                write!(f, ")").unwrap();
            }
            IonType::List => {
                write!(f, "[")?;
                while let Some(value) = reader.next().unwrap() {
                    write!(f, "{:?},", value.read().unwrap()).unwrap();
                }
                write!(f, "]").unwrap();
            }
            _ => unreachable!("LazyRawSequence is only created for list and sexp"),
        }

        Ok(())
    }
}

pub struct RawSequenceIterator<'data> {
    source: DataSource<'data>,
}

impl<'data> RawSequenceIterator<'data> {
    pub(crate) fn new(input: ImmutableBuffer<'data>) -> RawSequenceIterator<'data> {
        RawSequenceIterator {
            source: DataSource::new(input),
        }
    }

    pub fn next(&mut self) -> IonResult<Option<LazyRawValue<'data>>> {
        self.source
            .try_parse_next(ImmutableBuffer::peek_value_without_field_id)
    }
}
