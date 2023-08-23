use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::reader::DataSource;
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::LazyRawSequence;
use crate::lazy::encoding::BinaryEncoding;
use crate::{IonResult, IonType};
use std::fmt;
use std::fmt::{Debug, Formatter};

#[derive(Clone)]
pub struct LazyRawBinarySequence<'data> {
    pub(crate) value: LazyRawBinaryValue<'data>,
}

impl<'data> LazyRawBinarySequence<'data> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawBinarySequenceIterator<'data> {
        // Get as much of the sequence's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinarySequenceIterator::new(buffer_slice)
    }
}

impl<'data> LazyContainerPrivate<'data, BinaryEncoding> for LazyRawBinarySequence<'data> {
    fn from_value(value: LazyRawBinaryValue<'data>) -> Self {
        LazyRawBinarySequence { value }
    }
}

impl<'data> LazyRawSequence<'data, BinaryEncoding> for LazyRawBinarySequence<'data> {
    type Iterator = RawBinarySequenceIterator<'data>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        LazyRawBinarySequence::iter(self)
    }

    fn as_value(&self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'a, 'data> IntoIterator for &'a LazyRawBinarySequence<'data> {
    type Item = IonResult<LazyRawBinaryValue<'data>>;
    type IntoIter = RawBinarySequenceIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawBinarySequence<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.value.encoded_value.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                for value in self {
                    write!(
                        f,
                        "{:?} ",
                        value
                            .map_err(|_| fmt::Error)?
                            .read()
                            .map_err(|_| fmt::Error)?
                    )?;
                }
                write!(f, ")").unwrap();
            }
            IonType::List => {
                write!(f, "[")?;
                for value in self {
                    write!(
                        f,
                        "{:?},",
                        value
                            .map_err(|_| fmt::Error)?
                            .read()
                            .map_err(|_| fmt::Error)?
                    )?;
                }
                write!(f, "]").unwrap();
            }
            _ => unreachable!("LazyRawSequence is only created for list and sexp"),
        }

        Ok(())
    }
}

pub struct RawBinarySequenceIterator<'data> {
    source: DataSource<'data>,
}

impl<'data> RawBinarySequenceIterator<'data> {
    pub(crate) fn new(input: ImmutableBuffer<'data>) -> RawBinarySequenceIterator<'data> {
        RawBinarySequenceIterator {
            source: DataSource::new(input),
        }
    }
}

impl<'data> Iterator for RawBinarySequenceIterator<'data> {
    type Item = IonResult<LazyRawBinaryValue<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.source
            .try_parse_next(ImmutableBuffer::peek_value_without_field_id)
            .transpose()
    }
}
