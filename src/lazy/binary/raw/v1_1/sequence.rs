#![allow(non_camel_case_types)]

use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::v1_1::value::LazyRawBinaryValue_1_1;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{LazyRawSequence, LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::{IonResult, IonType};
use std::fmt::{Debug, Formatter};

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryList_1_1<'top> {
    pub(crate) sequence: LazyRawBinarySequence_1_1<'top>,
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinarySExp_1_1<'top> {
    pub(crate) sequence: LazyRawBinarySequence_1_1<'top>,
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinaryList_1_1<'top> {
    fn from_value(value: LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawBinaryList_1_1 {
            sequence: LazyRawBinarySequence_1_1 { value },
        }
    }
}

impl<'top> LazyRawSequence<'top, BinaryEncoding_1_1> for LazyRawBinaryList_1_1<'top> {
    type Iterator = RawBinarySequenceIterator<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.sequence.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::List
    }

    fn iter(&self) -> Self::Iterator {
        self.sequence.iter()
    }

    fn as_value(&self) -> LazyRawBinaryValue_1_1<'top> {
        self.sequence.value
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinarySExp_1_1<'top> {
    fn from_value(value: LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawBinarySExp_1_1 {
            sequence: LazyRawBinarySequence_1_1 { value },
        }
    }
}

impl<'top> LazyRawSequence<'top, BinaryEncoding_1_1> for LazyRawBinarySExp_1_1<'top> {
    type Iterator = RawBinarySequenceIterator<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'top> {
        self.sequence.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    fn iter(&self) -> Self::Iterator {
        self.sequence.iter()
    }

    fn as_value(&self) -> LazyRawBinaryValue_1_1<'top> {
        self.sequence.value
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawBinarySequence_1_1<'top> {
    pub(crate) value: LazyRawBinaryValue_1_1<'top>,
}

impl<'top> LazyRawBinarySequence_1_1<'top> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawBinarySequenceIterator<'top> {
        // Get as much of the sequence's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = self.value.available_body();
        RawBinarySequenceIterator::new(buffer_slice)
    }
}

impl<'a, 'top> IntoIterator for &'a LazyRawBinarySequence_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = RawBinarySequenceIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawBinarySequence_1_1<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.value.encoded_value.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                for value in self {
                    write!(f, "{:?} ", value?)?;
                }
                write!(f, ")").unwrap();
            }
            IonType::List => {
                write!(f, "[")?;
                for value in self {
                    write!(f, "{:?},", value?)?;
                }
                write!(f, "]").unwrap();
            }
            _ => unreachable!("LazyRawSequence is only created for list and sexp"),
        }

        Ok(())
    }
}

pub struct RawBinarySequenceIterator<'top> {
    source: ImmutableBuffer<'top>,
}

impl<'top> RawBinarySequenceIterator<'top> {
    pub(crate) fn new(input: ImmutableBuffer<'top>) -> RawBinarySequenceIterator<'top> {
        RawBinarySequenceIterator { source: input }
    }
}

impl<'top> Iterator for RawBinarySequenceIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self
            .source
            .try_parse_next(ImmutableBuffer::<'top>::peek_sequence_value)
        {
            Ok(Some(value)) => Some(Ok(RawValueExpr::ValueLiteral(value))),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}
