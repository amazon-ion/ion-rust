#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};

use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator_1_1;
use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::v1_1::value::LazyRawBinaryValue_1_1;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{Decoder, LazyRawContainer, LazyRawSequence, LazyRawValueExpr};
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::{try_or_some_err, IonResult, IonType};

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinaryList_1_1<'top> {
    pub(crate) sequence: LazyRawBinarySequence_1_1<'top>,
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawBinarySExp_1_1<'top> {
    pub(crate) sequence: LazyRawBinarySequence_1_1<'top>,
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinaryList_1_1<'top> {
    fn from_value(value: &'top LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawBinaryList_1_1 {
            sequence: LazyRawBinarySequence_1_1 { value },
        }
    }
}

impl<'top> LazyRawContainer<'top, BinaryEncoding_1_1> for LazyRawBinaryList_1_1<'top> {
    fn as_value(&self) -> <BinaryEncoding_1_1 as Decoder>::Value<'top> {
        self.sequence.value
    }
}

impl<'top> LazyRawSequence<'top, BinaryEncoding_1_1> for LazyRawBinaryList_1_1<'top> {
    type Iterator = RawBinarySequenceIterator_1_1<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        self.sequence.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::List
    }

    fn iter(&self) -> Self::Iterator {
        self.sequence.iter()
    }
}

impl<'top> LazyContainerPrivate<'top, BinaryEncoding_1_1> for LazyRawBinarySExp_1_1<'top> {
    fn from_value(value: &'top LazyRawBinaryValue_1_1<'top>) -> Self {
        LazyRawBinarySExp_1_1 {
            sequence: LazyRawBinarySequence_1_1 { value },
        }
    }
}

impl<'top> LazyRawContainer<'top, BinaryEncoding_1_1> for LazyRawBinarySExp_1_1<'top> {
    fn as_value(&self) -> <BinaryEncoding_1_1 as Decoder>::Value<'top> {
        self.sequence.value
    }
}

impl<'top> LazyRawSequence<'top, BinaryEncoding_1_1> for LazyRawBinarySExp_1_1<'top> {
    type Iterator = RawBinarySequenceIterator_1_1<'top>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator_1_1<'top> {
        self.sequence.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    fn iter(&self) -> Self::Iterator {
        self.sequence.iter()
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawBinarySequence_1_1<'top> {
    pub(crate) value: &'top LazyRawBinaryValue_1_1<'top>,
}

impl<'top> LazyRawBinarySequence_1_1<'top> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawBinarySequenceIterator_1_1<'top> {
        let buffer_slice = self.value.value_body_buffer();
        RawBinarySequenceIterator_1_1::new(buffer_slice)
    }
}

impl<'a, 'top> IntoIterator for &'a LazyRawBinarySequence_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = RawBinarySequenceIterator_1_1<'top>;

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

pub struct RawBinarySequenceIterator_1_1<'top> {
    input: ImmutableBuffer<'top>,
}

impl<'top> RawBinarySequenceIterator_1_1<'top> {
    pub(crate) fn new(input: ImmutableBuffer<'top>) -> RawBinarySequenceIterator_1_1<'top> {
        RawBinarySequenceIterator_1_1 { input }
    }
}

impl<'top> Iterator for RawBinarySequenceIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (maybe_item, remaining_input) = try_or_some_err!(self.input.read_sequence_value_expr());
        if let Some(item) = maybe_item {
            self.input = remaining_input;
            return Some(Ok(item));
        }
        None
    }
}
