#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};

use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator_1_1;
use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::v1_1::value::{DelimitedContents, LazyRawBinaryValue_1_1};
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
        let delimited_expr_cache = match value.delimited_contents {
            DelimitedContents::None => None,
            DelimitedContents::Values(values) => Some(values),
            DelimitedContents::Fields(_) => unreachable!("sequence contained fields"),
        };
        LazyRawBinaryList_1_1 {
            sequence: LazyRawBinarySequence_1_1 {
                value,
                delimited_expr_cache,
            },
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
        let delimited_expr_cache = match value.delimited_contents {
            DelimitedContents::None => None,
            DelimitedContents::Values(values) => Some(values),
            DelimitedContents::Fields(_) => unreachable!("sequence contained fields"),
        };
        LazyRawBinarySExp_1_1 {
            sequence: LazyRawBinarySequence_1_1 {
                value,
                delimited_expr_cache,
            },
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
    pub(crate) delimited_expr_cache: Option<&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]>,
}

impl<'top> LazyRawBinarySequence_1_1<'top> {
    pub fn new(
        value: &'top LazyRawBinaryValue_1_1<'top>,
        delimited_expr_cache: Option<&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]>,
    ) -> Self {
        Self {
            value,
            delimited_expr_cache,
        }
    }

    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawBinarySequenceIterator_1_1<'top> {
        // Get as much of the sequence's body as is available in the input buffer.
        // Reading a child value may fail as `Incomplete`
        let buffer_slice = if self.value.is_delimited() {
            self.value.input
        } else {
            self.value.value_body_buffer()
        };
        RawBinarySequenceIterator_1_1::new(buffer_slice, self.delimited_expr_cache)
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

#[derive(Debug, Copy, Clone)]
pub struct RawBinarySequenceIterator_1_1<'top> {
    source: ImmutableBuffer<'top>,
    bytes_to_skip: usize,
    delimited_expr_cache: Option<&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]>,
    expr_cache_index: usize,
}

impl<'top> RawBinarySequenceIterator_1_1<'top> {
    pub(crate) fn new(
        input: ImmutableBuffer<'top>,
        delimited_expr_cache: Option<&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]>,
    ) -> RawBinarySequenceIterator_1_1<'top> {
        RawBinarySequenceIterator_1_1 {
            source: input,
            bytes_to_skip: 0,
            delimited_expr_cache,
            expr_cache_index: 0,
        }
    }
}

impl<'top> Iterator for RawBinarySequenceIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(expr_cache) = self.delimited_expr_cache {
            let expr = expr_cache.get(self.expr_cache_index)?;
            self.expr_cache_index += 1;
            Some(Ok(*expr))
        } else {
            self.source = self.source.consume(self.bytes_to_skip);
            let (maybe_item, remaining_input) =
                try_or_some_err!(self.source.read_sequence_value_expr());
            if let Some(item) = maybe_item {
                self.source = remaining_input;
                return Some(Ok(item));
            }
            None
        }
    }
}
