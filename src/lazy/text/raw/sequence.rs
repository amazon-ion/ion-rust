use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{LazyDecoder, LazyRawSequence, LazyRawValue};
use crate::lazy::encoding::TextEncoding;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::AddContext;
use crate::lazy::text::parse_result::ToIteratorOutput;
use crate::lazy::text::value::LazyRawTextValue;
use crate::{IonResult, IonType};
use std::fmt;
use std::fmt::{Debug, Formatter};

#[derive(Copy, Clone)]
pub struct LazyRawTextSequence<'data> {
    pub(crate) value: LazyRawTextValue<'data>,
}

impl<'data> LazyRawTextSequence<'data> {
    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn iter(&self) -> RawTextSequenceIterator<'data> {
        // Make an iterator over the input bytes that follow the initial `[`
        RawTextSequenceIterator::new(self.value.input.slice_to_end(1))
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding> for LazyRawTextSequence<'data> {
    fn from_value(value: LazyRawTextValue<'data>) -> Self {
        LazyRawTextSequence { value }
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding> for LazyRawTextSequence<'data> {
    type Iterator = RawTextSequenceIterator<'data>;

    fn annotations(&self) -> <TextEncoding as LazyDecoder<'data>>::AnnotationsIterator {
        todo!("lazy sequence annotations")
    }

    fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        LazyRawTextSequence::iter(self)
    }

    fn as_value(&self) -> &LazyRawTextValue<'data> {
        &self.value
    }
}

impl<'a, 'data> IntoIterator for &'a LazyRawTextSequence<'data> {
    type Item = IonResult<LazyRawTextValue<'data>>;
    type IntoIter = RawTextSequenceIterator<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> Debug for LazyRawTextSequence<'a> {
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

pub struct RawTextSequenceIterator<'data> {
    input: TextBufferView<'data>,
}

impl<'data> RawTextSequenceIterator<'data> {
    pub(crate) fn new(input: TextBufferView<'data>) -> RawTextSequenceIterator<'data> {
        RawTextSequenceIterator { input }
    }
}

impl<'data> Iterator for RawTextSequenceIterator<'data> {
    type Item = IonResult<LazyRawTextValue<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.input.match_list_value() {
            Ok((remaining, Some(value))) => {
                self.input = remaining;
                Some(Ok(value))
            }
            Ok((_remaining, None)) => None,
            Err(e) => e
                .with_context("reading the next list value", self.input)
                .transpose(),
        }
    }
}
