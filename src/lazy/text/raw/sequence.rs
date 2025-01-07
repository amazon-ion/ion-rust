#![allow(non_camel_case_types)]
#![deny(dead_code)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use winnow::combinator::{alt, opt, peek, terminated};
use winnow::Parser;

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, LazyRawContainer, LazyRawSequence, LazyRawValue, LazyRawValueExpr, RawValueExpr,
};
use crate::lazy::encoding::TextEncoding;
use crate::lazy::text::buffer::{whitespace_and_then, TextBuffer};
use crate::lazy::text::matched::MatchedValue;
use crate::lazy::text::parse_result::AddContext;
use crate::lazy::text::raw::v1_1::reader::RawTextSequenceCacheIterator;
use crate::lazy::text::value::{LazyRawTextValue, RawTextAnnotationsIterator};
use crate::{IonResult, IonType};
// ===== Lists =====

#[derive(Copy, Clone)]
pub struct RawTextList<'data, E: TextEncoding<'data>> {
    pub(crate) value: LazyRawTextValue<'data, E>,
}

impl<'data, E: TextEncoding<'data>> RawTextList<'data, E> {
    pub fn ion_type(&self) -> IonType {
        IonType::List
    }

    pub fn iter(&self) -> RawTextSequenceCacheIterator<'data, E> {
        let MatchedValue::List(child_exprs) = self.value.encoded_value.matched() else {
            unreachable!("list contained a matched value of the wrong type")
        };
        RawTextSequenceCacheIterator::new(child_exprs)
    }
}

impl<'data, E: TextEncoding<'data>> LazyContainerPrivate<'data, E> for RawTextList<'data, E> {
    fn from_value(value: LazyRawTextValue<'data, E>) -> Self {
        RawTextList { value }
    }
}

impl<'data, E: TextEncoding<'data>> LazyRawContainer<'data, E> for RawTextList<'data, E> {
    fn as_value(&self) -> <E as Decoder>::Value<'data> {
        self.value
    }
}

impl<'data, E: TextEncoding<'data>> LazyRawSequence<'data, E> for RawTextList<'data, E> {
    type Iterator = RawTextSequenceCacheIterator<'data, E>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::List
    }

    fn iter(&self) -> Self::Iterator {
        Self::iter(self)
    }
}

impl<'data, E: TextEncoding<'data>> IntoIterator for &RawTextList<'data, E> {
    type Item = IonResult<LazyRawValueExpr<'data, E>>;
    type IntoIter = RawTextSequenceCacheIterator<'data, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'data, E: TextEncoding<'data>> Debug for RawTextList<'data, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for value in self {
            write!(f, "{:?}, ", value?.expect_value()?.read()?)?;
        }
        write!(f, "]").unwrap();

        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct RawTextListIterator<'data, E: TextEncoding<'data>> {
    input: TextBuffer<'data>,
    has_returned_error: bool,
    spooky: PhantomData<E>,
}

impl<'data, E: TextEncoding<'data>> RawTextListIterator<'data, E> {
    pub(crate) fn new(input: TextBuffer<'data>) -> RawTextListIterator<'data, E> {
        RawTextListIterator {
            input,
            has_returned_error: false,
            spooky: PhantomData,
        }
    }
}

impl<'data, E: TextEncoding<'data>> Iterator for RawTextListIterator<'data, E> {
    type Item = IonResult<LazyRawValueExpr<'data, E>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        let result = whitespace_and_then(alt((
            "]".value(None),
            terminated(
                E::value_expr_matcher(),
                whitespace_and_then(alt((",", peek("]")))),
            )
            .map(Some),
        )))
        .parse_next(&mut self.input);

        match result {
            Ok(Some(value_expr)) => Some(Ok(value_expr)),
            Ok(None) => {
                // Don't update `remaining` so subsequent calls will continue to return None
                None
            }
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next list value", self.input)
                    .transpose()
            }
        }
    }
}

// ===== S-Expressions =====

#[derive(Copy, Clone)]
pub struct RawTextSExp<'top, E: TextEncoding<'top>> {
    pub(crate) value: LazyRawTextValue<'top, E>,
}

impl<'data, E: TextEncoding<'data>> RawTextSExp<'data, E> {
    pub fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    pub fn iter(&self) -> RawTextSequenceCacheIterator<'data, E> {
        let MatchedValue::SExp(child_exprs) = self.value.encoded_value.matched() else {
            unreachable!("sexp contained a matched value of the wrong type")
        };
        RawTextSequenceCacheIterator::new(child_exprs)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct RawTextSExpIterator<'top, E: TextEncoding<'top>> {
    input: TextBuffer<'top>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
    spooky: PhantomData<E>,
}

impl<'top, E: TextEncoding<'top>> RawTextSExpIterator<'top, E> {
    pub(crate) fn new(input: TextBuffer<'top>) -> RawTextSExpIterator<'top, E> {
        RawTextSExpIterator {
            input,
            has_returned_error: false,
            spooky: PhantomData,
        }
    }
}

impl<'data, E: TextEncoding<'data>> Iterator for RawTextSExpIterator<'data, E> {
    type Item = IonResult<LazyRawValueExpr<'data, E>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        // Copy the original input so we can include any matched annotations.
        let input = self.input;
        let result = whitespace_and_then(alt((
            // We only peek at the end so future calls to `next()` will continue to yield `None`.
            peek(")").value(None),
            // An annotated value or (in Ion 1.1) an e-expression
            E::value_expr_matcher().map(Some),
            // A potentially annotated operator literal
            (
                opt(TextBuffer::match_annotations),
                whitespace_and_then(TextBuffer::match_operator),
            )
                .map(|(maybe_annotations, value)| input.apply_annotations(maybe_annotations, value))
                .map(RawValueExpr::ValueLiteral)
                .map(Some),
        )))
        .parse_next(&mut self.input);

        match result {
            Ok(Some(value_expr)) => Some(Ok(value_expr)),
            Ok(None) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next s-expression value", self.input)
                    .transpose()
            }
        }
    }

    // fn next(&mut self) -> Option<Self::Item> {
    //     if self.has_returned_error {
    //         return None;
    //     }
    //     match self.input.match_sexp_item() {
    //         Ok(Some(value)) => Some(Ok(RawValueExpr::ValueLiteral(LazyRawTextValue::<E>::from(
    //             value,
    //         )))),
    //         Ok(None) => None,
    //         Err(e) => {
    //             self.has_returned_error = true;
    //             e.with_context("reading the next sexp value", self.input)
    //                 .transpose()
    //         }
    //     }
    // }
}

impl<'data, E: TextEncoding<'data>> LazyContainerPrivate<'data, E> for RawTextSExp<'data, E> {
    fn from_value(value: LazyRawTextValue<'data, E>) -> Self {
        RawTextSExp { value }
    }
}

impl<'data, E: TextEncoding<'data>> LazyRawContainer<'data, E> for RawTextSExp<'data, E> {
    fn as_value(&self) -> <E as Decoder>::Value<'data> {
        self.value
    }
}

impl<'data, E: TextEncoding<'data>> LazyRawSequence<'data, E> for RawTextSExp<'data, E> {
    type Iterator = RawTextSequenceCacheIterator<'data, E>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    fn iter(&self) -> Self::Iterator {
        RawTextSExp::<'data, E>::iter(self)
    }
}

impl<'data, E: TextEncoding<'data>> IntoIterator for &RawTextSExp<'data, E> {
    type Item = IonResult<LazyRawValueExpr<'data, E>>;
    type IntoIter = RawTextSequenceCacheIterator<'data, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top, E: TextEncoding<'top>> Debug for RawTextSExp<'top, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for value in self {
            write!(f, "{:?} ", value?.expect_value()?.read()?)?;
        }
        write!(f, ")").unwrap();

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
    use crate::IonResult;

    fn expect_sequence_range(ion_data: &str, expected: Range<usize>) -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let reader = &mut LazyRawTextReader_1_0::new(context, ion_data.as_bytes(), true);
        let value = reader.next()?.expect_value()?;
        let actual_range = value.data_range();
        assert_eq!(
            actual_range, expected,
            "Sequence range ({:?}) did not match expected range ({:?})",
            actual_range, expected
        );
        Ok(())
    }

    #[test]
    fn list_range() -> IonResult<()> {
        // For each pair below, we'll confirm that the top-level list is found to
        // occupy the specified input span.
        let tests = &[
            // (Ion input, expected range of the sequence)
            ("[]", 0..2),
            ("  []  ", 2..4),
            ("[1, 2]", 0..6),
            ("[1, /* comment ]]] */ 2]", 0..24),
            // Nested
            ("[1, 2, [3, 4, 5], 6]", 0..20),
            // Doubly nested
            ("[1, 2, [3, [a, b, c], 5], 6]", 0..28),
        ];
        for test in tests {
            println!("input: {}", test.0);
            expect_sequence_range(test.0, test.1.clone())?;
        }
        Ok(())
    }
}
