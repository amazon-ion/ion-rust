use crate::lazy::decoder::{Decoder, LazyRawSequence};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, LazyExpandedValue,
};
use crate::{IonResult, IonType};

/// The data source for a [`LazyExpandedList`].
//
// The `Template` variant this enum used to have was only reachable from macro expansion, which
// Ion 1.0 does not have.
#[derive(Clone, Copy)]
pub enum ExpandedListSource<'top, D: Decoder> {
    /// The list was a value literal in the input stream.
    ValueLiteral(D::List<'top>),
}

/// A list that came from a value literal in the input stream.
#[derive(Clone, Copy)]
pub struct LazyExpandedList<'top, D: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) source: ExpandedListSource<'top, D>,
}

impl<'top, D: Decoder> LazyExpandedList<'top, D> {
    pub fn from_literal(
        context: EncodingContextRef<'top>,
        list: D::List<'top>,
    ) -> LazyExpandedList<'top, D> {
        let source = ExpandedListSource::ValueLiteral(list);
        Self { source, context }
    }

    pub fn source(&self) -> ExpandedListSource<'top, D> {
        self.source
    }

    pub fn ion_type(&self) -> IonType {
        IonType::List
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        let ExpandedListSource::ValueLiteral(value) = &self.source;
        ExpandedAnnotationsIterator {
            source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
        }
    }

    pub fn iter(&self) -> ExpandedListIterator<'top, D> {
        let ExpandedListSource::ValueLiteral(list) = &self.source;
        ExpandedListIterator {
            context: self.context,
            source: ExpandedListIteratorSource::ValueLiteral(list.iter()),
        }
    }
}

/// The source of child values iterated over by an [`ExpandedListIterator`].
#[derive(Debug)]
pub enum ExpandedListIteratorSource<'top, D: Decoder> {
    ValueLiteral(<D::List<'top> as LazyRawSequence<'top, D>>::Iterator),
}

/// Iterates over the child values of a [`LazyExpandedList`].
#[derive(Debug)]
pub struct ExpandedListIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    source: ExpandedListIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for ExpandedListIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ExpandedListIteratorSource::ValueLiteral(iter) = &mut self.source;
        next_sequence_value(self.context, iter)
    }
}

/// The data source for a [`LazyExpandedSExp`].
//
// The `Template` variant this enum used to have was only reachable from macro expansion, which
// Ion 1.0 does not have.
#[derive(Clone, Copy)]
pub enum ExpandedSExpSource<'top, D: Decoder> {
    /// The SExp was a value literal in the input stream.
    ValueLiteral(D::SExp<'top>),
}

/// An s-expression that came from a value literal in the input stream.
#[derive(Clone, Copy)]
pub struct LazyExpandedSExp<'top, D: Decoder> {
    pub(crate) source: ExpandedSExpSource<'top, D>,
    pub(crate) context: EncodingContextRef<'top>,
}

impl<'top, D: Decoder> LazyExpandedSExp<'top, D> {
    pub fn source(&self) -> ExpandedSExpSource<'top, D> {
        self.source
    }

    pub fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        let ExpandedSExpSource::ValueLiteral(value) = &self.source;
        ExpandedAnnotationsIterator {
            source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
        }
    }

    pub fn iter(&self) -> ExpandedSExpIterator<'top, D> {
        let ExpandedSExpSource::ValueLiteral(sexp) = &self.source;
        ExpandedSExpIterator {
            context: self.context,
            source: ExpandedSExpIteratorSource::ValueLiteral(sexp.iter()),
        }
    }

    pub fn from_literal(
        context: EncodingContextRef<'top>,
        sexp: D::SExp<'top>,
    ) -> LazyExpandedSExp<'top, D> {
        let source = ExpandedSExpSource::ValueLiteral(sexp);
        Self { source, context }
    }
}

/// The source of child values iterated over by an [`ExpandedSExpIterator`].
#[derive(Debug)]
pub enum ExpandedSExpIteratorSource<'top, D: Decoder> {
    /// The SExp was a literal in the data stream
    ValueLiteral(<D::SExp<'top> as LazyRawSequence<'top, D>>::Iterator),
}

/// Iterates over the child values of a [`LazyExpandedSExp`].
#[derive(Debug)]
pub struct ExpandedSExpIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    source: ExpandedSExpIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for ExpandedSExpIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ExpandedSExpIteratorSource::ValueLiteral(iter) = &mut self.source;
        next_sequence_value(self.context, iter)
    }
}

/// For both lists and s-expressions, yields the next child value from the input stream.
fn next_sequence_value<'top, D: Decoder>(
    context: EncodingContextRef<'top>,
    iter: &mut impl Iterator<Item = IonResult<D::Value<'top>>>,
) -> Option<IonResult<LazyExpandedValue<'top, D>>> {
    let raw_value = match iter.next()? {
        Ok(raw_value) => raw_value,
        Err(e) => return Some(Err(e)),
    };
    Some(Ok(LazyExpandedValue::from_literal(context, raw_value)))
}
