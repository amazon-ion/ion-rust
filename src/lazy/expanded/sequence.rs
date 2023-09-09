use crate::lazy::decoder::{LazyDecoder, LazyRawSequence, LazyRawValueExpr};
use crate::lazy::expanded::macro_evaluator::TransientEExpEvaluator;
use crate::lazy::expanded::template::TemplateSequenceIterator;
use crate::lazy::expanded::{
    EncodingContext, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueSource,
    LazyExpandedValue,
};
use crate::{Annotations, IonResult, IonType, Sequence};

#[derive(Clone)]
pub enum ExpandedListSource<'top, 'data, D: LazyDecoder<'data>> {
    ValueLiteral(D::List),
    Template(&'top Annotations, &'top Sequence),
    // TODO: Constructed
}

#[derive(Clone)]
pub struct LazyExpandedList<'top, 'data, D: LazyDecoder<'data>> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) source: ExpandedListSource<'top, 'data, D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> LazyExpandedList<'top, 'data, D> {
    pub fn from_literal(
        context: EncodingContext<'top>,
        list: D::List,
    ) -> LazyExpandedList<'top, 'data, D> {
        let source = ExpandedListSource::ValueLiteral(list);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContext<'top>,
        annotations: &'top Annotations,
        sequence: &'top Sequence,
    ) -> LazyExpandedList<'top, 'data, D> {
        let source = ExpandedListSource::Template(annotations, sequence);
        Self { source, context }
    }

    pub fn ion_type(&self) -> IonType {
        IonType::List
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, 'data, D> {
        match self.source {
            ExpandedListSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedListSource::Template(annotations, _sequence) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::Template(annotations.iter()),
            },
        }
    }

    pub fn iter(&self) -> ExpandedListIterator<'top, 'data, D> {
        let source = match &self.source {
            ExpandedListSource::ValueLiteral(list) => {
                let evaluator = TransientEExpEvaluator::new_transient(self.context);
                ExpandedListIteratorSource::ValueLiteral(evaluator, list.iter())
            }
            ExpandedListSource::Template(_annotations, sequence) => {
                ExpandedListIteratorSource::Template(TemplateSequenceIterator::new(
                    self.context,
                    sequence,
                ))
            }
        };
        ExpandedListIterator {
            context: self.context,
            source,
        }
    }
}

pub enum ExpandedListIteratorSource<'top, 'data: 'top, D: LazyDecoder<'data>> {
    ValueLiteral(
        // Giving the list iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        TransientEExpEvaluator<'top, 'data, D>,
        <D::List as LazyRawSequence<'data, D>>::Iterator,
    ),
    Template(TemplateSequenceIterator<'top>),
    // TODO: Constructed
}

pub struct ExpandedListIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    source: ExpandedListIteratorSource<'top, 'data, D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for ExpandedListIterator<'top, 'data, D> {
    type Item = IonResult<LazyExpandedValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            ExpandedListIteratorSource::ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value(self.context, evaluator, iter)
            }
            ExpandedListIteratorSource::Template(iter) => iter.next().map(|element| {
                Ok(LazyExpandedValue {
                    source: ExpandedValueSource::Template(element),
                    context: self.context,
                })
            }),
        }
    }
}

#[derive(Clone)]
pub enum ExpandedSExpSource<'top, 'data, D: LazyDecoder<'data>> {
    ValueLiteral(D::SExp),
    Template(&'top Annotations, &'top Sequence),
}

#[derive(Clone)]
pub struct LazyExpandedSExp<'top, 'data, D: LazyDecoder<'data>> {
    source: ExpandedSExpSource<'top, 'data, D>,
    context: EncodingContext<'top>,
}

impl<'top, 'data, D: LazyDecoder<'data>> LazyExpandedSExp<'top, 'data, D> {
    pub fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, 'data, D> {
        match self.source {
            ExpandedSExpSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedSExpSource::Template(annotations, _sequence) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::Template(annotations.iter()),
            },
        }
    }

    pub fn iter(&self) -> ExpandedSExpIterator<'top, 'data, D> {
        let source = match &self.source {
            ExpandedSExpSource::ValueLiteral(sexp) => {
                let evaluator = TransientEExpEvaluator::new_transient(self.context);
                ExpandedSExpIteratorSource::ValueLiteral(evaluator, sexp.iter())
            }
            ExpandedSExpSource::Template(_annotations, sequence) => {
                ExpandedSExpIteratorSource::Template(TemplateSequenceIterator::new(
                    self.context,
                    sequence,
                ))
            }
        };
        ExpandedSExpIterator {
            context: self.context,
            source,
        }
    }

    pub fn from_literal(
        context: EncodingContext<'top>,
        sexp: D::SExp,
    ) -> LazyExpandedSExp<'top, 'data, D> {
        let source = ExpandedSExpSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContext<'top>,
        annotations: &'top Annotations,
        sequence: &'top Sequence,
    ) -> LazyExpandedSExp<'top, 'data, D> {
        let source = ExpandedSExpSource::Template(annotations, sequence);
        Self { source, context }
    }
}

pub enum ExpandedSExpIteratorSource<'top, 'data: 'top, D: LazyDecoder<'data>> {
    ValueLiteral(
        // Giving the sexp iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        TransientEExpEvaluator<'top, 'data, D>,
        <D::SExp as LazyRawSequence<'data, D>>::Iterator,
    ),
    Template(TemplateSequenceIterator<'top>),
    // TODO: Constructed
}

pub struct ExpandedSExpIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    source: ExpandedSExpIteratorSource<'top, 'data, D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for ExpandedSExpIterator<'top, 'data, D> {
    type Item = IonResult<LazyExpandedValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            ExpandedSExpIteratorSource::ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value(self.context, evaluator, iter)
            }
            ExpandedSExpIteratorSource::Template(iter) => iter.next().map(|element| {
                Ok(LazyExpandedValue {
                    source: ExpandedValueSource::Template(element),
                    context: self.context,
                })
            }),
        }
    }
}

/// For both lists and s-expressions, yields the next sequence value by either continuing a macro
/// evaluation already in progress or reading the next item from the input stream.
fn expand_next_sequence_value<'top, 'data, D: LazyDecoder<'data>>(
    context: EncodingContext<'top>,
    evaluator: &mut TransientEExpEvaluator<'top, 'data, D>,
    iter: &mut impl Iterator<Item = IonResult<LazyRawValueExpr<'data, D>>>,
) -> Option<IonResult<LazyExpandedValue<'top, 'data, D>>> {
    loop {
        // If the evaluator's stack is not empty, it's still expanding a macro.
        if evaluator.stack_depth() > 0 {
            let value = evaluator.next(context, 0).transpose();
            if value.is_some() {
                // The `Some` may contain a value or an error; either way, that's the next return value.
                return value;
            }
            // It's possible for a macro to produce zero values. If that happens, we continue on to
            // pull another expression from the list iterator.
        }

        match iter.next() {
            None => return None,
            Some(Ok(LazyRawValueExpr::ValueLiteral(value))) => {
                return Some(Ok(LazyExpandedValue {
                    source: ExpandedValueSource::ValueLiteral(value),
                    context,
                }))
            }
            Some(Ok(LazyRawValueExpr::MacroInvocation(invocation))) => {
                let begin_expansion_result = evaluator.push(context, invocation);
                if let Err(e) = begin_expansion_result {
                    return Some(Err(e));
                }
                continue;
            }
            Some(Err(e)) => return Some(Err(e)),
        }
    }
}
