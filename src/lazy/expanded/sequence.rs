use bumpalo::collections::Vec as BumpVec;

use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::{Decoder, LazyRawSequence, LazyRawValueExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, RawEExpression, ValueExpr};
use crate::lazy::expanded::template::{
    AnnotationsRange, ExprRange, TemplateMacroRef, TemplateSequenceIterator,
};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, LazyExpandedValue,
};
use crate::result::IonFailure;
use crate::{IonError, IonResult, IonType};

/// A sequence of not-yet-evaluated expressions passed as arguments to a macro invocation.
///
/// The number of expressions is required to match the number of parameters in the macro's signature,
/// and the order of the expressions corresponds to the order of the parameters.
///
/// For example, given this macro definition:
/// ```ion_1_1
///     (macro foo (x y z) [x, y, z])
/// ```
/// and this invocation:
/// ```ion_1_1
///     (:foo 1 2 (:values 3))
/// ```
/// The `Environment` would contain the expressions `1`, `2` and `3`, corresponding to parameters
/// `x`, `y`, and `z` respectively.
#[derive(Copy, Clone, Debug)]
pub struct Environment<'top, D: Decoder> {
    expressions: &'top [ValueExpr<'top, D>],
}

impl<'top, D: Decoder> Environment<'top, D> {
    pub(crate) fn new(args: BumpVec<'top, ValueExpr<'top, D>>) -> Self {
        Environment {
            expressions: args.into_bump_slice(),
        }
    }

    /// Returns the expression for the corresponding signature index -- the variable's offset within
    /// the template's signature. If the requested index is out of bounds, returns `Err`.
    pub fn get_expected(&self, signature_index: usize) -> IonResult<ValueExpr<'top, D>> {
        self.expressions()
            .get(signature_index)
            .copied()
            // The TemplateCompiler should detect any invalid variable references prior to evaluation
            .ok_or_else(|| {
                IonError::decoding_error(format!(
                    "reference to variable with signature index {} not valid",
                    signature_index
                ))
            })
    }

    /// Returns an empty environment without performing any allocations. This is used for evaluating
    /// e-expressions, which never have named parameters.
    pub fn empty() -> Environment<'top, D> {
        Environment { expressions: &[] }
    }
    pub fn expressions(&self) -> &'top [ValueExpr<'top, D>] {
        self.expressions
    }
}

/// The data source for a [`LazyExpandedList`].
#[derive(Clone, Copy)]
pub enum ExpandedListSource<'top, D: Decoder> {
    /// The list was a value literal in the input stream.
    ValueLiteral(D::List<'top>),
    /// The list was part of a template definition.
    Template(
        Environment<'top, D>,
        TemplateMacroRef<'top>,
        AnnotationsRange,
        ExprRange,
    ),
    // TODO: Constructed
}

/// A list that may have come from either a value literal in the input stream or from evaluating
/// a template.
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

    pub fn from_template(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        template: TemplateMacroRef<'top>,
        annotations_range: AnnotationsRange,
        step_range: ExprRange,
    ) -> LazyExpandedList<'top, D> {
        let source =
            ExpandedListSource::Template(environment, template, annotations_range, step_range);
        Self { source, context }
    }

    pub fn source(&self) -> ExpandedListSource<'top, D> {
        self.source
    }

    pub fn ion_type(&self) -> IonType {
        IonType::List
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        match &self.source {
            ExpandedListSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedListSource::Template(_environment, template, annotations, _sequence) => {
                let annotations = template
                    .body
                    .annotations_storage()
                    .get(annotations.ops_range())
                    .unwrap();
                ExpandedAnnotationsIterator {
                    source: ExpandedAnnotationsSource::Template(SymbolsIterator::new(annotations)),
                }
            }
        }
    }

    pub fn iter(&self) -> ExpandedListIterator<'top, D> {
        let source = match &self.source {
            ExpandedListSource::ValueLiteral(list) => {
                let evaluator = MacroEvaluator::new(self.context, Environment::empty());
                ExpandedListIteratorSource::ValueLiteral(evaluator, list.iter())
            }
            ExpandedListSource::Template(environment, template, _annotations, steps) => {
                let steps = template.body.expressions().get(steps.ops_range()).unwrap();
                let evaluator = MacroEvaluator::new(self.context, *environment);
                ExpandedListIteratorSource::Template(TemplateSequenceIterator::new(
                    self.context,
                    evaluator,
                    *template,
                    steps,
                ))
            }
        };
        ExpandedListIterator {
            context: self.context,
            source,
        }
    }
}

/// The source of child values iterated over by an [`ExpandedListIterator`].
pub enum ExpandedListIteratorSource<'top, D: Decoder> {
    ValueLiteral(
        // Giving the list iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        MacroEvaluator<'top, D>,
        <D::List<'top> as LazyRawSequence<'top, D>>::Iterator,
    ),
    Template(TemplateSequenceIterator<'top, D>),
    // TODO: Constructed
}

/// Iterates over the child values of a [`LazyExpandedList`].
pub struct ExpandedListIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    source: ExpandedListIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for ExpandedListIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            ExpandedListIteratorSource::ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value(self.context, evaluator, iter)
            }
            ExpandedListIteratorSource::Template(iter) => iter.next(),
        }
    }
}

/// The data source for a [`LazyExpandedSExp`].
#[derive(Clone, Copy)]
pub enum ExpandedSExpSource<'top, D: Decoder> {
    /// The SExp was a value literal in the input stream.
    ValueLiteral(D::SExp<'top>),
    /// The SExp was part of a template definition.
    Template(
        Environment<'top, D>,
        TemplateMacroRef<'top>,
        AnnotationsRange,
        ExprRange,
    ),
}

/// An s-expression that may have come from either a value literal in the input stream or from
/// evaluating a template.
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
        match &self.source {
            ExpandedSExpSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedSExpSource::Template(_environment, template, annotations, _sequence) => {
                let annotations = template
                    .body
                    .annotations_storage()
                    .get(annotations.ops_range())
                    .unwrap();
                ExpandedAnnotationsIterator {
                    source: ExpandedAnnotationsSource::Template(SymbolsIterator::new(annotations)),
                }
            }
        }
    }

    pub fn iter(&self) -> ExpandedSExpIterator<'top, D> {
        let source = match &self.source {
            ExpandedSExpSource::ValueLiteral(sexp) => {
                let evaluator = MacroEvaluator::new(self.context, Environment::empty());
                ExpandedSExpIteratorSource::ValueLiteral(evaluator, sexp.iter())
            }
            ExpandedSExpSource::Template(environment, template, _annotations, steps) => {
                let steps = template.body.expressions().get(steps.ops_range()).unwrap();
                let evaluator = MacroEvaluator::new(self.context, *environment);
                ExpandedSExpIteratorSource::Template(TemplateSequenceIterator::new(
                    self.context,
                    evaluator,
                    *template,
                    steps,
                ))
            }
        };
        ExpandedSExpIterator {
            context: self.context,
            source,
        }
    }

    pub fn from_literal(
        context: EncodingContextRef<'top>,
        sexp: D::SExp<'top>,
    ) -> LazyExpandedSExp<'top, D> {
        let source = ExpandedSExpSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        template: TemplateMacroRef<'top>,
        annotations: AnnotationsRange,
        expressions: ExprRange,
    ) -> LazyExpandedSExp<'top, D> {
        let source = ExpandedSExpSource::Template(environment, template, annotations, expressions);
        Self { source, context }
    }
}

/// The source of child values iterated over by an [`ExpandedSExpIterator`].
pub enum ExpandedSExpIteratorSource<'top, D: Decoder> {
    ValueLiteral(
        // Giving the sexp iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        MacroEvaluator<'top, D>,
        <D::SExp<'top> as LazyRawSequence<'top, D>>::Iterator,
    ),
    Template(TemplateSequenceIterator<'top, D>),
    // TODO: Constructed
}

/// Iterates over the child values of a [`LazyExpandedSExp`].
pub struct ExpandedSExpIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    source: ExpandedSExpIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for ExpandedSExpIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            ExpandedSExpIteratorSource::ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value(self.context, evaluator, iter)
            }
            ExpandedSExpIteratorSource::Template(iter) => iter.next(),
        }
    }
}

/// For both lists and s-expressions, yields the next sequence value by either continuing a macro
/// evaluation already in progress or reading the next item from the input stream.
fn expand_next_sequence_value<'top, D: Decoder>(
    context: EncodingContextRef<'top>,
    evaluator: &mut MacroEvaluator<'top, D>,
    iter: &mut impl Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>,
) -> Option<IonResult<LazyExpandedValue<'top, D>>> {
    loop {
        // If the evaluator's stack is not empty, it's still expanding a macro.
        if evaluator.macro_stack_depth() > 0 {
            let value = evaluator.next().transpose();
            if value.is_some() {
                // The `Some` may contain a value or an error; either way, that's the next return value.
                return value;
            }
            // It's possible for a macro to produce zero values. If that happens, we continue on to
            // pull another expression from the list iterator.
        }

        match iter.next() {
            None => return None,
            Some(Ok(RawValueExpr::ValueLiteral(value))) => {
                return Some(Ok(LazyExpandedValue::from_literal(context, value)))
            }
            Some(Ok(RawValueExpr::EExp(invocation))) => {
                let resolved_invocation = match invocation.resolve(context) {
                    Ok(resolved) => resolved,
                    Err(e) => return Some(Err(e)),
                };
                let begin_expansion_result = evaluator.push(resolved_invocation);
                if let Err(e) = begin_expansion_result {
                    return Some(Err(e));
                }
                continue;
            }
            Some(Err(e)) => return Some(Err(e)),
        }
    }
}
