use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::{Decoder, LazyRawSequence, LazyRawValueExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, RawEExpression, ValueExpr};
use crate::lazy::expanded::template::{TemplateElement, TemplateSequenceIterator};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, LazyExpandedValue,
};
use crate::{try_or_some_err, IonResult, IonType};

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
/// The `Environment` would contain the expressions `1`, `2` and `(:values 3)`, corresponding to parameters
/// `x`, `y`, and `z` respectively.
#[derive(Copy, Clone, Debug)]
pub struct Environment<'top, D: Decoder> {
    expressions: &'top [ValueExpr<'top, D>],
}

impl<'top, D: Decoder> Environment<'top, D> {
    pub(crate) fn new(args: &'top [ValueExpr<'top, D>]) -> Self {
        Environment { expressions: args }
    }

    /// Returns the expression for the corresponding signature index -- the variable's offset within
    /// the template's signature.
    ///
    /// Panics if the requested index is out of bounds, as the rules of the template compiler
    /// should make that impossible.
    #[inline]
    pub fn require_expr(&self, signature_index: usize) -> ValueExpr<'top, D> {
        if let Some(expr) = self.expressions().get(signature_index).copied() {
            return expr;
        }
        unreachable!("found a macro signature index reference that was out of bounds")
    }

    /// Returns an empty environment without performing any allocations. This is used for evaluating
    /// e-expressions, which never have named parameters.
    pub const fn empty() -> Environment<'top, D> {
        Environment { expressions: &[] }
    }
    pub fn expressions(&self) -> &'top [ValueExpr<'top, D>] {
        self.expressions
    }
    pub fn for_eexp(context: EncodingContextRef<'top>, eexp: D::EExp<'top>) -> IonResult<Self> {
        use bumpalo::collections::Vec as BumpVec;
        let allocator = context.allocator();
        let raw_args = eexp.raw_arguments();
        let capacity_hint = raw_args.size_hint().0;
        let mut env_exprs = BumpVec::with_capacity_in(capacity_hint, allocator);
        // Populate the environment by parsing the arguments from input
        for expr in raw_args {
            env_exprs.push(expr?.resolve(context)?);
        }

        Ok(Environment::new(env_exprs.into_bump_slice()))
    }
}

impl<'top, D: Decoder> Default for Environment<'top, D> {
    fn default() -> Self {
        Self::empty()
    }
}

/// The data source for a [`LazyExpandedList`].
#[derive(Clone, Copy)]
pub enum ExpandedListSource<'top, D: Decoder> {
    /// The list was a value literal in the input stream.
    ValueLiteral(D::List<'top>),
    /// The list was part of a template definition.
    Template(Environment<'top, D>, TemplateElement<'top>),
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
        element: TemplateElement<'top>,
    ) -> LazyExpandedList<'top, D> {
        let source = ExpandedListSource::Template(environment, element);
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
            ExpandedListSource::Template(_environment, element) => {
                let annotations = element.annotations();
                ExpandedAnnotationsIterator {
                    source: ExpandedAnnotationsSource::Template(SymbolsIterator::new(annotations)),
                }
            }
        }
    }

    pub fn iter(&self) -> ExpandedListIterator<'top, D> {
        let source = match &self.source {
            ExpandedListSource::ValueLiteral(list) => {
                ExpandedListIteratorSource::ValueLiteral(MacroEvaluator::new(), list.iter())
            }
            ExpandedListSource::Template(environment, element) => {
                let nested_expressions = element.nested_expressions();
                let evaluator = MacroEvaluator::new_with_environment(*environment);
                ExpandedListIteratorSource::Template(TemplateSequenceIterator::new(
                    self.context,
                    evaluator,
                    element.template(),
                    nested_expressions,
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
    Template(Environment<'top, D>, TemplateElement<'top>),
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
            ExpandedSExpSource::Template(_environment, element) => {
                let annotations = element.annotations();
                ExpandedAnnotationsIterator {
                    source: ExpandedAnnotationsSource::Template(SymbolsIterator::new(annotations)),
                }
            }
        }
    }

    pub fn iter(&self) -> ExpandedSExpIterator<'top, D> {
        let source = match &self.source {
            ExpandedSExpSource::ValueLiteral(sexp) => {
                ExpandedSExpIteratorSource::ValueLiteral(MacroEvaluator::new(), sexp.iter())
            }
            ExpandedSExpSource::Template(environment, element) => {
                let nested_expressions = element.nested_expressions();
                let evaluator = MacroEvaluator::new_with_environment(*environment);
                ExpandedSExpIteratorSource::Template(TemplateSequenceIterator::new(
                    self.context,
                    evaluator,
                    element.template(),
                    nested_expressions,
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
        element: TemplateElement<'top>,
    ) -> LazyExpandedSExp<'top, D> {
        let source = ExpandedSExpSource::Template(environment, element);
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
        if !evaluator.is_empty() {
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
                evaluator.push(try_or_some_err!(resolved_invocation.expand()));
                continue;
            }
            Some(Err(e)) => return Some(Err(e)),
        }
    }
}
