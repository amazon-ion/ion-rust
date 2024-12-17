use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::{Decoder, LazyRawSequence, LazyRawValueExpr};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, RawEExpression, ValueExpr};
use crate::lazy::expanded::template::{TemplateElement, TemplateSequenceIterator};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, LazyExpandedValue,
};
use crate::{try_or_some_err, IonResult, IonType};
use std::fmt::Debug;

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
#[derive(Copy, Clone)]
pub struct Environment<'top, D: Decoder> {
    expressions: &'top [ValueExpr<'top, D>],
}

impl<D: Decoder> Debug for Environment<'_, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Environment::[")?;
        for expr in self.expressions {
            writeln!(f, "{:?}", expr)?;
        }
        write!(f, "]")
    }
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

    /// Constructs a new environment with the expressions found in the provided EExp.
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

impl<D: Decoder> Default for Environment<'_, D> {
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

    #[cfg(feature = "experimental-tooling-apis")]
    pub fn iter_value_expr(&self) -> ListValueExprIterator<'top, D> {
        let ExpandedListIterator { context, source } = self.iter();
        ListValueExprIterator { context, source }
    }
}

/// The source of child values iterated over by an [`ExpandedListIterator`].
#[derive(Debug)]
pub enum ExpandedListIteratorSource<'top, D: Decoder> {
    ValueLiteral(
        // Giving the list iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        MacroEvaluator<'top, D>,
        <D::List<'top> as LazyRawSequence<'top, D>>::Iterator,
    ),
    Template(TemplateSequenceIterator<'top, D>),
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
        match &mut self.source {
            ExpandedListIteratorSource::ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value(self.context, evaluator, iter)
            }
            ExpandedListIteratorSource::Template(iter) => iter.next(),
        }
    }
}

/// Like an [`ExpandedListIterator`], but will yield macro invocations before also yielding
/// that macro's expansion.
#[derive(Debug)]
pub struct ListValueExprIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    source: ExpandedListIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for ListValueExprIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        use ExpandedListIteratorSource::*;
        match &mut self.source {
            ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value_expr(self.context, evaluator, iter)
            }
            Template(iter) => iter.next_value_expr(),
        }
    }
}

/// Like an [`ExpandedSExpIterator`], but will yield macro invocations before also yielding
/// that macro's expansion.
#[derive(Debug)]
pub struct SExpValueExprIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    source: ExpandedSExpIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for SExpValueExprIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        use ExpandedSExpIteratorSource::*;
        match &mut self.source {
            ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value_expr(self.context, evaluator, iter)
            }
            Template(iter) => iter.next_value_expr(),
        }
    }
}

/// The data source for a [`LazyExpandedSExp`].
#[derive(Clone, Copy)]
pub enum ExpandedSExpSource<'top, D: Decoder> {
    /// The SExp was a value literal in the input stream.
    ValueLiteral(D::SExp<'top>),
    /// The SExp was part of a template definition.
    /// Because the TDL treats s-expressions as literals, this variant only applies when the
    /// s-expression appeared within a `literal` operation.
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

    #[cfg(feature = "experimental-tooling-apis")]
    pub fn iter_value_expr(&self) -> SExpValueExprIterator<'top, D> {
        let ExpandedSExpIterator { context, source } = self.iter();
        SExpValueExprIterator { context, source }
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
#[derive(Debug)]
pub enum ExpandedSExpIteratorSource<'top, D: Decoder> {
    /// The SExp was a literal in the data stream
    ValueLiteral(
        // Giving the sexp iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        MacroEvaluator<'top, D>,
        <D::SExp<'top> as LazyRawSequence<'top, D>>::Iterator,
    ),
    /// The SExp was in the body of a macro
    Template(TemplateSequenceIterator<'top, D>),
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
        use ExpandedSExpIteratorSource::*;
        match &mut self.source {
            ValueLiteral(evaluator, iter) => {
                expand_next_sequence_value(self.context, evaluator, iter)
            }
            Template(iter) => iter.next(),
        }
    }
}

fn expand_next_sequence_value_expr<'top, D: Decoder>(
    context: EncodingContextRef<'top>,
    evaluator: &mut MacroEvaluator<'top, D>,
    iter: &mut impl Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>,
) -> Option<IonResult<ValueExpr<'top, D>>> {
    if let Some(value) = try_or_some_err!(evaluator.next()) {
        return Some(Ok(ValueExpr::ValueLiteral(value)));
    }

    // At this point, the evaluator is empty.

    let value_expr = try_or_some_err!(iter.next()?.and_then(|raw_expr| raw_expr.resolve(context)));

    if let ValueExpr::MacroInvocation(invocation) = value_expr {
        evaluator.push(try_or_some_err!(invocation.expand()));
    }

    Some(Ok(value_expr))
}

/// For both lists and s-expressions, yields the next sequence value by either continuing a macro
/// evaluation already in progress or reading the next item from the input stream.
fn expand_next_sequence_value<'top, D: Decoder>(
    context: EncodingContextRef<'top>,
    evaluator: &mut MacroEvaluator<'top, D>,
    iter: &mut impl Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>,
) -> Option<IonResult<LazyExpandedValue<'top, D>>> {
    let mut resolving_iter =
        iter.map(|result| result.and_then(|raw_expr| raw_expr.resolve(context)));
    expand_next_sequence_value_from_resolved(evaluator, &mut resolving_iter)
}

fn expand_next_sequence_value_from_resolved<'top, D: Decoder>(
    evaluator: &mut MacroEvaluator<'top, D>,
    iter: &mut impl Iterator<Item = IonResult<ValueExpr<'top, D>>>,
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
            Some(Ok(ValueExpr::ValueLiteral(value))) => return Some(Ok(value)),
            Some(Ok(ValueExpr::MacroInvocation(invocation))) => {
                evaluator.push(try_or_some_err!(invocation.expand()));
                continue;
            }
            Some(Err(e)) => return Some(Err(e)),
        }
    }
}

/// Represents a sequence (list or sexp) whose contents are being traversed.
/// This is used in `flatten` to store an iterator for each of its
/// sequence arguments in turn.
#[derive(Debug)]
pub enum ExpandedSequenceIterator<'top, D: Decoder> {
    List(ExpandedListIterator<'top, D>),
    SExp(ExpandedSExpIterator<'top, D>),
}

impl<'top, D: Decoder> Iterator for ExpandedSequenceIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        use ExpandedSequenceIterator::*;
        match self {
            List(l) => l.next(),
            SExp(s) => s.next(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{v1_1, ExpandedValueRef, Int, MacroExprKind, Reader};

    fn expect_int<'top, D: Decoder>(
        value_exprs: &mut impl Iterator<Item = IonResult<ValueExpr<'top, D>>>,
        expected_value: impl Into<Int>,
    ) -> IonResult<()> {
        assert!(matches!(
            value_exprs.next().unwrap()?,
            ValueExpr::ValueLiteral(v) if v.read()? == ExpandedValueRef::Int(expected_value.into())
        ));
        Ok(())
    }

    fn expect_eexp<'top, D: Decoder>(
        value_exprs: &mut impl Iterator<Item = IonResult<ValueExpr<'top, D>>>,
        expected_macro_name: &str,
    ) -> IonResult<()> {
        assert!(matches!(
            value_exprs.next().unwrap()?,
            ValueExpr::MacroInvocation(i) if matches!(
                i.kind(),
                MacroExprKind::EExp(e) if e.invoked_macro.name() == Some(expected_macro_name)
            )
        ));
        Ok(())
    }

    #[test]
    fn list_iter_value_expr() -> IonResult<()> {
        let source = r#"
                $ion_1_1
                (:add_macros
                    (macro three_values ()
                        (.values 1 2 3)
                    )
                )
                [0, (:three_values), 4, (:flatten (5 6)), 7]
            "#;
        let mut reader = Reader::new(v1_1::Text, source)?;
        let list = reader.expect_next()?.read()?.expect_list()?;
        let value_exprs = &mut list.expanded_list.iter_value_expr();

        expect_int(value_exprs, 0)?;
        expect_eexp(value_exprs, "three_values")?;
        expect_int(value_exprs, 1)?;
        expect_int(value_exprs, 2)?;
        expect_int(value_exprs, 3)?;
        expect_int(value_exprs, 4)?;
        expect_eexp(value_exprs, "flatten")?;
        expect_int(value_exprs, 5)?;
        expect_int(value_exprs, 6)?;
        expect_int(value_exprs, 7)?;
        assert!(value_exprs.next().is_none());
        Ok(())
    }

    #[test]
    fn sexp_iter_value_expr() -> IonResult<()> {
        let source = r#"
                $ion_1_1
                (:add_macros
                    (macro three_values ()
                        (.values 1 2 3)
                    )
                )
                (0 (:three_values) 4 (:flatten (5 6)) 7)
            "#;
        let mut reader = Reader::new(v1_1::Text, source)?;
        let sexp = reader.expect_next()?.read()?.expect_sexp()?;
        let value_exprs = &mut sexp.expanded_sexp.iter_value_expr();

        expect_int(value_exprs, 0)?;
        expect_eexp(value_exprs, "three_values")?;
        expect_int(value_exprs, 1)?;
        expect_int(value_exprs, 2)?;
        expect_int(value_exprs, 3)?;
        expect_int(value_exprs, 4)?;
        expect_eexp(value_exprs, "flatten")?;
        expect_int(value_exprs, 5)?;
        expect_int(value_exprs, 6)?;
        expect_int(value_exprs, 7)?;
        assert!(value_exprs.next().is_none());
        Ok(())
    }
}
