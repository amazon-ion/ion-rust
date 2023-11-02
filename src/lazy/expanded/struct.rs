use std::ops::ControlFlow;

use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::{
    LazyDecoder, LazyRawFieldExpr, LazyRawStruct, RawFieldExpr, RawValueExpr,
};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, MacroExpr, RawEExpression};
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    AnnotationsRange, ExprRange, TemplateMacroRef, TemplateStructRawFieldsIterator,
};
use crate::lazy::expanded::{
    EncodingContext, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueRef,
    ExpandedValueSource, LazyExpandedValue,
};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::{IonError, IonResult, RawSymbolTokenRef};

#[derive(Debug, Clone)]
pub struct LazyExpandedField<'top, D: LazyDecoder> {
    name: RawSymbolTokenRef<'top>,
    pub(crate) value: LazyExpandedValue<'top, D>,
}

impl<'top, D: LazyDecoder> LazyExpandedField<'top, D> {
    pub fn new(name: RawSymbolTokenRef<'top>, value: LazyExpandedValue<'top, D>) -> Self {
        Self { name, value }
    }

    pub fn name(&self) -> RawSymbolTokenRef<'top> {
        self.name.clone()
    }

    pub fn value(&self) -> &LazyExpandedValue<'top, D> {
        &self.value
    }
}

#[derive(Clone)]
pub enum ExpandedStructSource<'top, D: LazyDecoder> {
    ValueLiteral(D::Struct<'top>),
    Template(
        Environment<'top, D>,
        TemplateMacroRef<'top>,
        AnnotationsRange,
        ExprRange,
    ),
    // TODO: Constructed
}

#[derive(Clone)]
pub struct LazyExpandedStruct<'top, D: LazyDecoder> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) source: ExpandedStructSource<'top, D>,
}

impl<'top, D: LazyDecoder> LazyExpandedStruct<'top, D> {
    pub fn from_literal(
        context: EncodingContext<'top>,
        sexp: D::Struct<'top>,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContext<'top>,
        environment: Environment<'top, D>,
        template: TemplateMacroRef<'top>,
        annotations: AnnotationsRange,
        expressions: ExprRange,
    ) -> LazyExpandedStruct<'top, D> {
        let source =
            ExpandedStructSource::Template(environment, template, annotations, expressions);
        Self { source, context }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        match &self.source {
            ExpandedStructSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedStructSource::Template(_environment, template, annotations, _expressions) => {
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

    pub fn iter(&self) -> ExpandedStructIterator<'top, D> {
        let source = match &self.source {
            ExpandedStructSource::ValueLiteral(raw_struct) => {
                ExpandedStructIteratorSource::ValueLiteral(
                    MacroEvaluator::new(self.context, Environment::empty()),
                    raw_struct.iter(),
                )
            }
            ExpandedStructSource::Template(environment, template, _annotations, expressions) => {
                let evaluator = MacroEvaluator::new(self.context, *environment);
                ExpandedStructIteratorSource::Template(
                    evaluator,
                    TemplateStructRawFieldsIterator::new(
                        self.context,
                        *environment,
                        *template,
                        &template.body.expressions[expressions.ops_range()],
                    ),
                )
            }
        };
        ExpandedStructIterator {
            context: self.context,
            source,
            state: ExpandedStructIteratorState::ReadingFieldFromSource,
        }
    }

    fn environment(&self) -> Environment<'top, D> {
        match &self.source {
            ExpandedStructSource::ValueLiteral(_) => Environment::empty(),
            ExpandedStructSource::Template(environment, _, _, _) => *environment,
        }
    }

    pub fn bump_iter(&self) -> &'top mut ExpandedStructIterator<'top, D> {
        self.context.allocator.alloc_with(|| self.iter())
    }

    pub fn find(&self, name: &str) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        for field_result in self.iter() {
            let field = field_result?;
            if field.name() == name.as_raw_symbol_token_ref() {
                return Ok(Some(*field.value()));
            }
        }
        Ok(None)
    }

    pub fn get(&self, name: &str) -> IonResult<Option<ExpandedValueRef<'top, D>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    pub fn get_expected(&self, name: &str) -> IonResult<ExpandedValueRef<'top, D>> {
        if let Some(value) = self.get(name)? {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("did not find expected struct field '{}'", name))
        }
    }
}

pub enum ExpandedStructIteratorSource<'top, D: LazyDecoder> {
    // The struct we're iterating over is a literal in the data stream. It may contain
    // e-expressions that need to be evaluated.
    ValueLiteral(
        // Giving the struct iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        MacroEvaluator<'top, D>,
        <D::Struct<'top> as LazyRawStruct<'top, D>>::Iterator,
    ),
    // The struct we're iterating over is a value in a TDL template. It may contain macro
    // invocations that need to be evaluated.
    Template(
        MacroEvaluator<'top, D>,
        TemplateStructRawFieldsIterator<'top, D>,
    ),
    // TODO: Constructed
}

pub struct ExpandedStructIterator<'top, D: LazyDecoder> {
    context: EncodingContext<'top>,
    source: ExpandedStructIteratorSource<'top, D>,
    // Stores information about any operations that are still in progress.
    state: ExpandedStructIteratorState<'top, D>,
}

/// Ion 1.1's struct is very versatile, and supports a variety of expansion operations. This
/// types indicates which operation is in the process of being carried out.
enum ExpandedStructIteratorState<'top, D: LazyDecoder> {
    // The iterator is not performing any operations. It is ready to pull the next field from its
    // source.
    ReadingFieldFromSource,
    // The iterator is expanding a macro invocation that was found in value position; for example:
    //     foo: (:values 1 2 3)
    // would be expanded to:
    //     foo: 1,
    //     foo: 2,
    //     foo: 3,
    // This variant holds the field name that will be repeated for every value in the macro's
    // expansion.
    ExpandingValueExpr(RawSymbolTokenRef<'top>),
    // The iterator is in the process of incrementally inlining a macro found in field name
    // position that expands to a struct; for example:
    //     (:values {foo: 1, bar: 2})
    // would expand to:
    //     foo: 1,
    //     bar: 2,
    // This variant holds a pointer to that struct's iterator living in the
    // EncodingContext's bump allocator.
    InliningAStruct(
        LazyExpandedStruct<'top, D>,
        &'top mut ExpandedStructIterator<'top, D>,
    ),
}

impl<'top, D: LazyDecoder> Iterator for ExpandedStructIterator<'top, D> {
    type Item = IonResult<LazyExpandedField<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            context,
            ref mut source,
            ref mut state,
        } = *self;
        match source {
            ExpandedStructIteratorSource::Template(tdl_macro_evaluator, template_iterator) => {
                Self::next_field_from(context, state, tdl_macro_evaluator, template_iterator)
            }
            ExpandedStructIteratorSource::ValueLiteral(e_exp_evaluator, raw_struct_iter) => {
                let mut iter_adapter = raw_struct_iter.map(
                    |field: IonResult<LazyRawFieldExpr<'top, D>>| match field? {
                        RawFieldExpr::NameValuePair(name, RawValueExpr::MacroInvocation(m)) => {
                            let resolved_invocation = m.resolve(context)?;
                            Ok(RawFieldExpr::NameValuePair(
                                name,
                                RawValueExpr::MacroInvocation(resolved_invocation.into()),
                            ))
                        }
                        RawFieldExpr::NameValuePair(name, RawValueExpr::ValueLiteral(value)) => Ok(
                            RawFieldExpr::NameValuePair(name, RawValueExpr::ValueLiteral(value)),
                        ),
                        RawFieldExpr::MacroInvocation(invocation) => {
                            let resolved_invocation = invocation.resolve(context)?;
                            Ok(RawFieldExpr::MacroInvocation(resolved_invocation.into()))
                        }
                    },
                );
                Self::next_field_from(context, state, e_exp_evaluator, &mut iter_adapter)
            }
        }
    }
}

// Struct expansion is rather complex, and we need to perform it in text Ion, binary Ion, and in
// the body of templates. This implementation covers all of those use cases, but involves some
// potentially intimidating generics as a result. We'll walk through them as they're introduced.
//
//  'top: The lifetime associated with the top-level value we're currently reading at some depth.
// 'data: The lifetime associated with the byte array containing the Ion we're reading from.
//     D: The decoder being used to read the Ion data stream. For example: `TextEncoding_1_1`
impl<'top, D: LazyDecoder> ExpandedStructIterator<'top, D> {
    /// Pulls the next expanded field from the raw source struct. The field returned may correspond
    /// to a `(name, value literal)` pair in the raw struct, or it may be the product of a macro
    /// evaluation.
    fn next_field_from<
        // The lifetime of this method invocation.
        'a,
        // The lifetime of the field name that we return; it needs to live at least as long as
        // `top -- the amount of time that the reader will be parked on this top level value.
        'name: 'top,
        // We have an iterator (see `I` below) that gives us raw fields from an input struct.
        // This type, `V`, is the type of value in that raw field. For example: `LazyRawTextValue_1_1`
        // when reading text Ion 1.1, or `&'top Element` when evaluating a TDL macro.
        V: Into<ExpandedValueSource<'top, D>>,
        // An iterator over the struct we're expanding. It may be the fields iterator from a
        // LazyRawStruct, or it could be a `TemplateStructRawFieldsIterator`.
        I: Iterator<Item = IonResult<RawFieldExpr<'name, V, MacroExpr<'top, D>>>>,
    >(
        context: EncodingContext<'top>,
        state: &'a mut ExpandedStructIteratorState<'top, D>,
        evaluator: &'a mut MacroEvaluator<'top, D>,
        iter: &'a mut I,
    ) -> Option<IonResult<LazyExpandedField<'top, D>>> {
        // This method begins by pulling raw field expressions from the source iterator.
        // If the expression is a (name, value literal) pair, we can wrap it in an LazyExpandedField
        // and return it immediately. However, if it is a (name, macro) pair or (macro) expression,
        // then an unknown amount of evaluation will need to happen before we can return our next
        // field.
        loop {
            use ControlFlow::{Break, Continue};
            use ExpandedStructIteratorState::*;
            match state {
                // This is the initial state. We're reading a raw field expression from our source
                // iterator.
                ReadingFieldFromSource => {
                    // We'll see what kind of expression it is.
                    match Self::next_from_iterator(context, state, evaluator, iter) {
                        // The iterator found a (name, value literal) pair.
                        Break(maybe_result) => return maybe_result,
                        // The iterator found a (name, macro) pair or a macro; further evaluation
                        // is needed to yield a (name, value) pair.
                        Continue(_) => continue,
                    }
                }
                // The iterator previously encountered a macro in field-name position. That macro
                // yielded a struct, and now we're merging that expanded struct's fields into our
                // own one at a time.
                InliningAStruct(_struct, struct_iter) => {
                    if let Some(inlined_field) = struct_iter.next() {
                        // We pulled another field from the struct we're inlining.
                        return Some(inlined_field);
                    } else {
                        // We're done inlining this struct. Switch back to reading from the source.
                        *state = ReadingFieldFromSource;
                        continue;
                    }
                }
                // The iterator previously encountered a (name, macro) pair. We're evaluating the
                // macro in field value position, emitting (name, value) pairs for each value
                // in the expansion, one at a time.
                ExpandingValueExpr(field_name) => {
                    match evaluator.next(context) {
                        Err(e) => return Some(Err(e)),
                        Ok(Some(next_value)) => {
                            // We got another value from the macro we're evaluating. Emit
                            // it as another field using the same field_name.
                            return Some(Ok(LazyExpandedField::new(
                                field_name.clone(),
                                next_value,
                            )));
                        }
                        Ok(None) => {
                            // The macro in the value position is no longer emitting values. Switch
                            // back to reading from the source.
                            *state = ReadingFieldFromSource;
                        }
                    }
                }
            }
        }
    }

    /// Pulls a single raw field expression from the source iterator and sets `state` according to
    /// the expression's kind.
    fn next_from_iterator<
        // These generics are all carried over from the function above.
        'a,
        'name: 'top,
        V: Into<ExpandedValueSource<'top, D>>,
        I: Iterator<Item = IonResult<RawFieldExpr<'name, V, MacroExpr<'top, D>>>>,
    >(
        context: EncodingContext<'top>,
        state: &mut ExpandedStructIteratorState<'top, D>,
        evaluator: &mut MacroEvaluator<'top, D>,
        iter: &mut I,
    ) -> ControlFlow<Option<IonResult<LazyExpandedField<'top, D>>>> {
        // Because this helper function is always being invoked from within a loop, it uses
        // the `ControlFlow` enum to signal whether its return value should cause the loop to
        // terminate (`ControlFlow::Break`) or continue (`ControlFlow::Continue`).
        use ControlFlow::*;

        // If the iterator is empty, we're done.
        let field_expr_result = match iter.next() {
            Some(result) => result,
            None => return Break(None),
        };

        return match field_expr_result {
            Err(e) => Break(Some(Err::<LazyExpandedField<'top, D>, IonError>(e))),
            // Plain (name, value literal) pair. For example: `foo: 1`
            Ok(RawFieldExpr::NameValuePair(name, RawValueExpr::ValueLiteral(value))) => {
                Break(Some(Ok(LazyExpandedField::new(
                    name,
                    LazyExpandedValue {
                        context,
                        source: value.into(),
                    },
                ))))
            }
            // (name, macro invocation) pair. For example: `foo: (:bar)`
            Ok(RawFieldExpr::NameValuePair(name, RawValueExpr::MacroInvocation(invocation))) => {
                if let Err(e) = evaluator.push(context, invocation) {
                    return Break(Some(Err(e)));
                };
                *state = ExpandedStructIteratorState::ExpandingValueExpr(name);
                // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
                // is needed to get our next field.
                Continue(())
            }
            // Macro invocation in field name position.
            Ok(RawFieldExpr::MacroInvocation(invocation)) => {
                // The next expression from the iterator was a macro. We expect it to expand to a
                // single struct whose fields will be merged into the one we're iterating over. For example:
                //     {a: 1, (:make_struct b 2 c 3), d: 4}
                // expands to:
                //     {a: 1, b: 2, c: 3, d: 4}
                match Self::begin_inlining_struct_from_macro(context, state, evaluator, invocation)
                {
                    // If the macro expanded to a struct as expected, continue the evaluation
                    // until we get a field to return.
                    Ok(_) => Continue(()),
                    // If something went wrong, surface the error.
                    Err(e) => Break(Some(Err(e))),
                }
            }
        };
    }

    /// Pulls the next value from the evaluator, confirms that it's a struct, and then switches
    /// the iterator state to `InliningAStruct` so it can begin merging its fields.
    fn begin_inlining_struct_from_macro<'a, 'name: 'top>(
        context: EncodingContext<'top>,
        state: &mut ExpandedStructIteratorState<'top, D>,
        evaluator: &mut MacroEvaluator<'top, D>,
        invocation: MacroExpr<'top, D>,
    ) -> IonResult<()> {
        let mut evaluation = evaluator.evaluate(context, invocation)?;
        let expanded_value = match evaluation.next() {
            Some(Ok(item)) => item,
            Some(Err(e)) => return Err(e),
            None => return IonResult::decoding_error(format!("macros in field name position must produce a single struct; '{:?}' produced nothing", invocation)),
        };
        let struct_ = match expanded_value.read()? {
            ExpandedValueRef::Struct(s) => s,
            other => {
                return IonResult::decoding_error(format!(
                    "macros in field name position must produce structs; '{:?}' produced: {:?}",
                    invocation, other
                ))
            }
        };
        let iter: &'top mut ExpandedStructIterator<'top, D> = struct_.bump_iter();
        *state = ExpandedStructIteratorState::InliningAStruct(struct_, iter);
        Ok(())
    }
}
