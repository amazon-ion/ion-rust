use std::ops::ControlFlow;

use crate::lazy::decoder::{LazyDecoder, LazyRawStruct, RawFieldExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{
    MacroEvaluator, MacroExpansion, MacroInvocation, TransientEExpEvaluator,
    TransientTdlMacroEvaluator,
};
use crate::lazy::expanded::stack::Stack;
use crate::lazy::expanded::template::TemplateStructRawFieldsIterator;
use crate::lazy::expanded::{
    EncodingContext, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueRef,
    ExpandedValueSource, LazyExpandedValue,
};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::{Annotations, IonError, IonResult, RawSymbolTokenRef, Struct};

#[derive(Debug, Clone)]
pub struct LazyExpandedField<'top, 'data, D: LazyDecoder<'data>> {
    name: RawSymbolTokenRef<'top>,
    pub(crate) value: LazyExpandedValue<'top, 'data, D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> LazyExpandedField<'top, 'data, D> {
    pub fn new(name: RawSymbolTokenRef<'top>, value: LazyExpandedValue<'top, 'data, D>) -> Self {
        Self { name, value }
    }

    pub fn name(&self) -> RawSymbolTokenRef<'top> {
        self.name.clone()
    }

    pub fn value(&self) -> &LazyExpandedValue<'top, 'data, D> {
        &self.value
    }
}

#[derive(Clone)]
pub enum ExpandedStructSource<'top, 'data, D: LazyDecoder<'data>> {
    ValueLiteral(D::Struct),
    Template(&'top Annotations, &'top Struct),
    // TODO: Constructed
}

#[derive(Clone)]
pub struct LazyExpandedStruct<'top, 'data, D: LazyDecoder<'data>> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) source: ExpandedStructSource<'top, 'data, D>,
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> LazyExpandedStruct<'top, 'data, D> {
    pub fn from_literal(
        context: EncodingContext<'top>,
        sexp: D::Struct,
    ) -> LazyExpandedStruct<'top, 'data, D> {
        let source = ExpandedStructSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContext<'top>,
        annotations: &'top Annotations,
        struct_: &'top Struct,
    ) -> LazyExpandedStruct<'top, 'data, D> {
        let source = ExpandedStructSource::Template(annotations, struct_);
        Self { source, context }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, 'data, D> {
        match self.source {
            ExpandedStructSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedStructSource::Template(annotations, _struct) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::Template(annotations.iter()),
            },
        }
    }

    pub fn iter(&self) -> ExpandedStructIterator<'top, 'data, D> {
        let source = match self.source {
            ExpandedStructSource::ValueLiteral(raw_struct) => {
                ExpandedStructIteratorSource::ValueLiteral(
                    MacroEvaluator::<
                        D,
                        <D as LazyDecoder<'_>>::MacroInvocation,
                        bumpalo::collections::Vec<'top, _>,
                    >::new_transient(self.context),
                    raw_struct.iter(),
                )
            }
            ExpandedStructSource::Template(_annotations, struct_) => {
                ExpandedStructIteratorSource::Template(
                    TransientTdlMacroEvaluator::new_transient(self.context),
                    TemplateStructRawFieldsIterator::new(struct_),
                )
            }
        };
        ExpandedStructIterator {
            context: self.context,
            source,
            state: ExpandedStructIteratorState::ReadingFieldFromSource,
        }
    }

    pub fn bump_iter(&self) -> &'top mut ExpandedStructIterator<'top, 'data, D> {
        self.context.allocator.alloc_with(|| self.iter())
    }

    pub fn find(&self, name: &str) -> IonResult<Option<LazyExpandedValue<'top, 'data, D>>> {
        for field_result in self.iter() {
            let field = field_result?;
            if field.name() == name.as_raw_symbol_token_ref() {
                return Ok(Some(field.value().clone()));
            }
        }
        Ok(None)
    }

    pub fn get(&self, name: &str) -> IonResult<Option<ExpandedValueRef<'top, 'data, D>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    pub fn get_expected(&self, name: &str) -> IonResult<ExpandedValueRef<'top, 'data, D>> {
        if let Some(value) = self.get(name)? {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("did not find expected struct field '{}'", name))
        }
    }
}

pub enum ExpandedStructIteratorSource<'top, 'data, D: LazyDecoder<'data>> {
    // The struct we're iterating over is a literal in the data stream. It may contain
    // e-expressions that need to be evaluated.
    ValueLiteral(
        // Giving the struct iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        TransientEExpEvaluator<'top, 'data, D>,
        <D::Struct as LazyRawStruct<'data, D>>::Iterator,
    ),
    // The struct we're iterating over is a value in a TDL template. It may contain macro
    // invocations that need to be evaluated.
    Template(
        TransientTdlMacroEvaluator<'top, 'data, D>,
        TemplateStructRawFieldsIterator<'top>,
    ),
    // TODO: Constructed
}

pub struct ExpandedStructIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    source: ExpandedStructIteratorSource<'top, 'data, D>,
    // Stores information about any operations that are still in progress.
    state: ExpandedStructIteratorState<'top, 'data, D>,
}

/// Ion 1.1's struct is very versatile, and supports a variety of expansion operations. This
/// types indicates which operation is in the process of being carried out.
enum ExpandedStructIteratorState<'top, 'data: 'top, D: LazyDecoder<'data>> {
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
        LazyExpandedStruct<'top, 'data, D>,
        &'top mut ExpandedStructIterator<'top, 'data, D>,
    ),
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> Iterator for ExpandedStructIterator<'top, 'data, D> {
    type Item = IonResult<LazyExpandedField<'top, 'data, D>>;

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
            ExpandedStructIteratorSource::ValueLiteral(e_exp_evaluator, iter) => {
                Self::next_field_from(context, state, e_exp_evaluator, iter)
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
impl<'top, 'data: 'top, D: LazyDecoder<'data>> ExpandedStructIterator<'top, 'data, D> {
    /// Pulls the next expanded field from the raw source struct. The field returned may correspond
    /// to a `(name, value literal)` pair in the raw struct, or it may be the product of a macro
    /// evaluation.
    fn next_field_from<
        // The lifetime of this method invocation.
        'a,
        // The lifetime of the field name that we return; it needs to live at least as long as
        // `top -- the amount of time that the reader will be parked on this top level value.
        'name: 'top,
        // The syntactic element that represents a macro invocation in this context. For
        // example: a `RawTextMacroInvocation` when reading text Ion 1.1 or a `&'top Sequence` when
        // evaluating a TDL macro.
        M: MacroInvocation<'data, D> + 'top,
        // We have an iterator (see `I` below) that gives us raw fields from an input struct.
        // This type, `V`, is the type of value in that raw field. For example: `LazyRawTextValue_1_1`
        // when reading text Ion 1.1, or `&'top Element` when evaluating a TDL macro.
        V: Into<ExpandedValueSource<'top, 'data, D>>,
        // The type of backing storage used by our macro evaluator. If struct we're iterating over is
        // at the top level of the data stream, the evaluator will use a `Vec` for its stack to have
        // storage that can persist across top level values. If this is a nested struct or part of
        // a template, this will be a transient `BumpVec` with a lifetime tied to the top level.
        S: Stack<MacroExpansion<'data, D, M>>,
        // An iterator over the struct we're expanding. It may be the fields iterator from a
        // LazyRawStruct, or it could be a `TemplateStructRawFieldsIterator`.
        I: Iterator<Item = IonResult<RawFieldExpr<'name, V, M>>>,
    >(
        context: EncodingContext<'top>,
        state: &'a mut ExpandedStructIteratorState<'top, 'data, D>,
        evaluator: &'a mut MacroEvaluator<'data, D, M, S>,
        iter: &'a mut I,
    ) -> Option<IonResult<LazyExpandedField<'top, 'data, D>>> {
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
                    match evaluator.next(context, 0) {
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
        M: MacroInvocation<'data, D> + 'top,
        V: Into<ExpandedValueSource<'top, 'data, D>>,
        S: Stack<MacroExpansion<'data, D, M>>,
        I: Iterator<Item = IonResult<RawFieldExpr<'name, V, M>>>,
    >(
        context: EncodingContext<'top>,
        state: &mut ExpandedStructIteratorState<'top, 'data, D>,
        evaluator: &mut MacroEvaluator<'data, D, M, S>,
        iter: &mut I,
    ) -> ControlFlow<Option<IonResult<LazyExpandedField<'top, 'data, D>>>> {
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
            Err(e) => Break(Some(Err::<LazyExpandedField<'top, 'data, D>, IonError>(e))),
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
    fn begin_inlining_struct_from_macro<
        'a,
        'name: 'top,
        M: MacroInvocation<'data, D> + 'top,
        S: Stack<MacroExpansion<'data, D, M>>,
    >(
        context: EncodingContext<'top>,
        state: &mut ExpandedStructIteratorState<'top, 'data, D>,
        evaluator: &mut MacroEvaluator<'data, D, M, S>,
        invocation: M,
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
        let iter: &'top mut ExpandedStructIterator<'top, 'data, D> = struct_.bump_iter();
        *state = ExpandedStructIteratorState::InliningAStruct(struct_, iter);
        Ok(())
    }
}
