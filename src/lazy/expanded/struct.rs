use crate::lazy::decoder::{LazyDecoder, LazyRawFieldExpr, LazyRawStruct, LazyRawValueExpr};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, TransientEExpEvaluator};
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
    context: EncodingContext<'top>,
    source: ExpandedStructSource<'top, 'data, D>,
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
            ExpandedStructSource::Template(_, _) => {
                todo!("iterate over struct from template")
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

    fn find(&self, name: &str) -> IonResult<Option<LazyExpandedValue<'top, 'data, D>>> {
        for field_result in self.iter() {
            let field = field_result?;
            if field.name() == name.as_raw_symbol_token_ref() {
                return Ok(Some(field.value().clone()));
            }
        }
        Ok(None)
    }

    fn get(&self, name: &str) -> IonResult<Option<ExpandedValueRef<'top, 'data, D>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    fn get_expected(&self, name: &str) -> IonResult<ExpandedValueRef<'top, 'data, D>> {
        if let Some(value) = self.get(name)? {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("did not find expected struct field '{}'", name))
        }
    }
}

pub enum ExpandedStructIteratorSource<'top, 'data: 'top, D: LazyDecoder<'data>> {
    ValueLiteral(
        // Giving the struct iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        TransientEExpEvaluator<'top, 'data, D>,
        <D::Struct as LazyRawStruct<'data, D>>::Iterator,
    ),
    // TODO: Template
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
enum ExpandedStructIteratorState<'top, 'data, D: LazyDecoder<'data>> {
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

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for ExpandedStructIterator<'top, 'data, D> {
    type Item = IonResult<LazyExpandedField<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            context,
            ref mut source,
            ref mut state,
        } = *self;
        match source {
            ExpandedStructIteratorSource::ValueLiteral(evaluator, iter) => {
                loop {
                    use ExpandedStructIteratorState::*;
                    match state {
                        ReadingFieldFromSource => {
                            match iter.next()? {
                                Err(e) => {
                                    return Some(
                                        Err::<LazyExpandedField<'top, 'data, D>, IonError>(e),
                                    );
                                }
                                // Plain (name, value literal) pair. For example: `foo: 1`
                                Ok(LazyRawFieldExpr::NameValuePair(
                                    name,
                                    LazyRawValueExpr::ValueLiteral(value),
                                )) => {
                                    return Some(Ok(LazyExpandedField::new(
                                        name,
                                        LazyExpandedValue {
                                            context,
                                            source: ExpandedValueSource::ValueLiteral(value),
                                        },
                                    )));
                                }
                                // (name, macro invocation) pair. For example: `foo: (:bar)`
                                Ok(LazyRawFieldExpr::NameValuePair(
                                    name,
                                    LazyRawValueExpr::MacroInvocation(invocation),
                                )) => {
                                    if let Err(e) = evaluator.push(context, invocation) {
                                        return Some(Err(e));
                                    };
                                    *state = ExpandingValueExpr(name);
                                    continue;
                                }
                                // Macro invocation in field name position.
                                Ok(LazyRawFieldExpr::MacroInvocation(invocation)) => {
                                    // The next item was a macro. We expect it to expand to a single
                                    // struct whose fields will be merged into the one we're iterating
                                    // over. For example:
                                    //     {a: 1, (:make_struct b 2 c 3), d: 4}
                                    // expands to:
                                    //     {a: 1, b: 2, c: 3, d: 4}
                                    let mut evaluation =
                                        match evaluator.evaluate(context, invocation) {
                                            Ok(iter) => iter,
                                            Err(e) => return Some(Err(e)),
                                        };
                                    let expanded_value = match evaluation.next() {
                                        Some(Ok(item)) => item,
                                        Some(Err(e)) => return Some(Err(e)),
                                        None => return Some(IonResult::decoding_error(format!("macros in field name position must produce a single struct; '{:?}' produced nothing", invocation))),
                                    };
                                    let struct_ = match expanded_value.read() {
                                        Ok(ExpandedValueRef::Struct(s)) => s,
                                        Ok(other) => return Some(IonResult::decoding_error(format!("macros in field name position must produce structs; '{:?}' produced: {:?}", invocation, other))),
                                        Err(e) => return Some(Err(e)),
                                    };
                                    let iter: &'top mut ExpandedStructIterator<'top, 'data, D> =
                                        struct_.bump_iter();
                                    *state = InliningAStruct(struct_, iter);
                                    continue;
                                }
                            };
                        }
                        InliningAStruct(_struct, struct_iter) => {
                            if let Some(inlined_field) = struct_iter.next() {
                                // We pulled another field from the struct we're inlining.
                                return Some(inlined_field);
                            } else {
                                // We're done inlining this struct. Switch back to reading from the source.
                                *state = ReadingFieldFromSource;
                            }
                        }
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
        }
    }
}
