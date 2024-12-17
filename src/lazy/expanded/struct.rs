use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::private::{LazyRawStructPrivate, RawStructFieldSourceIterator};
use crate::lazy::decoder::{Decoder, LazyRawFieldName, LazyRawStruct};
use crate::lazy::expanded::macro_evaluator::{
    MacroEvaluator, MacroExpr, MacroExprArgsIterator, ValueExpr,
};
use crate::lazy::expanded::r#struct::tooling::FieldSourceIterator;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    TemplateElement, TemplateMacroRef, TemplateStructFieldSourceIterator, TemplateStructIndex,
};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueRef,
    LazyExpandedValue,
};
use crate::result::IonFailure;
use crate::{try_next, try_or_some_err, IonResult, RawSymbolRef, SymbolRef};

/// A unified type embodying all possible field representations coming from both input data
/// (i.e. raw structs of some encoding) and template bodies.
// LazyRawStruct implementations have a `unexpanded_fields` method that lifts its raw fields into
// `FieldSource` instances. Similarly, the `TemplateStructFieldSourceIterator` turns a
// template's struct body into `FieldSource` instances. The `ExpandedStructIterator` unpacks
// and expands the field as part of its iteration process.
#[derive(Debug, Clone, Copy)]
pub enum FieldSource<'top, D: Decoder> {
    NameValue(LazyExpandedFieldName<'top, D>, LazyExpandedValue<'top, D>),
    NameMacro(LazyExpandedFieldName<'top, D>, MacroExpr<'top, D>),
    Macro(MacroExpr<'top, D>),
}

#[derive(Debug, Clone, Copy)]
pub struct LazyExpandedField<'top, D: Decoder> {
    name: LazyExpandedFieldName<'top, D>,
    value: LazyExpandedValue<'top, D>,
}

impl<D: Decoder> LazyExpandedField<'_, D> {}

impl<'top, D: Decoder> LazyExpandedField<'top, D> {
    pub fn new(name: LazyExpandedFieldName<'top, D>, value: LazyExpandedValue<'top, D>) -> Self {
        Self { name, value }
    }

    pub fn value(&self) -> LazyExpandedValue<'top, D> {
        self.value
    }

    pub fn name(&self) -> LazyExpandedFieldName<'top, D> {
        self.name
    }

    pub fn to_field_source(&self) -> FieldSource<'top, D> {
        FieldSource::NameValue(self.name(), self.value())
    }
}

impl<'top, D: Decoder> LazyExpandedField<'top, D> {
    fn from_raw_field(
        context: EncodingContextRef<'top>,
        name: D::FieldName<'top>,
        value: impl Into<LazyExpandedValue<'top, D>>,
    ) -> Self {
        Self {
            name: LazyExpandedFieldName::RawName(context, name),
            value: value.into(),
        }
    }

    fn from_template(
        template: TemplateMacroRef<'top>,
        name: SymbolRef<'top>,
        value: impl Into<LazyExpandedValue<'top, D>>,
    ) -> Self {
        Self {
            name: LazyExpandedFieldName::TemplateName(template, name),
            value: value.into(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LazyExpandedFieldName<'top, D: Decoder> {
    RawName(EncodingContextRef<'top>, D::FieldName<'top>),
    TemplateName(TemplateMacroRef<'top>, SymbolRef<'top>),
    MakeField(SymbolRef<'top>),
}

impl<'top, D: Decoder> LazyExpandedFieldName<'top, D> {
    pub(crate) fn read(&self) -> IonResult<SymbolRef<'top>> {
        match self {
            LazyExpandedFieldName::RawName(context, name) => {
                name.read()?.resolve("a field name", *context)
            }
            LazyExpandedFieldName::TemplateName(_template_ref, symbol_ref) => Ok(*symbol_ref),
            LazyExpandedFieldName::MakeField(symbol) => Ok(*symbol),
        }
    }

    pub(crate) fn read_raw(&self) -> IonResult<RawSymbolRef<'top>> {
        match self {
            LazyExpandedFieldName::RawName(_, name) => name.read(),
            LazyExpandedFieldName::TemplateName(_, name) => Ok((*name).into()),
            LazyExpandedFieldName::MakeField(name) => Ok((*name).into()),
        }
    }
}

#[derive(Copy, Clone)]
pub enum ExpandedStructSource<'top, D: Decoder> {
    ValueLiteral(D::Struct<'top>),
    Template(
        Environment<'top, D>,
        TemplateElement<'top>,
        &'top TemplateStructIndex,
    ),
    // The struct was produced by the `make_struct` macro.
    MakeStruct(Environment<'top, D>, MacroExprArgsIterator<'top, D>),
    // The single-field struct was produced by the `make_field` macro
    MakeField(LazyExpandedField<'top, D>),
}

impl<'top, D: Decoder> ExpandedStructSource<'top, D> {
    fn environment(&self) -> Environment<'top, D> {
        match self {
            ExpandedStructSource::ValueLiteral(_) => Environment::empty(),
            ExpandedStructSource::Template(environment, _, _) => *environment,
            ExpandedStructSource::MakeStruct(environment, _) => *environment,
            ExpandedStructSource::MakeField(_field) => {
                unreachable!("make_field structs never need to supply an environment")
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct LazyExpandedStruct<'top, D: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) source: ExpandedStructSource<'top, D>,
}

#[cfg(feature = "experimental-tooling-apis")]
impl<'top, D: Decoder> LazyExpandedStruct<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
    pub fn source(&self) -> ExpandedStructSource<'top, D> {
        self.source
    }
}

impl<'top, D: Decoder> LazyExpandedStruct<'top, D> {
    pub fn from_literal(
        context: EncodingContextRef<'top>,
        sexp: D::Struct<'top>,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        element: &TemplateElement<'top>,
        index: &'top TemplateStructIndex,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::Template(environment, *element, index);
        Self { source, context }
    }

    pub fn from_make_struct(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        arguments: MacroExprArgsIterator<'top, D>,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::MakeStruct(environment, arguments);
        Self { source, context }
    }

    pub fn from_make_field(
        context: EncodingContextRef<'top>,
        field: LazyExpandedField<'top, D>,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::MakeField(field);
        Self { source, context }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        use ExpandedStructSource::*;
        let iter_source = match &self.source {
            ValueLiteral(value) => ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            Template(_environment, element, _index) => {
                let annotations = element.annotations();
                ExpandedAnnotationsSource::Template(SymbolsIterator::new(annotations))
            }
            // Constructed struct instances never have annotations.
            MakeStruct(_, _) | MakeField(_) => ExpandedAnnotationsSource::empty(),
        };
        ExpandedAnnotationsIterator::new(iter_source)
    }

    pub fn iter(&self) -> ExpandedStructIterator<'top, D> {
        let evaluator = self
            .context
            .allocator()
            .alloc_with(|| MacroEvaluator::new());
        use ExpandedStructSource::*;
        let source = match &self.source {
            ValueLiteral(raw_struct) => ExpandedStructIteratorSource::ValueLiteral(
                evaluator,
                raw_struct.unexpanded_fields(self.context),
            ),
            Template(environment, element, _index) => {
                evaluator.set_root_environment(*environment);
                let template = element.template();
                ExpandedStructIteratorSource::Template(
                    evaluator,
                    TemplateStructFieldSourceIterator::new(
                        self.context,
                        *environment,
                        template,
                        template
                            .body()
                            .expressions
                            .get(element.expr_range().tail())
                            .unwrap(),
                    ),
                )
            }
            MakeStruct(environment, arguments) => {
                let evaluator = self
                    .context
                    .allocator()
                    .alloc_with(|| MacroEvaluator::new_with_environment(*environment));
                let current_struct_iter = self.context.allocator().alloc_with(|| None);
                ExpandedStructIteratorSource::MakeStruct(evaluator, current_struct_iter, *arguments)
            }
            MakeField(field) => ExpandedStructIteratorSource::MakeField(Some(*field)),
        };
        ExpandedStructIterator {
            source,
            state: ExpandedStructIteratorState::ReadingFieldFromSource,
        }
    }

    #[cfg(feature = "experimental-tooling-apis")]
    fn field_source_iter(&self) -> FieldSourceIterator<'top, D> {
        // The field source iterator has the same data as the regular iterator, it just uses it differently.
        // Since the regular iterator's initialization process is non-trivial, we'll just make a regular iterator
        // and use it for parts.
        let ExpandedStructIterator { source, state } = self.iter();
        FieldSourceIterator { source, state }
    }

    fn environment(&self) -> Environment<'top, D> {
        self.source.environment()
    }

    pub fn bump_iter(&self) -> &'top mut ExpandedStructIterator<'top, D> {
        self.context.allocator().alloc_with(|| self.iter())
    }

    pub fn find(&self, name: &str) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        use ExpandedStructSource::*;
        match &self.source {
            // If we're reading from a struct in a template, consult its field index to see if one or
            // more fields with the requested name exist.
            Template(environment, element, index) => {
                let Some(value_expr_addresses) = index.get(name) else {
                    // If the field name is not in the index, it's not in the struct.
                    return Ok(None);
                };
                // If there are fields with the requested name, return the first one.
                // TODO: This is a starting point. There's room for an API that returns an iterator
                //       over all matching entries. Note, however, that it would be difficult to
                //       offer an efficient implementation of 'get last' because that could require
                //       fully evaluating one or more macros to find the last value.
                let first_result_address = value_expr_addresses[0];
                let first_result_expr = element
                    .template()
                    .body()
                    .expressions()
                    .get(first_result_address)
                    .unwrap();
                let value_expr =
                    first_result_expr.to_value_expr(self.context, *environment, element.template());
                match value_expr {
                    ValueExpr::ValueLiteral(lazy_expanded_value) => Ok(Some(lazy_expanded_value)),
                    ValueExpr::MacroInvocation(invocation) => {
                        // Evaluate the invocation enough to get the first result.
                        let mut evaluator = MacroEvaluator::for_macro_expr(invocation)?;
                        evaluator.next()
                    }
                }
            }
            // For any other kind of struct, do a linear scan over its fields until we encounter
            // one with the requested name.
            ValueLiteral(..) | MakeField(..) | MakeStruct(..) => {
                for field_result in self.iter() {
                    let field = field_result?;
                    if field.name().read()?.text() == Some(name) {
                        return Ok(Some(field.value));
                    }
                }
                // If there is no such field, return None.
                Ok(None)
            }
        }
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

pub enum ExpandedStructIteratorSource<'top, D: Decoder> {
    // The struct we're iterating over is a literal in the data stream. It may contain
    // e-expressions that need to be evaluated.
    ValueLiteral(
        // Giving the struct iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        &'top mut MacroEvaluator<'top, D>,
        RawStructFieldSourceIterator<'top, D>,
    ),
    // The struct we're iterating over is a value in a TDL template. It may contain macro
    // invocations that need to be evaluated.
    Template(
        &'top mut MacroEvaluator<'top, D>,
        TemplateStructFieldSourceIterator<'top, D>,
    ),
    MakeField(Option<LazyExpandedField<'top, D>>),
    MakeStruct(
        &'top mut MacroEvaluator<'top, D>,
        // This is `&mut Option<_>` instead of `Option<&mut _>` so we can re-use the allocated space
        // for each iterator we traverse.
        &'top mut Option<ExpandedStructIterator<'top, D>>,
        // Remaining argument expressions
        MacroExprArgsIterator<'top, D>,
    ),
}

impl<'top, D: Decoder> ExpandedStructIteratorSource<'top, D> {
    fn next_field(&mut self) -> Option<IonResult<FieldSource<'top, D>>> {
        // Get the next unexpanded field from our source's iterator.
        match self {
            ExpandedStructIteratorSource::Template(_, template_iterator) => {
                template_iterator.next()
            }
            ExpandedStructIteratorSource::ValueLiteral(_, raw_struct_iter) => {
                raw_struct_iter.next()
            }
            ExpandedStructIteratorSource::MakeField(maybe_field) => {
                let field = maybe_field.take()?;
                Some(Ok(field.to_field_source()))
            }
            ExpandedStructIteratorSource::MakeStruct(
                evaluator,
                maybe_current_struct,
                arguments,
            ) => {
                loop {
                    // If we're already traversing a struct, see if it has any fields remaining.
                    if let Some(current_struct) = maybe_current_struct {
                        match current_struct.next() {
                            // If we get a field, we're done.
                            Some(Ok(field)) => return Some(Ok(field.to_field_source())),
                            Some(Err(e)) => return Some(Err(e)),
                            // If we get `None`, the iterator is exhausted and we should continue on to the next struct.
                            None => **maybe_current_struct = None,
                        }
                    }

                    // If we reach this point, we don't have a current struct.
                    // We've either just started evaluation and haven't set one yet or
                    // we just finished inlining a struct and need to set a new one.

                    // See if the evaluator has an expansion in progress.
                    let mut next_struct = try_or_some_err!(evaluator.next());
                    if next_struct.is_none() {
                        // If we don't get anything from the evaluator, we'll get our struct from the
                        // next argument expression. If there isn't a next argument expression,
                        // then evaluation is complete.
                        next_struct = match try_next!(arguments.next()) {
                            // If the expression is a value literal, that's our new sequence.
                            ValueExpr::ValueLiteral(value) => Some(value),
                            // If the expression is a macro invocation, we'll start evaluating it
                            // and return to the top of the loop.
                            ValueExpr::MacroInvocation(invocation) => {
                                evaluator.push(try_or_some_err!(invocation.expand()));
                                continue;
                            }
                        }
                    }

                    // At this point, `next_struct` is definitely populated, so we can safely unwrap it.
                    let next_struct = next_struct.unwrap();
                    // Set it as our new current struct.
                    let ExpandedValueRef::Struct(next_struct) =
                        try_or_some_err!(next_struct.read())
                    else {
                        return Some(IonResult::decoding_error(format!(
                            "`make_struct` only accepts structs, received {next_struct:?}"
                        )));
                    };
                    **maybe_current_struct = Some(next_struct.iter());
                }
            }
        }
    }

    fn evaluator(&mut self) -> &mut MacroEvaluator<'top, D> {
        match self {
            ExpandedStructIteratorSource::Template(evaluator, _) => evaluator,
            ExpandedStructIteratorSource::ValueLiteral(evaluator, _) => evaluator,
            ExpandedStructIteratorSource::MakeField(_) => {
                unreachable!("`make_field` structs never need to have an evaluator")
            }
            ExpandedStructIteratorSource::MakeStruct(evaluator, _, _) => evaluator,
        }
    }
}

pub struct ExpandedStructIterator<'top, D: Decoder> {
    // Each variant of 'source' below holds its own encoding context reference
    source: ExpandedStructIteratorSource<'top, D>,
    // Stores information about any operations that are still in progress.
    state: ExpandedStructIteratorState<'top, D>,
}

/// Ion 1.1's struct is very versatile, and supports a variety of expansion operations. This
/// types indicates which operation is in the process of being carried out.
enum ExpandedStructIteratorState<'top, D: Decoder> {
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
    ExpandingValueExpr(LazyExpandedFieldName<'top, D>),
    // The iterator is in the process of incrementally inlining a macro found in field name
    // position that expands to a struct; for example:
    //     (:values {foo: 1, bar: 2})
    // would expand to:
    //     foo: 1,
    //     bar: 2,
    // This variant holds a pointer to that struct's iterator living in the
    // EncodingContext's bump allocator.
    InliningAStruct(&'top mut ExpandedStructIterator<'top, D>),
}

impl<'top, D: Decoder> Iterator for ExpandedStructIterator<'top, D> {
    type Item = IonResult<LazyExpandedField<'top, D>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.next_field()
    }
}

// Struct expansion is rather complex, and we need to perform it in text Ion, binary Ion, and in
// the body of templates. This implementation covers all of those use cases, but involves some
// potentially intimidating generics as a result. We'll walk through them as they're introduced.
//
//  'top: The lifetime associated with the top-level value we're currently reading at some depth.
//     D: The decoder being used to read the Ion data stream. For example: `TextEncoding_1_1`
impl<'top, D: Decoder> ExpandedStructIterator<'top, D> {
    /// Pulls the next expanded field from the raw source struct. The field returned may correspond
    /// to a `(name, value literal)` pair in the raw struct, or it may be the product of a macro
    /// evaluation.
    fn next_field(&mut self) -> Option<IonResult<LazyExpandedField<'top, D>>> {
        // Temporarily destructure 'Self' to get simultaneous mutable references to its fields.
        let Self {
            ref mut source,
            ref mut state,
        } = *self;

        loop {
            use ExpandedStructIteratorState::*;
            match state {
                // This is the initial state. We're reading a field expression from our source
                // iterator.
                ReadingFieldFromSource => {
                    use FieldSource::*;
                    match try_or_some_err!(source.next_field()?) {
                        NameValue(name, value) => {
                            return Some(Ok(LazyExpandedField::new(name, value)))
                        }
                        NameMacro(name, invocation) => {
                            match Self::begin_expanding_field_macro(
                                state,
                                source.evaluator(),
                                name,
                                invocation,
                            ) {
                                Some(field_result) => return Some(field_result),
                                None => continue,
                            }
                        }
                        Macro(invocation) => {
                            // The next expression from the iterator was a macro. We expect it to expand to a
                            // single struct whose fields will be merged into the one we're iterating over. For example:
                            //     {a: 1, (:make_struct b 2 c 3), d: 4}
                            // expands to:
                            //     {a: 1, b: 2, c: 3, d: 4}
                            try_or_some_err!(begin_inlining_struct_from_macro(
                                state,
                                source.evaluator(),
                                invocation,
                            ))
                        }
                    };
                }
                // The iterator previously encountered a macro in field-name position. That macro
                // yielded a struct, and now we're merging that expanded struct's fields into our
                // own one at a time.
                InliningAStruct(struct_iter) => {
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
                    // Get the next expression from our source's macro evaluator.
                    let evaluator = source.evaluator();
                    match try_or_some_err!(evaluator.next()) {
                        Some(next_value) => {
                            let field_name = *field_name;
                            if evaluator.is_empty() {
                                // The evaluator is empty, so we should return to reading from
                                // source.
                                *state = ReadingFieldFromSource;
                            }
                            // We got another value from the macro we're evaluating. Emit
                            // it as another field using the same field_name.
                            return Some(Ok(LazyExpandedField::new(field_name, next_value)));
                        }
                        None => {
                            // The macro in the value position is no longer emitting values. Switch
                            // back to reading from the source.
                            *state = ReadingFieldFromSource;
                        }
                    }
                }
            }
        }
    }

    /// Pulls a single unexpanded field expression from the source iterator and sets `state` according to
    /// the expression's kind.
    fn begin_expanding_field_macro(
        state: &mut ExpandedStructIteratorState<'top, D>,
        evaluator: &mut MacroEvaluator<'top, D>,
        field_name: LazyExpandedFieldName<'top, D>,
        invocation: MacroExpr<'top, D>,
    ) -> Option<IonResult<LazyExpandedField<'top, D>>> {
        let expansion = try_or_some_err!(invocation.expand());
        // If the macro is guaranteed to expand to exactly one value, we can evaluate it
        // in place.
        if invocation
            .expansion_analysis()
            .must_produce_exactly_one_value()
        {
            let value = try_or_some_err!(expansion.expand_singleton());
            return Some(Ok(LazyExpandedField::new(field_name, value)));
        }
        // Otherwise, we'll add it to the evaluator's stack and return to the top of the loop.
        evaluator.push(expansion);
        *state = ExpandedStructIteratorState::ExpandingValueExpr(field_name);
        // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
        // is needed to get our next field.
        None
    }
}

/// Pulls the next value from the evaluator, confirms that it's a struct, and then switches
/// the iterator state to `InliningAStruct` so it can begin merging its fields.
fn begin_inlining_struct_from_macro<'top, D: Decoder>(
    state: &mut ExpandedStructIteratorState<'top, D>,
    evaluator: &mut MacroEvaluator<'top, D>,
    invocation: MacroExpr<'top, D>,
) -> IonResult<()> {
    let expansion = invocation.expand()?;
    evaluator.push(expansion);
    let Some(struct_) = next_struct_from_macro(evaluator)? else {
        // If the invocation didn't produce anything, don't bother switching states.
        return Ok(());
    };
    // Otherwise, save the resulting struct's iterator and remember that we're inlining it.
    let iter: &'top mut ExpandedStructIterator<'top, D> = struct_.bump_iter();
    *state = ExpandedStructIteratorState::InliningAStruct(iter);
    Ok(())
}

fn next_struct_from_macro<'top, D: Decoder>(
    evaluator: &mut MacroEvaluator<'top, D>,
) -> IonResult<Option<LazyExpandedStruct<'top, D>>> {
    let Some(expanded_value) = evaluator.next()? else {
        // The macro produced an empty stream; return to reading from input.
        return Ok(None);
    };
    let value_ref = expanded_value.read()?;
    let ExpandedValueRef::Struct(struct_) = value_ref else {
        return IonResult::decoding_error(format!(
            "macros in field name position must produce structs; found: {:?}",
            value_ref
        ));
    };
    Ok(Some(struct_))
}

#[cfg(feature = "experimental-tooling-apis")]
mod tooling {
    use super::*;

    /// Like the [`ExpandedStructIterator`], but also yields the expressions that back the fields.
    ///
    /// Given this Ion stream:
    /// ```ion
    /// {
    ///   bar: (:values 1 2 3),
    /// }
    /// ```
    /// An `ExpandedStructIterator` would yield a `LazyExpandedField` representing each
    /// of the name/values pairs in the expansion: `(bar, 1)`, `(bar, 2)`, and `(bar, 3)`.
    ///
    /// In contrast, the `FieldSourceIterator` would yield a `FieldSource` for the name/macro
    /// field expression (`NameMacro("foo", MacroExpr)`) followed by a `FieldSource` for each of
    /// the fields in the expansion `NameValue(bar, 1)`, `NameValue(bar, 2)`, and `NameValue(bar, 3)`.
    pub struct FieldSourceIterator<'top, D: Decoder> {
        // Each variant of 'source' below holds its own encoding context reference
        pub(crate) source: ExpandedStructIteratorSource<'top, D>,
        // Stores information about any operations that are still in progress.
        pub(crate) state: ExpandedStructIteratorState<'top, D>,
    }

    impl<'top, D: Decoder> Iterator for FieldSourceIterator<'top, D> {
        type Item = IonResult<FieldSource<'top, D>>;

        fn next(&mut self) -> Option<Self::Item> {
            let Self {
                ref mut source,
                ref mut state,
            } = *self;

            loop {
                use ExpandedStructIteratorState::*;
                match state {
                    // This is the initial state. We're reading a field expression from our source
                    // iterator.
                    ReadingFieldFromSource => {
                        use FieldSource::*;
                        let field = try_or_some_err!(source.next_field()?);
                        match field {
                            // It's a regular field, no special handling required.
                            NameValue(..) => {}
                            // It's a name/macro pair. We'll push the macro on the stack and record
                            // the field name so we can emit it with each value this macro eventually
                            // produces.
                            NameMacro(name, invocation) => {
                                let expansion = try_or_some_err!(invocation.expand());
                                source.evaluator().push(expansion);
                                *state = ExpandingValueExpr(name);
                            }
                            // It's a macro in field name position. Start evaluating the macro until
                            // we get our first struct, then save that struct's iterator.
                            Macro(invocation) => {
                                try_or_some_err!(begin_inlining_struct_from_macro(
                                    state,
                                    source.evaluator(),
                                    invocation
                                ));
                            }
                        };
                        return Some(Ok(field));
                    }
                    // The iterator previously encountered a macro in field-name position. That macro
                    // yielded a struct, and now we're merging that expanded struct's fields into our
                    // own one at a time.
                    InliningAStruct(struct_iter) => {
                        if let Some(inlined_field) =
                            try_or_some_err!(struct_iter.next().transpose())
                        {
                            // We pulled another field from the struct we're inlining.
                            return Some(Ok(inlined_field.to_field_source()));
                        } else {
                            // We're done inlining this struct. Try to get another one.
                            match try_or_some_err!(next_struct_from_macro(source.evaluator())) {
                                Some(struct_) => {
                                    // If there is one, save its iterator and continue on.
                                    let iter: &'top mut ExpandedStructIterator<'top, D> =
                                        struct_.bump_iter();
                                    *state = InliningAStruct(iter);
                                }
                                None => {
                                    // If there isn't another one, switch back to reading from the source.
                                    *state = ReadingFieldFromSource;
                                    continue;
                                }
                            }
                        }
                    }
                    // The iterator previously encountered a (name, macro) pair. We're evaluating the
                    // macro in field value position, emitting (name, value) pairs for each value
                    // in the expansion, one at a time.
                    ExpandingValueExpr(field_name) => {
                        // Get the next expression from our source's macro evaluator.
                        let evaluator = source.evaluator();
                        match try_or_some_err!(evaluator.next()) {
                            Some(next_value) => {
                                let field_name = *field_name;
                                if evaluator.is_empty() {
                                    // The evaluator is empty, so we should return to reading from
                                    // source.
                                    *state = ReadingFieldFromSource;
                                }
                                // We got another value from the macro we're evaluating. Emit
                                // it as another field using the same field_name.
                                return Some(Ok(FieldSource::NameValue(field_name, next_value)));
                            }
                            None => {
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

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::{v1_1, Element, MacroExprKind, Reader};

        #[test]
        fn field_kinds() -> IonResult<()> {
            let source = r#"
                $ion_1_1
                (:add_macros
                    (macro three_values ()
                        (.values 1 2 3)
                    )
                    (macro three_structs ()
                        (.values {dog: 1} {cat: 2} {mouse: 3})
                    )
                )
                {
                    foo: 0,
                    bar: (:three_values),
                    (:three_structs),
                    quux: true,
                }
            "#;
            let mut reader = Reader::new(v1_1::Text, source)?;
            let struct_ = reader.expect_next()?.read()?.expect_struct()?;
            let fields = &mut struct_.expanded_struct.field_source_iter();

            fn expect_name_value<'top, D: Decoder>(
                fields: &mut impl Iterator<Item = IonResult<FieldSource<'top, D>>>,
                expected_name: &str,
                expected_value: impl Into<Element>,
            ) -> IonResult<()> {
                let field = fields.next().unwrap()?;
                let expected_value = expected_value.into();
                assert!(
                    matches!(
                        field,
                        FieldSource::NameValue(name, value)
                            if name.read()?.text() == Some(expected_name)
                            && Element::try_from(value.read_resolved()?)? == expected_value,
                    ),
                    "{field:?} did not match name={expected_name:?}, value={expected_value:?}"
                );
                Ok(())
            }

            expect_name_value(fields, "foo", 0)?;
            assert!(matches!(
                fields.next().unwrap()?,
                FieldSource::NameMacro(name, invocation)
                    if name.read()?.text() == Some("bar") && matches!(invocation.kind(), MacroExprKind::EExp(eexp) if eexp.invoked_macro.name() == Some("three_values"))
            ));
            expect_name_value(fields, "bar", 1)?;
            expect_name_value(fields, "bar", 2)?;
            expect_name_value(fields, "bar", 3)?;
            assert!(matches!(
                fields.next().unwrap()?,
                FieldSource::Macro(invocation)
                    if matches!(invocation.kind(), MacroExprKind::EExp(eexp) if eexp.invoked_macro.name() == Some("three_structs"))
            ));
            expect_name_value(fields, "dog", 1)?;
            expect_name_value(fields, "cat", 2)?;
            expect_name_value(fields, "mouse", 3)?;
            expect_name_value(fields, "quux", true)?;
            assert!(fields.next().is_none());
            Ok(())
        }
    }
}
