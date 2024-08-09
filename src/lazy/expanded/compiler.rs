//! Compiles template definition language (TDL) expressions into a form suitable for fast incremental
//! evaluation.
use std::ops::Range;

use rustc_hash::FxHashMap;

use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::template::{
    ExprRange, MacroSignature, Parameter, ParameterCardinality, ParameterEncoding,
    RestSyntaxPolicy, TemplateBody, TemplateBodyElement, TemplateBodyExpr, TemplateMacro,
    TemplateStructIndex, TemplateValue,
};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::value::LazyValue;
use crate::lazy::value_ref::ValueRef;
use crate::result::IonFailure;
use crate::symbol_ref::AsSymbolRef;
use crate::{v1_1, IonError, IonResult, IonType, Reader, SymbolRef};

/// Information inferred about a template's expansion at compile time.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ExpansionAnalysis {
    pub(crate) could_produce_system_value: bool,
    pub(crate) must_produce_exactly_one_value: bool,
    // A memoized combination of the above flags.
    pub(crate) can_be_lazily_evaluated_at_top_level: bool,
    pub(crate) expansion_singleton: Option<ExpansionSingleton>,
}

impl ExpansionAnalysis {
    pub fn could_produce_system_value(&self) -> bool {
        self.could_produce_system_value
    }

    pub fn must_produce_exactly_one_value(&self) -> bool {
        self.must_produce_exactly_one_value
    }

    pub fn can_be_lazily_evaluated_at_top_level(&self) -> bool {
        self.can_be_lazily_evaluated_at_top_level
    }

    pub fn expansion_singleton(&self) -> Option<ExpansionSingleton> {
        self.expansion_singleton
    }
}

/// When static analysis can detect that a template body will always expand to a single value,
/// information inferred about that value is stored in this type. When this template backs a
/// lazy value, having these fields available allows the lazy value to answer basic queries without
/// needing to fully evaluate the template.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ExpansionSingleton {
    pub(crate) is_null: bool,
    pub(crate) ion_type: IonType,
    pub(crate) num_annotations: u8,
}

impl ExpansionSingleton {
    pub fn is_null(&self) -> bool {
        self.is_null
    }

    pub fn ion_type(&self) -> IonType {
        self.ion_type
    }

    pub fn has_annotations(&self) -> bool {
        self.num_annotations > 0
    }

    pub fn num_annotations(&self) -> usize {
        self.num_annotations as usize
    }
}

/// Validates a given TDL expression and compiles it into a `TemplateMacro` that can be added
/// to a [`MacroTable`](crate::lazy::expanded::macro_table::MacroTable).
pub struct TemplateCompiler {}

impl TemplateCompiler {
    /// Takes a TDL expression in the form:
    /// ```ion_1_1
    ///     (macro name (param1 param2 [...] paramN) body)
    /// ```
    /// and compiles it into a [`TemplateMacro`].
    ///
    /// The [`TemplateMacro`] stores a sequence of [`TemplateBodyExpr`]s that need to be evaluated
    /// in turn. Each step is either a value literal, a reference to one of the parameters (that is:
    /// a variable), or a macro invocation.
    ///
    /// A `TemplateBodyExpr` can be made up of more than one expression. Each `TemplateBodyExpr`
    /// stores the number of expressions that it includes. For example, scalar value
    /// literals are always a single expression and so will have `num_expressions=1`. However,
    /// container value literals can have nested expressions, and macro invocations can take
    /// expressions as arguments; in both these cases, `num_expressions` can be `1` or higher.
    /// This arrangement--expressions storing their composite expression count--enables the reader
    /// to skip the entire parent expression as desired. For example, in this macro:
    ///
    /// ```ion_1_1
    /// (macro foo ()
    ///                  // Template body expressions
    ///     [            // #0, num_expressions=5, range=0..5
    ///         1,       // #1, num_expressions=1, range=1..2
    ///         (values  // #2, num_expressions=3, range=2..5
    ///             2    // #3, num_expressions=1, range=3..4
    ///             3    // #4, num_expressions=1, range=4..5
    ///         )
    ///     ]
    /// )
    /// ```
    ///
    /// the step corresponding to `(values 2 3)` would store the range `2..5`, indicating that
    /// it includes not only template body expression #2, but #3 and #4 as well. A reader wishing to
    /// skip that call to `values` could do so by moving ahead to expression number `5`. The outer
    /// list (`[1, (values 2 3)]`) would store a `0..5`, indicating that it contains the `1`,
    /// the macro invocation `values`, and the two arguments that belong to `values`.
    ///
    /// The compiler recognizes the `(literal expr1 expr2 [...] exprN)` form, adding each subexpression
    /// to the template without interpretation. `(literal ...)` does not appear in the compiled
    /// template as there is nothing more for it to do at expansion time.
    pub fn compile_from_text(
        context: EncodingContextRef,
        expression: &str,
    ) -> IonResult<TemplateMacro> {
        // TODO: This is a rudimentary implementation that panics instead of performing thorough
        //       validation. Where it does surface errors, the messages are too terse.
        let mut reader = Reader::new(v1_1::Text, expression.as_bytes())?;
        let macro_def_sexp = reader.expect_next()?.read()?.expect_sexp()?;

        Self::compile_from_sexp(context, macro_def_sexp)
    }

    /// Pulls the next value from the provided source and confirms that it is a symbol whose
    /// text matches the `keyword` string.
    fn expect_keyword<'a, Encoding: Decoder>(
        keyword: &str,
        source: &mut impl Iterator<Item = IonResult<LazyValue<'a, Encoding>>>,
    ) -> IonResult<()> {
        let value = match source.next() {
            None => {
                return IonResult::decoding_error(format!(
                    "expected keyword '{keyword}', but found nothing"
                ))
            }
            Some(Err(e)) => {
                return IonResult::decoding_error(format!(
                    "expected keyword '{keyword}', but encountered an error: {e:?}"
                ))
            }
            Some(Ok(value)) => value,
        };
        match value.read()? {
            ValueRef::Symbol(s) if s.text() == Some(keyword) => Ok(()),
            value_ref => IonResult::decoding_error(format!(
                "expected keyword '{keyword}', but found {value_ref:?}"
            )),
        }
    }

    /// Confirms that the provided `value` is a symbol with known text. If so, returns `Ok(text)`.
    /// If not, returns a decoding error containing the specified label.
    fn expect_symbol_text<'a, Encoding: Decoder>(
        label: &str,
        value: LazyValue<'a, Encoding>,
    ) -> IonResult<&'a str> {
        match value.read()? {
            ValueRef::Symbol(s) => {
                if let Some(text) = s.text() {
                    Ok(text)
                } else {
                    IonResult::decoding_error(format!(
                        "expected {label}, but found a symbol with no text"
                    ))
                }
            }
            value_ref => {
                IonResult::decoding_error(format!("expected {label}, but found a(n) {value_ref:?}"))
            }
        }
    }

    /// Confirms that the provided `value` is a symbol with known text. If so, returns `Ok(text)`.
    /// If not, returns a decoding error containing the specified label.
    fn expect_symbol<'a, Encoding: Decoder>(
        label: &str,
        source: &mut impl Iterator<Item = IonResult<LazyValue<'a, Encoding>>>,
    ) -> IonResult<LazyValue<'a, Encoding>> {
        match source.next() {
            None => IonResult::decoding_error(format!("expected {label} but found nothing")),
            Some(Ok(value)) if value.ion_type() == IonType::Symbol => Ok(value),
            Some(Ok(value)) => IonResult::decoding_error(format!(
                "expected {label} but found {}",
                value.ion_type()
            )),
            Some(Err(e)) => IonResult::decoding_error(format!(
                "expected {label} but encountered an error: {e:?}"
            )),
        }
    }

    /// Tries to pull the next `LazyValue` from the provided iterator. If the iterator is empty,
    /// returns a `IonError::Decoding` that includes the specified label.
    fn expect_next<'a, Encoding: Decoder>(
        label: &str,
        source: &mut impl Iterator<Item = IonResult<LazyValue<'a, Encoding>>>,
    ) -> IonResult<LazyValue<'a, Encoding>> {
        match source.next() {
            None => IonResult::decoding_error(format!("expected {label} but found nothing")),
            Some(Err(e)) => IonResult::decoding_error(format!(
                "expected {label} but encountered an error: {e:?}"
            )),
            Some(Ok(value)) => Ok(value),
        }
    }

    /// Tries to pull the next `LazyValue` from the provided iterator, confirming that it is
    /// a symbol with text.
    fn expect_name<'a, Encoding: Decoder>(
        label: &str,
        source: &mut impl Iterator<Item = IonResult<LazyValue<'a, Encoding>>>,
    ) -> IonResult<&'a str> {
        let value = Self::expect_next(label, source)?;
        Self::expect_symbol_text(label, value)
    }

    /// Tries to pull the next `LazyValue` from the provided iterator, confirming that it is
    /// either a symbol with text, `null`, or `null.symbol`.
    fn expect_nullable_name<'a, Encoding: Decoder>(
        label: &str,
        source: &mut impl Iterator<Item = IonResult<LazyValue<'a, Encoding>>>,
    ) -> IonResult<Option<&'a str>> {
        let value = Self::expect_next(label, source)?;
        if value.is_null() && matches!(value.ion_type(), IonType::Null | IonType::Symbol) {
            Ok(None)
        } else {
            Ok(Some(Self::expect_symbol_text(label, value)?))
        }
    }

    /// Tries to pull the next `LazyValue` from the provided iterator, confirming that it is
    /// an s-expression.
    fn expect_sexp<'a, Encoding: Decoder>(
        label: &str,
        source: &mut impl Iterator<Item = IonResult<LazyValue<'a, Encoding>>>,
    ) -> IonResult<LazySExp<'a, Encoding>> {
        let value = Self::expect_next(label, source)?;
        match value.read()? {
            ValueRef::SExp(clause) => Ok(clause),
            other => {
                IonResult::decoding_error(format!("expected {label}, but found a(n) {other:?}"))
            }
        }
    }

    fn encoding_for<Encoding: Decoder>(value: LazyValue<Encoding>) -> IonResult<ParameterEncoding> {
        match value.annotations().next() {
            None => Ok(ParameterEncoding::Tagged),
            Some(Ok(text)) => match text.expect_text()? {
                "flex_uint" => Ok(ParameterEncoding::FlexUInt),
                other => IonResult::decoding_error(format!(
                    "unsupported encoding '{other}' specified for parameter"
                )),
            },
            Some(Err(e)) => IonResult::decoding_error(format!(
                "error occurred while parsing annotations for parameter: {e:?}"
            )),
        }
    }

    pub fn compile_from_sexp<'a, Encoding: Decoder>(
        context: EncodingContextRef<'a>,
        macro_def_sexp: LazySExp<'a, Encoding>,
    ) -> Result<TemplateMacro, IonError> {
        let mut values = macro_def_sexp.iter();

        Self::expect_keyword("macro", &mut values)?;

        // TODO: Enforce 'identifier' syntax subset of symbol
        // TODO: Syntactic support for address IDs like `(14 ...)`
        let template_name =
            Self::expect_nullable_name("a macro name", &mut values)?.map(|name| name.to_owned());

        // The `params` clause of the macro definition is an s-expression enumerating the parameters
        // that the macro accepts. For example: `(flex_uint::x, y*, z?)`.
        let params_clause = Self::expect_sexp("an s-expression defining parameters", &mut values)?;

        let mut compiled_params = Vec::new();
        // `param_items` is a peekable iterator over the Ion values in `params_clause`. Because it
        // is peekable, we can look ahead at each step to see if there are more values. This is
        // important because:
        //   * when adding a parameter, we need to look ahead to see if the next token is a
        //     cardinality modifier.
        //   * special syntax rules apply to `*` and `+` parameters in tail position.
        let mut param_items = params_clause.iter().peekable();

        let mut is_final_parameter = false;
        while let Some(item) = param_items.next().transpose()? {
            is_final_parameter |= param_items.peek().is_none();
            let name = Self::expect_symbol_text("a parameter name", item)?.to_owned();
            let parameter_encoding = Self::encoding_for(item)?;

            use ParameterCardinality::*;
            let mut cardinality = ExactlyOne;
            if let Some(next_item_result) = param_items.peek() {
                let next_item = match next_item_result {
                    Ok(item_ref) => *item_ref,
                    // Because we are borrowing the peek()ed result, we must clone the error
                    Err(e) => return Err(e.clone()),
                };
                let text = Self::expect_symbol_text("a cardinality modifier", next_item)?;
                cardinality = match text {
                    "!" => ExactlyOne,
                    "?" => ZeroOrOne,
                    "*" => ZeroOrMore,
                    "+" => OneOrMore,
                    // The next item doesn't appear to be a cardinality specifier, it's probably a parameter.
                    // Finish processing this parameter, then move on to the next item.
                    _ => {
                        // We know there are more items in the signature, so this isn't the last parameter.
                        // Therefore, rest syntax is not allowed.
                        let compiled_param = Parameter::new(
                            name,
                            parameter_encoding,
                            cardinality,
                            RestSyntaxPolicy::NotAllowed,
                        );
                        compiled_params.push(compiled_param);
                        continue;
                    }
                };
                // If we reach this point, the item was a cardinality specifier and we're done
                // processing it. We can discard the item and continue on to the next parameter.
                let _cardinality_specifier = param_items.next().unwrap();
                is_final_parameter |= param_items.peek().is_none();
            }

            let rest_syntax_policy = if is_final_parameter && cardinality != ExactlyOne {
                RestSyntaxPolicy::Allowed
            } else {
                RestSyntaxPolicy::NotAllowed
            };

            let compiled_param =
                Parameter::new(name, parameter_encoding, cardinality, rest_syntax_policy);
            compiled_params.push(compiled_param);
        }
        let signature = MacroSignature::new(compiled_params)?;
        let body = Self::expect_next("the template body", &mut values)?;
        let expansion_analysis = Self::analyze_body_expr(body)?;
        let mut compiled_body = TemplateBody {
            expressions: Vec::new(),
            annotations_storage: Vec::new(),
        };
        Self::compile_value(
            context,
            &signature,
            &mut compiled_body,
            /*is_literal=*/ false,
            body,
        )?;
        let template_macro = TemplateMacro {
            name: template_name,
            signature,
            body: compiled_body,
            expansion_analysis,
        };
        Ok(template_macro)
    }

    /// The entry point for static analysis of a template body expression.
    fn analyze_body_expr<D: Decoder>(body_expr: LazyValue<D>) -> IonResult<ExpansionAnalysis> {
        let could_produce_system_value = Self::body_expr_could_produce_system_values(body_expr);
        let must_produce_exactly_one_value =
            Self::body_expr_must_produce_exactly_one_value(body_expr);
        let num_annotations = u8::try_from(body_expr.annotations().count()).map_err(|_| {
            IonError::decoding_error("template body expression can only have up to 255 annotations")
        })?;
        let expansion_singleton = if must_produce_exactly_one_value {
            Some(ExpansionSingleton {
                ion_type: body_expr.ion_type(),
                num_annotations,
                is_null: body_expr.is_null(),
            })
        } else {
            None
        };
        Ok(ExpansionAnalysis {
            could_produce_system_value,
            must_produce_exactly_one_value,
            can_be_lazily_evaluated_at_top_level: must_produce_exactly_one_value
                && !could_produce_system_value,
            expansion_singleton,
        })
    }

    /// Indicates whether the provided expression *could* produce a system value (e.g. a symbol table
    /// or encoding directive) when expanded.
    ///
    /// If the expression is guaranteed to never produce a system value, returns `false`.
    /// If the expression *could* produce one, returns `true`.
    ///
    /// For the time being, this is a simple, lightweight heuristic.
    fn body_expr_could_produce_system_values<D: Decoder>(body_expr: LazyValue<D>) -> bool {
        use IonType::*;
        match body_expr.ion_type() {
            // If the expression is an s-expression, it could expand to anything. If desired, we could
            // inspect the macro it invokes to see if it's a `literal`, `make_string`, `make_struct`, etc.
            // For now, we simply say "Producing a system value is possible."
            SExp => true,
            // If the value is a struct, it would need to be annotated with `$ion_symbol_table`
            // to produce a system value.
            Struct => {
                matches!(body_expr.annotations().next(), Some(Ok(s)) if s.text() == Some("$ion_symbol_table"))
            }
            _ => false,
        }
    }

    /// Indicates whether the provided expression is guaranteed to produce exactly one Ion value
    /// when expanded.
    ///
    /// If the expression will always produce a single value, returns `true`.
    /// If the expression could potentially produce an empty stream or a stream with multiple
    /// values, returns `false`.
    fn body_expr_must_produce_exactly_one_value<D: Decoder>(body_expr: LazyValue<D>) -> bool {
        body_expr.ion_type() != IonType::SExp
    }

    /// Recursively visits all of the expressions in `lazy_value` and adds their corresponding
    /// [`TemplateBodyExpr`] sequences to the `TemplateBody`.
    ///
    /// If `is_literal` is true, nested symbols and s-expressions will not be interpreted.
    fn compile_value<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_literal: bool,
        lazy_value: LazyValue<'top, D>,
    ) -> IonResult<()> {
        // Add the value's annotations to the annotations storage vec and take note of the
        // vec range that belongs to this value.
        let annotations_range_start = definition.annotations_storage.len();
        for annotation_result in lazy_value.annotations() {
            let annotation = annotation_result?;
            definition.annotations_storage.push(annotation.to_owned());
        }
        let annotations_range_end = definition.annotations_storage.len();
        let annotations_range = annotations_range_start..annotations_range_end;

        // Make a `TemplateValue` that represent's the value's unannotated data. Scalar `TemplateValue`s
        // are very similar to their scalar `Value` counterparts, but its container types are more
        // barebones.
        let value = match lazy_value.read()? {
            ValueRef::Null(ion_type) => TemplateValue::Null(ion_type),
            ValueRef::Bool(b) => TemplateValue::Bool(b),
            ValueRef::Int(i) => TemplateValue::Int(i),
            ValueRef::Float(f) => TemplateValue::Float(f),
            ValueRef::Decimal(d) => TemplateValue::Decimal(d),
            ValueRef::Timestamp(t) => TemplateValue::Timestamp(t),
            ValueRef::String(s) => TemplateValue::String(s.to_owned()),
            ValueRef::Symbol(s) if is_literal => TemplateValue::Symbol(s.to_owned()),
            ValueRef::Symbol(s) => {
                return Self::compile_variable_reference(
                    context,
                    signature,
                    definition,
                    annotations_range,
                    s,
                )
            }
            ValueRef::Blob(b) => TemplateValue::Blob(b.to_owned()),
            ValueRef::Clob(c) => TemplateValue::Clob(c.to_owned()),
            // For the container types, compile the value's nested values/fields and take note
            // of the total number of expressions that belong to this container.
            ValueRef::SExp(s) => {
                return Self::compile_sexp(
                    context,
                    signature,
                    definition,
                    is_literal,
                    annotations_range.clone(),
                    s,
                );
            }
            ValueRef::List(l) => {
                return Self::compile_list(
                    context,
                    signature,
                    definition,
                    is_literal,
                    annotations_range.clone(),
                    l,
                )
            }
            ValueRef::Struct(s) => {
                return Self::compile_struct(
                    context,
                    signature,
                    definition,
                    is_literal,
                    annotations_range.clone(),
                    s,
                )
            }
        };
        // At this point, we're only looking at scalars.
        let scalar_expr_index = definition.expressions().len();
        definition.push_element(
            TemplateBodyElement::with_value(value).with_annotations(annotations_range),
            // Scalars are always a single expression.
            ExprRange::new(scalar_expr_index..scalar_expr_index + 1),
        );
        Ok(())
    }

    /// Helper method for visiting all of the child expressions in a list.
    fn compile_list<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_literal: bool,
        annotations_range: Range<usize>,
        lazy_list: LazyList<'top, D>,
    ) -> IonResult<()> {
        let list_element_index = definition.expressions.len();
        let list_element = TemplateBodyElement::with_value(TemplateValue::List);
        // Use an empty range for now. When we finish reading the list, we'll overwrite the empty
        // range with the correct one.
        definition.push_element(list_element, ExprRange::empty());
        for value_result in &lazy_list {
            let value = value_result?;
            Self::compile_value(context, signature, definition, is_literal, value)?;
        }
        let list_children_end = definition.expressions.len();
        // Update the list entry to reflect the number of child expressions it contains
        let list_element = TemplateBodyElement::with_value(TemplateValue::List)
            .with_annotations(annotations_range);
        let list_expr_range = ExprRange::new(list_element_index..list_children_end);
        definition.expressions[list_element_index] =
            TemplateBodyExpr::element(list_element, list_expr_range);
        Ok(())
    }

    /// Helper method for visiting all of the child expressions in a sexp.
    fn compile_sexp<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_literal: bool,
        annotations_range: Range<usize>,
        lazy_sexp: LazySExp<'top, D>,
    ) -> IonResult<()> {
        if is_literal {
            // If `is_literal` is true, this s-expression is nested somewhere inside a `(literal ...)`
            // macro invocation. The sexp and its child expressions can be added to the TemplateBody
            // without interpretation.
            Self::compile_quoted_sexp(context, signature, definition, annotations_range, lazy_sexp)
        } else {
            // If `is_quoted` is false, the sexp is a macro invocation.
            // First, verify that it doesn't have annotations.
            if !annotations_range.is_empty() {
                return IonResult::decoding_error("found annotations on a macro invocation");
            }
            // Peek at the first expression in the sexp. If it's the symbol `literal`...
            if Self::sexp_is_literal_macro(&lazy_sexp)? {
                // ...then we set `is_quoted` to true and compile all of its child expressions.
                Self::compile_quoted_elements(context, signature, definition, lazy_sexp)
            } else {
                // Otherwise, add the macro invocation to the template body.
                Self::compile_macro(context, signature, definition, lazy_sexp)
            }
        }?;

        Ok(())
    }

    /// Adds a `lazy_sexp` that has been determined to represent a macro invocation to the
    /// TemplateBody.
    fn compile_macro<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        lazy_sexp: LazySExp<'top, D>,
    ) -> IonResult<()> {
        let mut expressions = lazy_sexp.iter();
        // Convert the macro ID (name or address) into an address. If this refers to a macro that
        // doesn't exist yet, this will return an error. This prevents recursion.
        // TODO: Consider storing the name of the invoked target macro in the host's definition
        //       as debug information. The name cannot be stored directly on the
        //       TemplateBodyMacroInvocation as that would prevent the type from being `Copy`.
        let (_maybe_name, macro_address) =
            Self::name_and_address_from_id_expr(context, expressions.next())?;
        let macro_step_index = definition.expressions.len();
        // Assume the macro contains zero argument expressions to start, we'll update
        // this at the end of the function.
        definition.push_macro_invocation(macro_address, ExprRange::empty());
        for argument_result in expressions {
            let argument = argument_result?;
            Self::compile_value(
                context, signature, definition, /*is_quoted=*/ false, argument,
            )?;
        }
        let arguments_end = definition.expressions.len();
        // Update the macro step to reflect the macro's address and number of child expressions it
        // contains
        let invocation_expr_range = ExprRange::new(macro_step_index..arguments_end);
        definition.expressions[macro_step_index] =
            TemplateBodyExpr::macro_invocation(macro_address, invocation_expr_range);
        Ok(())
    }

    /// Given a `LazyValue` that represents a macro ID (name or address), attempts to resolve the
    /// ID to a macro address.
    fn name_and_address_from_id_expr<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        id_expr: Option<IonResult<LazyValue<'top, D>>>,
    ) -> IonResult<(Option<String>, usize)> {
        match id_expr {
            None => IonResult::decoding_error("found an empty s-expression in an unquoted context"),
            Some(Err(e)) => Err(e),
            Some(Ok(value)) => match value.read()? {
                ValueRef::Symbol(s) => {
                    if let Some(name) = s.text() {
                        let address =
                            context.macro_table.address_for_name(name).ok_or_else(|| {
                                IonError::decoding_error(format!("unrecognized macro name: {name}"))
                            })?;
                        Ok((Some(name.to_string()), address))
                    } else {
                        IonResult::decoding_error("macro names must be an identifier")
                    }
                }
                ValueRef::Int(int) => {
                    let address = usize::try_from(int.expect_i64()?).map_err(|_| {
                        IonError::decoding_error(format!("found an invalid macro address: {int}"))
                    })?;
                    if context.macro_table.macro_at_address(address).is_none() {
                        IonResult::decoding_error(format!(
                            "invocation of invalid macro address {address}"
                        ))
                    } else {
                        Ok((None, address))
                    }
                }
                other => IonResult::decoding_error(format!(
                    "expected a macro name (symbol) or address (int), but found: {other:?}"
                )),
            },
        }
    }

    /// Visits all of the child expressions of `lazy_sexp`, adding them to the `TemplateBody`
    /// without interpretation. `lazy_sexp` itself is the `quote` macro, and does not get added
    /// to the template body as there is nothing more for it to do at evaluation time.
    fn compile_quoted_elements<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        lazy_sexp: LazySExp<'top, D>,
    ) -> IonResult<()> {
        let mut elements = lazy_sexp.iter();
        // If this method is called, we've already peeked at the first element to confirm that
        // it's the symbol `quote`. We can discard it.
        let _ = elements.next().unwrap()?;
        for element_result in elements {
            Self::compile_value(
                context,
                signature,
                definition,
                /*is_quoted=*/ true,
                element_result?,
            )?;
        }
        Ok(())
    }

    /// Adds `lazy_sexp` to the template body without interpretation.
    fn compile_quoted_sexp<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        annotations_range: Range<usize>,
        lazy_sexp: LazySExp<'top, D>,
    ) -> IonResult<()> {
        let sexp_element_index = definition.expressions.len();
        let sexp_element = TemplateBodyElement::with_value(TemplateValue::SExp);
        // Use an empty range for now; we'll overwrite it with the correct one later.
        definition.push_element(sexp_element, ExprRange::empty());
        for value_result in &lazy_sexp {
            let value = value_result?;
            Self::compile_value(
                context, signature, definition, /*is_quoted=*/ true, value,
            )?;
        }
        let sexp_children_end = definition.expressions.len();
        let sexp_element = TemplateBodyElement::with_value(TemplateValue::SExp)
            .with_annotations(annotations_range);
        let sexp_expr_range = ExprRange::new(sexp_element_index..sexp_children_end);
        // Update the sexp entry to reflect the number of child expressions it contains
        definition.expressions[sexp_element_index] =
            TemplateBodyExpr::element(sexp_element, sexp_expr_range);
        Ok(())
    }

    /// Returns `Ok(true)` if the first child value in the `LazySexp` is the symbol `literal`.
    /// This method should only be called in a non-literal context.
    fn sexp_is_literal_macro<D: Decoder>(sexp: &LazySExp<D>) -> IonResult<bool> {
        let first_expr = sexp.iter().next();
        match first_expr {
            // If the sexp is empty and we're not in a literal context, that's an error.
            None => {
                IonResult::decoding_error("found an empty s-expression in a non-literal context")
            }
            Some(Err(e)) => Err(e),
            Some(Ok(lazy_value)) => {
                let value = lazy_value.read()?;
                Ok(value == ValueRef::Symbol("literal".as_symbol_ref()))
            }
        }
    }

    /// Recursively adds all of the expressions in `lazy_struct` to the `TemplateBody`.
    fn compile_struct<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_literal: bool,
        annotations_range: Range<usize>,
        lazy_struct: LazyStruct<'top, D>,
    ) -> IonResult<()> {
        let struct_element_index = definition.expressions.len();
        let struct_element = TemplateBodyElement::with_value(TemplateValue::Struct(
            // Creating a new HashMap does not allocate; we'll overwrite this value with an
            // actual map of field names to indexes at the end of the method.
            FxHashMap::default(),
        ));
        // Use an empty range for now; we'll overwrite it with the correct range later.
        definition.push_element(struct_element, ExprRange::empty());

        let mut fields: TemplateStructIndex = FxHashMap::default();
        for field_result in &lazy_struct {
            let field = field_result?;
            let name = field.name()?.to_owned();
            let name_expr_index = definition.expressions().len();
            let name_element = TemplateBodyElement::with_value(TemplateValue::Symbol(name.clone()));
            let name_expr_range = ExprRange::new(name_expr_index..name_expr_index + 1);
            definition.push_element(name_element, name_expr_range);
            // If this field name has defined text (which is everything besides `$0` and equivalents),
            // add that text to the fields map. Future queries for `$0` will require a linear scan,
            // but that's a niche use case. If there is call for it, this approach can be revised.
            if let Some(text) = name.text() {
                let value_expr_address = definition.expressions.len();
                match fields.get_mut(text) {
                    Some(value_expr_addresses) => value_expr_addresses.push(value_expr_address),
                    None => {
                        let _ = fields.insert(name.clone(), vec![value_expr_address]);
                    }
                }
            }

            Self::compile_value(context, signature, definition, is_literal, field.value())?;
        }
        let struct_end = definition.expressions.len();
        // Update the struct entry to reflect the range of expansion steps it contains.
        let struct_element = TemplateBodyElement::with_value(TemplateValue::Struct(fields))
            .with_annotations(annotations_range);
        let struct_expr_range = ExprRange::new(struct_element_index..struct_end);
        definition.expressions[struct_element_index] =
            TemplateBodyExpr::element(struct_element, struct_expr_range);
        Ok(())
    }

    /// Resolves `variable` to a parameter in the macro signature and adds a corresponding
    /// `TemplateExpansionStep` to the `TemplateBody`.
    fn compile_variable_reference(
        _context: EncodingContextRef,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        annotations_range: Range<usize>,
        variable: SymbolRef,
    ) -> IonResult<()> {
        let name = variable.text().ok_or_else(|| {
            IonError::decoding_error("found variable whose name is unknown text ($0)")
        })?;
        if !annotations_range.is_empty() {
            return IonResult::decoding_error(format!(
                "found a variable reference '{name}' with annotations"
            ));
        }
        let signature_index = signature
            .parameters()
            .iter()
            .position(|p| p.name() == name)
            .ok_or_else(|| {
                IonError::decoding_error(format!("variable '{name}' is not recognized"))
            })?;
        if signature_index > u16::MAX as usize {
            return IonResult::decoding_error("this implementation supports up to 65K parameters");
        }
        definition.push_variable(signature_index as u16);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;

    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::template::{
        ExprRange, ParameterEncoding, TemplateBodyExpr, TemplateMacro, TemplateValue,
    };
    use crate::lazy::expanded::{EncodingContext, EncodingContextRef};
    use crate::{Int, IntoAnnotations, IonResult, Symbol};

    // This function only looks at the value portion of the TemplateElement. To compare annotations,
    // see the `expect_annotations` method.
    fn expect_value(
        definition: &TemplateMacro,
        index: usize,
        expected: TemplateValue,
    ) -> IonResult<()> {
        let actual = definition
            .body()
            .expressions()
            .get(index)
            .expect("no such expansion step")
            .kind()
            .require_element();
        assert_eq!(actual.value(), &expected);
        Ok(())
    }

    fn expect_macro(
        definition: &TemplateMacro,
        index: usize,
        expected_address: usize,
        expected_num_arguments: usize,
    ) -> IonResult<()> {
        expect_step(
            definition,
            index,
            TemplateBodyExpr::macro_invocation(
                expected_address,
                // First arg position to last arg position (exclusive)
                ExprRange::new(index..index + 1 + expected_num_arguments),
            ),
        )
    }

    fn expect_variable(
        definition: &TemplateMacro,
        index: usize,
        expected_signature_index: usize,
    ) -> IonResult<()> {
        expect_step(
            definition,
            index,
            TemplateBodyExpr::variable(
                expected_signature_index as u16,
                ExprRange::new(index..index + 1),
            ),
        )
    }

    fn expect_step(
        definition: &TemplateMacro,
        index: usize,
        expected: TemplateBodyExpr,
    ) -> IonResult<()> {
        let step = definition
            .body()
            .expressions()
            .get(index)
            .expect("no such expansion step");
        assert_eq!(step, &expected, "(actual, expected)");
        Ok(())
    }

    fn expect_annotations<A: IntoAnnotations>(
        definition: &TemplateMacro,
        index: usize,
        expected: A,
    ) {
        let element = definition
            .body
            .expressions()
            .get(index)
            .expect("requested index does not exist")
            .kind()
            .require_element();
        let actual_annotations = definition
            .body
            .annotations_storage()
            .get(element.annotations_range().ops_range())
            .expect("invalid annotations range")
            .into_annotations();
        let expected_annotations = expected.into_annotations();
        assert_eq!(actual_annotations, expected_annotations);
    }

    struct TestResources {
        context: EncodingContext,
    }

    impl TestResources {
        fn new() -> Self {
            Self {
                context: EncodingContext::empty(),
            }
        }

        fn context(&self) -> EncodingContextRef {
            self.context.get_ref()
        }
    }

    #[test]
    fn single_scalar() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = "(macro foo () 42)";

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "foo");
        assert_eq!(template.signature().len(), 0);
        expect_value(&template, 0, TemplateValue::Int(42.into()))?;
        Ok(())
    }

    #[test]
    fn single_list() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = "(macro foo () [1, 2, 3])";

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "foo");
        assert_eq!(template.signature().len(), 0);
        expect_value(&template, 0, TemplateValue::List)?;
        expect_value(&template, 1, TemplateValue::Int(1.into()))?;
        expect_value(&template, 2, TemplateValue::Int(2.into()))?;
        expect_value(&template, 3, TemplateValue::Int(3.into()))?;
        Ok(())
    }

    #[test]
    fn multiple_scalar() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = r#"(macro foo () (values 42 "hello" false))"#;

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "foo");
        assert_eq!(template.signature().len(), 0);
        expect_macro(
            &template,
            0,
            context.macro_table.address_for_name("values").unwrap(),
            3,
        )?;
        expect_value(&template, 1, TemplateValue::Int(42.into()))?;
        expect_value(&template, 2, TemplateValue::String("hello".into()))?;
        expect_value(&template, 3, TemplateValue::Bool(false))?;
        Ok(())
    }

    #[test]
    fn try_it() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = "(macro foo (x y z) [100, [200, a::b::300], x, {y: [true, false, z]}])";

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        expect_value(&template, 0, TemplateValue::List)?;
        expect_value(&template, 1, TemplateValue::Int(Int::from(100)))?;
        expect_value(&template, 2, TemplateValue::List)?;
        expect_value(&template, 3, TemplateValue::Int(Int::from(200)))?;
        expect_value(&template, 4, TemplateValue::Int(Int::from(300)))?;
        expect_annotations(&template, 4, ["a", "b"]);
        expect_variable(&template, 5, 0)?;
        let mut struct_index = FxHashMap::default();
        struct_index.insert(Symbol::from("y"), vec![8]);
        expect_value(&template, 6, TemplateValue::Struct(struct_index))?;
        expect_value(&template, 7, TemplateValue::Symbol(Symbol::from("y")))?;
        expect_value(&template, 8, TemplateValue::List)?;
        expect_value(&template, 9, TemplateValue::Bool(true))?;
        expect_value(&template, 10, TemplateValue::Bool(false))?;
        expect_variable(&template, 11, 2)?;
        Ok(())
    }

    #[test]
    fn identity_macro() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = "(macro identity (x) x)";

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "identity");
        assert_eq!(template.signature().len(), 1);
        expect_variable(&template, 0, 0)?;
        Ok(())
    }

    #[test]
    fn identity_with_flex_uint() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = "(macro identity (flex_uint::x) x)";

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "identity");
        assert_eq!(template.signature().len(), 1);
        assert_eq!(
            template
                .signature()
                .parameters()
                .first()
                .unwrap()
                .encoding(),
            ParameterEncoding::FlexUInt
        );
        expect_variable(&template, 0, 0)?;
        Ok(())
    }

    #[test]
    fn literal() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = r#"
            (macro foo (x)
                // Outer 'values' call allows multiple expressions in the body 
                (values
                    // This `values` is a macro call that has a single argument: the variable `x`
                    (values x)
                    // This `literal` call causes the inner `(values x)` to be an uninterpreted s-expression.
                    (literal
                        (values x))))
        "#;

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "foo");
        assert_eq!(template.signature().len(), 1);
        // Outer `values`
        expect_macro(
            &template,
            0,
            context.macro_table.address_for_name("values").unwrap(),
            5,
        )?;
        // First argument: `(values x)`
        expect_macro(
            &template,
            1,
            context.macro_table.address_for_name("values").unwrap(),
            1,
        )?;
        expect_variable(&template, 2, 0)?;
        // Second argument: `(literal (values x))`
        // Notice that the `literal` is not part of the compiled output, only its arguments
        expect_value(&template, 3, TemplateValue::SExp)?;
        expect_value(&template, 4, TemplateValue::Symbol("values".into()))?;
        expect_value(&template, 5, TemplateValue::Symbol("x".into()))?;

        Ok(())
    }
}
