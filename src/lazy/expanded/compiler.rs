//! Compiles template definition language (TDL) expressions into a form suitable for fast incremental
//! evaluation.
use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::template::{
    ExprRange, MacroSignature, Parameter, ParameterCardinality, ParameterEncoding,
    RestSyntaxPolicy, TemplateBody, TemplateBodyElement, TemplateBodyExpr, TemplateMacro,
    TemplateStructIndex, TemplateValue,
};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::sequence::{LazyList, LazySExp, SExpIterator};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::lazy::value::LazyValue;
use crate::lazy::value_ref::ValueRef;
use crate::result::IonFailure;
use crate::{v1_1, IonError, IonResult, IonType, Macro, MacroTable, Reader, Symbol, SymbolRef};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::ops::Range;
use std::rc::Rc;

/// Information inferred about a template's expansion at compile time.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ExpansionAnalysis {
    pub(crate) could_produce_system_value: bool,
    pub(crate) must_produce_exactly_one_value: bool,
    // A memoized combination of the above flags.
    pub(crate) can_be_lazily_evaluated_at_top_level: bool,
    pub(crate) expansion_singleton: Option<ExpansionSingleton>,
}

impl Default for ExpansionAnalysis {
    /// By default, macros are assumed to be capable of expanding to produce multiple values,
    /// any of which could be system values.
    fn default() -> Self {
        ExpansionAnalysis {
            could_produce_system_value: true,
            must_produce_exactly_one_value: false,
            can_be_lazily_evaluated_at_top_level: false,
            expansion_singleton: None,
        }
    }
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

/// When the [`TemplateCompiler`] is able to determine that a macro's template will always produce
/// exactly one value, that macro is considered a "singleton macro." Singleton macros offer
/// a few benefits:
///
/// * Because evaluation will produce be exactly one value, the reader can hand out a LazyValue
///   holding the e-expression as its backing data. Other macros cannot do this because if you're
///   holding a LazyValue and the macro later evaluates to 0 values or 100 values, there's not a way
///   for the application to handle those outcomes.
/// * Expanding a singleton macro doesn't require an evaluator with a stack because as soon as
///   you've gotten a value, you're done--no need to `pop()` and preserve state.
///
/// Information inferred about a singleton macro's output value is stored in an `ExpansionSingleton`.
/// When a singleton macro backs a lazy value, having these fields available allows the lazy value to
/// answer basic queries without needing to fully evaluate the template.
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

    pub fn annotations<'a>(&self, annotations_storage: &'a [Symbol]) -> SymbolsIterator<'a> {
        let annotations_range = 0..self.num_annotations();
        let annotations = &annotations_storage[annotations_range];
        SymbolsIterator::new(annotations)
    }
}

/// Validates a given TDL expression and compiles it into a `TemplateMacro` that can be added
/// to a [`MacroTable`].
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
        // TODO: This is a rudimentary implementation that surfaces terse errors.
        let mut reader = Reader::new(v1_1::Text, expression.as_bytes())?;
        let macro_def_sexp = reader.expect_next()?.read()?.expect_sexp()?;

        Self::compile_from_sexp(context, &MacroTable::empty(), macro_def_sexp)
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

    /// Interprets the annotations on the parameter name to determine its encoding.
    fn encoding_for<Encoding: Decoder>(
        context: EncodingContextRef,
        pending_macros: &MacroTable,
        parameter: LazyValue<Encoding>,
    ) -> IonResult<ParameterEncoding> {
        // * If the parameter has no annotations, it uses the default encoding.
        //   For example:
        //       foo
        // * If the parameter has one annotation, the annotation is the encoding name. This can be
        //   either a built-in encoding like `uint8` or a user-defined macro that takes at least
        //   one parameter of its own.
        //   For example:
        //          uint8::foo
        //        float32::foo
        //       my_macro::foo
        // * If the parameter has two annotations, the first annotation is the module name and the
        //   second is the name of an encoding in that module.
        //   For example:
        //               $ion::uint8::foo
        //             $ion::float32::foo
        //       my_module::my_macro::foo
        let mut annotations_iter = parameter.annotations();
        let annotation1 = match annotations_iter.next().transpose()? {
            // If there aren't any annotations, this parameter uses the default encoding: tagged.
            None => return Ok(ParameterEncoding::Tagged),
            // Otherwise, it's a module name or encoding name. We'll have to see if there's a
            // second annotation to know for certain. Either way, the annotation must have known text.
            Some(symbol) => symbol.expect_text()?,
        };
        let annotation2 = match annotations_iter.next().transpose()? {
            // If there's a second annotation, get its associated text.
            Some(symbol) => Some(symbol.expect_text()?),
            None => None,
        };

        // Make sure there isn't a third annotation.
        match annotations_iter.next() {
            // This is the expected case. Having more than 2 annotations is illegal.
            None => {}
            Some(Err(e)) => return Err(e),
            Some(Ok(annotation)) => {
                return IonResult::decoding_error(format!(
                    "found unexpected third annotation ('{:?}') on parameter",
                    annotation
                ))
            }
        };

        // If it's an unqualified name, look for the associated macro in the local scope.
        if let (encoding_name, None) = (annotation1, annotation2) {
            if let Some(macro_ref) =
                Self::resolve_unqualified_macro_id(context, pending_macros, encoding_name)
            {
                Self::validate_macro_shape_for_encoding(&macro_ref)?;
                return Ok(ParameterEncoding::MacroShaped(macro_ref));
            }
            // If it's not in the local scope, see if it's a built-in.
            return match encoding_name {
                "flex_uint" => Ok(ParameterEncoding::FlexUInt),
                _ => IonResult::decoding_error(format!(
                    "unrecognized encoding '{encoding_name}' specified for parameter"
                )),
            };
        };

        // At this point we know that we have a qualified name. Look it up in the active encoding
        // context.
        let (module_name, encoding_name) = (annotation1, annotation2.unwrap());
        let macro_ref = Self::resolve_qualified_macro_id(context, module_name, encoding_name)
            .ok_or_else(|| {
                IonError::decoding_error(format!(
                    "unrecognized encoding '{encoding_name}' specified for parameter"
                ))
            })?;
        Self::validate_macro_shape_for_encoding(&macro_ref)?;
        Ok(ParameterEncoding::MacroShaped(macro_ref))
    }

    /// Confirms that the selected macro is legal to use as a parameter encoding.
    pub fn validate_macro_shape_for_encoding(macro_ref: &Macro) -> IonResult<()> {
        if macro_ref.signature().len() == 0 {
            // This macro had to have a name to reach the validation step, so we can safely `unwrap()` it.
            return IonResult::decoding_error(format!(
                "macro '{}' cannot be used as an encoding because it takes no parameters",
                macro_ref.name().unwrap()
            ));
        }
        Ok(())
    }

    pub fn resolve_unqualified_macro_id<'a>(
        context: EncodingContextRef,
        pending_macros: &'a MacroTable,
        macro_id: impl Into<MacroIdRef<'a>>,
    ) -> Option<Rc<Macro>> {
        let macro_id = macro_id.into();
        // Since this ID is unqualified, it must be in either...
        // ...the local namespace, having just been defined...
        pending_macros
            .clone_macro_with_id(macro_id)
            // ...or in the active encoding environment.
            .or_else(|| context.macro_table().clone_macro_with_id(macro_id))
    }

    pub fn resolve_qualified_macro_id<'a>(
        context: EncodingContextRef,
        module_name: &'a str,
        macro_id: impl Into<MacroIdRef<'a>>,
    ) -> Option<Rc<Macro>> {
        let macro_id = macro_id.into();
        match module_name {
            // If the module is `$ion`, this refers to the system module.
            "$ion" => context
                .system_module
                .macro_table()
                .clone_macro_with_id(macro_id),
            // If the module is `$ion_encoding`, this refers to the active encoding module.
            "$ion_encoding" => context.macro_table().clone_macro_with_id(macro_id),
            _ => todo!(
                "qualified references to modules other than $ion_encoding (found {module_name}"
            ),
        }
    }

    pub fn compile_from_sexp<'a: 'b, 'b, Encoding: Decoder>(
        context: EncodingContextRef<'a>,
        pending_macros: &'b MacroTable,
        macro_def_sexp: LazySExp<'a, Encoding>,
    ) -> Result<TemplateMacro, IonError> {
        let mut values = macro_def_sexp.iter();

        Self::expect_keyword("macro", &mut values)?;

        // TODO: Enforce 'identifier' syntax subset of symbol
        let template_name =
            Self::expect_nullable_name("a macro name", &mut values)?.map(|name| name.into());

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
            let parameter_encoding = Self::encoding_for(context, pending_macros, item)?;

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
        // Information that will be propagated to each subexpression
        let tdl_context = TdlContext {
            context,
            pending_macros,
            signature: &signature,
        };
        Self::compile_value(
            tdl_context,
            &mut compiled_body,
            /*is_literal=*/ false,
            /*target_parameter=*/ None, /*; this is not a macro invocation arg.*/
            body,
        )?;
        // Make sure there aren't any unexpected expressions following the body.
        match values.next() {
            None => {}
            Some(expr) => {
                let name = template_name.unwrap_or_else(|| "<anonymous>".into());
                return IonResult::decoding_error(format!(
                    "found unexpected expression following the body of macro '{name}': {:?}",
                    expr?
                ));
            }
        }
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
    ///
    /// If this value is being passed to a macro as an argument, `target_parameter` will be the
    /// parameter to which the argument corresponds.
    fn compile_value<D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        is_literal: bool,
        target_parameter: Option<&Parameter>,
        lazy_value: LazyValue<D>,
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

        // Make a `TemplateValue` that represents the value's unannotated data. Scalar `TemplateValue`s
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
                    tdl_context,
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
                    tdl_context,
                    definition,
                    is_literal,
                    target_parameter,
                    annotations_range.clone(),
                    s,
                );
            }
            ValueRef::List(l) => {
                return Self::compile_list(
                    tdl_context,
                    definition,
                    is_literal,
                    annotations_range.clone(),
                    l,
                )
            }
            ValueRef::Struct(s) => {
                return Self::compile_struct(
                    tdl_context,
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
    fn compile_list<D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        is_literal: bool,
        annotations_range: Range<usize>,
        lazy_list: LazyList<D>,
    ) -> IonResult<()> {
        let list_element_index = definition.expressions.len();
        let list_element = TemplateBodyElement::with_value(TemplateValue::List);
        // Use an empty range for now. When we finish reading the list, we'll overwrite the empty
        // range with the correct one.
        definition.push_element(list_element, ExprRange::empty());
        for value_result in &lazy_list {
            let value = value_result?;
            Self::compile_value(
                tdl_context,
                definition,
                is_literal,
                None, /*<-- target_parameter; this is a list element, not a macro arg.*/
                value,
            )?;
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
    ///
    /// If this sexp appears in macro argument position, `target_parameter` will be a reference to
    /// the `Parameter` to which this sexp is being passed as an argument. If the sexp is an
    /// arg expression group, the `Parameter` will be consulted to make sure that variadics
    /// are legal.
    fn compile_sexp<D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        is_literal: bool,
        target_parameter: Option<&Parameter>,
        annotations_range: Range<usize>,
        lazy_sexp: LazySExp<D>,
    ) -> IonResult<()> {
        // First, verify that it doesn't have annotations.
        if !annotations_range.is_empty() {
            return IonResult::decoding_error("found annotations on a macro invocation");
        }
        // See if we should interpret this s-expression or leave it as-is.
        if is_literal {
            // If `is_literal` is true, this s-expression is nested somewhere inside a `(literal ...)`
            // macro invocation. The sexp and its child expressions can be added to the TemplateBody
            // without interpretation.
            return Self::compile_quoted_sexp(
                tdl_context,
                definition,
                annotations_range,
                lazy_sexp,
            );
        }

        // If `is_literal` is false, we need to interpret this s-expression. Peek at the first
        // child expression.
        match TdlSExpKind::of(tdl_context, lazy_sexp, target_parameter)? {
            // If it's the symbol `literal`...
            TdlSExpKind::Literal(arguments) => {
                // ...then we set `is_quoted` to true and compile all of its child expressions.
                Self::compile_literal_elements(tdl_context, definition, arguments)
            }
            // If it's a macro ID...
            TdlSExpKind::MacroInvocation(macro_ref, arguments) => {
                // ...add the macro invocation to the template body.
                Self::compile_macro(tdl_context, definition, macro_ref, arguments)
            }
            // If it's a semicolon (`;`)...
            TdlSExpKind::ArgExprGroup(parameter, arguments) => {
                // ...add the arg expr group to the template body.
                Self::compile_arg_expr_group(tdl_context, definition, arguments, parameter)
            }
        }
    }

    /// Adds a `lazy_sexp` that has been determined to represent a macro invocation to the
    /// TemplateBody.
    fn compile_macro<'top, D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        macro_ref: Rc<Macro>,
        mut arguments: impl Iterator<Item = IonResult<LazyValue<'top, D>>>,
    ) -> IonResult<()> {
        // If this macro doesn't accept any parameters but arg expressions have been passed,
        // raise an error.
        if macro_ref.signature().len() == 0 && arguments.next().is_some() {
            return IonResult::decoding_error(format!(
                "unexpected argument passed to macro '{}', which takes no parameters",
                macro_ref.name().unwrap_or("<anonymous>")
            ));
        }

        // Get the 'compiled' step index that the macro invocation will occupy.
        let macro_step_index = definition.expressions.len();
        // Assume the macro contains zero argument expressions to start, we'll update
        // this at the end of the function after we've compiled any argument expressions.
        definition.push_macro_invocation(Rc::clone(&macro_ref), ExprRange::empty());

        // We'll step through the parameters one at a time, looking for a corresponding argument
        // expression for each. If the ratio of arguments to parameters isn't 1:1, we'll also
        // handle placeholder `none`s and implicit expression groups.
        for (index, param) in macro_ref.signature().parameters().iter().enumerate() {
            // If this is the last parameter...
            if index + 1 == macro_ref.signature().len() {
                // ...handle the possibility that there are going to be more arguments than
                // parameters, indicating an implicit expression group.
                Self::compile_trailing_args(
                    tdl_context,
                    definition,
                    macro_ref.name(),
                    arguments,
                    param,
                )?;
                break;
            }
            // Otherwise, get the next argument.
            let Some(arg) = arguments.next().transpose()? else {
                // If there isn't another argument, then that means there are fewer arg expressions
                // than parameters. For each remaining parameter (including this one) confirm that
                // it accepts the empty stream and insert a placeholder call to `none`.
                Self::insert_placeholder_none_invocations::<D>(
                    tdl_context,
                    definition,
                    &macro_ref,
                    index,
                )?;
                break;
            };

            // From here on we're dealing with the simple case of the expression `arg` being passed
            // to `param`.
            Self::compile_value(
                tdl_context,
                definition,
                /*is_quoted=*/ false,
                Some(param),
                arg,
            )?;
        }
        let arguments_end = definition.expressions.len();
        // update the macro step to reflect the number of child expressions it
        // contains
        let invocation_expr_range = ExprRange::new(macro_step_index..arguments_end);
        definition.expressions[macro_step_index] =
            TemplateBodyExpr::macro_invocation(macro_ref, invocation_expr_range);
        Ok(())
    }

    /// Compiles a TDL macro invocation's final argument expression(s).
    ///
    /// If `arguments` contains more than one expression, this method will construct an expression
    /// group.
    fn compile_trailing_args<'top, D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        invoked_macro_name: Option<&str>,
        arguments: impl Iterator<Item = IonResult<LazyValue<'top, D>>> + Sized,
        param: &Parameter,
    ) -> IonResult<()> {
        // Collect the remaining argument expressions into a (probably) stack-allocated SmallVec.
        let arguments: SmallVec<[LazyValue<'_, D>; 2]> =
            arguments.collect::<IonResult<SmallVec<_>>>()?;

        // If there aren't any more arguments, make sure `param` will accept `none`.
        if arguments.is_empty() {
            return if param.accepts_none() {
                // ...and then insert a placeholder `none` invocation.
                Self::compile_macro(
                    tdl_context,
                    definition,
                    tdl_context.context.none_macro(),
                    std::iter::empty::<Result<LazyValue<'_, D>, IonError>>(),
                )
            } else {
                IonResult::decoding_error(
                    format!(
                        "missing argument in call to macro '{}'; final parameter '{}' has cardinality '{:?}' and cannot be omitted",
                        invoked_macro_name.unwrap_or("<anonymous>"),
                        param.name(),
                        param.cardinality()
                    )
                )
            };
        }

        // If it turns out there was only one expression, we can simply compile it like we would
        // any other argument.
        if arguments.len() == 1 {
            return Self::compile_value(
                tdl_context,
                definition,
                /*is_quoted=*/ false,
                Some(param),
                arguments[0],
            );
        }

        // Otherwise, there were multiple argument expressions remaining. If the parameter is
        // neither `*` nor `+` (the two cardinalities that accept an expression group), raise an error.
        if !param.accepts_multi() {
            return IonResult::decoding_error(
                format!(
                    "too many arguments passed to macro '{}'; final parameter '{}' has cardinality '{:?}' and cannot accept multiple expressions",
                    invoked_macro_name.unwrap_or("<anonymous>"),
                    param.name(),
                    param.cardinality()
                )
            );
        }

        // Otherwise, construct an arg expr group using the remaining arguments.
        Self::compile_arg_expr_group(
            tdl_context,
            definition,
            arguments.iter().cloned().map(Ok),
            param.clone(),
        )
    }

    /// Inserts a `(none)` invocation for each remaining parameter that did not receive an explicit
    /// argument expression. If any of the remaining parameters are required (`!` or `+`), raises an
    /// error.
    fn insert_placeholder_none_invocations<D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        macro_ref: &Rc<Macro>,
        index: usize,
    ) -> Result<(), IonError> {
        // There are fewer args than parameters. That's ok as long as all of the remaining
        // parameters are `?` or `*`. For each remaining parameter...
        for remaining_param in &macro_ref.signature().parameters()[index..] {
            // ...confirm that the parameter is either `?` or `*` (and can be omitted)
            if !remaining_param.can_be_omitted() {
                return IonResult::decoding_error(format!(
                    "invocation of macro '{}' is missing required parameter '{}'",
                    macro_ref.name().unwrap_or("<anonymous>"),
                    remaining_param.name()
                ));
            }
            // ...and then insert a placeholder `none` invocation.
            Self::compile_macro(
                tdl_context,
                definition,
                tdl_context.context.none_macro(),
                std::iter::empty::<Result<LazyValue<'_, D>, IonError>>(),
            )?;
        }
        Ok(())
    }

    /// Adds a `lazy_sexp` that has been determined to represent an expression group to the
    /// TemplateBody.
    fn compile_arg_expr_group<'a, D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        expressions: impl Iterator<Item = IonResult<LazyValue<'a, D>>>,
        parameter: Parameter,
    ) -> IonResult<()> {
        let expr_group_start_index = definition.expressions.len();
        // Put a placeholder expression in the template body. We'll overwrite it at the end of this
        // method when we have more information.
        definition.push_placeholder();
        for argument_result in expressions {
            let argument = argument_result?;
            Self::compile_value(
                tdl_context,
                definition,
                /*is_quoted=*/ false,
                None,
                argument,
            )?;
        }
        let arguments_end = definition.expressions.len();

        // See if this was an empty arg group `(;)`
        let is_none = expr_group_start_index == arguments_end - 1;

        // Confirm that this was a legal expression for the corresponding parameter.
        if is_none {
            if !parameter.accepts_none() {
                return IonResult::decoding_error(format!(
                    "parameter '{}' has cardinality {:?}; it does not accept empty argument groups: `(;)`",
                    parameter.name(),
                    parameter.cardinality()
                ));
            }
        } else if !parameter.accepts_multi() {
            return IonResult::decoding_error(format!(
                "parameter '{}' has cardinality {:?}; it does not accept populated argument groups",
                parameter.name(),
                parameter.cardinality()
            ));
        }

        // update the macro step to reflect the number of child expressions it
        // contains
        let invocation_expr_range = ExprRange::new(expr_group_start_index..arguments_end);
        definition.expressions[expr_group_start_index] =
            TemplateBodyExpr::arg_expr_group(parameter, invocation_expr_range);
        Ok(())
    }

    fn resolve_maybe_macro_id_expr<D: Decoder>(
        tdl_context: TdlContext,
        id_expr: Option<IonResult<LazyValue<D>>>,
    ) -> IonResult<Rc<Macro>> {
        // Get the name or address from the `Option<IonResult<LazyValue<_>>>` if possible, or
        // surface an appropriate error message.
        let value = match id_expr {
            None => {
                return IonResult::decoding_error(
                    "found an empty s-expression in an unquoted context",
                )
            }
            Some(Err(e)) => return Err(e),
            Some(Ok(value)) => value,
        };
        Self::resolve_macro_id_expr(tdl_context, value)
    }

    /// Given a `LazyValue` that represents a macro ID (name or address), attempts to resolve the
    /// ID to a macro reference.
    fn resolve_macro_id_expr<D: Decoder>(
        tdl_context: TdlContext,
        id_expr: LazyValue<D>,
    ) -> IonResult<Rc<Macro>> {
        let macro_id = match id_expr.read()? {
            ValueRef::Symbol(s) => {
                if let Some(name) = s.text() {
                    MacroIdRef::LocalName(name)
                } else {
                    return IonResult::decoding_error("macro names must be an identifier");
                }
            }
            ValueRef::Int(int) => {
                let address = usize::try_from(int.expect_i64()?).map_err(|_| {
                    IonError::decoding_error(format!("found an invalid macro address: {int}"))
                })?;
                MacroIdRef::LocalAddress(address)
            }
            other => {
                return IonResult::decoding_error(format!(
                    "expected a macro name (symbol) or address (int), but found: {other:?}"
                ))
            }
        };

        let mut annotations = id_expr.annotations();
        if let Some(module_name) = annotations.next().transpose()? {
            Self::resolve_qualified_macro_id(
                tdl_context.context,
                module_name.expect_text()?,
                macro_id,
            )
            .ok_or_else(|| {
                IonError::decoding_error(format!(
                    "macro '{module_name:?}::{macro_id}' has not been defined (yet?)"
                ))
            })
        } else {
            Self::resolve_unqualified_macro_id(
                tdl_context.context,
                tdl_context.pending_macros,
                macro_id,
            )
            .ok_or_else(|| {
                IonError::decoding_error(format!("macro '{macro_id}' has not been defined (yet?)"))
            })
        }
    }

    /// Visits all of the arguments to a `(literal ...)` operation, adding them to the `TemplateBody`
    /// without interpretation.
    fn compile_literal_elements<'top, D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        arguments: impl Iterator<Item = IonResult<LazyValue<'top, D>>>,
    ) -> IonResult<()> {
        // Collect the remaining argument expressions into a (probably) stack-allocated SmallVec.
        let arguments: SmallVec<[LazyValue<'_, D>; 2]> =
            arguments.collect::<IonResult<SmallVec<_>>>()?;
        // If there's only one expression, add it to the body directly.
        if arguments.len() == 1 {
            return Self::compile_value(
                tdl_context,
                definition,
                /*is_quoted=*/ true,
                /*target_parameter=*/ None, /*; this is a literal, not an arg expr. */
                arguments[0],
            );
        }

        // Otherwise, we'll call `values` and pass the literal expressions as arguments.
        let expr_group_start_index = definition.expressions.len();
        // Add a placeholder expression; we'll overwrite this with a properly defined macro invocation
        // expression at the end of the method when we know how many argument expressions there are.
        definition.push_placeholder();
        // Add the compiled form of each literal as arguments to `(values ...)`
        for argument in arguments {
            Self::compile_value(
                tdl_context,
                definition,
                /*is_quoted=*/ true,
                None,
                argument,
            )?;
        }
        let arguments_end = definition.expressions.len();

        // Update the macro step to reflect the number of child expressions it contains
        let invocation_expr_range = ExprRange::new(expr_group_start_index..arguments_end);
        definition.expressions[expr_group_start_index] = TemplateBodyExpr::macro_invocation(
            tdl_context.context.values_macro(),
            invocation_expr_range,
        );
        Ok(())
    }

    /// Adds `lazy_sexp` to the template body without interpretation.
    fn compile_quoted_sexp<D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        annotations_range: Range<usize>,
        lazy_sexp: LazySExp<D>,
    ) -> IonResult<()> {
        let sexp_element_index = definition.expressions.len();
        let sexp_element = TemplateBodyElement::with_value(TemplateValue::SExp);
        // Use an empty range for now; we'll overwrite it with the correct one later.
        definition.push_element(sexp_element, ExprRange::empty());
        for value_result in &lazy_sexp {
            let value = value_result?;
            Self::compile_value(
                tdl_context,
                definition,
                /*is_quoted=*/ true,
                /*target_parameter=*/ None,
                value,
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

    /// Recursively adds all of the expressions in `lazy_struct` to the `TemplateBody`.
    fn compile_struct<D: Decoder>(
        tdl_context: TdlContext,
        definition: &mut TemplateBody,
        is_literal: bool,
        annotations_range: Range<usize>,
        lazy_struct: LazyStruct<D>,
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

            Self::compile_value(
                tdl_context,
                definition,
                is_literal,
                /*target_parameter=*/
                None, /*; we're in a struct, not a macro invocation.*/
                field.value(),
            )?;
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
        tdl_context: TdlContext,
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
        let signature_index = tdl_context
            .signature
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

/// Possible meanings of an S-expression in the template definition language (TDL).
enum TdlSExpKind<'a, D: Decoder> {
    /// The `literal` operation, which (in this implementation) exists only at compile time.
    ///     (literal ...)
    /// * Associated iterator returns the s-expression's remaining child expressions.
    Literal(SExpIterator<'a, D>),
    /// A macro invocation in the template body.
    ///     (macro_id ...)
    /// * Associated `Rc<Macro>` is a reference to the macro definition to which the `macro_id` referred.
    /// * Associated iterator returns the s-expression's remaining child expressions.
    MacroInvocation(Rc<Macro>, SExpIterator<'a, D>),
    /// An expression group being passed as an argument to a macro invocation.
    ///     (; ...)
    /// * Associated `Parameter` is the parameter to which this arg expression group is being passed.
    /// * Associated iterator returns the s-expression's remaining child expressions.
    ArgExprGroup(Parameter, SExpIterator<'a, D>),
}

impl<'top, D: Decoder> TdlSExpKind<'top, D> {
    /// Inspects the contents of `sexp` to determine whether it is a special form (e.g. `literal`),
    /// macro invocation (e.g. `make_string`), or arg expression group (e.g. `(;)`).
    pub fn of(
        tdl_context: TdlContext,
        sexp: LazySExp<'top, D>,
        target_parameter: Option<&Parameter>,
    ) -> IonResult<Self> {
        let mut values = sexp.iter();
        let Some(first_value) = values.next().transpose()? else {
            return IonResult::decoding_error(
                "found an empty s-expression instead of a macro invocation or arg group",
            );
        };
        let symbol = first_value.read()?.expect_symbol()?.expect_text()?;
        // `values` now yields all of the arguments that follow the first value, whatever that may be.
        // This creates a new binding that reflects that.
        let arguments = values;

        // If this is an argument expression group...
        if symbol == ";" {
            let Some(parameter) = target_parameter else {
                return IonResult::decoding_error("argument expression groups `(; ...)` are only valid in macro argument position");
            };
            return Ok(TdlSExpKind::ArgExprGroup(parameter.clone(), arguments));
        }

        // If the operation name is `literal`, we need to see if it's the special form or a user-defined macro.
        if symbol == "literal" {
            // If it's `$ion::literal`, it's the special form.
            if first_value.annotations().are(["$ion"])?
                // Otherwise, if it has no annotations...
                || (!first_value.has_annotations()
                // ...and has not been shadowed by a user-defined macro name...
                    && tdl_context.pending_macros.macro_with_name("literal").is_none()
                    && tdl_context.context.macro_table.macro_with_name("literal").is_none())
            {
                // ...then it's the special form.
                return Ok(TdlSExpKind::Literal(arguments));
            }
        }

        // Otherwise, the symbol is a macro ID to resolve.
        let macro_ref = TemplateCompiler::resolve_macro_id_expr(tdl_context, first_value)?;
        Ok(TdlSExpKind::MacroInvocation(macro_ref, arguments))
    }
}

#[derive(Copy, Clone)]
struct TdlContext<'top> {
    // The encoding context that was active when compilation began. The body of the macro we're
    // compiling may reference macros and/or symbols found in the active encoding context.
    pub context: EncodingContextRef<'top>,
    // Macros that were defined in the same encoding directive. They can be referenced by new
    // macros being defined, but have not yet been added to the encoding context.
    pub pending_macros: &'top MacroTable,
    // The signature of the macro that owns the body expression we're compiling. If we find any
    // variables in the body expression, we can resolve them to an offset in the signature.
    pub signature: &'top MacroSignature,
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;
    use std::rc::Rc;

    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::template::{
        ExprRange, ParameterEncoding, TemplateBodyExpr, TemplateMacro, TemplateValue,
    };
    use crate::lazy::expanded::{EncodingContext, EncodingContextRef};
    use crate::{
        AnyEncoding, Element, ElementReader, Int, IntoAnnotations, IonResult, Macro, Reader, Symbol,
    };

    // XXX: The tests in this module compile inputs and expect a specific output. There is no "correct"
    // output, only correct behavior. As such, these tests are fragile; it is possible that optimizing
    // the compiler to produce different output will cause these tests to fail. That does not necessarily
    // indicate that the compiled output is invalid.

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
        expected_macro: Rc<Macro>,
        expected_num_args: usize,
    ) -> IonResult<()> {
        expect_step(
            definition,
            index,
            TemplateBodyExpr::macro_invocation(
                Rc::clone(&expected_macro),
                // First arg position to last arg position (exclusive)
                ExprRange::new(index..index + 1 + expected_num_args),
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
            context.macro_table.clone_macro_with_name("values").unwrap(),
            4,
        )?;
        expect_value(&template, 2, TemplateValue::Int(42.into()))?;
        expect_value(&template, 3, TemplateValue::String("hello".into()))?;
        expect_value(&template, 4, TemplateValue::Bool(false))?;
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
            &ParameterEncoding::FlexUInt
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
        expect_macro(&template, 0, context.values_macro(), 6)?;
        // First argument: `(values x)`
        expect_macro(&template, 2, context.values_macro(), 1)?;
        expect_variable(&template, 3, 0)?;
        // Second argument: `(literal (values x))`
        // Notice that the `literal` is not part of the compiled output, only its arguments
        expect_value(&template, 4, TemplateValue::SExp)?;
        expect_value(&template, 5, TemplateValue::Symbol("values".into()))?;
        expect_value(&template, 6, TemplateValue::Symbol("x".into()))?;

        Ok(())
    }

    #[cfg(feature = "experimental-ion-1-1")]
    #[test]
    fn dependent_macros() -> IonResult<()> {
        let ion = r#"
            $ion_1_1
            $ion_encoding::(
                (macro_table
                    $ion_encoding
                    (macro hello ($name) (make_string "hello " $name))
                    (macro hello_world () (hello "world")) // Depends on macro 'hello'
                )
            )
            (:hello_world)
        "#;
        let mut reader = Reader::new(AnyEncoding, ion)?;
        assert_eq!(reader.read_one_element()?, Element::string("hello world"));
        Ok(())
    }
}
