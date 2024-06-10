//! Compiles template definition language (TDL) expressions into a form suitable for fast incremental
//! evaluation.
use std::collections::HashMap;
use std::ops::Range;

use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::template::{
    ExprRange, MacroSignature, Parameter, ParameterEncoding, TemplateBody, TemplateBodyElement,
    TemplateBodyMacroInvocation, TemplateBodyValueExpr, TemplateMacro, TemplateStructIndex,
    TemplateValue,
};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::value::LazyValue;
use crate::lazy::value_ref::ValueRef;
use crate::result::IonFailure;
use crate::symbol_ref::AsSymbolRef;
use crate::{v1_1, IonError, IonResult, IonType, Reader, SymbolRef};

/// Validates a given TDL expression and compiles it into a [`TemplateMacro`] that can be added
/// to a [`MacroTable`](crate::lazy::expanded::macro_table::MacroTable).
pub struct TemplateCompiler {}

impl TemplateCompiler {
    /// Takes a TDL expression in the form:
    /// ```ion_1_1
    ///     (macro name (param1 param2 [...] paramN) body)
    /// ```
    /// and compiles it into a [`TemplateMacro`].
    ///
    /// The [`TemplateMacro`] stores a sequence of [`TemplateBodyValueExpr`]s that need to be evaluated
    /// in turn. Each step is either a value literal, a reference to one of the parameters (that is:
    /// a variable), or a macro invocation.
    ///
    /// Expressions that contain other expressions (i.e. containers and macro invocations) each
    /// store the range of subexpressions that they contain, allowing a reader to skip the entire
    /// parent expression as desired. For example, in this macro:
    ///
    /// ```ion_1_1
    /// (macro foo ()
    ///                  // Template body expressions
    ///     [            // #0, contains expressions 1..=4
    ///         1,       // #1
    ///         (values  // #2, contains expressions 3..=4
    ///             2    // #3
    ///             3    // #4
    ///         )
    ///     ]
    /// )
    /// ```
    ///
    /// the step corresponding to `(values 2 3)` would store the range `3..=4`, indicating that
    /// it contains template body expressions number `3` and `4`. A reader wishing to skip that call
    /// to `values` could do so by moving ahead to expression number `5`. The outer
    /// list (`[1, (values 2 3)]`) would store a `1..=4`, indicating that it contains the `1`,
    /// the a macro invocation `values`, and the two arguments that belong to `values`.
    ///
    /// The compiler recognizes the `(quote expr1 expr2 [...] exprN)` form, adding each subexpression
    /// to the template without interpretation. `(quote ...)` does not appear in the compiled
    /// template as there is nothing more for it to do at expansion time.
    pub fn compile_from_text(
        context: EncodingContextRef,
        expression: &str,
    ) -> IonResult<TemplateMacro> {
        // TODO: This is a rudimentary implementation that panics instead of performing thorough
        //       validation. Where it does surface errors, the messages are too terse.
        let mut reader = Reader::new(v1_1::Text, expression.as_bytes())?;
        let invocation = reader.expect_next()?.read()?.expect_sexp()?;
        let mut values = invocation.iter();

        let macro_keyword = values.next().expect("macro ID")?.read()?.expect_symbol()?;
        if macro_keyword != "macro" {
            return IonResult::decoding_error(
                "macro compilation expects a sexp starting with the keyword `macro`",
            );
        }

        // TODO: Enforce 'identifier' syntax subset of symbol
        // TODO: Syntactic support address IDs like `(:14 ...)`
        let template_name = match values.next().expect("template name")?.read()? {
            ValueRef::Symbol(s) if s.text().is_none() => {
                return IonResult::decoding_error("$0 is not a valid macro name")
            }
            ValueRef::Symbol(s) => Some(s.text().unwrap().to_owned()),
            ValueRef::Null(IonType::Symbol | IonType::Null) => None,
            other => {
                return IonResult::decoding_error(format!(
                    "expected identifier as macro name but found: {other:?}"
                ))
            }
        };

        let params = values
            .next()
            .expect("parameters sexp")?
            .read()?
            .expect_sexp()?;

        let mut compiled_params = Vec::new();
        for param_result in &params {
            let compiled_param = Parameter::new(
                param_result?
                    .read()?
                    .expect_symbol()?
                    .text()
                    .unwrap()
                    .to_string(),
                ParameterEncoding::Tagged,
            );
            compiled_params.push(compiled_param);
        }
        let signature = MacroSignature::new(compiled_params);
        let body = values.next().expect("template body")?;
        let mut compiled_body = TemplateBody {
            expressions: Vec::new(),
            annotations_storage: Vec::new(),
        };
        Self::compile_value(
            context,
            &signature,
            &mut compiled_body,
            /*is_quoted=*/ false,
            body,
        )?;
        let template_macro = TemplateMacro {
            name: template_name,
            signature,
            body: compiled_body,
        };
        Ok(template_macro)
    }

    /// Recursively visits all of the expressions in `lazy_value` and adds their corresponding
    /// [`TemplateBodyValueExpr`] sequences to the `TemplateBody`.
    ///
    /// If `is_quoted` is true, nested symbols and s-expressions will not be interpreted.
    fn compile_value<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_quoted: bool,
        lazy_value: LazyValue<'top, D>,
    ) -> IonResult<()> {
        let annotations_range_start = definition.annotations_storage.len();
        for annotation_result in lazy_value.annotations() {
            let annotation = annotation_result?;
            definition.annotations_storage.push(annotation.to_owned());
        }
        let annotations_range_end = definition.annotations_storage.len();
        let annotations_range = annotations_range_start..annotations_range_end;

        let value = match lazy_value.read()? {
            ValueRef::Null(ion_type) => TemplateValue::Null(ion_type),
            ValueRef::Bool(b) => TemplateValue::Bool(b),
            ValueRef::Int(i) => TemplateValue::Int(i),
            ValueRef::Float(f) => TemplateValue::Float(f),
            ValueRef::Decimal(d) => TemplateValue::Decimal(d),
            ValueRef::Timestamp(t) => TemplateValue::Timestamp(t),
            ValueRef::String(s) => TemplateValue::String(s.to_owned()),
            ValueRef::Symbol(s) if is_quoted => TemplateValue::Symbol(s.to_owned()),
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
            ValueRef::SExp(s) => {
                return Self::compile_sexp(
                    context,
                    signature,
                    definition,
                    is_quoted,
                    annotations_range.clone(),
                    s,
                );
            }
            ValueRef::List(l) => {
                return Self::compile_list(
                    context,
                    signature,
                    definition,
                    is_quoted,
                    annotations_range.clone(),
                    l,
                )
            }
            ValueRef::Struct(s) => {
                return Self::compile_struct(
                    context,
                    signature,
                    definition,
                    is_quoted,
                    annotations_range.clone(),
                    s,
                )
            }
        };
        definition.push_element(
            TemplateBodyElement::with_value(value).with_annotations(annotations_range),
        );
        Ok(())
    }

    /// Helper method for visiting all of the child expressions in a list.
    fn compile_list<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_quoted: bool,
        annotations_range: Range<usize>,
        lazy_list: LazyList<'top, D>,
    ) -> IonResult<()> {
        let list_element_index = definition.expressions.len();
        // Assume the list contains zero expressions to start, we'll update this at the end
        let list_element = TemplateBodyElement::with_value(TemplateValue::List(ExprRange::empty()));
        definition.push_element(list_element);
        let list_children_start = definition.expressions.len();
        for value_result in &lazy_list {
            let value = value_result?;
            Self::compile_value(context, signature, definition, is_quoted, value)?;
        }
        let list_children_end = definition.expressions.len();
        // Update the list entry to reflect the number of child expressions it contains
        let list_element = TemplateBodyElement::with_value(TemplateValue::List(ExprRange::new(
            list_children_start..list_children_end,
        )))
        .with_annotations(annotations_range);
        definition.expressions[list_element_index] = TemplateBodyValueExpr::Element(list_element);
        Ok(())
    }

    /// Helper method for visiting all of the child expressions in a sexp.
    fn compile_sexp<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_quoted: bool,
        annotations_range: Range<usize>,
        lazy_sexp: LazySExp<'top, D>,
    ) -> IonResult<()> {
        if is_quoted {
            // If `is_quoted` is true, this s-expression is nested somewhere inside a `(quote ...)`
            // macro invocation. The sexp and its child expressions can be added to the TemplateBody
            // without interpretation.
            Self::compile_quoted_sexp(context, signature, definition, annotations_range, lazy_sexp)
        } else {
            // If `is_quoted` is false, the sexp is a macro invocation.
            // First, verify that it doesn't have annotations.
            if !annotations_range.is_empty() {
                return IonResult::decoding_error("found annotations on a macro invocation");
            }
            // Peek at the first expression in the sexp. If it's the symbol `quoted`...
            if Self::sexp_is_quote_macro(&lazy_sexp)? {
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
        let arguments_start = definition.expressions.len();
        for argument_result in expressions {
            let argument = argument_result?;
            Self::compile_value(
                context, signature, definition, /*is_quoted=*/ false, argument,
            )?;
        }
        let arguments_end = definition.expressions.len();
        // Update the macro step to reflect the macro's address and number of child expressions it
        // contains
        let template_macro_invocation = TemplateBodyMacroInvocation::new(
            macro_address,
            ExprRange::new(arguments_start..arguments_end),
        );
        definition.expressions[macro_step_index] =
            TemplateBodyValueExpr::MacroInvocation(template_macro_invocation);
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
        // Assume the sexp contains zero expressions to start, we'll update this at the end
        let sexp_element = TemplateBodyElement::with_value(TemplateValue::SExp(ExprRange::empty()));
        definition.push_element(sexp_element);
        let sexp_children_start = definition.expressions.len();
        for value_result in &lazy_sexp {
            let value = value_result?;
            Self::compile_value(
                context, signature, definition, /*is_quoted=*/ true, value,
            )?;
        }
        let sexp_children_end = definition.expressions.len();
        let sexp_element = TemplateBodyElement::with_value(TemplateValue::SExp(ExprRange::new(
            sexp_children_start..sexp_children_end,
        )))
        .with_annotations(annotations_range);
        // Update the sexp entry to reflect the number of child expressions it contains
        definition.expressions[sexp_element_index] = TemplateBodyValueExpr::Element(sexp_element);
        Ok(())
    }

    /// Returns `Ok(true)` if the first child value in the `LazySexp` is the symbol `quote`.
    /// This method should only be called in an unquoted context.
    fn sexp_is_quote_macro<D: Decoder>(sexp: &LazySExp<D>) -> IonResult<bool> {
        let first_expr = sexp.iter().next();
        match first_expr {
            // If the sexp is empty and we're not in a quoted context, that's an error.
            None => IonResult::decoding_error("found an empty s-expression in an unquoted context"),
            Some(Err(e)) => Err(e),
            Some(Ok(lazy_value)) => {
                let value = lazy_value.read()?;
                Ok(value == ValueRef::Symbol("quote".as_symbol_ref()))
            }
        }
    }

    /// Recursively adds all of the expressions in `lazy_struct` to the `TemplateBody`.
    fn compile_struct<'top, D: Decoder>(
        context: EncodingContextRef<'top>,
        signature: &MacroSignature,
        definition: &mut TemplateBody,
        is_quoted: bool,
        annotations_range: Range<usize>,
        lazy_struct: LazyStruct<'top, D>,
    ) -> IonResult<()> {
        let struct_element_index = definition.expressions.len();
        let struct_element = TemplateBodyElement::with_value(
            // Assume the struct contains zero expressions to start, we'll update this entry with
            // the actual range at the end of the method.
            TemplateValue::Struct(
                ExprRange::empty(),
                // Creating a new HashMap does not allocate; we'll overwrite this value with an
                // actual map of field names to indexes at the end of the method.
                HashMap::new(),
            ),
        );
        definition.push_element(struct_element);

        let mut fields: TemplateStructIndex = HashMap::new();
        let struct_start = definition.expressions.len();
        for field_result in &lazy_struct {
            let field = field_result?;
            let name = field.name()?.to_owned();
            let name_element = TemplateBodyElement::with_value(TemplateValue::Symbol(name.clone()));
            definition.push_element(name_element);
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

            Self::compile_value(context, signature, definition, is_quoted, field.value())?;
        }
        let struct_end = definition.expressions.len();
        // Update the struct entry to reflect the range of expansion steps it contains.
        let struct_element = TemplateBodyElement::with_value(TemplateValue::Struct(
            ExprRange::new(struct_start..struct_end),
            fields,
        ))
        .with_annotations(annotations_range);
        definition.expressions[struct_element_index] =
            TemplateBodyValueExpr::Element(struct_element);
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
    use std::collections::HashMap;

    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::template::{
        ExprRange, TemplateBodyMacroInvocation, TemplateBodyValueExpr,
        TemplateBodyVariableReference, TemplateMacro, TemplateValue,
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
            .expect_element()
            .unwrap_or_else(|_| panic!("expected value {expected:?}"));
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
            TemplateBodyValueExpr::MacroInvocation(TemplateBodyMacroInvocation::new(
                expected_address,
                // The arg range starts just after the macro invocation step and goes for `expected_num_arguments`.
                ExprRange::new(index + 1..index + 1 + expected_num_arguments),
            )),
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
            TemplateBodyValueExpr::Variable(TemplateBodyVariableReference::new(
                expected_signature_index as u16,
            )),
        )
    }

    fn expect_step(
        definition: &TemplateMacro,
        index: usize,
        expected: TemplateBodyValueExpr,
    ) -> IonResult<()> {
        let step = definition
            .body()
            .expressions()
            .get(index)
            .expect("no such expansion step");
        assert_eq!(step, &expected);
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
            .expect_element()
            .unwrap();
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
        assert_eq!(template.signature().parameters().len(), 0);
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
        assert_eq!(template.signature().parameters().len(), 0);
        expect_value(&template, 0, TemplateValue::List(ExprRange::new(1..4)))?;
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
        assert_eq!(template.signature().parameters().len(), 0);
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
        expect_value(&template, 0, TemplateValue::List(ExprRange::new(1..12)))?;
        expect_value(&template, 1, TemplateValue::Int(Int::from(100)))?;
        expect_value(&template, 2, TemplateValue::List(ExprRange::new(3..5)))?;
        expect_value(&template, 3, TemplateValue::Int(Int::from(200)))?;
        expect_value(&template, 4, TemplateValue::Int(Int::from(300)))?;
        expect_annotations(&template, 4, ["a", "b"]);
        expect_variable(&template, 5, 0)?;
        let mut struct_index = HashMap::new();
        struct_index.insert(Symbol::from("y"), vec![8]);
        expect_value(
            &template,
            6,
            TemplateValue::Struct(ExprRange::new(7..12), struct_index),
        )?;
        expect_value(&template, 7, TemplateValue::Symbol(Symbol::from("y")))?;
        expect_value(&template, 8, TemplateValue::List(ExprRange::new(9..12)))?;
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
        assert_eq!(template.signature().parameters().len(), 1);
        expect_variable(&template, 0, 0)?;
        Ok(())
    }

    #[test]
    fn quote() -> IonResult<()> {
        let resources = TestResources::new();
        let context = resources.context();

        let expression = r#"
            (macro foo (x)
                // Outer 'values' call allows multiple expressions in the body 
                (values
                    // This `values` is a macro call that has a single argument: the variable `x`
                    (values x)
                    // This `quote` call causes the inner `(values x)` to be an uninterpreted s-expression.
                    (quote 
                        (values x))))
        "#;

        let template = TemplateCompiler::compile_from_text(context.get_ref(), expression)?;
        assert_eq!(template.name(), "foo");
        assert_eq!(template.signature().parameters().len(), 1);
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
        // Second argument: `(quote (values x))`
        // Notice that the `quote` is not part of the compiled output, only its arguments
        expect_value(&template, 3, TemplateValue::SExp(ExprRange::new(4..6)))?;
        expect_value(&template, 4, TemplateValue::Symbol("values".into()))?;
        expect_value(&template, 5, TemplateValue::Symbol("x".into()))?;

        Ok(())
    }
}
