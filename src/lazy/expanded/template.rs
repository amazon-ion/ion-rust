use bumpalo::collections::Vec as BumpVec;
use rustc_hash::FxHashMap;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, Range};
use std::sync::Arc;
use compact_str::CompactString;
use crate::lazy::binary::raw::v1_1::immutable_buffer::ArgGroupingBitmap;
use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::compiler::ExpansionAnalysis;
use crate::lazy::expanded::macro_evaluator::{AnnotateExpansion, MacroEvaluator, MacroExpansion, MacroExpansionKind, MacroExpr, MacroExprArgsIterator, TemplateExpansion, ValueExpr, ExprGroupExpansion, MakeTextExpansion, FlattenExpansion, ConditionalExpansion, MakeStructExpansion, MakeFieldExpansion};
use crate::lazy::expanded::macro_table::{Macro, MacroKind};
use crate::lazy::expanded::r#struct::FieldSource;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::{
    EncodingContextRef,  LazyExpandedValue, TemplateVariableReference,
};
use crate::result::IonFailure;
use crate::{
    try_or_some_err, Bytes, Decimal, Int, IonResult, IonType, LazyExpandedFieldName, Str, Symbol,
    SymbolRef, Timestamp, Value,
};

/// A parameter in a user-defined macro's signature.
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    name: CompactString,
    encoding: ParameterEncoding,
    cardinality: ParameterCardinality,
    rest_syntax_policy: RestSyntaxPolicy,
}

impl Parameter {
    pub fn new(
        name: impl Into<CompactString>,
        encoding: ParameterEncoding,
        cardinality: ParameterCardinality,
        rest_syntax_policy: RestSyntaxPolicy,
    ) -> Self {
        Self {
            name: name.into(),
            encoding,
            cardinality,
            rest_syntax_policy,
        }
    }

    /// Creates a tagged [`Parameter`] with the given name and a cardinality of `exactly-one`.
    pub fn required(name: impl Into<CompactString>) -> Self {
        Parameter::new(
            name,
            ParameterEncoding::Tagged,
            ParameterCardinality::ExactlyOne,
            RestSyntaxPolicy::NotAllowed,
        )
    }

    /// Creates a tagged [`Parameter`] with the given name and a cardinality of `zero-or-one`.
    pub fn optional(name: impl Into<CompactString>) -> Self {
        Parameter::new(
            name,
            ParameterEncoding::Tagged,
            ParameterCardinality::ZeroOrOne,
            RestSyntaxPolicy::NotAllowed,
        )
    }

    /// Creates a tagged, tail-position [`Parameter`] with the given name, a cardinality
    /// of `zero-or-more`, and support for "rest" syntax.
    pub fn rest(name: impl Into<CompactString>) -> Self {
        Parameter::new(
            name,
            ParameterEncoding::Tagged,
            ParameterCardinality::ZeroOrMore,
            RestSyntaxPolicy::Allowed,
        )
    }

    /// Creates a tagged, [`Parameter`] with the given name and a cardinality
    /// of `zero-or-more`.
    ///
    /// This should not be used in tail position as it does not support rest syntax.
    /// See [`rest`](Self::rest) instead.
    pub fn zero_or_more(name: impl Into<CompactString>) -> Self {
        Parameter::new(
            name,
            ParameterEncoding::Tagged,
            ParameterCardinality::ZeroOrMore,
            RestSyntaxPolicy::NotAllowed,
        )
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
    pub fn encoding(&self) -> &ParameterEncoding {
        &self.encoding
    }
    pub fn cardinality(&self) -> ParameterCardinality {
        self.cardinality
    }
    pub fn rest_syntax_policy(&self) -> RestSyntaxPolicy {
        self.rest_syntax_policy
    }

    /// Returns `true` if this parameter is of any cardinality other than `ExactlyOne` (`!`).
    pub fn is_variadic(&self) -> bool {
        !matches!(self.cardinality, ParameterCardinality::ExactlyOne)
    }

    /// Returns `true` if this parameter accepts populated expression groups.
    pub fn accepts_multi(&self) -> bool {
        matches!(self.cardinality, ParameterCardinality::ZeroOrMore | ParameterCardinality::OneOrMore)
    }

    /// Returns `true` if this parameter accepts empty expression groups.
    pub fn accepts_none(&self) -> bool {
        matches!(self.cardinality, ParameterCardinality::ZeroOrOne | ParameterCardinality::ZeroOrMore)
    }

    /// Returns `true` if this parameter is using a tagged encoding.
    pub fn is_tagged(&self) -> bool {
        self.encoding == ParameterEncoding::Tagged
    }

    /// Returns true if a text e-expression can omit this argument.
    ///
    /// Arguments for parameters with a cardinality of zero-or-one (`?`) or zero-or-more (`*`) can
    /// be omitted if there are no other arguments being passed.
    pub fn can_be_omitted(&self) -> bool {
        matches!(
            self.cardinality,
            ParameterCardinality::ZeroOrOne | ParameterCardinality::ZeroOrMore
        )
    }
}

/// The encoding used to serialize and deserialize the associated parameter.
#[derive(Debug, Clone, PartialEq)]
pub enum ParameterEncoding {
    /// A 'tagged' type is one whose binary encoding begins with an opcode (sometimes called a 'tag'.)
    Tagged,
    FlexUInt,
    // TODO: tagless types, including fixed-width types and macros
    MacroShaped(Arc<Macro>),
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ParameterCardinality {
    ExactlyOne, // !
    ZeroOrOne,  // ?
    ZeroOrMore, // *
    OneOrMore,  // +
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum RestSyntaxPolicy {
    NotAllowed,
    Allowed,
}

/// The sequence of parameters for which callers must pass expressions when invoking the macro.
#[derive(Debug, Clone, PartialEq)]
pub struct MacroSignature {
    parameters: Vec<Parameter>,
    num_variadic_params: usize,
}

impl MacroSignature {
    fn with_parameter(
        mut self,
        name: impl Into<String>,
        encoding: ParameterEncoding,
        cardinality: ParameterCardinality,
    ) -> IonResult<Self> {
        // We're adding a new parameter, so the previous "final position" parameter is no longer in the final position.
        // Disable rest syntax for that parameter.
        if let Some(final_position_param) = self.parameters.last_mut() {
            final_position_param.rest_syntax_policy = RestSyntaxPolicy::NotAllowed;
        }
        let rest_syntax_policy = if cardinality == ParameterCardinality::ExactlyOne {
            RestSyntaxPolicy::NotAllowed
        } else {
            self.num_variadic_params += 1;
            if self.num_variadic_params > ArgGroupingBitmap::MAX_VARIADIC_PARAMS {
                return IonResult::decoding_error(format!(
                    "macro found with {} variadic parameters; the max supported is {}",
                    self.num_variadic_params,
                    ArgGroupingBitmap::MAX_VARIADIC_PARAMS,
                ));
            };
            RestSyntaxPolicy::Allowed
        };
        let param = Parameter::new(name.into(), encoding, cardinality, rest_syntax_policy);
        self.parameters.push(param);
        Ok(self)
    }

    /// Constructs a new instance of a signature with no arguments (the signature of a "constant" template).
    pub(crate) fn constant() -> Self {
        Self::new(Vec::new()).unwrap()
    }

    pub fn len(&self) -> usize {
        self.parameters().len()
    }
    pub fn parameters(&self) -> &[Parameter] {
        self.parameters.as_slice()
    }
    pub fn new(parameters: Vec<Parameter>) -> IonResult<Self> {
        let num_variadic_params = parameters
            .iter()
            .filter(|p| p.cardinality != ParameterCardinality::ExactlyOne)
            .count();
        if num_variadic_params > ArgGroupingBitmap::MAX_VARIADIC_PARAMS {
            return IonResult::decoding_error(format!(
                "macro found with {num_variadic_params} variadic parameters; the max supported is {}",
                ArgGroupingBitmap::MAX_VARIADIC_PARAMS
            ));
        };
        Ok(Self {
            parameters,
            num_variadic_params,
        })
    }
    pub fn num_variadic_params(&self) -> usize {
        self.num_variadic_params
    }
    pub fn bitmap_size_in_bytes(&self) -> usize {
        const BITS_PER_VARIADIC_PARAM: usize = 2;
        const BITS_PER_BYTE: usize = 8;
        ((self.num_variadic_params * BITS_PER_VARIADIC_PARAM) + 7) / 8
    }
}

#[cfg(test)]
mod macro_signature_tests {
    use crate::lazy::expanded::template::{
        MacroSignature, ParameterCardinality, ParameterEncoding,
    };
    use crate::IonResult;

    #[test]
    fn bitmap_sizes() -> IonResult<()> {
        let signature = MacroSignature::constant();
        assert_eq!(signature.num_variadic_params(), 0);
        assert_eq!(signature.bitmap_size_in_bytes(), 0);

        let signature = MacroSignature::new(Vec::new())?.with_parameter(
            "foo",
            ParameterEncoding::Tagged,
            ParameterCardinality::ExactlyOne,
        )?;
        assert_eq!(signature.num_variadic_params(), 0);
        assert_eq!(signature.bitmap_size_in_bytes(), 0);

        let signature = MacroSignature::new(Vec::new())?.with_parameter(
            "foo",
            ParameterEncoding::Tagged,
            ParameterCardinality::ZeroOrOne,
        )?;
        assert_eq!(signature.num_variadic_params(), 1);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter(
                "foo",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "bar",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?;
        assert_eq!(signature.num_variadic_params(), 2);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter(
                "foo",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "bar",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrMore,
            )?
            .with_parameter(
                "baz",
                ParameterEncoding::Tagged,
                ParameterCardinality::OneOrMore,
            )?;
        assert_eq!(signature.num_variadic_params(), 3);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter(
                "foo",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "bar",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "baz",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "quux",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?;
        assert_eq!(signature.num_variadic_params(), 4);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter(
                "foo",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "bar",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "baz",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "quux",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?
            .with_parameter(
                "quuz",
                ParameterEncoding::Tagged,
                ParameterCardinality::ZeroOrOne,
            )?;
        assert_eq!(signature.num_variadic_params(), 5);
        assert_eq!(signature.bitmap_size_in_bytes(), 2);

        Ok(())
    }
}

/// A user-defined macro which expands the parameters in the signature into a series of Ion values
/// according to a template.
///
/// Macros can be made anonymous by passing `null` in the definition's name position.
/// ```ion_1_1
///     (macro null (x y z) [x, y, z])
/// ```
/// This simplifies the use of machine-authored macros, which are always invoked by their address
/// in the macro table rather than by a human-friendly name.
#[derive(Clone, PartialEq)]
pub struct TemplateMacro {
    pub(crate) name: Option<CompactString>,
    pub(crate) signature: MacroSignature,
    pub(crate) body: TemplateBody,
    pub(crate) expansion_analysis: ExpansionAnalysis,
}

impl Debug for TemplateMacro {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Template {}", self.name())?;
        writeln!(f, "    signature:")?;
        // Writes each parameter in the signature on its own indented line
        for param in self.signature().parameters() {
            let name = param.name();
            let encoding = param.encoding();
            let cardinality = param.cardinality();
            writeln!(f, "        {name} ({encoding:?}, {cardinality:?})")?;
        }
        writeln!(f, "    body:")?;
        let indentation = &mut String::from("        ");
        let mut index = 0usize;
        while let Some(expr) = self.body().expressions().get(index) {
            index += TemplateBodyExprKind::fmt_expr(f, indentation, self, expr)?;
        }

        Ok(())
    }
}

impl TemplateMacro {
    pub fn name(&self) -> &str {
        self.name.as_deref().unwrap_or("<anonymous>")
    }
    pub fn signature(&self) -> &MacroSignature {
        &self.signature
    }
    pub fn body(&self) -> &TemplateBody {
        &self.body
    }
}

/// A reference to a template macro definition paired with the more general macro reference.
#[derive(Copy, Clone, Debug)]
pub struct TemplateMacroRef<'top> {
    macro_ref: &'top Macro,
    template_body: &'top TemplateBody,
}

impl<'top> TemplateMacroRef<'top> {
    pub fn new(macro_ref: &'top Macro, template_body: &'top TemplateBody) -> Self {
        Self {
            macro_ref,
            template_body,
        }
    }
    pub fn body(&self) -> &'top TemplateBody {
        self.template_body
    }

    pub fn macro_ref(&self) -> &'top Macro {
        self.macro_ref
    }
}

impl<'top> Deref for TemplateMacroRef<'top> {
    type Target = &'top Macro;

    fn deref(&self) -> &Self::Target {
        &self.macro_ref
    }
}

/// Steps over the child expressions of a list or s-expression found in the body of a template.
#[derive(Debug)]
pub struct TemplateSequenceIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    template: TemplateMacroRef<'top>,
    evaluator: MacroEvaluator<'top, D>,
    value_expressions: &'top [TemplateBodyExpr],
    index: usize,
}

impl<'top, D: Decoder> TemplateSequenceIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        evaluator: MacroEvaluator<'top, D>,
        template: TemplateMacroRef<'top>,
        nested_expressions: &'top [TemplateBodyExpr],
    ) -> Self {
        Self {
            context,
            template,
            evaluator,
            value_expressions: nested_expressions,
            index: 0,
        }
    }
}

impl<'top, D: Decoder> Iterator for TemplateSequenceIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If the evaluator's stack is not empty, give it the opportunity to yield a value.
            if let Some(value) = try_or_some_err!(self.evaluator.next()) {
                return Some(Ok(value));
            }
            // The stack did not produce values and is empty, pull the next expression from `self.value_expressions`
            // and start expanding it.
            let current_expr = self.value_expressions.get(self.index)?;
            let environment = self.evaluator.environment();
            self.index += current_expr.num_expressions();

            let value_expr = current_expr.to_value_expr(self.context, environment, self.template);
            break match value_expr {
                ValueExpr::ValueLiteral(lazy_expanded_value) => Some(Ok(lazy_expanded_value)),
                ValueExpr::MacroInvocation(invocation) => {
                    // If the macro is guaranteed to expand to exactly one value, we can evaluate it
                    // in place.
                    let new_expansion = try_or_some_err!(invocation.expand());
                    if invocation
                        .expansion_analysis()
                        .must_produce_exactly_one_value()
                    {
                        Some(new_expansion.expand_singleton())
                    } else {
                        // Otherwise, add it to the evaluator's stack and return to the top of the loop.
                        self.evaluator.push(new_expansion);
                        continue;
                    }
                }
            };
        }
    }
}

/// An iterator that pulls expressions from a template body and wraps them in a [`FieldSource`] to
/// mimic reading them from input. The [`LazyExpandedStruct`](crate::lazy::expanded::struct::LazyExpandedStruct) handles
/// evaluating any macro invocations that this yields.
pub struct TemplateStructFieldSourceIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    environment: Environment<'top, D>,
    template: TemplateMacroRef<'top>,
    nested_expressions: &'top [TemplateBodyExpr],
    index: usize,
}

impl<'top, D: Decoder> TemplateStructFieldSourceIterator<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
}

impl<'top, D: Decoder> TemplateStructFieldSourceIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        template: TemplateMacroRef<'top>,
        nested_expressions: &'top [TemplateBodyExpr],
    ) -> Self {
        Self {
            context,
            environment,
            template,
            nested_expressions,
            index: 0,
        }
    }
}

impl<'top, D: Decoder> Iterator for TemplateStructFieldSourceIterator<'top, D> {
    type Item = IonResult<FieldSource<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let name_expr_address = self.index;
        let name_element = self
            .nested_expressions
            .get(name_expr_address)?
            .kind()
            .require_element();
        let name: SymbolRef<'_> = match &name_element.value {
            TemplateValue::Symbol(s) => s.into(),
            TemplateValue::String(s) => s.text().into(),
            _ => unreachable!("template struct field had a non-text field name"),
        };
        let value_expr_address = name_expr_address + 1;
        let field_value_tdl_expr = self
            .nested_expressions
            .get(value_expr_address)
            .expect("template struct had field name with no value");

        let field_name = LazyExpandedFieldName::TemplateName(self.template, name);
        let value_expr = field_value_tdl_expr.to_value_expr(self.context, self.environment, self.template);
        let unexpanded_field = match value_expr {
            ValueExpr::ValueLiteral(lazy_expanded_value) => FieldSource::NameValue(
                field_name,
                lazy_expanded_value
            ),
            ValueExpr::MacroInvocation(invocation) => FieldSource::NameMacro(
                field_name,
                invocation,
            ),
        };
        self.index += /* name expr count -> */ 1 + field_value_tdl_expr.num_expressions();
        Some(Ok(unexpanded_field))
    }
}

/// Stores a sequence of expansion steps that need to be evaluated in turn.
///
/// See [`TemplateBodyExprKind`] for details.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBody {
    // A vector of expressions that will be visited in turn during expansion.
    pub(crate) expressions: Vec<TemplateBodyExpr>,
    // All of the elements stored in the Vec above share the Vec below for storing their annotations.
    // This allows us to avoid allocating a `Vec<Symbol>` for every value in the template, saving
    // a small amount of time and memory during compilation. Each values hold an index range
    // into this `Vec`.
    pub(crate) annotations_storage: Vec<Symbol>,
}

impl TemplateBody {
    pub fn expressions(&self) -> &[TemplateBodyExpr] {
        self.expressions.as_slice()
    }
    pub fn annotations_storage(&self) -> &[Symbol] {
        &self.annotations_storage
    }

    pub fn push_element(&mut self, element: TemplateBodyElement, expr_range: ExprRange) {
        self.expressions
            .push(TemplateBodyExpr::element(element, expr_range))
    }

    pub fn push_variable(&mut self, signature_index: u16) {
        let index = self.expressions.len();
        self.expressions.push(TemplateBodyExpr::variable(
            signature_index,
            ExprRange::new(index..index + 1),
        ))
    }

    pub fn push_macro_invocation(&mut self, macro_ref: Arc<Macro>, expr_range: ExprRange) {
        self.expressions.push(TemplateBodyExpr::macro_invocation(
            macro_ref,
            expr_range,
        ))
    }

    pub fn push_placeholder(&mut self) {
        self.expressions.push(TemplateBodyExpr::element(
                TemplateBodyElement::with_value(TemplateValue::Bool(false)),
                ExprRange::empty()
            )
        )
    }
}

#[derive(Clone, PartialEq)]
pub struct TemplateBodyExpr {
    kind: TemplateBodyExprKind,
    expr_range: ExprRange,
}

impl Debug for TemplateBodyExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "tdl_expr=")?;
        match &self.kind {
            TemplateBodyExprKind::Element(e) => write!(f, "{e:?}"),
            TemplateBodyExprKind::Variable(v) => write!(f, "{v:?}"),
            TemplateBodyExprKind::MacroInvocation(i) => write!(f, "{i:?}"),
            TemplateBodyExprKind::ExprGroup(g) => write!(f, "{g:?}")
        }
    }
}

impl TemplateBodyExpr {
    pub fn new(kind: TemplateBodyExprKind, expr_range: ExprRange) -> Self {
        Self { kind, expr_range }
    }

    pub fn element(element: TemplateBodyElement, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::Element(element),
            expr_range,
        }
    }

    pub fn variable(signature_index: u16, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::Variable(TemplateBodyVariableReference::new(
                signature_index,
            )),
            expr_range,
        }
    }

    pub fn macro_invocation(invoked_macro: Arc<Macro>, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::MacroInvocation(TemplateBodyMacroInvocation::new(
                invoked_macro,
            )),
            expr_range,
        }
    }

    pub fn arg_expr_group(parameter: Parameter, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::ExprGroup(parameter),
            expr_range
        }
    }

    pub fn kind(&self) -> &TemplateBodyExprKind {
        &self.kind
    }

    pub fn num_expressions(&self) -> usize {
        self.expr_range.len()
    }

    pub fn expr_range(&self) -> ExprRange {
        self.expr_range
    }

    pub fn to_value_expr<'top, D: Decoder>(&'top self,
                                           context: EncodingContextRef<'top>,
                                           environment: Environment<'top, D>,
                                           host_template: TemplateMacroRef<'top>
    ) -> ValueExpr<'top, D> {
        match self.kind() {
            TemplateBodyExprKind::Element(e) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_template(
                    context,
                    environment,
                    TemplateElement::new(host_template, e, self.expr_range()),
                ))
            }
            TemplateBodyExprKind::Variable(variable_ref) => {
                let expr = environment.require_expr(variable_ref.signature_index());
                let template_variable_ref = variable_ref.resolve(host_template.macro_ref());
                // If this is a value (and therefore needs no further evaluation), tag it as having
                // come from this variable in the template body.
                expr.via_variable(Some(template_variable_ref))
            }
            TemplateBodyExprKind::ExprGroup(parameter) => {
                let template_arg_group = TemplateExprGroup::new(
                    context,
                    environment,
                    host_template,
                    ExprRange::new(self.expr_range().tail()),
                    parameter
                );
                let macro_expr = MacroExpr::from_template_expr_group(template_arg_group);
                ValueExpr::MacroInvocation(macro_expr)
            }
            TemplateBodyExprKind::MacroInvocation(body_invocation)
            => {
                let invocation = body_invocation.resolve(
                    context,
                    environment,
                    host_template,
                    self.expr_range(),
                );
                ValueExpr::MacroInvocation(invocation.into())
            }
        }
    }
}

/// An expression appearing in value position in a template body.
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateBodyExprKind {
    /// A potentially annotated value literal.
    Element(TemplateBodyElement),
    /// A reference to a variable that needs to be expanded.
    Variable(TemplateBodyVariableReference),
    /// A macro invocation that needs to be expanded.
    MacroInvocation(TemplateBodyMacroInvocation),
    /// An expression group. In TDL, expression groups (syntax: `(; ...)`) can only appear in macro
    /// argument position. However, the compiler reserves the right to insert them as an optimization
    /// when the resulting behavior would be equivalent. For example, substituting an invocation of
    /// `values` with the equivalent expression group avoids a stack frame during macro evaluation
    /// but yields identical output.
    ExprGroup(Parameter),
}

impl TemplateBodyExprKind {
    /// Confirms that this value expression is a value literal and panics if it is not.
    ///
    /// When this method is called, it is because the rules of the template compiler have
    /// dictated that an element in this position be a value literal.
    #[inline]
    pub fn require_element(&self) -> &TemplateBodyElement {
        if let TemplateBodyExprKind::Element(e) = self {
            return e;
        }
        unreachable!("The compiled template contained a non-element in element position");
    }

    /// This helper method is invoked by the `Debug` implementation of `TemplateMacro`, which provides
    /// a neatly indented, recursive printout of the compiled form of a template definition.
    ///
    /// `TemplateBodyValueExpr` also provides its own "shallow" implementation of `Debug` that simply
    /// prints the contents of each field in the data of its variant.
    pub(crate) fn fmt_expr(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        expr: &TemplateBodyExpr,
    ) -> Result<usize, fmt::Error> {
        match &expr.kind() {
            TemplateBodyExprKind::Element(e) => {
                Self::fmt_element(f, indentation, host_template, e, expr.expr_range())
            }
            TemplateBodyExprKind::Variable(v) => {
                Self::fmt_variable(f, indentation, host_template, v)
            }
            TemplateBodyExprKind::MacroInvocation(m) => {
                Self::fmt_invocation(f, indentation, host_template, m, expr.expr_range())
            }
            TemplateBodyExprKind::ExprGroup(parameter) => {
                Self::fmt_arg_group(f, indentation, host_template, parameter, expr.expr_range())
            }
        }
    }

    /// A helper method to recursively print the 'compiled' form of a `TemplateBodyValueExpr::Element(_)`.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_element(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        element: &TemplateBodyElement,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        let annotations_range = element.annotations_range.ops_range();
        let annotations = host_template
            .body()
            .annotations_storage()
            .get(annotations_range)
            .unwrap();
        write!(f, "{indentation}")?;
        for annotation in annotations {
            write!(f, "{}::", annotation.text().unwrap_or("$0"))?;
        }
        use TemplateValue::*;
        match element.value() {
            List => {
                writeln!(f, "list")?;
                return Self::fmt_sequence_body(f, indentation, host_template, ExprRange::new(expr_range.tail()));
            }
            SExp => {
                writeln!(f, "sexp")?;
                return Self::fmt_sequence_body(f, indentation, host_template, ExprRange::new(expr_range.tail()));
            }
            Struct(_) => {
                writeln!(f, "struct")?;
                return Self::fmt_struct(f, indentation, host_template, ExprRange::new(expr_range.tail()));
            }
            Null(n) => writeln!(f, "{}", Value::Null(*n)),
            Bool(b) => writeln!(f, "{b}"),
            Int(i) => writeln!(f, "{i}"),
            Float(float) => writeln!(f, "{}", *float),
            Decimal(d) => writeln!(f, "{d}"),
            Timestamp(t) => writeln!(f, "{t}"),
            String(s) => writeln!(f, "{s}"),
            Symbol(s) => writeln!(f, "{s}"),
            Blob(b) => writeln!(f, "blob {:x?}", &b.as_ref()[..16.min(b.as_ref().len())]),
            Clob(c) => writeln!(f, "clob {:x?}", &c.as_ref()[..16.min(c.as_ref().len())]),
        }?;
        Ok(1)
    }

    /// A helper method to recursively print the 'compiled' form of lists, s-expressions, and
    /// macro invocation argument sequences.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_sequence_body(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        let range = expr_range.ops_range();
        let expressions = host_template.body().expressions().get(range).unwrap();
        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while expr_index < expressions.len() {
            let expr = &expressions[expr_index];
            expr_index += Self::fmt_expr(f, indentation, host_template, expr)?;
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + expressions.len())
    }

    /// A helper method to recursively print the 'compiled' form of a struct.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_struct(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        let range = expr_range.ops_range();
        let expressions = host_template.body().expressions().get(range).unwrap();
        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while expr_index < expressions.len() {
            let TemplateBodyExprKind::Element(name_element) = &expressions[expr_index].kind()
            else {
                unreachable!(
                    "non-element field name in template struct: {:?}",
                    &expressions[expr_index]
                )
            };
            let name = match name_element.value() {
                TemplateValue::String(s) => s.text(),
                TemplateValue::Symbol(s) => s.text().unwrap_or("$0"),
                unexpected => unreachable!(
                    "non-string, non-symbol field name in template struct: {:?}",
                    unexpected
                ),
            };
            let value = &expressions[expr_index + 1];
            writeln!(f, "{indentation}'{name}':")?;
            indentation.push_str("    ");
            expr_index += 1 + Self::fmt_expr(f, indentation, host_template, value)?;
            indentation.truncate(indentation.len() - 4);
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + expressions.len())
    }

    /// A helper method to recursively print the 'compiled' form of a macro invocation within a template.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_invocation(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        invocation: &TemplateBodyMacroInvocation,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        writeln!(
            f,
            "{indentation}<invoke macro '{}'>",
            invocation.invoked_macro.name().unwrap_or("<anonymous>")
        )?;

        let args = host_template
            .body
            .expressions
            .get(expr_range.tail())
            .unwrap();

        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while let Some(arg) = args.get(expr_index) {
            expr_index += Self::fmt_expr(f, indentation, host_template, arg)?;
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + args.len())
    }

    /// A helper method to recursively print the 'compiled' form of an argument group within a template.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_arg_group(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        parameter: &Parameter,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        writeln!(
            f,
            "{indentation}<arg group for param '{}'>",
            parameter.name(),
        )?;

        let args = host_template
            .body
            .expressions
            .get(expr_range.tail())
            .unwrap();

        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while let Some(arg) = args.get(expr_index) {
            expr_index += Self::fmt_expr(f, indentation, host_template, arg)?;
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + args.len())
    }

    /// A helper method to recursively print the 'compiled' form of a variable reference in the
    /// body of a template.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_variable(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        variable: &TemplateBodyVariableReference,
    ) -> Result<usize, fmt::Error> {
        let index = variable.signature_index();
        let name = host_template
            .signature()
            .parameters()
            .get(index)
            .unwrap()
            .name();
        writeln!(f, "{indentation}<param {name}>")?;
        Ok(1)
    }
}

/// A macro invocation found in the body of a template.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBodyMacroInvocation {
    pub(crate) invoked_macro: Arc<Macro>,
}

impl TemplateBodyMacroInvocation {
    pub fn new(invoked_macro: Arc<Macro>) -> Self {
        Self {
            invoked_macro,
        }
    }

    /// Finds the definition of the macro being invoked in the provided `context`'s macro table.
    ///
    /// It is a logic error for this method to be called with an [`EncodingContextRef`] that does not
    /// contain the necessary information; doing so will cause this method to panic.
    pub(crate) fn resolve<'a, D: Decoder>(
        &'a self,
        context: EncodingContextRef<'a>,
        environment: Environment<'a, D>,
        host_template: TemplateMacroRef<'a>,
        expr_range: ExprRange,
    ) -> TemplateMacroInvocation<'a, D> {
        let arg_expr_range = ExprRange::new(expr_range.tail());

        TemplateMacroInvocation::new(
            context,
            environment,
            host_template,
            self.invoked_macro.as_ref(),
            arg_expr_range,
        )
    }
}

/// An expression group in the body of a macro. This behaves like the `values` macro, but is not
/// user-addressable.
#[derive(Copy, Clone)]
pub struct TemplateExprGroup<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    environment: Environment<'top, D>,
    host_template: TemplateMacroRef<'top>,
    arg_expressions_range: ExprRange,
    parameter: &'top Parameter,
}

impl<'top, D: Decoder> TemplateExprGroup<'top, D> {
    pub fn new(context: EncodingContextRef<'top>, environment: Environment<'top, D>, host_template: TemplateMacroRef<'top>, arg_expressions_range: ExprRange, parameter: &'top Parameter) -> Self {
        Self { context, environment, host_template, arg_expressions_range, parameter }
    }

    // Doesn't take an environment b/c template arg groups capture their environment at creation time.
    // In contrast, template macro invocations need you to provide an environment when you begin expansion.
    pub(crate) fn expand(&self) -> IonResult<MacroExpansion<'top, D>> {
        let arguments = MacroExprArgsIterator::from_template_arg_group(self.arguments());
        let expr_group_expansion = ExprGroupExpansion::new(arguments);
        let expansion_kind =  MacroExpansionKind::ExprGroup(expr_group_expansion);
        Ok(MacroExpansion::new(
            self.context(),
            self.environment,
            expansion_kind,
        ))
    }

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    pub fn host_template(&self) -> TemplateMacroRef<'top> {
        self.host_template
    }

    pub fn arg_expressions_range(&self) -> ExprRange {
        self.arg_expressions_range
    }

    pub fn parameter(&self) -> &'top Parameter {
        self.parameter
    }

    pub fn arg_expressions(&self) -> &'top [TemplateBodyExpr] {
        self.host_template()
            .body()
            .expressions()
            .get(self.arg_expressions_range.ops_range())
            .unwrap()
    }

    pub fn arguments(
        &self,
    ) -> TemplateMacroInvocationArgsIterator<'top, D> {
        TemplateMacroInvocationArgsIterator::new(
            self.context,
            self.environment,
            self.arg_expressions(),
            self.host_template(),
        )
    }
}

impl<D: Decoder> Debug for TemplateExprGroup<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "<param={}:", self.parameter().name()
        )?;
        for expr in self.arg_expressions() {
            write!(f, " {:?}", expr)?;
        }
        write!(
            f,
            ">",
        )
    }
}

/// A resolved version of [`TemplateBodyMacroInvocation`]; instead of holding addresses, this type
/// holds references to the invoked macro and its argument expressions.
#[derive(Copy, Clone)]
pub struct TemplateMacroInvocation<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    host_template: TemplateMacroRef<'top>,
    environment: Environment<'top, D>,
    invoked_macro: &'top Macro,
    // The range of value expressions in the host template's body that are arguments to the
    // macro being invoked
    arg_expressions_range: ExprRange,
}

impl<D: Decoder> Debug for TemplateMacroInvocation<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}",
            self.invoked_macro().name().unwrap_or("<anonymous>")
        )?;
        for expr in self.arg_expressions() {
            write!(f, " {:?}", expr)?;
        }
        write!(f, ")")
    }
}

impl<'top, D: Decoder> TemplateMacroInvocation<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        host_template: TemplateMacroRef<'top>,
        invoked_macro: &'top Macro,
        arg_expressions_range: ExprRange,
    ) -> Self {
        Self {
            context,
            host_template,
            environment,
            invoked_macro,
            arg_expressions_range,
        }
    }

    pub fn arguments(
        &self
    ) -> TemplateMacroInvocationArgsIterator<'top, D> {
        TemplateMacroInvocationArgsIterator::new(
            self.context,
            self.environment,
            self.arg_expressions(),
            self.host_template(),
        )
    }

    /// Helper method to access the definition of the host template. Useful for debugging,
    /// but not required for macro expansion.
    pub fn host_macro_ref(&self) -> &'top Macro {
        self.host_template.macro_ref
    }

    /// Helper method to access the definition of the host template. Useful for debugging,
    /// but not required for macro expansion.
    pub fn host_template(&self) -> TemplateMacroRef<'top> {
        self.host_template
    }

    pub fn arg_expressions(&self) -> &'top [TemplateBodyExpr] {
        self.host_template()
            .body()
            .expressions()
            .get(self.arg_expressions_range.ops_range())
            .unwrap()
    }

    pub fn invoked_macro(&self) -> &'top Macro {
        self.invoked_macro
    }

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    pub fn new_evaluation_environment(
        &self,
    ) -> IonResult<Environment<'top, D>> {
        let arguments = self.arguments();
        let allocator = self.context().allocator();
        // Use the iterator's size hint to determine an initial capacity to aim for.
        let num_args_hint = arguments.size_hint();
        let capacity_hint = num_args_hint.1.unwrap_or(num_args_hint.0);
        let mut env_exprs = BumpVec::with_capacity_in(capacity_hint, allocator);
        for arg in arguments {
            env_exprs.push(arg?);
        }
        let new_environment = Environment::new(env_exprs.into_bump_slice());
        Ok(new_environment)
    }

    pub fn expand(
        &self,
    ) -> IonResult<MacroExpansion<'top, D>> {
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let macro_ref = self.invoked_macro();
        let arguments = MacroExprArgsIterator::from_template_macro(self.arguments());
        let expansion_kind = match macro_ref.kind() {
            MacroKind::None => MacroExpansionKind::None,
            MacroKind::ExprGroup => {
                unreachable!("cannot invoke ExprGroup from a TemplateMacroInvocation")
            },
            MacroKind::MakeString => {
                MacroExpansionKind::MakeString(MakeTextExpansion::string_maker(arguments))
            }
            MacroKind::MakeSymbol => {
                MacroExpansionKind::MakeSymbol(MakeTextExpansion::symbol_maker(arguments))
            }
            MacroKind::MakeStruct => {
                MacroExpansionKind::MakeStruct(MakeStructExpansion::new(arguments))
            }
            MacroKind::MakeField => {
                MacroExpansionKind::MakeField(MakeFieldExpansion::new(arguments))
            }
            MacroKind::Annotate => MacroExpansionKind::Annotate(AnnotateExpansion::new(arguments)),
            MacroKind::Flatten => MacroExpansionKind::Flatten(FlattenExpansion::new(self.context(), self.environment, arguments)),
            MacroKind::Template(template_body) => {
                let template_ref = TemplateMacroRef::new(macro_ref, template_body);
                let new_environment = self.new_evaluation_environment()?;
                let kind = MacroExpansionKind::Template(TemplateExpansion::new(template_ref));
                return Ok(MacroExpansion::new(self.context(), new_environment, kind));
            }
            MacroKind::ToDo => todo!("system macro {}", macro_ref.name().unwrap()),

            MacroKind::IfNone => MacroExpansionKind::Conditional(ConditionalExpansion::if_none(arguments)),
            MacroKind::IfSome => MacroExpansionKind::Conditional(ConditionalExpansion::if_some(arguments)),
            MacroKind::IfSingle => MacroExpansionKind::Conditional(ConditionalExpansion::if_single(arguments)),
            MacroKind::IfMulti => MacroExpansionKind::Conditional(ConditionalExpansion::if_multi(arguments)),
        };
        Ok(MacroExpansion::new(
            self.context(),
            self.environment,
            expansion_kind,
        ))
    }
}

impl<'top, D: Decoder> From<TemplateMacroInvocation<'top, D>> for MacroExpr<'top, D> {
    fn from(value: TemplateMacroInvocation<'top, D>) -> Self {
        MacroExpr::from_template_macro(value)
    }
}

/// Steps over the argument expressions passed to a macro invocation found in a template body.
#[derive(Copy, Clone, Debug)]
pub struct TemplateMacroInvocationArgsIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    environment: Environment<'top, D>,
    host_template: TemplateMacroRef<'top>,
    // The range of value expressions in the host template's body that are arguments to the
    // macro being invoked
    arg_expressions: &'top [TemplateBodyExpr],
    arg_index: usize,
}

impl<'top, D: Decoder> TemplateMacroInvocationArgsIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        arg_expressions: &'top [TemplateBodyExpr],
        host_template: TemplateMacroRef<'top>,
    ) -> Self {
        Self {
            environment,
            context,
            arg_expressions,
            host_template,
            arg_index: 0,
        }
    }

    pub fn is_exhausted(&self) -> bool {
        let current = self.arg_index;
        let max = self.arg_expressions.len();
        current == max
    }
}

impl<'top, D: Decoder> Iterator for TemplateMacroInvocationArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let arg = self.arg_expressions.get(self.arg_index)?;
        let arg_expr = arg.to_value_expr(self.context, self.environment, self.host_template);
        self.arg_index += arg.num_expressions();
        Some(Ok(arg_expr))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let num_args = self.arg_expressions.len();
        (num_args, Some(num_args))
    }
}

/// A reference to a variable in a template body.
#[derive(Copy, Clone, PartialEq)]
pub struct TemplateBodyVariableReference {
    signature_index: u16,
}

impl Debug for TemplateBodyVariableReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "var_index={}", self.signature_index)
    }
}

impl TemplateBodyVariableReference {
    pub fn new(signature_index: u16) -> Self {
        Self { signature_index }
    }
    pub fn signature_index(&self) -> usize {
        self.signature_index as usize
    }
    pub fn name<'a>(&self, signature: &'a MacroSignature) -> &'a str {
        signature
            .parameters()
            .get(self.signature_index())
            .unwrap()
            .name()
    }
    /// Pairs this variable reference with the given template macro reference, allowing information
    /// about the template definition to be retrieved later.
    pub(crate) fn resolve<'top>(&self, host_macro: &'top Macro) -> TemplateVariableReference<'top> {
        TemplateVariableReference::new(host_macro, self.signature_index)
    }
}

/// A value literal found in the body of a template.
///
/// This type is similar to [`TemplateBodyElement`], but holds resolved references rather than
/// addresses.
#[derive(Clone, Copy, Debug)]
pub struct TemplateElement<'top> {
    // This type holds a reference to the host template macro, which contains some shared resources
    // like a `Vec` of annotation definitions.
    template: TemplateMacroRef<'top>,
    element: &'top TemplateBodyElement,
    expr_range: ExprRange,
}

impl<'top> TemplateElement<'top> {
    pub fn new(
        template: TemplateMacroRef<'top>,
        element: &'top TemplateBodyElement,
        expr_range: ExprRange,
    ) -> Self {
        Self {
            template,
            element,
            expr_range,
        }
    }
    pub fn annotations(&self) -> &'top [Symbol] {
        self.template
            .body()
            .annotations_storage()
            .get(self.element.annotations_range().ops_range())
            .unwrap()
    }
    pub fn annotations_range(&self) -> AnnotationsRange {
        self.element.annotations_range
    }
    pub fn value(&self) -> &'top TemplateValue {
        &self.element.value
    }
    pub fn template(&self) -> TemplateMacroRef<'top> {
        self.template
    }
    pub fn expr_range(&self) -> ExprRange {
        self.expr_range
    }
    pub fn nested_expressions(&self) -> &'top [TemplateBodyExpr] {
        self.template()
            .body()
            .expressions()
            .get(self.expr_range.tail())
            .unwrap()
    }
}

/// An annotated value in a template body.
#[derive(Clone, PartialEq)]
pub struct TemplateBodyElement {
    // To minimize allocations, all annotations live in a single `Vec` in the `TemplateBody`.
    // Each element holds a range pointing to its annotation sequence.
    pub(crate) annotations_range: AnnotationsRange,
    pub(crate) value: TemplateValue,
}

impl Debug for TemplateBodyElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "tdl_element={:?}", self.value)
    }
}

impl TemplateBodyElement {
    pub fn with_value(value: TemplateValue) -> Self {
        Self {
            annotations_range: AnnotationsRange::empty(),
            value,
        }
    }
    pub fn with_annotations(mut self, range: Range<usize>) -> Self {
        self.annotations_range = AnnotationsRange::new(range);
        self
    }

    pub fn value(&self) -> &TemplateValue {
        &self.value
    }
    pub fn annotations_range(&self) -> AnnotationsRange {
        self.annotations_range
    }

    pub fn annotations<'a>(&self, template: &'a TemplateMacro) -> &'a [Symbol] {
        template
            .body()
            .annotations_storage()
            .get(self.annotations_range().ops_range())
            // If the annotations range is invalid, that's a bug; we cannot return an error.
            .unwrap()
    }
}

/// A value literal found int he body of a template. This type is similar to [`Value`], but its
/// container types hold ranges of expression addresses rather than a materialized tree of data.
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateValue {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    Symbol(Symbol),
    String(Str),
    Clob(Bytes),
    Blob(Bytes),
    // The range of ensuing `TemplateBodyValueExpr`s that belong to this container.
    List,
    SExp,
    // A 'closed' struct quasi-literal. All field names are known at compile time.
    Struct(TemplateStructIndex),
    // TODO: Implementation of a `make_struct` macro requires an 'open' struct whose fields will
    //       often not be known at compile time.
}

/// A mapping of struct field names to one or more template body addresses that have that
/// field name. This type is used to allow field lookups within a template struct to happen in
/// constant rather than linear time.
pub type TemplateStructIndex = FxHashMap<Symbol, Vec<usize>>;

impl TemplateValue {
    pub fn is_null(&self) -> bool {
        matches!(self, TemplateValue::Null(_))
    }

    pub fn ion_type(&self) -> IonType {
        // TODO: Implement this with a Rust macro instead.
        //       See: https://github.com/amazon-ion/ion-rust/issues/650
        use TemplateValue::*;
        match self {
            Null(ion_type) => *ion_type,
            Bool(_) => IonType::Bool,
            Int(_) => IonType::Int,
            Float(_) => IonType::Float,
            Decimal(_) => IonType::Decimal,
            Timestamp(_) => IonType::Timestamp,
            Symbol(_) => IonType::Symbol,
            String(_) => IonType::String,
            Clob(_) => IonType::Clob,
            Blob(_) => IonType::Blob,
            List => IonType::List,
            SExp => IonType::SExp,
            Struct(_) => IonType::Struct,
        }
    }
}

/// A slice of a [`TemplateBody`]'s sequence of `TemplateExpansionStep`. This type can be used to
/// represent containers (list, sexp, struct) or macro invocations, all of which use an evaluator
/// to iteratively evaluate a series of `TemplateExpansionStep`s. This type does not hold a reference
/// to the template definition itself.
pub type ExprRange = SmallRange;

/// A slice of a [`TemplateBody`]'s shared `Vec` of annotation definitions. Each value in the
/// template body holds an `AnnotationsRange` that indicates which annotations in the shared
/// collections apply to it.
pub type AnnotationsRange = SmallRange;

/// A range that takes 8 bytes instead of `Range<usize>`'s 16. This is useful for cases like
/// annotations where a capacity of 4 billion+ is more than enough. It also implements `Copy`,
/// making it possible for enclosing types to also implement `Copy`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SmallRange {
    start: u32,
    end: u32,
}

impl SmallRange {
    pub fn empty() -> Self {
        Self { start: 0, end: 0 }
    }

    pub fn new(range: Range<usize>) -> Self {
        debug_assert!(u32::try_from(range.start).is_ok());
        debug_assert!(u32::try_from(range.end).is_ok());
        Self {
            start: range.start as u32,
            end: range.end as u32,
        }
    }

    pub fn start(&self) -> usize {
        self.start as usize
    }

    pub fn end(&self) -> usize {
        self.end as usize
    }

    /// Produces an equivalent [`std::ops::Range`].
    ///
    /// `std::ops::Range` is twice as large as `SmallRange` on 64 bit machines and does not
    /// implement the `Copy` trait. This method is a convenience that allows a `SmallRange` to be
    /// used as a collection index.
    // We are not able to implement `std::ops::Index<SmallRange>` for the stdlib's collections as
    // this crate owns neither the `Index` trait nor the collections themselves.
    pub fn ops_range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }

    pub fn tail(&self) -> Range<usize> {
        self.start as usize + 1..self.end as usize
    }

    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
