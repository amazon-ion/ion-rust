use crate::lazy::encoder::writer::WriterMacroTable;
use crate::lazy::expanded::compiler::ExpansionAnalysis;
use crate::lazy::expanded::template::{
    MacroSignature, ParameterCardinality, ParameterEncoding, SignatureIterator, TemplateBody,
    TemplateElement, TemplateMacro, TemplateMacroRef, TemplateValue,
};
use crate::lazy::text::raw::v1_1::reader::{
    MacroAddress, MacroIdRef, ModuleKind, QualifiedAddress, SystemMacroAddress,
};
use crate::result::IonFailure;
use crate::{
    AnnotatableWriter, EncodingContext, IonResult, IonType, IonVersion, SequenceWriter,
    StructWriter, SymbolRef, TemplateBodyExpr, TemplateBodyExprKind, TemplateCompiler, ValueWriter,
    WriteAsIon,
};
use compact_str::CompactString;
use delegate::delegate;
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::cell::RefCell;
use std::sync::{Arc, LazyLock};

impl From<TemplateMacro> for MacroDef {
    fn from(template: TemplateMacro) -> Self {
        MacroDef::new(
            template.name,
            template.signature,
            MacroKind::Template(template.body),
            template.expansion_analysis,
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroDef {
    name: Option<CompactString>,
    signature: MacroSignature,
    kind: MacroKind,
    // Compile-time heuristics that allow the reader to evaluate e-expressions lazily or using fewer
    // resources in many cases.
    //
    // For the time being, e-expressions that could produce multiple values cannot be lazily evaluated.
    // This is because the reader gives out lazy value handles for each value in the stream. If it knows
    // in advance that an expression will produce one value, it can give out a lazy value that is
    // backed by that e-expression.
    //
    // At the top level, e-expressions that both:
    // 1. Produce a single value
    //   and
    // 2. Will not produce a system value
    // can be lazily evaluated.
    //
    // At other levels of nesting, the single-value expansion is the only requirement for lazy
    // evaluation.
    expansion_analysis: ExpansionAnalysis,
}

impl MacroDef {
    pub fn named(
        name: impl Into<CompactString>,
        signature: MacroSignature,
        kind: MacroKind,
        expansion_analysis: ExpansionAnalysis,
    ) -> Self {
        Self::new(Some(name.into()), signature, kind, expansion_analysis)
    }

    pub fn anonymous(
        signature: MacroSignature,
        kind: MacroKind,
        expansion_analysis: ExpansionAnalysis,
    ) -> Self {
        Self::new(None, signature, kind, expansion_analysis)
    }

    pub fn from_template_macro(template_macro: TemplateMacro) -> Self {
        MacroDef::new(
            template_macro.name,
            template_macro.signature,
            MacroKind::Template(template_macro.body),
            template_macro.expansion_analysis,
        )
    }

    pub fn new(
        name: Option<CompactString>,
        signature: MacroSignature,
        kind: MacroKind,
        expansion_analysis: ExpansionAnalysis,
    ) -> Self {
        Self {
            name,
            signature,
            kind,
            expansion_analysis,
        }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
    pub(crate) fn clone_name(&self) -> Option<CompactString> {
        self.name.clone()
    }
    pub fn signature(&self) -> &MacroSignature {
        &self.signature
    }

    pub fn kind(&self) -> &MacroKind {
        &self.kind
    }

    pub fn require_template(&self) -> TemplateMacroRef<'_> {
        if let MacroKind::Template(body) = &self.kind() {
            return TemplateMacroRef::new(self, body);
        }
        unreachable!(
            "caller required a template macro but found {:?}",
            self.kind()
        )
    }

    pub fn expansion_analysis(&self) -> ExpansionAnalysis {
        self.expansion_analysis
    }

    pub fn can_be_lazily_evaluated_at_top_level(&self) -> bool {
        self.expansion_analysis()
            .can_be_lazily_evaluated_at_top_level()
    }

    pub fn must_produce_exactly_one_value(&self) -> bool {
        self.expansion_analysis().must_produce_exactly_one_value()
    }
}

impl WriteAsIon for TemplateMacroRef<'_> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> IonResult<()> {
        let mut outer_sexp = writer.sexp_writer()?;
        outer_sexp.write_symbol("macro")?;
        if let Some(name) = &self.name {
            outer_sexp.write_symbol(name.as_str())?;
        }
        // If there isn't a name, it's an anonymous macro. Move on to writing the signature.
        write_macro_signature_as_ion(outer_sexp.value_writer(), self.signature())?;
        let body = self.body();
        // The first expression on the compiled 'tape' version of the body contains all of the subexpressions.
        let root_expr = body.expressions().first().expect("empty body");
        debug_assert!(root_expr.expr_range().len() == body.expressions.len());
        write_body_expr_as_ion(outer_sexp.value_writer(), *self, root_expr)?;
        outer_sexp.close()
    }
}

fn write_macro_signature_as_ion<V: ValueWriter>(
    value_writer: V,
    macro_signature: &MacroSignature,
) -> IonResult<()> {
    let mut signature = value_writer.sexp_writer()?;
    for param in macro_signature.parameters() {
        let value_writer = signature.value_writer();
        match param.encoding() {
            ParameterEncoding::Tagged => value_writer.write_symbol(param.name())?,
            ParameterEncoding::FlexUInt => value_writer
                .with_annotations("flex_uint")?
                .write_symbol(param.name())?,
            ParameterEncoding::UInt8 => value_writer
                .with_annotations("uint8")?
                .write_symbol(param.name())?,
            ParameterEncoding::UInt16 => value_writer
                .with_annotations("uint16")?
                .write_symbol(param.name())?,
            ParameterEncoding::UInt32 => value_writer
                .with_annotations("uint32")?
                .write_symbol(param.name())?,
            ParameterEncoding::UInt64 => value_writer
                .with_annotations("uint64")?
                .write_symbol(param.name())?,
            ParameterEncoding::MacroShaped(_) => todo!(),
        };
        let cardinality_modifier = match param.cardinality() {
            ParameterCardinality::ExactlyOne => None,
            ParameterCardinality::ZeroOrOne => Some("?"),
            ParameterCardinality::ZeroOrMore => Some("*"),
            ParameterCardinality::OneOrMore => Some("+"),
        };
        if let Some(modifier) = cardinality_modifier {
            signature.write_symbol(modifier)?;
        }
    }
    signature.close()
}

fn write_body_expr_as_ion<V: ValueWriter>(
    value_writer: V,
    template_macro: TemplateMacroRef<'_>,
    body_expr: &TemplateBodyExpr,
) -> IonResult<()> {
    use TemplateBodyExprKind::*;
    let expr_range = body_expr.expr_range();
    match body_expr.kind() {
        Element(body_element) => {
            let element = TemplateElement::new(template_macro, body_element, expr_range);
            write_template_element_as_ion(value_writer, element)
        }
        Variable(variable) => {
            let mut sexp_writer = value_writer.sexp_writer()?;
            let parameter = &template_macro.signature().parameters()[variable.signature_index()];
            sexp_writer
                .write_symbol("%")?
                .write_symbol(parameter.name())?;
            sexp_writer.close()
        }
        MacroInvocation(invocation_expr) => {
            let mut sexp_writer = value_writer.sexp_writer()?;
            let Some(macro_name) = &invocation_expr.invoked_macro.name else {
                // TODO: When compiling the macro, store the address of the macro invocation in the
                //       TemplateBodyMacroInvocation along with the Arc<MacroDef>. If the macro is
                //       anonymous, we can use the address instead.
                todo!("serializing invocations of anonymous macros")
            };
            sexp_writer
                .write_symbol(".")?
                .write_symbol(macro_name.as_str())?;

            // All of the expressions after the first one are arguments to the invocation.
            let macro_args_start = expr_range.start() + 1;
            let num_arg_exprs = expr_range.len() - 1;
            let macro_args_end = macro_args_start + num_arg_exprs;
            let arg_exprs = &template_macro.body().expressions()[macro_args_start..macro_args_end];

            let mut arg_expr_index: usize = 0;
            while arg_expr_index < num_arg_exprs {
                let arg_expr = arg_exprs.get(arg_expr_index).unwrap_or_else(|| {
                    panic!(
                        "arg expr index {arg_expr_index} out of bounds, arg_exprs.len()={}",
                        arg_exprs.len()
                    )
                });
                // If this is an expression group...
                if matches!(arg_expr.kind(), ExprGroup(_))
                    // ...and it contains all of the remaining expressions...
                    && arg_expr.expr_range().end() >= macro_args_end
                {
                    // ...then we can write all of the expressions inline, taking advantage of rest syntax.
                    let nested_exprs = &arg_exprs[1..];
                    write_sequence_contents(&mut sexp_writer, template_macro, nested_exprs)?;
                    arg_expr_index += arg_expr.num_expressions();
                    continue;
                }
                write_body_expr_as_ion(sexp_writer.value_writer(), template_macro, arg_expr)?;
                arg_expr_index += arg_expr.num_expressions();
            }
            sexp_writer.close()
        }
        ExprGroup(_parameter) => {
            let nested_exprs_start = expr_range.start() + 1;
            let group_end = expr_range.end();
            let expressions = &template_macro.body().expressions()[nested_exprs_start..group_end];
            let mut sexp_writer = value_writer.sexp_writer()?;
            sexp_writer.write_symbol("..")?;
            write_sequence_contents(&mut sexp_writer, template_macro, expressions)?;
            sexp_writer.close()
        }
    }
}

fn write_template_element_as_ion<V: ValueWriter>(
    value_writer: V,
    element: TemplateElement<'_>,
) -> IonResult<()> {
    let annotations = element.annotations();
    use TemplateValue::*;
    let value_writer = value_writer.with_annotations(annotations)?;
    match element.value() {
        Null(ion_type) => value_writer.write_null(*ion_type),
        Bool(b) => value_writer.write_bool(*b),
        Int(i) => value_writer.write_int(i),
        Float(f) => value_writer.write_f64(*f),
        Decimal(d) => value_writer.write_decimal(d),
        Timestamp(t) => value_writer.write_timestamp(t),
        Symbol(s) => value_writer.write_symbol(s),
        String(s) => value_writer.write_string(s),
        Clob(c) => value_writer.write_clob(c),
        Blob(b) => value_writer.write_blob(b),
        List => write_template_sequence_element(
            value_writer.list_writer()?,
            element.template(),
            element.nested_expressions(),
        ),
        SExp => write_template_sequence_element(
            value_writer.sexp_writer()?,
            element.template(),
            element.nested_expressions(),
        ),
        Struct(_field_index) => write_template_struct_element(element, value_writer),
    }
}

fn write_template_sequence_element<S: SequenceWriter>(
    mut sequence: S,
    template_macro: TemplateMacroRef<'_>,
    expressions: &[TemplateBodyExpr],
) -> IonResult<S::Resources> {
    write_sequence_contents(&mut sequence, template_macro, expressions)?;
    sequence.close()
}

fn write_sequence_contents<S: SequenceWriter>(
    parent_writer: &mut S,
    template_macro: TemplateMacroRef<'_>,
    expressions: &[TemplateBodyExpr],
) -> IonResult<()> {
    let mut expr_index: usize = 0;
    while expr_index < expressions.len() {
        let expression = expressions
            .get(expr_index)
            .expect("expr group expr out of bounds");
        write_body_expr_as_ion(parent_writer.value_writer(), template_macro, expression)?;
        expr_index += expression.num_expressions();
    }
    Ok(())
}

fn write_template_struct_element<V: ValueWriter>(
    element: TemplateElement<'_>,
    value_writer: V,
) -> IonResult<()> {
    let mut struct_writer = value_writer.struct_writer()?;
    let mut expr_index: usize = 0;
    let nested_expressions = element.nested_expressions();
    while expr_index < nested_expressions.len() {
        let name_element = nested_expressions
            .get(expr_index)
            .expect("out of bounds")
            .kind()
            // In a template, struct field names are always literals.
            .require_element();
        let name: SymbolRef<'_> = match &name_element.value {
            TemplateValue::Symbol(s) => s.into(),
            TemplateValue::String(s) => s.text().into(),
            _ => unreachable!("template struct field had a non-text field name"),
        };
        let value_expr_address = expr_index + 1;
        let value_expr = nested_expressions
            .get(value_expr_address)
            .expect("template struct had field name with no value");

        write_body_expr_as_ion(
            struct_writer.field_writer(name),
            element.template(),
            value_expr,
        )?;

        // Move beyond the current value expression.
        expr_index = value_expr_address + value_expr.num_expressions();
    }

    struct_writer.close()
}

/// The kinds of macros supported by
/// [`MacroEvaluator`](crate::MacroEvaluator)
/// This list parallels
/// [`MacroExpansionKind`](crate::MacroExpansionKind),
/// but its variants do not hold any associated state.
#[derive(Debug, Clone, PartialEq)]
pub enum MacroKind {
    None, // `(.none)` returns the empty stream
    ExprGroup,
    MakeDecimal,
    MakeString,
    MakeSymbol,
    MakeField,
    MakeStruct,
    MakeTimestamp,
    Annotate,
    Flatten,
    Template(TemplateBody),
    IfNone,
    IfSome,
    IfSingle,
    IfMulti,
    Delta,
    Repeat,
    Sum,
    // A placeholder for not-yet-implemented macros
    ToDo,
}

/// A Macro reference that is guaranteed to be valid for its lifespan.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct MacroRef<'top> {
    qualified_address: QualifiedAddress,
    def: &'top MacroDef,
}

impl<'top> MacroRef<'top> {
    pub(crate) fn new(qualified_address: QualifiedAddress, def: &'top MacroDef) -> Self {
        Self {
            qualified_address,
            def,
        }
    }

    pub fn require_template(self) -> TemplateMacroRef<'top> {
        if let MacroKind::Template(body) = &self.kind() {
            return TemplateMacroRef::new(self.definition(), body);
        }
        unreachable!(
            "caller required a template macro but found {:?}",
            self.kind()
        )
    }

    pub fn module(&self) -> ModuleKind {
        self.qualified_address.module()
    }

    pub fn address(&self) -> MacroAddress {
        self.qualified_address.address()
    }

    pub fn id(&self) -> MacroIdRef<'top> {
        match self.qualified_address.module() {
            ModuleKind::Default => MacroIdRef::LocalAddress(self.qualified_address.address()),
            ModuleKind::System => MacroIdRef::SystemAddress(SystemMacroAddress::new_unchecked(
                self.qualified_address.address(),
            )),
        }
    }

    pub fn definition(&self) -> &'top MacroDef {
        self.def
    }

    pub(crate) fn iter_signature(&self) -> SignatureIterator<'top> {
        SignatureIterator::new(*self)
    }

    delegate! {
        to self.definition() {
            pub fn name(&self) -> Option<&'top str>;
            pub fn signature(self) -> &'top MacroSignature;
            pub fn kind(&self) -> &'top MacroKind;
            pub fn expansion_analysis(&self) -> ExpansionAnalysis;
            pub fn can_be_lazily_evaluated_at_top_level(&self) -> bool;
            pub fn must_produce_exactly_one_value(&self) -> bool;
        }
    }
}

/// An owned handle to a macro table entry.
/// If the encoding context changes after this handle is created, it may be invalidated.
/// In this case, creating an e-expression writer with this handle will produce an `Err`.
#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct Macro {
    // The compiled definition of the macro.
    definition: Arc<MacroDef>,
    // The `(module, address)` pair indicating where this macro was last installed
    // in the encoding context.
    path: QualifiedAddress,
}

impl Macro {
    pub(crate) fn new(definition: Arc<MacroDef>, path: QualifiedAddress) -> Self {
        Self { definition, path }
    }

    pub fn qualified_address(&self) -> QualifiedAddress {
        self.path
    }

    pub fn module(&self) -> ModuleKind {
        self.path.module()
    }

    pub fn address(&self) -> MacroAddress {
        self.path.address()
    }

    pub fn name(&self) -> Option<&str> {
        self.definition.name()
    }

    pub fn signature(&self) -> &MacroSignature {
        self.definition.signature()
    }

    pub(crate) fn definition(&self) -> &Arc<MacroDef> {
        &self.definition
    }

    pub fn as_ref(&self) -> MacroRef<'_> {
        MacroRef::new(self.qualified_address(), &self.definition)
    }
}

/// Allows callers to resolve a macro ID (that is: name or address) to a [`MacroKind`], confirming
/// its validity and allowing evaluation to begin.
#[derive(Debug, Clone)]
pub struct MacroTable {
    // Stores `Rc` references to the macro definitions to make cloning the table's contents cheaper.
    macros_by_address: Vec<Arc<MacroDef>>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: FxHashMap<CompactString, usize>,
}

/// A lazily initialized singleton instance of the Ion 1.1 system macro table.
///
/// This instance is shared by all readers, minimizing the number of times that macro compilation
/// and heap allocation occurs.
pub static ION_1_1_SYSTEM_MACROS: LazyLock<MacroTable> =
    LazyLock::new(MacroTable::construct_system_macro_table);

/// A lazily initialized singleton instance of an empty system macro table.
/// This is useful in places where the APIs require version-agnostic access to the macro table.
pub static EMPTY_MACRO_TABLE: LazyLock<WriterMacroTable> =
    LazyLock::new(|| WriterMacroTable::new(MacroTable::empty()));

impl Default for MacroTable {
    fn default() -> Self {
        Self::with_system_macros(IonVersion::default())
    }
}

impl MacroTable {
    // The system macros range from address 0 to 23
    pub const NUM_SYSTEM_MACROS: usize = 24;
    // When a user defines new macros, this is the first ID that will be assigned. This value
    // is expected to change as development continues. It is currently used in several unit tests.
    pub const FIRST_USER_MACRO_ID: usize = Self::NUM_SYSTEM_MACROS;

    fn compile_system_macros() -> Vec<Arc<MacroDef>> {
        // This is wrapped in a `RefCell` in order to allow two different closures to hold
        // runtime-checked mutating references to the context. This overhead is minimal and is only
        // paid during the initialization of the singleton system macro table.
        let bootstrap_context = RefCell::new(EncodingContext::empty());

        // Creates a `Macro` from a TDL expression
        let template = |source: &str| {
            // Compile the given TDL source expression using the current context.
            let macro_ref = Arc::new(MacroDef::from_template_macro(
                TemplateCompiler::compile_from_source(
                    bootstrap_context.borrow().macro_table(),
                    source,
                )
                .unwrap(),
            ));
            // Add the new macro to the context so 'downstream' macros can invoke it.
            bootstrap_context
                .borrow_mut()
                .macro_table_mut()
                .append_macro(&macro_ref)
                .unwrap();
            macro_ref
        };

        // Creates a `Macro` whose implementation is provided by the system
        let builtin = |name: &str,
                       signature: &str,
                       kind: MacroKind,
                       expansion_analysis: ExpansionAnalysis| {
            // Construct a macro from the provided parameters using the current context.
            let macro_ref = Arc::new(MacroDef::named(
                name,
                TemplateCompiler::compile_signature(
                    bootstrap_context.borrow().get_ref(),
                    signature,
                )
                .unwrap(),
                kind,
                expansion_analysis,
            ));
            // Add the new macro to the context so 'downstream' macros can invoke it.
            bootstrap_context
                .borrow_mut()
                .macro_table_mut()
                .append_macro(&macro_ref)
                .unwrap();
            macro_ref
        };

        // Macro definitions in the system table are encoded in **Ion 1.0** because it does not
        // require the Ion 1.1 system macros to exist.
        vec![
            builtin(
                "none",
                "()",
                MacroKind::None,
                ExpansionAnalysis::application_value_stream(),
            ),
            template("(macro values (x*) (%x))"),
            template(
                "(macro default (expr* default_expr*) (.if_none (%expr) (%default_expr) (%expr) ))",
            ),
            template("(macro meta (expr*) (.none))"),
            builtin(
                "repeat",
                "(n expr*)",
                MacroKind::Repeat,
                ExpansionAnalysis::no_assertions_made(),
            ),
            builtin(
                "flatten",
                "(sequences*)",
                MacroKind::Flatten,
                ExpansionAnalysis::application_value_stream(),
            ),
            builtin(
                "delta",
                "(deltas*)",
                MacroKind::Delta,
                ExpansionAnalysis::application_value_stream(),
            ),
            builtin(
                "sum",
                "(a b)",
                MacroKind::Sum,
                ExpansionAnalysis::single_application_value(IonType::Int),
            ),
            builtin(
                "annotate",
                "(annotations* value_to_annotate)",
                MacroKind::Annotate,
                ExpansionAnalysis::possible_system_value(),
            ),
            builtin(
                "make_string",
                "(text_values*)",
                MacroKind::MakeString,
                ExpansionAnalysis::single_application_value(IonType::String),
            ),
            builtin(
                "make_symbol",
                "(text_values*)",
                MacroKind::MakeSymbol,
                ExpansionAnalysis::single_application_value(IonType::Symbol),
            ),
            builtin(
                "make_decimal",
                "(coefficient exponent)",
                MacroKind::MakeDecimal,
                ExpansionAnalysis::single_application_value(IonType::Decimal),
            ),
            builtin(
                "make_timestamp",
                "(year month? day? hour? minute? second? offset_minutes?)",
                MacroKind::MakeTimestamp,
                ExpansionAnalysis::single_application_value(IonType::Timestamp),
            ),
            builtin(
                "make_blob",
                "(lob_values*)",
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Blob),
            ),
            template(
                r#"
                (macro make_list (sequences*)
                    [(.flatten (%sequences))])
            "#,
            ),
            template(
                r#"
                (macro make_sexp (sequences*)
                    ((.flatten (%sequences))))
            "#,
            ),
            builtin(
                "make_field",
                "(name value)",
                MacroKind::MakeField,
                ExpansionAnalysis::single_application_value(IonType::Struct),
            ),
            builtin(
                "make_struct",
                "(fields*)",
                MacroKind::MakeStruct,
                ExpansionAnalysis::single_application_value(IonType::Struct),
            ),
            builtin(
                "parse_ion",
                "(data*)",
                MacroKind::ToDo,
                ExpansionAnalysis::application_value_stream(),
            ),
            template(
                r#"
                        (macro set_symbols (symbols*)
                             $ion::
                             (module _
                               // Set a new symbol table
                               (symbol_table [(%symbols)])
                               // Include the active encoding module macros
                               (macro_table _)
                             )
                       )
                    "#,
            ),
            template(
                r#"
                        (macro add_symbols (symbols*)
                             $ion::
                             (module _
                               // Set a new symbol table
                               (symbol_table _ [(%symbols)])
                               // Include the active encoding module macros
                               (macro_table _)
                             )
                       )
                    "#,
            ),
            template(
                r#"
                       (macro set_macros (macro_definitions*)
                           $ion::
                           (module _
                               // Include the active encoding module symbols
                               (symbol_table _)
                               // Set a new macro table
                               (macro_table (%macro_definitions))
                           )
                       )
                    "#,
            ),
            template(
                r#"
                       (macro add_macros (macro_definitions*)
                           $ion::
                           (module _
                               // Include the active encoding module symbols
                               (symbol_table _)
                               // Set a new macro table
                               (macro_table _ (%macro_definitions))
                           )
                       )
                    "#,
            ),
            builtin(
                "use",
                "(catalog_key version)",
                MacroKind::ToDo,
                ExpansionAnalysis::directive(),
            ),
        ]
    }

    pub(crate) fn construct_system_macro_table() -> Self {
        let macros_by_id = Self::compile_system_macros();
        let mut macros_by_name =
            FxHashMap::with_capacity_and_hasher(macros_by_id.len(), FxBuildHasher);
        for (id, mac) in macros_by_id.iter().enumerate() {
            if let Some(name) = mac.name() {
                macros_by_name.insert(name.into(), id);
            }
            // Anonymous macros are not entered into the macros_by_name lookup table
        }
        Self {
            macros_by_address: macros_by_id,
            macros_by_name,
        }
    }

    // TODO: When multi-module support is added, this can be updated to avoid allocating.
    //       The 1.1 system macro table is now available as a singleton (`ION_1_1_SYSTEM_MACROS`).
    //       While its `Arc<Macro>` contents may be cloned into the user address space, there
    //       isn't a use case for creating a new instance of `MacroTable` to represent the same thing.
    pub fn with_system_macros(ion_version: IonVersion) -> Self {
        match ion_version {
            IonVersion::v1_0 => MacroTable::empty(),
            IonVersion::v1_1 => ION_1_1_SYSTEM_MACROS.clone(),
        }
    }

    pub fn empty() -> Self {
        Self {
            macros_by_address: Vec::new(),
            macros_by_name: FxHashMap::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.macros_by_address.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn macro_with_id<'a, 'b, I: Into<MacroIdRef<'b>>>(&'a self, id: I) -> Option<&'a MacroDef> {
        let id = id.into();
        match id {
            MacroIdRef::LocalName(name) => self.macro_with_name(name),
            MacroIdRef::LocalAddress(address) => self.macro_at_address(address),
            MacroIdRef::SystemAddress(system_address) => {
                ION_1_1_SYSTEM_MACROS.macro_at_address(system_address.as_usize())
            }
        }
    }

    pub fn address_for_id<'a, 'b, I: Into<MacroIdRef<'b>>>(&'a self, id: I) -> Option<usize> {
        let id = id.into();
        match id {
            MacroIdRef::LocalName(name) => self.macros_by_name.get(name).copied(),
            MacroIdRef::LocalAddress(address) if address >= self.macros_by_address.len() => None,
            MacroIdRef::LocalAddress(address) => Some(address),
            // If they're asking the user table for a system address, report that we couldn't find it.
            // TODO: Replace this enum variant with a `QualifiedAddress`.
            // We cannot look the macro up in the system macro table because the meaning of the
            // returned address would be ambiguous—into which macro table does the `usize` index?
            MacroIdRef::SystemAddress(_system_address) => None,
        }
    }

    pub fn macro_at_address(&self, address: usize) -> Option<&MacroDef> {
        Some(self.macros_by_address.get(address)?)
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<&MacroDef> {
        let address = self.address_for_name(name)?;
        self.macro_at_address(address)
    }

    pub(crate) fn clone_macro_with_name(&self, name: &str) -> Option<Arc<MacroDef>> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(Arc::clone(reference))
    }

    pub(crate) fn clone_macro_with_address(&self, address: usize) -> Option<Arc<MacroDef>> {
        let reference = self.macros_by_address.get(address)?;
        Some(Arc::clone(reference))
    }

    pub(crate) fn clone_macro_with_id(&self, macro_id: MacroIdRef<'_>) -> Option<Arc<MacroDef>> {
        use MacroIdRef::*;
        match macro_id {
            LocalName(name) => self.clone_macro_with_name(name),
            LocalAddress(address) => self.clone_macro_with_address(address),
            SystemAddress(system_address) => {
                ION_1_1_SYSTEM_MACROS.clone_macro_with_address(system_address.as_usize())
            }
        }
    }

    pub fn add_template_macro(&mut self, template: TemplateMacro) -> IonResult<usize> {
        let id = self.macros_by_address.len();
        // If the macro has a name, make sure that name is not already in use and then add it.
        if let Some(name) = &template.name {
            if self.macros_by_name.contains_key(name.as_str()) {
                return IonResult::decoding_error(format!("macro named '{name}' already exists"));
            }
            self.macros_by_name.insert(name.clone(), id);
        }

        let new_macro = MacroDef::new(
            template.name,
            template.signature,
            MacroKind::Template(template.body),
            template.expansion_analysis,
        );

        self.macros_by_address.push(Arc::new(new_macro));
        Ok(id)
    }

    pub(crate) fn append_macro(&mut self, macro_ref: &Arc<MacroDef>) -> IonResult<()> {
        let next_id = self.len();
        if let Some(name) = macro_ref.clone_name() {
            if self.macros_by_name.contains_key(name.as_str()) {
                return IonResult::decoding_error(format!("macro named '{name}' already exists"));
            }
            self.macros_by_name.insert(name, next_id);
        }
        self.macros_by_address.push(Arc::clone(macro_ref));
        Ok(())
    }

    pub(crate) fn append_all_macros_from(&mut self, other: &MacroTable) -> IonResult<()> {
        for macro_ref in &other.macros_by_address {
            self.append_macro(macro_ref)?
        }
        Ok(())
    }

    pub(crate) fn reset_to_system_macros(&mut self) {
        self.macros_by_name.clear();
        self.macros_by_address.clear();
        self.append_all_macros_from(&ION_1_1_SYSTEM_MACROS).unwrap()
    }

    pub(crate) fn macros_tail(&self, num_tail_macros: usize) -> &[Arc<MacroDef>] {
        let num_macros = self.macros_by_address.len();
        &self.macros_by_address[num_macros - num_tail_macros..]
    }

    // This method only exists to support the `ion_tests` feature.
    // See: https://github.com/amazon-ion/ion-rust/issues/967
    pub fn iter(&self) -> impl Iterator<Item = Macro> + '_ {
        self.macros_by_address
            .iter()
            .enumerate()
            .map(move |(index, macro_def)| {
                Macro::new(
                    Arc::clone(macro_def),
                    // TODO: This currently sets the module to 'default'.
                    //       We need it to set it to whatever module this MacroTable belongs to,
                    //       which will require a different API.
                    QualifiedAddress::new(ModuleKind::Default, index),
                )
            })
    }
}

#[cfg(all(test, feature = "experimental-ion-1-1"))]
mod tests {
    use crate::lazy::expanded::template::TemplateMacroRef;
    use crate::{
        v1_1, Element, EncodingContext, IonResult, IonVersion, MacroDef, TemplateCompiler,
        WriteAsIon,
    };
    use rstest::rstest;

    fn serialization_test(macro_source: &str) -> IonResult<()> {
        // Read the macro source directly to get the expected Ion.
        let expected = Element::read_one(macro_source)?;
        // Compile the source to a `TemplateMacro`.
        let context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let compiled_template =
            TemplateCompiler::compile_from_source(context.macro_table(), macro_source)?;
        let compiled_macro = MacroDef::from_template_macro(compiled_template.clone());
        let template_ref = TemplateMacroRef::new(&compiled_macro, compiled_template.body());
        // Serialize the template macro to text, then read it back.
        let encoded_text = template_ref.encode_as(v1_1::Text)?;
        let actual = Element::read_one(&encoded_text)?;
        println!("{encoded_text}");
        // Confirm the round-tripped Element is Ion-equal to the expected one.
        assert_eq!(
            actual, expected,
            "actual\n{actual:?}\nwas not equal to expected\n{expected:?}"
        );
        Ok(())
    }

    #[rstest]
    // No params, scalar body
    #[case::constant_bool(r#" (macro True () true) "#)]
    #[case::constant_str(r#" (macro pi () 3.141592654) "#)]
    #[case::constant_timestamp(r#" (macro today () 2025-03-06T) "#)]
    // No params, container body
    #[case::constant_list(r#" (macro list () [1, 2, 3]) "#)]
    #[case::constant_sexp(r#" (macro sexp () (1 2 3)) "#)]
    #[case::constant_struct(r#" (macro strukt () {a: 1, b: 2, c: 3}) "#)]
    // No params, macro invocation body
    #[case::constant_values(r#" (macro abc123 () (.values a b c 1 2 3))"#)]
    // One param, includes variable reference
    #[case::identity(r#" (macro identity (x) (%x)) "#)]
    // Multiple params, includes macro invocation and variable references.
    #[case::identitwo(r#" (macro identitwo (x y) (.values (%x) (%y))) "#)]
    #[case::identithree(r#" (macro identithree (x y z) (.values (%x) (.values (%y) (%z)))) "#)]
    // Variadic params
    #[case::zero_or_one(r#" (macro foo (x y?) {x: (%x), y: (%y)}) "#)]
    #[case::zero_or_more(r#" (macro foo (x y*) {x: (%x), y: (%y)}) "#)]
    #[case::one_or_more(r#" (macro foo (x y+) {x: (%x), y: (%y)}) "#)]
    #[case::assorted(r#" (macro foo (w x? y* z+) {w: (%w), x: (%x), y: (%y), z: (%z)}) "#)]
    // Tagless encoding
    #[case::flex_uint(r#" (macro foo (flex_uint::x) (%x))"#)]
    #[case::flex_uint(r#" (macro foo (flex_uint::x* flex_uint::y+ flex_uint::z?) (%x))"#)]
    fn serialize_template_macro(#[case] macro_source: &str) -> IonResult<()> {
        serialization_test(macro_source)
    }
}
