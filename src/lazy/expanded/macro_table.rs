use crate::lazy::expanded::compiler::ExpansionAnalysis;
use crate::lazy::expanded::template::{
    MacroSignature, TemplateBody, TemplateMacro, TemplateMacroRef,
};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::result::IonFailure;
use crate::{EncodingContext, IonResult, IonType, IonVersion, TemplateCompiler};
use compact_str::CompactString;
use delegate::delegate;
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::cell::RefCell;
use std::sync::{Arc, LazyLock};

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
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

impl Macro {
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
        Macro::new(
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

/// The kinds of macros supported by
/// [`MacroEvaluator`](crate::MacroEvaluator)
/// This list parallels
/// [`MacroExpansionKind`](crate::MacroExpansionKind),
/// but its variants do not hold any associated state.
#[derive(Debug, Clone, PartialEq)]
pub enum MacroKind {
    None, // `(.none)` returns the empty stream
    ExprGroup,
    MakeString,
    MakeSymbol,
    MakeField,
    MakeStruct,
    Annotate,
    Flatten,
    Template(TemplateBody),
    IfNone,
    IfSome,
    IfSingle,
    IfMulti,
    // A placeholder for not-yet-implemented macros
    ToDo,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct MacroRef<'top> {
    id: MacroIdRef<'top>,
    reference: &'top Macro,
}

impl<'top> MacroRef<'top> {
    pub fn new(macro_id: MacroIdRef<'top>, reference: &'top Macro) -> Self {
        Self {
            id: macro_id,
            reference,
        }
    }

    pub fn require_template(self) -> TemplateMacroRef<'top> {
        if let MacroKind::Template(body) = &self.kind() {
            return TemplateMacroRef::new(self.reference(), body);
        }
        unreachable!(
            "caller required a template macro but found {:?}",
            self.kind()
        )
    }

    pub fn id(&self) -> MacroIdRef<'top> {
        self.id
    }

    pub fn reference(&self) -> &'top Macro {
        self.reference
    }

    delegate! {
        to self.reference {
            pub fn name(&'top self) -> Option<&'top str>;
            pub fn signature(self) -> &'top MacroSignature;
            pub fn kind(&self) -> &'top MacroKind;
            pub fn expansion_analysis(&self) -> ExpansionAnalysis;
            pub fn can_be_lazily_evaluated_at_top_level(&self) -> bool;
            pub fn must_produce_exactly_one_value(&self) -> bool;
        }
    }
}

/// Allows callers to resolve a macro ID (that is: name or address) to a [`MacroKind`], confirming
/// its validity and allowing evaluation to begin.
#[derive(Debug, Clone)]
pub struct MacroTable {
    // Stores `Rc` references to the macro definitions to make cloning the table's contents cheaper.
    macros_by_address: Vec<Arc<Macro>>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: FxHashMap<CompactString, usize>,
}

/// A lazily initialized singleton instance of the Ion 1.1 system macro table.
///
/// This instance is shared by all readers, minimizing the number of times that macro compilation
/// and heap allocation occurs.
pub static ION_1_1_SYSTEM_MACROS: LazyLock<MacroTable> =
    LazyLock::new(MacroTable::construct_system_macro_table);

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

    fn compile_system_macros() -> Vec<Arc<Macro>> {
        // This is wrapped in a `RefCell` in order to allow two different closures to hold
        // runtime-checked mutating references to the context. This overhead is minimal and is only
        // paid during the initialization of the singleton system macro table.
        let bootstrap_context = RefCell::new(EncodingContext::empty());

        // Creates a `Macro` from a TDL expression
        let template = |source: &str| {
            // Compile the given TDL source expression using the current context.
            let macro_ref = Arc::new(Macro::from_template_macro(
                TemplateCompiler::compile_from_source(bootstrap_context.borrow().get_ref(), source)
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
            let macro_ref = Arc::new(Macro::named(
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
                MacroKind::ToDo,
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
                MacroKind::ToDo,
                ExpansionAnalysis::application_value_stream(),
            ),
            builtin(
                "sum",
                "(a b)",
                MacroKind::ToDo,
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
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Decimal),
            ),
            builtin(
                "make_timestamp",
                "(year month? day? hour? minute? second? offset_minutes?)",
                MacroKind::ToDo,
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

    pub fn macro_with_id<'a, 'b, I: Into<MacroIdRef<'b>>>(&'a self, id: I) -> Option<MacroRef<'a>> {
        let id = id.into();
        match id {
            MacroIdRef::LocalName(name) => self.macro_with_name(name),
            MacroIdRef::LocalAddress(address) => self.macro_at_address(address),
            MacroIdRef::SystemAddress(system_address) => {
                ION_1_1_SYSTEM_MACROS.macro_at_address(system_address.as_usize())
            }
        }
    }

    pub fn macro_at_address(&self, address: usize) -> Option<MacroRef<'_>> {
        let id = MacroIdRef::LocalAddress(address);
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { id, reference })
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<MacroRef<'_>> {
        let address = *self.macros_by_name.get(name)?;
        let id = MacroIdRef::LocalAddress(address);
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { id, reference })
    }

    pub(crate) fn clone_macro_with_name(&self, name: &str) -> Option<Arc<Macro>> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(Arc::clone(reference))
    }

    pub(crate) fn clone_macro_with_address(&self, address: usize) -> Option<Arc<Macro>> {
        let reference = self.macros_by_address.get(address)?;
        Some(Arc::clone(reference))
    }

    pub(crate) fn clone_macro_with_id(&self, macro_id: MacroIdRef<'_>) -> Option<Arc<Macro>> {
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

        let new_macro = Macro::new(
            template.name,
            template.signature,
            MacroKind::Template(template.body),
            template.expansion_analysis,
        );

        self.macros_by_address.push(Arc::new(new_macro));
        Ok(id)
    }

    pub(crate) fn append_macro(&mut self, macro_ref: &Arc<Macro>) -> IonResult<()> {
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
}
