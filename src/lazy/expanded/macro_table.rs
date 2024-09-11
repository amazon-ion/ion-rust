use delegate::delegate;
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::borrow::Cow;
use std::rc::Rc;

use crate::lazy::expanded::compiler::{ExpansionAnalysis, ExpansionSingleton};
use crate::lazy::expanded::template::{
    MacroSignature, Parameter, ParameterCardinality, ParameterEncoding, RestSyntaxPolicy,
    TemplateBody, TemplateMacro, TemplateMacroRef,
};
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
use crate::result::IonFailure;
use crate::{IonResult, IonType};

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    name: Option<Rc<str>>,
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
        name: impl Into<Rc<str>>,
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

    pub fn new(
        name: Option<Rc<str>>,
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
    pub(crate) fn clone_name(&self) -> Option<Rc<str>> {
        self.name.as_ref().map(Rc::clone)
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
    Void,
    Values,
    MakeString,
    MakeSExp,
    Annotate,
    Template(TemplateBody),
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct MacroRef<'top> {
    address: MacroAddress,
    reference: &'top Macro,
}

impl<'top> MacroRef<'top> {
    pub fn new(address: MacroAddress, reference: &'top Macro) -> Self {
        Self { address, reference }
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

    pub fn id_text(&'top self) -> Cow<'top, str> {
        self.name()
            .map(Cow::from)
            .unwrap_or_else(move || Cow::from(format!("{}", self.address())))
    }

    pub fn address(&self) -> MacroAddress {
        self.address
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
    macros_by_address: Vec<Rc<Macro>>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: FxHashMap<Rc<str>, usize>,
}

thread_local! {
    /// An instance of the Ion 1.1 system macro table is lazily instantiated once per thread,
    /// minimizing the number of times macro compilation occurs.
    ///
    /// The thread-local instance holds `Rc` references to its macro names and macro definitions,
    /// making its contents inexpensive to `clone()` and reducing the number of duplicate `String`s
    /// being allocated over time.
    ///
    /// Each time the user constructs a reader, it clones the thread-local copy of the system macro
    /// table.
    pub static ION_1_1_SYSTEM_MACROS: MacroTable = MacroTable::construct_system_macro_table();
}

impl Default for MacroTable {
    fn default() -> Self {
        Self::with_system_macros()
    }
}

impl MacroTable {
    pub const SYSTEM_MACRO_KINDS: &'static [MacroKind] = &[
        MacroKind::Void,
        MacroKind::Values,
        MacroKind::MakeString,
        MacroKind::MakeSExp,
        MacroKind::Annotate,
    ];
    pub const NUM_SYSTEM_MACROS: usize = Self::SYSTEM_MACRO_KINDS.len();
    // When a user defines new macros, this is the first ID that will be assigned. This value
    // is expected to change as development continues. It is currently used in several unit tests.
    pub const FIRST_USER_MACRO_ID: usize = Self::NUM_SYSTEM_MACROS;

    fn compile_system_macros() -> Vec<Rc<Macro>> {
        vec![
            Rc::new(Macro::named(
                "void",
                MacroSignature::new(vec![]).unwrap(),
                MacroKind::Void,
                ExpansionAnalysis {
                    could_produce_system_value: false,
                    must_produce_exactly_one_value: false,
                    // This is false because lazy evaluation requires giving out a LazyValue as a
                    // handle to eventually read the expression. We cannot give out a `LazyValue`
                    // for e-expressions that will produce 0 or 2+ values.
                    can_be_lazily_evaluated_at_top_level: false,
                    expansion_singleton: None,
                },
            )),
            Rc::new(Macro::named(
                "values",
                MacroSignature::new(vec![Parameter::new(
                    "expr_group",
                    ParameterEncoding::Tagged,
                    ParameterCardinality::ZeroOrMore,
                    RestSyntaxPolicy::Allowed,
                )])
                .unwrap(),
                MacroKind::Values,
                ExpansionAnalysis {
                    could_produce_system_value: true,
                    must_produce_exactly_one_value: false,
                    can_be_lazily_evaluated_at_top_level: false,
                    expansion_singleton: None,
                },
            )),
            Rc::new(Macro::named(
                "make_string",
                MacroSignature::new(vec![Parameter::new(
                    "expr_group",
                    ParameterEncoding::Tagged,
                    ParameterCardinality::ZeroOrMore,
                    RestSyntaxPolicy::Allowed,
                )])
                .unwrap(),
                MacroKind::MakeString,
                ExpansionAnalysis {
                    could_produce_system_value: false,
                    must_produce_exactly_one_value: true,
                    can_be_lazily_evaluated_at_top_level: true,
                    expansion_singleton: Some(ExpansionSingleton {
                        is_null: false,
                        ion_type: IonType::String,
                        num_annotations: 0,
                    }),
                },
            )),
            Rc::new(Macro::named(
                "make_sexp",
                MacroSignature::new(vec![Parameter::new(
                    "sequences",
                    ParameterEncoding::Tagged,
                    ParameterCardinality::ZeroOrMore,
                    RestSyntaxPolicy::Allowed,
                )])
                .unwrap(),
                MacroKind::MakeSExp,
                ExpansionAnalysis {
                    // `make_sexp` produces an unannotated s-expression, so it can't make a system
                    // value when it's the body of a macro. (It would need to be nested in a call
                    // to `annotate`.
                    could_produce_system_value: false,
                    must_produce_exactly_one_value: true,
                    can_be_lazily_evaluated_at_top_level: true,
                    expansion_singleton: Some(ExpansionSingleton {
                        is_null: false,
                        ion_type: IonType::SExp,
                        num_annotations: 0,
                    }),
                },
            )),
            Rc::new(Macro::named(
                "annotate",
                MacroSignature::new(vec![
                    Parameter::new(
                        "annotations",
                        ParameterEncoding::Tagged,
                        ParameterCardinality::ZeroOrMore,
                        RestSyntaxPolicy::NotAllowed,
                    ),
                    Parameter::new(
                        "value_to_annotate",
                        ParameterEncoding::Tagged,
                        ParameterCardinality::ExactlyOne,
                        RestSyntaxPolicy::NotAllowed,
                    ),
                ])
                .unwrap(),
                MacroKind::Annotate,
                ExpansionAnalysis {
                    could_produce_system_value: true,
                    must_produce_exactly_one_value: true,
                    can_be_lazily_evaluated_at_top_level: false,
                    expansion_singleton: None,
                },
            )),
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

    pub fn with_system_macros() -> Self {
        ION_1_1_SYSTEM_MACROS.with(|system_macros| system_macros.clone())
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
        }
    }

    pub fn macro_at_address(&self, address: usize) -> Option<MacroRef<'_>> {
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { address, reference })
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<MacroRef> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { address, reference })
    }

    pub(crate) fn clone_macro_with_name(&self, name: &str) -> Option<Rc<Macro>> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(Rc::clone(reference))
    }

    pub(crate) fn clone_macro_with_address(&self, address: usize) -> Option<Rc<Macro>> {
        let reference = self.macros_by_address.get(address)?;
        Some(Rc::clone(reference))
    }

    pub(crate) fn clone_macro_with_id(&self, macro_id: MacroIdRef) -> Option<Rc<Macro>> {
        use MacroIdRef::*;
        match macro_id {
            LocalName(name) => self.clone_macro_with_name(name),
            LocalAddress(address) => self.clone_macro_with_address(address),
        }
    }

    pub fn add_macro(&mut self, template: TemplateMacro) -> IonResult<usize> {
        let id = self.macros_by_address.len();
        // If the macro has a name, make sure that name is not already in use and then add it.
        if let Some(name) = &template.name {
            if self.macros_by_name.contains_key(name.as_ref()) {
                return IonResult::decoding_error(format!("macro named '{name}' already exists"));
            }
            self.macros_by_name.insert(Rc::clone(name), id);
        }

        let new_macro = Macro::new(
            template.name,
            template.signature,
            MacroKind::Template(template.body),
            template.expansion_analysis,
        );

        self.macros_by_address.push(Rc::new(new_macro));
        Ok(id)
    }

    pub(crate) fn append_all_macros_from(&mut self, other: &MacroTable) -> IonResult<()> {
        for macro_ref in &other.macros_by_address {
            let next_id = self.len();
            if let Some(name) = macro_ref.clone_name() {
                if self.macros_by_name.contains_key(name.as_ref()) {
                    return IonResult::decoding_error(format!(
                        "macro named '{name}' already exists"
                    ));
                }
                self.macros_by_name.insert(name, next_id);
            }
            self.macros_by_address.push(Rc::clone(macro_ref))
        }
        Ok(())
    }
}
