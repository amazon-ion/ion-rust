use std::borrow::Cow;
use std::collections::HashMap;

use delegate::delegate;
use rustc_hash::FxHashMap;

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
    name: Option<String>,
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
        name: impl Into<String>,
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
        name: Option<String>,
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
            return TemplateMacroRef::new(self, body);
        }
        unreachable!(
            "caller required a template macro but found {:?}",
            self.kind()
        )
    }

    pub fn id_text(&'top self) -> Cow<'top, str> {
        self.name()
            .map(Cow::from)
            .unwrap_or_else(move || Cow::from(format!("<address={}>", self.address())))
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
    macros_by_address: Vec<Macro>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: FxHashMap<String, usize>,
}

impl Default for MacroTable {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroTable {
    pub const SYSTEM_MACRO_KINDS: &'static [MacroKind] = &[
        MacroKind::Void,
        MacroKind::Values,
        MacroKind::MakeString,
        MacroKind::Annotate,
    ];
    pub const NUM_SYSTEM_MACROS: usize = Self::SYSTEM_MACRO_KINDS.len();
    // When a user defines new macros, this is the first ID that will be assigned. This value
    // is expected to change as development continues. It is currently used in several unit tests.
    pub const FIRST_USER_MACRO_ID: usize = 4;

    pub fn new() -> Self {
        let macros_by_id = vec![
            Macro::named(
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
            ),
            Macro::named(
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
            ),
            Macro::named(
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
            ),
            Macro::named(
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
            ),
        ];
        let mut macros_by_name = HashMap::default();
        for (id, mac) in macros_by_id.iter().enumerate() {
            if let Some(name) = mac.name() {
                macros_by_name.insert(name.to_owned(), id);
            }
            // Anonymous macros are not entered into the macros_by_name lookup table
        }
        Self {
            macros_by_address: macros_by_id,
            macros_by_name,
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

    pub fn macro_with_name<'a>(&'a self, name: &str) -> Option<MacroRef<'a>> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { address, reference })
    }

    pub fn add_macro(&mut self, template: TemplateMacro) -> IonResult<usize> {
        let id = self.macros_by_address.len();
        // If the macro has a name, make sure that name is not already in use and then add it.
        if let Some(name) = template.name.as_deref() {
            if self.macros_by_name.contains_key(name) {
                return IonResult::decoding_error(format!("macro named '{name}' already exists"));
            }
            self.macros_by_name.insert(name.to_owned(), id);
        }

        let new_macro = Macro::new(
            template.name,
            template.signature,
            MacroKind::Template(template.body),
            template.expansion_analysis,
        );

        self.macros_by_address.push(new_macro);
        Ok(id)
    }
}
