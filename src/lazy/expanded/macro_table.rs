use std::borrow::Cow;
use std::collections::HashMap;

use crate::lazy::expanded::template::{
    MacroSignature, Parameter, ParameterCardinality, ParameterEncoding, RestSyntaxPolicy,
    TemplateBody, TemplateMacro, TemplateMacroRef,
};
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
use crate::result::IonFailure;
use crate::IonResult;

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    name: Option<String>,
    signature: MacroSignature,
    kind: MacroKind,
}

impl Macro {
    pub fn named(name: impl Into<String>, signature: MacroSignature, kind: MacroKind) -> Self {
        Self::new(Some(name.into()), signature, kind)
    }

    pub fn anonymous(signature: MacroSignature, kind: MacroKind) -> Self {
        Self::new(None, signature, kind)
    }

    pub fn new(name: Option<String>, signature: MacroSignature, kind: MacroKind) -> Self {
        Self {
            name,
            signature,
            kind,
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
}

/// The kinds of macros supported by
/// [`MacroEvaluator`](crate::lazy::expanded::macro_evaluator::MacroEvaluator).
/// This list parallels
/// [`MacroExpansionKind`](crate::lazy::expanded::macro_evaluator::MacroExpansionKind),
/// but its variants do not hold any associated state.
#[derive(Debug, Clone, PartialEq)]
pub enum MacroKind {
    Void,
    Values,
    MakeString,
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

    pub fn expect_template(self) -> IonResult<TemplateMacroRef<'top>> {
        if let MacroKind::Template(body) = &self.kind() {
            return Ok(TemplateMacroRef::new(self, body));
        }
        IonResult::decoding_error(format!(
            "expected a template macro but found {:?}",
            self.kind()
        ))
    }
    pub fn address(&self) -> MacroAddress {
        self.address
    }
    pub fn reference(&self) -> &'top Macro {
        self.reference
    }
    pub fn name(&'top self) -> Option<&'top str> {
        self.reference.name()
    }
    pub fn id_text(&'top self) -> Cow<'top, str> {
        self.name()
            .map(Cow::from)
            .unwrap_or_else(move || Cow::from(format!("<address={}>", self.address())))
    }
    pub fn signature(self) -> &'top MacroSignature {
        self.reference.signature()
    }
    pub fn kind(&self) -> &'top MacroKind {
        self.reference.kind()
    }
}

/// Allows callers to resolve a macro ID (that is: name or address) to a [`MacroKind`], confirming
/// its validity and allowing evaluation to begin.
#[derive(Debug, Clone)]
pub struct MacroTable {
    macros_by_address: Vec<Macro>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: HashMap<String, usize>,
}

impl Default for MacroTable {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroTable {
    pub const SYSTEM_MACRO_KINDS: &'static [MacroKind] =
        &[MacroKind::Void, MacroKind::Values, MacroKind::MakeString];
    pub const NUM_SYSTEM_MACROS: usize = Self::SYSTEM_MACRO_KINDS.len();
    // When a user defines new macros, this is the first ID that will be assigned. This value
    // is expected to change as development continues. It is currently used in several unit tests.
    pub const FIRST_USER_MACRO_ID: usize = 3;

    pub fn new() -> Self {
        let macros_by_id = vec![
            Macro::named("void", MacroSignature::new(vec![]), MacroKind::Void),
            Macro::named(
                "values",
                MacroSignature::new(vec![Parameter::new(
                    "expr_group",
                    ParameterEncoding::Tagged,
                    ParameterCardinality::ZeroOrMore,
                    RestSyntaxPolicy::Allowed,
                )]),
                MacroKind::Values,
            ),
            Macro::named(
                "make_string",
                MacroSignature::new(vec![Parameter::new(
                    "expr_group",
                    ParameterEncoding::Tagged,
                    ParameterCardinality::ZeroOrMore,
                    RestSyntaxPolicy::Allowed,
                )]),
                MacroKind::MakeString,
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
        );

        self.macros_by_address.push(new_macro);
        Ok(id)
    }
}
