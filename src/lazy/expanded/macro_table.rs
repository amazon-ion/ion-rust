use std::collections::HashMap;

use crate::lazy::expanded::template::{TemplateMacro, TemplateMacroRef};
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
use crate::result::IonFailure;
use crate::IonResult;

/// The kinds of macros supported by
/// [`MacroEvaluator`](crate::lazy::expanded::macro_evaluator::MacroEvaluator).
/// This list parallels
/// [`MacroExpansionKind`](crate::lazy::expanded::macro_evaluator::MacroExpansionKind),
/// but its variants do not hold any associated state.
#[derive(Debug, Clone)]
pub enum MacroKind {
    Void,
    Values,
    MakeString,
    Template(TemplateMacro),
}

impl MacroKind {
    fn name(&self) -> &str {
        match self {
            MacroKind::Void => "void",
            MacroKind::Values => "values",
            MacroKind::MakeString => "make_string",
            MacroKind::Template(template) => template.name(),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct MacroRef<'top> {
    address: MacroAddress,
    kind: &'top MacroKind,
}

impl<'top> MacroRef<'top> {
    pub fn new(address: MacroAddress, kind: &'top MacroKind) -> Self {
        Self { address, kind }
    }
    pub fn address(&self) -> MacroAddress {
        self.address
    }
    pub fn kind(&self) -> &'top MacroKind {
        self.kind
    }

    pub fn expect_template(self) -> IonResult<TemplateMacroRef<'top>> {
        if let MacroKind::Template(template) = &self.kind {
            return Ok(TemplateMacroRef::new(self.address, template));
        }
        IonResult::decoding_error(format!(
            "expected a template macro but found {:?}",
            self.kind
        ))
    }
}

/// Allows callers to resolve a macro ID (that is: name or address) to a [`MacroKind`], confirming
/// its validity and allowing evaluation to begin.
#[derive(Debug)]
pub struct MacroTable {
    macros_by_address: Vec<MacroKind>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: HashMap<String, usize>,
}

impl Default for MacroTable {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroTable {
    pub fn new() -> Self {
        let macros_by_id = vec![MacroKind::Void, MacroKind::Values, MacroKind::MakeString];
        let mut macros_by_name = HashMap::default();
        for (id, kind) in macros_by_id.iter().enumerate() {
            macros_by_name.insert(kind.name().to_string(), id);
        }
        Self {
            macros_by_address: macros_by_id,
            macros_by_name,
        }
    }

    pub fn macro_with_id(&'_ self, id: MacroIdRef<'_>) -> Option<MacroRef<'_>> {
        match id {
            MacroIdRef::LocalName(name) => self.macro_with_name(name),
            MacroIdRef::LocalAddress(address) => self.macro_at_address(address),
        }
    }

    pub fn macro_at_address(&self, address: usize) -> Option<MacroRef<'_>> {
        let kind = self.macros_by_address.get(address)?;
        Some(MacroRef { address, kind })
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<MacroRef<'_>> {
        let address = *self.macros_by_name.get(name)?;
        let kind = self.macros_by_address.get(address)?;
        Some(MacroRef { address, kind })
    }

    pub fn add_macro(&mut self, template: TemplateMacro) -> IonResult<usize> {
        let name = template.name();
        if self.macros_by_name.contains_key(name) {
            return IonResult::decoding_error(format!("macro named '{name}' already exists"));
        }
        let id = self.macros_by_address.len();
        self.macros_by_name.insert(name.to_owned(), id);
        self.macros_by_address.push(MacroKind::Template(template));
        Ok(id)
    }
}
