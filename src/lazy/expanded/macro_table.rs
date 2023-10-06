use std::collections::HashMap;

use crate::lazy::expanded::template::TemplateMacro;
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
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
    // The following macro types are implementation details for macro evaluation and are not
    // directly available to users. They do not appear in the macro table.
    ExpandVariable,
}

impl MacroKind {
    fn name(&self) -> &str {
        match self {
            MacroKind::Void => "void",
            MacroKind::Values => "values",
            MacroKind::MakeString => "make_string",
            MacroKind::Template(template) => template.name(),
            // The `#` prefix is an arbitrarily selected sigil that indicates this is macro kind is
            // not directly available to users. If this name appears in (e.g.) a macro evaluator
            // stack trace, users copy/pasting it into their own templates would get a syntax error.
            MacroKind::ExpandVariable => "#expand_variable",
        }
    }
}

#[derive(Debug, Clone)]
pub struct MacroKindRef<'top> {
    address: MacroAddress,
    kind: &'top MacroKind,
}

impl<'top> MacroKindRef<'top> {
    pub fn new(address: MacroAddress, kind: &'top MacroKind) -> Self {
        Self { address, kind }
    }
    pub fn address(&self) -> MacroAddress {
        self.address
    }
    pub fn kind(&self) -> &'top MacroKind {
        self.kind
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
        let mut macros_by_name = HashMap::new();
        for (id, kind) in macros_by_id.iter().enumerate() {
            macros_by_name.insert(kind.name().to_string(), id);
        }
        Self {
            macros_by_address: macros_by_id,
            macros_by_name,
        }
    }

    pub fn macro_at_address(&self, address: usize) -> Option<MacroKindRef<'_>> {
        let kind = self.macros_by_address.get(address)?;
        Some(MacroKindRef { address, kind })
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<MacroKindRef<'_>> {
        let address = *self.macros_by_name.get(name)?;
        let kind = self.macros_by_address.get(address)?;
        Some(MacroKindRef { address, kind })
    }

    pub fn add_macro(&mut self, template: TemplateMacro) -> IonResult<usize> {
        if self.macros_by_name.contains_key(template.name()) {
            return IonResult::decoding_error("macro named '{}' already exists");
        }
        let id = self.macros_by_address.len();
        self.macros_by_name.insert(template.name().to_owned(), id);
        self.macros_by_address.push(MacroKind::Template(template));
        let id = 0;
        Ok(id)
    }
}
