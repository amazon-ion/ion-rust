use crate::lazy::expanded::template::TemplateMacro;
use crate::result::IonFailure;
use crate::IonResult;
use std::collections::HashMap;

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

    pub fn macro_at_address(&self, id: usize) -> Option<&MacroKind> {
        self.macros_by_address.get(id)
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<&MacroKind> {
        let id = self.macros_by_name.get(name)?;
        self.macros_by_address.get(*id)
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
