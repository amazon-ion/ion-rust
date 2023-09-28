use std::collections::HashMap;

/// The kinds of macros supported by
/// [`MacroEvaluator`](crate::lazy::expanded::macro_evaluator::MacroEvaluator).
/// This list parallels
/// [`MacroExpansionKind`](crate::lazy::expanded::macro_evaluator::MacroExpansionKind),
/// but its variants do not hold any associated state.
#[derive(Debug, Copy, Clone)]
pub enum MacroKind {
    Void,
    Values,
    MakeString,
}

impl MacroKind {
    fn name(&self) -> &str {
        match self {
            MacroKind::Void => "void",
            MacroKind::Values => "values",
            MacroKind::MakeString => "make_string",
        }
    }
}

/// Allows callers to resolve a macro ID (that is: name or address) to a [`MacroKind`], confirming
/// its validity and allowing evaluation to begin.
#[derive(Debug)]
pub struct MacroTable {
    macros_by_address: Vec<MacroKind>,
    macros_by_name: HashMap<String, MacroKind>,
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
        for kind in &macros_by_id {
            macros_by_name.insert(kind.name().to_string(), *kind);
        }
        Self {
            macros_by_address: macros_by_id,
            macros_by_name,
        }
    }

    pub fn macro_at_address(&self, id: usize) -> Option<&MacroKind> {
        self.macros_by_address.get(id)
    }

    pub fn macro_with_name(&self, name: &str) -> Option<&MacroKind> {
        self.macros_by_name.get(name)
    }
}
