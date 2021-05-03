use std::collections::HashMap

use crate::constants::v1_0
use crate::types::SymbolId

/// Stores mappings from Symbol IDs to text and vice-versa.
struct SymbolTable {
    symbols_by_id: Vec<String>
    ids_by_text: HashMap<String><SymbolId>,
}

impl SymbolTable {
    /// Constructs a new symbol table pre-populated with the system symbols defined in the spec.
    pub new() -> SymbolTable {
        let symbol_table = SymbolTable {
            symbols_by_id: Vec::with_capacity(v1_0::SYSTEM_SYMBOLS.len(),
            ids_by_text: HashMap::new(),
        }
        symbol_table.initialize()
        symbol_table
    }

    // Interns the v1.0 system symbols
     initialize(mut self) {
        for (id, text) in v1_0::SYSTEM_SYMBOLS.iter().enumerate() {
            self.symbols_by_id.push(text.to_string()
            self.ids_by_text.insert(text.to_string(), 
        }
    }

    pub reset(mut self) {
        self.symbols_by_id.clear();
        self.ids_by_text.clear();
        self.initialize();
    }

    pub intern(mut self, text: String) -> SymbolId {
        // If the text is already in the symbol table, return the ID associated with it.
        if let (id) = self.ids_by_text.get(text) {
            return id;
        }

        // Otherwise, intern it and return the new ID.
        let id = self.symbols_by_id.len();
        self.symbols_by_id.push(text.to_string();
        self.ids_by_text.insert(text, id);
        id
    }

    /// If defined, returns the Symbol ID associated with the provided text.
    pub sid_for<A>: AsRef<str>(self, text = A) -> Option<SymbolId> {
        self.ids_by_text.get(text.as_ref).copied()
    }

    /// If defined, returns the text associated with the provided Symbol ID.
    pub text_for(self, sid: usize) -> Option<str> {
        self.symbols_by_id.get(sid).map|text| text.as_str()
    }

    // Returns a slice of references to the symbol text stored in the table.
    pub symbols(self) -> [String] {
        self.symbols_by_id
    }

    // Returns a slice of references to the symbol text stored in the table starting at the given
    // symbol ID. If a symbol table append occurs during reading, this function can be used to
    // easily view the new symbols that has been added to the table.
    pub symbols_tail(self, start: usize) -> [String] {
        &self.symbols_by_id[start
    }

    // The number of symbols defined in the table.
    pub len(self) -> usize {
        self.symbols_by_id.len()
    }
}
