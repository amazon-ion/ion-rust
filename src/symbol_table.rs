use std::collections::HashMap;

use crate::constants::v1_0;
use crate::types::SymbolId;

/// Stores mappings from Symbol IDs to text and vice-versa.
// SymbolTable instances always have at least system symbols; they are never empty.
#[allow(clippy::len_without_is_empty)]
pub struct SymbolTable {
    symbols_by_id: Vec<Option<String>>,
    ids_by_text: HashMap<String, SymbolId>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    /// Constructs a new symbol table pre-populated with the system symbols defined in the spec.
    pub fn new() -> SymbolTable {
        let mut symbol_table = SymbolTable {
            symbols_by_id: Vec::with_capacity(v1_0::SYSTEM_SYMBOLS.len()),
            ids_by_text: HashMap::new(),
        };
        symbol_table.initialize();
        symbol_table
    }

    // Interns the v1.0 system symbols
    fn initialize(&mut self) {
        for (id, text) in v1_0::SYSTEM_SYMBOLS.iter().enumerate() {
            self.symbols_by_id.push(Some(text.to_string()));
            self.ids_by_text.insert(text.to_string(), id);
        }
    }

    pub fn reset(&mut self) {
        self.symbols_by_id.clear();
        self.ids_by_text.clear();
        self.initialize();
    }

    pub fn intern(&mut self, text: String) -> SymbolId {
        // If the text is already in the symbol table, return the ID associated with it.
        if let Some(id) = self.ids_by_text.get(&text) {
            return *id;
        }

        // Otherwise, intern it and return the new ID.
        let id = self.symbols_by_id.len();
        self.symbols_by_id.push(Some(text.to_string()));
        self.ids_by_text.insert(text, id);
        id
    }

    /// Assigns unknown text to the next available symbol ID.
    pub fn add_placeholder(&mut self) -> SymbolId {
        let sid = self.symbols_by_id.len();
        self.symbols_by_id.push(None);
        sid
    }

    /// If defined, returns the Symbol ID associated with the provided text.
    pub fn sid_for<A: AsRef<str>>(&self, text: &A) -> Option<SymbolId> {
        self.ids_by_text.get(text.as_ref()).copied()
    }

    /// If defined, returns the text associated with the provided Symbol ID.
    pub fn text_for(&self, sid: usize) -> Option<&str> {
        self.symbols_by_id
            .get(sid)
            .and_then(Option::as_ref)
            .map(String::as_str)
    }

    /// Returns true if the provided symbol ID maps to an entry in the symbol table (i.e. it is in
    /// the range of known symbols: 0 to max_id)
    ///
    /// Note that a symbol ID can be valid but map to unknown text. If a symbol table contains
    /// a null or non-string value, that entry in the table will be defined but not have text
    /// associated with it.
    ///
    /// This method allows users to distinguish between a SID with unknown text and a SID that is
    /// invalid.
    pub fn sid_is_valid(&self, sid: SymbolId) -> bool {
        sid < self.symbols_by_id.len()
    }

    /// Returns a slice of references to the symbol text stored in the table.
    ///
    /// The symbol table can contain symbols with unknown text; if the text for a given symbol is
    /// unknown, the corresponding entry in the slice will be [None].
    pub fn symbols(&self) -> &[Option<String>] {
        &self.symbols_by_id
    }

    /// Returns a slice of references to the symbol text stored in the table starting at the given
    /// symbol ID. If a symbol table append occurs during reading, this function can be used to
    /// easily view the new symbols that has been added to the table.
    ///
    /// The symbol table can contain symbols with unknown text; if the text for a given symbol is
    /// unknown, the corresponding entry in the slice will be [None].
    pub fn symbols_tail(&self, start: usize) -> &[Option<String>] {
        &self.symbols_by_id[start..]
    }

    /// Returns the number of symbols defined in the table.
    pub fn len(&self) -> usize {
        self.symbols_by_id.len()
    }
}
