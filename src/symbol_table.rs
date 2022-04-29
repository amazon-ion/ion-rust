use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

use crate::constants::v1_0;
use crate::types::SymbolId;

/// Stores or points to the text of a given [Symbol].
#[derive(Debug, Eq)]
enum SymbolText {
    // This Symbol refers to a string in the symbol table
    Shared(Rc<str>),
    // This Symbol owns its own text
    Owned(String),
}

impl AsRef<str> for SymbolText {
    fn as_ref(&self) -> &str {
        match self {
            SymbolText::Owned(ref text) => text.as_str(),
            SymbolText::Shared(ref rc) => rc.as_ref(),
        }
    }
}

impl<A: AsRef<str>> PartialEq<A> for SymbolText {
    fn eq(&self, other: &A) -> bool {
        // Compare the Symbols' text, not their ownership models
        self.as_ref() == other.as_ref()
    }
}

impl Hash for SymbolText {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the Symbol's text, ignore where/how it's stored.
        self.as_ref().hash(state)
    }
}

impl Clone for SymbolText {
    fn clone(&self) -> Self {
        match self {
            SymbolText::Owned(text) => SymbolText::Owned(text.to_owned()),
            SymbolText::Shared(text) => SymbolText::Shared(Rc::clone(text)),
        }
    }
}

/// The text of a fully resolved field name, annotation, or symbol value. The text stored in this
/// Symbol may be either a `String` or a shared reference to text in a symbol table.
#[derive(Debug, Hash, Clone, Eq)]
pub struct Symbol {
    text: SymbolText,
}

impl<A: AsRef<str>> PartialEq<A> for Symbol {
    fn eq(&self, other: &A) -> bool {
        self.text.as_ref() == other.as_ref()
    }
}

impl PartialEq<Symbol> for String {
    fn eq(&self, other: &Symbol) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl PartialEq<Symbol> for &str {
    fn eq(&self, other: &Symbol) -> bool {
        self == &other.as_ref()
    }
}

impl Symbol {
    pub fn owned(text: String) -> Symbol {
        Symbol {
            text: SymbolText::Owned(text),
        }
    }

    pub fn shared(text: Rc<str>) -> Symbol {
        Symbol {
            text: SymbolText::Shared(text),
        }
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.text.as_ref()
    }
}

impl Deref for Symbol {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.text.as_ref()
    }
}

// Allows a HashMap<Symbol, _> to do lookups with a &str instead of a &Symbol
impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        self.as_ref()
    }
}

/// Stores mappings from Symbol IDs to text and vice-versa.
// SymbolTable instances always have at least system symbols; they are never empty.
#[allow(clippy::len_without_is_empty)]
pub struct SymbolTable {
    symbols_by_id: Vec<Option<Symbol>>,
    ids_by_text: HashMap<Symbol, SymbolId>,
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
        for (_id, text) in v1_0::SYSTEM_SYMBOLS.iter().enumerate() {
            self.intern(text);
        }
    }

    pub fn reset(&mut self) {
        self.symbols_by_id.clear();
        self.ids_by_text.clear();
        self.initialize();
    }

    /// If `text` is already in the symbol table, returns the corresponding [SymbolId].
    /// Otherwise, adds `text` to the symbol table and returns the newly assigned [SymbolId].
    pub fn intern<A: AsRef<str>>(&mut self, text: A) -> SymbolId {
        let text = text.as_ref();
        // If the text is already in the symbol table, return the ID associated with it.
        if let Some(id) = self.ids_by_text.get(text) {
            return *id;
        }

        // Otherwise, intern it and return the new ID.
        let id = self.symbols_by_id.len();
        let rc: Rc<str> = Rc::from(text);
        let symbol = Symbol::shared(rc);
        self.symbols_by_id.push(Some(symbol.clone()));
        self.ids_by_text.insert(symbol, id);
        id
    }

    /// Assigns unknown text to the next available symbol ID. This is used when an Ion reader
    /// encounters null or non-string values in a stream's symbol table.
    pub fn add_placeholder(&mut self) -> SymbolId {
        let sid = self.symbols_by_id.len();
        self.symbols_by_id.push(None);
        sid
    }

    /// If `maybe_text` is `Some(text)`, this method is equivalent to `intern(text)`.
    /// If `maybe_text` is `None`, this method is equivalent to `add_placeholder()`.
    pub fn intern_or_add_placeholder<A: AsRef<str>>(&mut self, maybe_text: Option<A>) -> SymbolId {
        match maybe_text {
            Some(text) => self.intern(text),
            None => self.add_placeholder(),
        }
    }

    /// If defined, returns the Symbol ID associated with the provided text.
    pub fn sid_for<A: AsRef<str>>(&self, text: &A) -> Option<SymbolId> {
        self.ids_by_text.get(text.as_ref()).copied()
    }

    /// If defined, returns the text associated with the provided Symbol ID.
    pub fn text_for(&self, sid: SymbolId) -> Option<&str> {
        self.symbols_by_id
            .get(sid)?
            .as_ref()
            .map(|symbol| symbol.as_ref())
    }

    /// If defined, returns the Symbol associated with the provided Symbol ID.
    pub fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
        self.symbols_by_id.get(sid)?.as_ref()
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
    pub fn symbols(&self) -> &[Option<Symbol>] {
        &self.symbols_by_id
    }

    /// Returns a slice of references to the symbol text stored in the table starting at the given
    /// symbol ID. If a symbol table append occurs during reading, this function can be used to
    /// easily view the new symbols that has been added to the table.
    ///
    /// The symbol table can contain symbols with unknown text; if the text for a given symbol is
    /// unknown, the corresponding entry in the slice will be [None].
    pub fn symbols_tail(&self, start: usize) -> &[Option<Symbol>] {
        &self.symbols_by_id[start..]
    }

    /// Returns the number of symbols defined in the table.
    pub fn len(&self) -> usize {
        self.symbols_by_id.len()
    }
}
