use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::constants::v1_0;
use crate::lazy::any_encoding::IonVersion;
use crate::{Symbol, SymbolId};

/// Stores mappings from Symbol IDs to text and vice-versa.
// SymbolTable instances always have at least system symbols; they are never empty.
#[allow(clippy::len_without_is_empty)]
#[derive(Debug, Clone)]
pub struct SymbolTable {
    ion_version: IonVersion,
    symbols_by_id: Vec<Symbol>,
    ids_by_text: FxHashMap<Symbol, SymbolId>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new(IonVersion::v1_0)
    }
}

impl SymbolTable {
    /// Constructs a new symbol table pre-populated with the system symbols defined in the spec.
    pub(crate) fn new(ion_version: IonVersion) -> SymbolTable {
        // Enough to hold the 1.0 system table and several user symbols.
        const INITIAL_SYMBOLS_CAPACITY: usize = 32;
        let mut symbol_table = SymbolTable {
            ion_version,
            symbols_by_id: Vec::with_capacity(INITIAL_SYMBOLS_CAPACITY),
            ids_by_text: FxHashMap::default(),
        };
        symbol_table.initialize();
        symbol_table
    }

    /// Adds system symbols to the table.
    pub(crate) fn initialize(&mut self) {
        self.add_placeholder(); // $0

        // TODO: If it's Ion 1.1, there are no other symbols in the symbol table. Implementing this
        //       requires having first implemented reading and writing system symbols in their own
        //       address space. For now, Ion 1.1's default symbol table matches Ion 1.0's.
        //       let remaining_system_symbols = match self.ion_version {
        //           IonVersion::v1_0 => &v1_0::SYSTEM_SYMBOLS[1..],
        //           IonVersion::v1_1 => &[],
        //       };
        let remaining_system_symbols = &v1_0::SYSTEM_SYMBOLS[1..];

        remaining_system_symbols
            .iter()
            .copied()
            .map(Option::unwrap)
            .for_each(|text| {
                let _sid = self.add_symbol_for_text(text);
            });
    }

    pub(crate) fn reset(&mut self) {
        self.symbols_by_id.clear();
        self.ids_by_text.clear();
        self.initialize();
    }

    pub(crate) fn reset_to_version(&mut self, new_version: IonVersion) {
        self.ion_version = new_version;
        self.reset();
    }

    /// adds `text` to the symbol table and returns the newly assigned [SymbolId].
    pub(crate) fn add_symbol_for_text<A: AsRef<str>>(&mut self, text: A) -> SymbolId {
        let arc: Arc<str> = Arc::from(text.as_ref());
        let symbol = Symbol::shared(arc);
        self.add_symbol(symbol)
    }

    pub(crate) fn add_symbol(&mut self, symbol: Symbol) -> SymbolId {
        let id = self.symbols_by_id.len();
        self.symbols_by_id.push(symbol.clone());
        self.ids_by_text.insert(symbol, id);
        id
    }

    /// Assigns unknown text to the next available symbol ID. This is used when an Ion reader
    /// encounters null or non-string values in a stream's symbol table.
    pub(crate) fn add_placeholder(&mut self) -> SymbolId {
        let sid = self.symbols_by_id.len();
        self.symbols_by_id.push(Symbol::unknown_text());
        sid
    }

    /// If `maybe_text` is `Some(text)`, this method is equivalent to `add_symbol_for_text(text)`.
    /// If `maybe_text` is `None`, this method is equivalent to `add_placeholder()`.
    pub(crate) fn add_symbol_or_placeholder<A: AsRef<str>>(
        &mut self,
        maybe_text: Option<A>,
    ) -> SymbolId {
        match maybe_text {
            Some(text) => self.add_symbol_for_text(text),
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
            // If the SID is out of bounds, returns None
            .get(sid)?
            // If the text is unknown, returns None
            .text()
    }

    /// If defined, returns the Symbol associated with the provided Symbol ID.
    pub fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
        self.symbols_by_id.get(sid)
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
    /// The symbol table can contain symbols with unknown text; see the documentation for
    /// [Symbol] for more information.
    pub fn symbols(&self) -> &[Symbol] {
        &self.symbols_by_id
    }

    /// Returns a slice of the last `n` symbols in the symbol table. The caller must confirm that
    /// `last_n` is less than the size of the symbol table.
    pub(crate) fn symbols_tail(&self, last_n: usize) -> &[Symbol] {
        let num_symbols = self.symbols_by_id.len();
        &self.symbols_by_id[num_symbols - last_n..]
    }

    /// Returns the number of symbols defined in the table.
    pub fn len(&self) -> usize {
        self.symbols_by_id.len()
    }
}
