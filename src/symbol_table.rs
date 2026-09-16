use std::fmt::{Debug, Formatter};
use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::constants::{v1_0, v1_1};
use crate::lazy::any_encoding::IonVersion;
use crate::types::SymbolAddress;
use crate::{Symbol, SymbolId};

/// Immutable system symbol tables defined by each version of the Ion specification.

#[derive(Debug, Copy, Clone)]
pub struct SystemSymbolTable {
    ion_version: IonVersion,
    symbols_by_address: &'static [&'static str],
    symbols_by_text: &'static phf::Map<&'static str, usize>,
}

impl SystemSymbolTable {
    pub const fn ion_version(&self) -> IonVersion {
        self.ion_version
    }

    /// Returns the number of symbols in this system table **including `$0`**.
    pub const fn len(&self) -> usize {
        self.symbols_by_address.len() + 1
    }

    pub fn address_for_text(&self, text: &str) -> Option<usize> {
        self.symbols_by_text.get(text).copied()
    }

    pub fn text_for_address(&self, address: SymbolAddress) -> Option<&'static str> {
        self.symbols_by_address.get(address - 1).copied()
    }

    pub fn symbol_for_address(&self, address: SymbolAddress) -> Option<Symbol> {
        self.text_for_address(address).map(Symbol::static_text)
    }
}

pub static SYSTEM_SYMBOLS_1_0: &SystemSymbolTable = &SystemSymbolTable {
    ion_version: IonVersion::v1_0,
    symbols_by_address: v1_0::SYSTEM_SYMBOLS,
    symbols_by_text: &v1_0::SYSTEM_SYMBOL_TEXT_TO_ID,
};

pub static SYSTEM_SYMBOLS_1_1: &SystemSymbolTable = &SystemSymbolTable {
    ion_version: IonVersion::v1_1,
    symbols_by_address: v1_1::SYSTEM_SYMBOLS,
    symbols_by_text: &v1_1::SYSTEM_SYMBOL_TEXT_TO_ID,
};

/// Stores mappings from Symbol IDs to text and vice-versa.
// SymbolTable instances always have at least system symbols; they are never empty.
#[allow(clippy::len_without_is_empty)]
#[derive(Clone)]
pub struct SymbolTable {
    ion_version: IonVersion,
    symbols_by_id: Vec<Symbol>,
    ids_by_text: FxHashMap<Symbol, SymbolId>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::empty(IonVersion::v1_0)
    }
}

impl SymbolTable {
    // These counts refer to the number of system symbols that are permanently prefixed to the user
    // table in each Ion version. The counts include SID `$0`.
    const NUM_PREFIX_SYSTEM_SYMBOLS_1_0: usize = 10;
    const NUM_PREFIX_SYSTEM_SYMBOLS_1_1: usize = 1;
    const INITIAL_SYMBOLS_CAPACITY: usize = 32; // TODO: Adjust this based ion_version?

    /// Constructs a new symbol table pre-populated with the system symbol prefix defined in the spec
    /// as well as any 'default' symbols that are guaranteed to be present at the outset of a stream.
    pub(crate) fn new(ion_version: IonVersion) -> SymbolTable {
        let mut symbol_table = SymbolTable {
            ion_version,
            symbols_by_id: Vec::with_capacity(Self::INITIAL_SYMBOLS_CAPACITY),
            ids_by_text: FxHashMap::default(),
        };
        symbol_table.initialize_with_all_system_symbols();
        symbol_table
    }

    /// Constructs a new symbol table pre-populated with the system symbol prefix defined in the spec.
    pub(crate) fn empty(ion_version: IonVersion) -> SymbolTable {
        // Enough to hold the 1.0 system table and several user symbols.
        let mut symbol_table = SymbolTable {
            ion_version,
            symbols_by_id: Vec::with_capacity(Self::INITIAL_SYMBOLS_CAPACITY),
            ids_by_text: FxHashMap::default(),
        };
        symbol_table.initialize_with_prefix_system_symbols();
        symbol_table
    }

    /// Adds the system symbols which are a permanent prefix to the table.
    pub(crate) fn initialize_with_prefix_system_symbols(&mut self) {
        match self.ion_version {
            IonVersion::v1_0 => self.initialize_with_all_system_symbols(),
            IonVersion::v1_1 => {
                // Only gets $0
                self.add_placeholder();
            }
        }
    }

    /// Adds **all** of the system symbols to the table, not just the permanent prefix symbols.
    pub(crate) fn initialize_with_all_system_symbols(&mut self) {
        self.add_placeholder(); // $0

        let system_symbols = match self.ion_version {
            IonVersion::v1_0 => v1_0::SYSTEM_SYMBOLS,
            IonVersion::v1_1 => v1_1::SYSTEM_SYMBOLS,
        };

        // The system symbol texts are `&'static str`s, so the symbols can refer to them
        // directly instead of heap-allocating a copy of each one.
        system_symbols.iter().copied().for_each(|text| {
            let _sid = self.add_symbol(Symbol::static_text(text));
        });
    }

    /// Sets the symbol table to the 'default' state used at the beginning of any stream of the
    /// current version.
    pub(crate) fn reset_to_default(&mut self) {
        self.symbols_by_id.clear();
        self.ids_by_text.clear();
        self.initialize_with_all_system_symbols()
    }

    /// Sets the symbol table's contents to the permanent prefix used by the current Ion version.
    /// In Ion 1.0, this is the system symbol table (`$0`-`$9`). In Ion 1.1, it is only `$0`.
    pub(crate) fn reset_to_prefix_only(&mut self) {
        match self.ion_version {
            IonVersion::v1_0 => {
                // Remove all symbols except for $0
                self.symbols_by_id
                    .truncate(Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_0);
                // Remove any symbol text mappings that point to an address from userspace ($10+)
                self.ids_by_text
                    .retain(|_symbol, address| *address < Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_0);
                // If a user symbol's text duplicated a system symbol's text, adding it overwrote
                // the system symbol's entry in `ids_by_text` with a user-space address--an entry
                // the `retain` above then removed. Restore any missing system text mappings so
                // the table is indistinguishable from a freshly initialized one. (This is
                // allocation-free: the keys are `&'static str`-backed symbols, and `or_insert`
                // leaves already-present entries untouched.)
                for (index, &text) in v1_0::SYSTEM_SYMBOLS.iter().enumerate() {
                    self.ids_by_text
                        .entry(Symbol::static_text(text))
                        .or_insert(index + 1); // SID 0 is the unknown-text placeholder `$0`
                }
            }
            IonVersion::v1_1 => {
                // Remove all symbols except for $0
                self.symbols_by_id
                    .truncate(Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_1);
                // In Ion 1.1, there are no permanent-prefix system symbols with text.
                self.ids_by_text.clear();
            }
        };
    }

    /// Resets the symbol table to the 'default' state for `new_version`, as used at the
    /// beginning of a stream of that version.
    ///
    /// When the version is unchanged and is Ion 1.0, this takes a cheaper path: the
    /// permanent system prefix is identical to the table's initial state, so truncating to
    /// the prefix (which also restores any system text-to-SID mappings that user symbols
    /// had shadowed) produces the same table state as a full rebuild at a fraction of the
    /// cost. See the unit test `reset_paths_equivalent_for_v1_0` below.
    pub(crate) fn reset_to_version(&mut self, new_version: IonVersion) {
        if new_version == IonVersion::v1_0 && self.ion_version == IonVersion::v1_0 {
            self.reset_to_prefix_only();
            return;
        }
        self.ion_version = new_version;
        self.reset_to_default();
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

    /// If defined, returns the Symbol ID associated with the provided text.
    pub fn sid_for<A: AsRef<str>>(&self, text: A) -> Option<SymbolId> {
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

    /// Returns the number of symbol addresses at the head of the symbol table that are
    /// guaranteed to be system symbols.
    /// In Ion 1.0, the complete system symbol table always appears at the beginning of the
    /// active symbol table.
    /// In Ion 1.1, only `$0` (the symbol with unknown text) is guaranteed to be present. Other
    /// system symbols may be removed from the table.
    pub fn permanent_system_prefix_count(&self) -> usize {
        match self.ion_version {
            IonVersion::v1_0 => Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_0,
            IonVersion::v1_1 => Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_1,
        }
    }

    /// Returns a slice of the symbols that were defined by the application--those that follow the
    /// system symbols in the table.
    pub fn application_symbols(&self) -> &[Symbol] {
        let num_sys_symbols = self.permanent_system_prefix_count();
        &self.symbols()[num_sys_symbols..]
    }

    /// Returns the slice of symbols that were defined by the specification and which are
    /// permanently prefixed to the beginning of the active symbol table.
    ///
    /// To get the full system symbol table for this Ion version (which may or may not be prefixed),
    /// use [`IonVersion::system_symbol_table`].
    pub fn prefixed_system_symbols(&self) -> &[Symbol] {
        let num_sys_symbols = self.permanent_system_prefix_count();
        &self.symbols()[0..num_sys_symbols]
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

    pub fn ion_version(&self) -> IonVersion {
        self.ion_version
    }
}

impl Debug for SymbolTable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "SymbolTable {{")?;
        for (address, symbol) in self.symbols().iter().enumerate() {
            write!(f, "{}: {:?}, ", address, symbol.text())?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The system symbols are stored as `Symbol`s with static text; confirm that they can
    /// still be resolved in both directions (text -> SID and SID -> text) like any other symbol.
    #[test]
    fn system_symbols_resolve_by_text_and_sid() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        assert_eq!(table.len(), 10);
        for (index, &text) in v1_0::SYSTEM_SYMBOLS.iter().enumerate() {
            let sid = index + 1; // SID 0 is the unknown-text placeholder `$0`
            assert_eq!(table.sid_for(text), Some(sid));
            assert_eq!(table.text_for(sid), Some(text));
        }
        // Symbols with heap-allocated text can coexist with the static system symbols.
        let sid = table.add_symbol_for_text("hello");
        assert_eq!(table.sid_for("hello"), Some(sid));
        assert_eq!(table.text_for(sid), Some("hello"));
    }

    /// `reset_to_prefix_only` must produce exactly the same Ion 1.0 table state as a full
    /// rebuild, even when user symbols shadowed system symbol texts. A user symbol whose text
    /// duplicates a system symbol's (e.g. `"name"`) overwrites the system entry in the
    /// text -> SID map; the reset must restore it.
    #[test]
    fn reset_paths_equivalent_for_v1_0() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        // Shadow every system symbol text with a user symbol, and add an ordinary user symbol.
        for &text in v1_0::SYSTEM_SYMBOLS {
            table.add_symbol_for_text(text);
        }
        table.add_symbol_for_text("user_symbol");
        // The shadowing user symbols have replaced the system entries in the text -> SID map:
        // "name" (system SID 4) now resolves to its user-space copy.
        assert_eq!(table.sid_for("name"), Some(13));

        table.reset_to_prefix_only();

        // The reset table must be indistinguishable from a freshly constructed one.
        let fresh = SymbolTable::new(IonVersion::v1_0);
        assert_eq!(table.len(), fresh.len());
        for sid in 0..fresh.len() {
            assert_eq!(table.text_for(sid), fresh.text_for(sid), "SID: {sid}");
        }
        for &text in v1_0::SYSTEM_SYMBOLS {
            assert_eq!(table.sid_for(text), fresh.sid_for(text), "text: {text}");
        }
        assert_eq!(table.sid_for("name"), Some(4));
        assert_eq!(table.text_for(4), Some("name"));
        assert_eq!(table.sid_for("user_symbol"), None);
    }
}
