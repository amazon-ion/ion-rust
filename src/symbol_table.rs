use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::num::NonZeroU32;

use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use rustc_hash::FxHasher;

use crate::constants::v1_0;
use crate::lazy::any_encoding::IonVersion;
use crate::types::SymbolAddress;
use crate::{Symbol, SymbolId};

/// Immutable system symbol tables defined by each version of the Ion specification.

#[derive(Debug, Copy, Clone)]
pub struct SystemSymbolTable {
    symbols_by_address: &'static [&'static str],
    symbols_by_text: &'static phf::Map<&'static str, usize>,
}

impl SystemSymbolTable {
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
    symbols_by_address: v1_0::SYSTEM_SYMBOLS,
    symbols_by_text: &v1_0::SYSTEM_SYMBOL_TEXT_TO_ID,
};

/// Stores the mapping from Symbol IDs to text.
// SymbolTable instances always have at least system symbols; they are never empty.
#[allow(clippy::len_without_is_empty)]
#[derive(Clone)]
pub struct SymbolTable {
    ion_version: IonVersion,
    symbols_by_id: Vec<Symbol>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::empty(IonVersion::v1_0)
    }
}

impl SymbolTable {
    // This count refers to the number of system symbols that are permanently prefixed to the user
    // table. The count includes SID `$0`.
    const NUM_PREFIX_SYSTEM_SYMBOLS_1_0: usize = 10;
    const INITIAL_SYMBOLS_CAPACITY: usize = 32; // TODO: Adjust this based ion_version?

    /// Constructs a new symbol table pre-populated with the system symbol prefix defined in the spec
    /// as well as any 'default' symbols that are guaranteed to be present at the outset of a stream.
    pub(crate) fn new(ion_version: IonVersion) -> SymbolTable {
        let mut symbol_table = SymbolTable {
            ion_version,
            symbols_by_id: Vec::with_capacity(Self::INITIAL_SYMBOLS_CAPACITY),
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
        };
        symbol_table.initialize_with_prefix_system_symbols();
        symbol_table
    }

    /// Adds the system symbols which are a permanent prefix to the table.
    pub(crate) fn initialize_with_prefix_system_symbols(&mut self) {
        match self.ion_version {
            IonVersion::v1_0 => self.initialize_with_all_system_symbols(),
        }
    }

    /// Adds **all** of the system symbols to the table, not just the permanent prefix symbols.
    pub(crate) fn initialize_with_all_system_symbols(&mut self) {
        self.add_placeholder(); // $0

        let system_symbols = match self.ion_version {
            IonVersion::v1_0 => v1_0::SYSTEM_SYMBOLS,
        };

        self.symbols_by_id
            .extend(system_symbols.iter().copied().map(Symbol::static_text));
    }

    /// Sets the symbol table to the 'default' state used at the beginning of any stream of the
    /// current version, retaining the storage it has grown.
    pub(crate) fn reset_to_default(&mut self) {
        self.symbols_by_id.clear();
        self.initialize_with_all_system_symbols()
    }

    /// Sets the symbol table's contents to the permanent prefix used by the current Ion version.
    /// In Ion 1.0, this is the system symbol table (`$0`-`$10`).
    pub(crate) fn reset_to_prefix_only(&mut self) {
        match self.ion_version {
            IonVersion::v1_0 => {
                // Remove all user symbols ($10+)
                self.symbols_by_id
                    .truncate(Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_0);
            }
        };
    }

    pub(crate) fn reset_to_version(&mut self, new_version: IonVersion) {
        self.ion_version = new_version;
        self.reset_to_default();
    }

    pub(crate) fn add_symbol(&mut self, symbol: Symbol) -> SymbolId {
        let id = self.symbols_by_id.len();
        self.symbols_by_id.push(symbol);
        id
    }

    /// Assigns unknown text to the next available symbol ID. This is used when an Ion reader
    /// encounters null or non-string values in a stream's symbol table.
    pub(crate) fn add_placeholder(&mut self) -> SymbolId {
        let sid = self.symbols_by_id.len();
        self.symbols_by_id.push(Symbol::unknown_text());
        sid
    }

    /// If defined, returns the Symbol ID associated with the provided text. If the text appears
    /// more than once, returns the lowest ID, as the Ion spec requires.
    ///
    /// This is a linear scan; readers resolve symbols by ID, not by text.
    pub fn sid_for<A: AsRef<str>>(&self, text: A) -> Option<SymbolId> {
        let text = text.as_ref();
        self.symbols_by_id
            .iter()
            .enumerate()
            .find(|(_, symbol)| symbol.text() == Some(text))
            .map(|(sid, _)| sid)
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
    pub fn permanent_system_prefix_count(&self) -> usize {
        match self.ion_version {
            IonVersion::v1_0 => Self::NUM_PREFIX_SYSTEM_SYMBOLS_1_0,
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

    /// Returns the number of symbols defined in the table.
    pub fn len(&self) -> usize {
        self.symbols_by_id.len()
    }

    pub fn ion_version(&self) -> IonVersion {
        self.ion_version
    }
}

/// Hashes symbol text for the writer's keyless lookup index.
fn symbol_text_hash(text: &str) -> u64 {
    let mut hasher = FxHasher::default();
    text.hash(&mut hasher);
    hasher.finish()
}

/// Symbol text stored back to back in one `String`, addressed by symbol ID.
struct SymbolTexts {
    arena: String,
    /// Each symbol's `(start, end)` byte range in `arena`, or `None` if its text is unknown.
    ranges: Vec<Option<(u32, NonZeroU32)>>,
}

impl SymbolTexts {
    fn with_capacity(num_symbols: usize, num_text_bytes: usize) -> Self {
        Self {
            arena: String::with_capacity(num_text_bytes),
            ranges: Vec::with_capacity(num_symbols),
        }
    }

    fn len(&self) -> usize {
        self.ranges.len()
    }

    fn get(&self, sid: SymbolId) -> Option<&str> {
        let (start, end) = (*self.ranges.get(sid)?)?;
        Some(&self.arena[start as usize..end.get() as usize])
    }

    fn get_bytes(&self, sid: SymbolId) -> Option<&[u8]> {
        let (start, end) = (*self.ranges.get(sid)?)?;
        Some(&self.arena.as_bytes()[start as usize..end.get() as usize])
    }

    /// Appends `text` and returns its symbol ID.
    fn insert(&mut self, text: &str) -> SymbolId {
        let sid = self.ranges.len();
        let start = self.arena.len() as u32;
        self.arena.push_str(text);
        // The system symbols are inserted first and have non-empty text, so `end` is never 0.
        let end = u32::try_from(self.arena.len())
            .ok()
            .and_then(NonZeroU32::new)
            .expect("symbol text exceeds 4 GiB");
        self.ranges.push(Some((start, end)));
        sid
    }

    /// Assigns unknown text to the next symbol ID and returns it.
    fn insert_unknown_text(&mut self) -> SymbolId {
        let sid = self.ranges.len();
        self.ranges.push(None);
        sid
    }

    /// Keeps the first `num_symbols` symbols and their text.
    fn truncate(&mut self, num_symbols: usize) {
        self.ranges.truncate(num_symbols);
        let text_len = self
            .ranges
            .iter()
            .rev()
            .find_map(|range| *range)
            .map_or(0, |(_, end)| end.get() as usize);
        self.arena.truncate(text_len);
    }
}

/// The symbol table a writer uses to assign symbol IDs to text.
// Like `SymbolTable`, this always contains the system symbols, so it is never empty.
#[allow(clippy::len_without_is_empty)]
pub struct WriterSymbolTable {
    ion_version: IonVersion,
    texts: SymbolTexts,
    ids_by_text: HashTable<SymbolId>,
    num_pending: usize,
}

impl WriterSymbolTable {
    const INITIAL_USER_SYMBOL_CAPACITY: usize = 32;
    const INITIAL_TEXT_CAPACITY: usize = 256;

    pub(crate) fn new(ion_version: IonVersion) -> Self {
        let num_system_symbols = ion_version.system_symbol_table().len();
        let mut table = Self {
            ion_version,
            texts: SymbolTexts::with_capacity(
                num_system_symbols + Self::INITIAL_USER_SYMBOL_CAPACITY,
                Self::INITIAL_TEXT_CAPACITY,
            ),
            ids_by_text: HashTable::with_capacity(
                num_system_symbols + Self::INITIAL_USER_SYMBOL_CAPACITY,
            ),
            num_pending: 0,
        };
        table.texts.insert_unknown_text(); // $0
        for text in ion_version.system_symbol_table().symbols_by_address {
            table.texts.insert(text);
        }
        table.index_system_symbols();
        table
    }

    fn num_system_symbols(&self) -> usize {
        self.ion_version.system_symbol_table().len()
    }

    /// Adds the system symbols, which are already in `texts`, to the empty text lookup index.
    fn index_system_symbols(&mut self) {
        let texts = &self.texts;
        // SID 0 has unknown text, so it is not part of the text lookup index.
        for sid in 1..self.num_system_symbols() {
            let text = texts.get(sid).unwrap_or("");
            self.ids_by_text
                .insert_unique(symbol_text_hash(text), sid, |sid| {
                    symbol_text_hash(texts.get(*sid).unwrap_or(""))
                });
        }
    }

    /// Returns the SID for `text`, interning the text and assigning it a new SID if needed.
    ///
    /// The Ion spec requires the lowest SID when more than one maps to the same text. This table
    /// never assigns a second SID to text it already holds, so the only matching SID is the lowest.
    pub(crate) fn get_or_add(&mut self, text: impl AsRef<str>) -> SymbolId {
        let text = text.as_ref();
        let texts = &self.texts;
        match self.ids_by_text.entry(
            symbol_text_hash(text),
            |sid| texts.get_bytes(*sid) == Some(text.as_bytes()),
            |sid| symbol_text_hash(texts.get(*sid).unwrap_or("")),
        ) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let sid = self.texts.insert(text);
                entry.insert(sid);
                self.num_pending += 1;
                sid
            }
        }
    }

    /// If defined, returns the lowest Symbol ID associated with the provided text, as the Ion spec
    /// requires. This table never assigns two SIDs to the same text, so there is only one match.
    pub fn sid_for(&self, text: impl AsRef<str>) -> Option<SymbolId> {
        let text = text.as_ref();
        self.ids_by_text
            .find(symbol_text_hash(text), |sid| {
                self.texts.get_bytes(*sid) == Some(text.as_bytes())
            })
            .copied()
    }

    /// If defined, returns the text associated with the provided Symbol ID.
    #[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
    pub fn text_for(&self, sid: SymbolId) -> Option<&str> {
        self.texts.get(sid)
    }

    /// Returns true if `sid` is in the range defined by this table.
    pub fn sid_is_valid(&self, sid: SymbolId) -> bool {
        sid < self.len()
    }

    /// Returns the number of symbol addresses defined by this table, including SID 0.
    pub fn len(&self) -> usize {
        self.texts.len()
    }

    #[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
    pub fn ion_version(&self) -> IonVersion {
        self.ion_version
    }

    pub(crate) fn num_pending(&self) -> usize {
        self.num_pending
    }

    pub(crate) fn reset_num_pending(&mut self) {
        self.num_pending = 0;
    }

    pub(crate) fn pending_texts(&self) -> impl Iterator<Item = &str> {
        debug_assert!(self.num_pending <= self.len() - self.num_system_symbols());
        let first_pending = self.len() - self.num_pending;
        (first_pending..self.len()).map(|sid| self.texts.get(sid).unwrap_or(""))
    }

    /// Clears all user symbols while retaining ordinary working capacity and the system symbols.
    /// Oversized entry storage and text storage are capped independently.
    pub(crate) fn reset_for_reuse(
        &mut self,
        max_retained_symbols: usize,
        max_retained_text_bytes: usize,
    ) {
        let num_system_symbols = self.num_system_symbols();
        self.texts.truncate(num_system_symbols);
        self.texts.arena.shrink_to(max_retained_text_bytes);
        self.texts.ranges.shrink_to(max_retained_symbols);
        self.num_pending = 0;

        // `retain` would leave tombstones that skew `capacity`, so clear and re-index instead.
        let oversized = self.ids_by_text.capacity() > max_retained_symbols;
        self.ids_by_text.clear();
        if oversized {
            // The table is empty, so the hasher is never called.
            self.ids_by_text.shrink_to(
                num_system_symbols + Self::INITIAL_USER_SYMBOL_CAPACITY,
                |_| 0,
            );
        }
        self.index_system_symbols();
    }

    /// The number of symbol entries this table can retain without reallocating.
    #[cfg(test)]
    pub(crate) fn retained_capacity(&self) -> usize {
        self.texts
            .ranges
            .capacity()
            .max(self.ids_by_text.capacity())
    }

    /// The number of symbol-text bytes this table can retain without reallocating.
    #[cfg(test)]
    pub(crate) fn retained_text_capacity(&self) -> usize {
        self.texts.arena.capacity()
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
mod reader_symbol_table_tests {
    use super::*;

    #[test]
    fn sid_for_returns_the_lowest_matching_sid() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        table.add_symbol(Symbol::owned("foo"));
        table.add_symbol(Symbol::owned("name"));
        table.add_symbol(Symbol::owned("foo"));

        assert_eq!(table.sid_for("$ion"), Some(1));
        assert_eq!(table.sid_for("name"), Some(4));
        assert_eq!(table.sid_for("foo"), Some(10));
        assert_eq!(table.sid_for("bar"), None);
    }

    #[test]
    fn sid_for_empty_text_does_not_match_sid_zero() {
        let table = SymbolTable::new(IonVersion::v1_0);
        assert_eq!(table.sid_for(""), None);
    }

    #[test]
    fn sid_for_empty_text_matches_only_empty_symbols() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        table.add_symbol(Symbol::unknown_text());
        assert_eq!(table.sid_for(""), None);

        table.add_symbol(Symbol::owned(""));
        assert_eq!(table.sid_for(""), Some(11));

        table.add_symbol(Symbol::unknown_text());
        assert_eq!(table.sid_for(""), Some(11));
    }

    #[test]
    fn reset_to_prefix_only_removes_user_symbols() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        table.add_symbol(Symbol::owned("foo"));
        table.add_symbol(Symbol::owned("name"));

        table.reset_to_prefix_only();
        table.add_symbol(Symbol::owned("bar"));

        assert_eq!(table.len(), 11);
        assert_eq!(table.sid_for("foo"), None);
        assert_eq!(table.sid_for("name"), Some(4));
        assert_eq!(table.sid_for("bar"), Some(10));
        assert_eq!(table.text_for(10), Some("bar"));
    }
}

#[cfg(test)]
mod writer_symbol_table_tests {
    use super::*;
    use rstest::rstest;

    #[test]
    fn system_symbols_are_indexed_without_becoming_pending() {
        let table = WriterSymbolTable::new(IonVersion::v1_0);
        assert_eq!(table.sid_for("$ion"), Some(1));
        assert_eq!(table.text_for(1), Some("$ion"));
        assert!(table.sid_is_valid(0));
        assert_eq!(table.text_for(0), None);
        assert_eq!(table.len(), 10);
        assert_eq!(table.num_pending(), 0);
    }

    #[test]
    fn user_symbols_are_arena_backed_and_deduplicated() {
        let mut table = WriterSymbolTable::new(IonVersion::v1_0);
        let foo_sid = table.get_or_add("foo");
        let bar_sid = table.get_or_add("bar");

        assert_eq!(foo_sid, 10);
        assert_eq!(bar_sid, 11);
        assert_eq!(table.get_or_add("foo"), foo_sid);
        assert_eq!(table.sid_for("bar"), Some(bar_sid));
        assert_eq!(table.text_for(foo_sid), Some("foo"));
        assert!(table.texts.arena.ends_with("foobar"));
        assert_eq!(table.num_pending(), 2);
        assert_eq!(table.pending_texts().collect::<Vec<_>>(), ["foo", "bar"]);
    }

    #[test]
    fn empty_text_is_a_regular_user_symbol() {
        let mut table = WriterSymbolTable::new(IonVersion::v1_0);
        assert_eq!(table.sid_for(""), None);
        let sid = table.get_or_add("");
        assert_eq!(sid, 10);
        assert_eq!(table.sid_for(""), Some(sid));
        assert_eq!(table.text_for(sid), Some(""));
    }

    #[test]
    fn pending_symbols_begin_after_the_last_reset() {
        let mut table = WriterSymbolTable::new(IonVersion::v1_0);
        table.get_or_add("foo");
        table.reset_num_pending();
        table.get_or_add("foo");
        table.get_or_add("bar");

        assert_eq!(table.num_pending(), 1);
        assert_eq!(table.pending_texts().collect::<Vec<_>>(), ["bar"]);
    }

    #[test]
    fn reset_for_reuse_keeps_system_symbols_and_discards_user_symbols() {
        let mut table = WriterSymbolTable::new(IonVersion::v1_0);
        table.get_or_add("foo");
        let entry_capacity = table.retained_capacity();
        let text_capacity = table.retained_text_capacity();

        table.reset_for_reuse(usize::MAX, usize::MAX);

        assert_eq!(table.sid_for("$ion"), Some(1));
        assert_eq!(table.sid_for("foo"), None);
        assert_eq!(table.len(), 10);
        assert_eq!(table.num_pending(), 0);
        assert_eq!(table.retained_capacity(), entry_capacity);
        assert_eq!(table.retained_text_capacity(), text_capacity);
    }

    #[rstest]
    #[case::neither_cap_exceeded(1, 0, false, false)]
    #[case::symbol_cap_only(128, 0, true, false)]
    #[case::text_cap_only(1, 4096, false, true)]
    #[case::both_caps(128, 4096, true, true)]
    fn reset_for_reuse_caps_storage_independently(
        #[case] short_symbols: usize,
        #[case] long_text_len: usize,
        #[case] expect_symbols_released: bool,
        #[case] expect_text_released: bool,
    ) {
        const MAX_SYMBOLS: usize = 64;
        const MAX_TEXT_BYTES: usize = 1024;
        let mut table = WriterSymbolTable::new(IonVersion::v1_0);
        for i in 0..short_symbols {
            table.get_or_add(format!("s{i}"));
        }
        if long_text_len > 0 {
            table.get_or_add("x".repeat(long_text_len));
        }
        let symbol_capacity = table.retained_capacity();
        let text_capacity = table.retained_text_capacity();
        assert_eq!(symbol_capacity > MAX_SYMBOLS, expect_symbols_released);
        assert_eq!(text_capacity > MAX_TEXT_BYTES, expect_text_released);

        table.reset_for_reuse(MAX_SYMBOLS, MAX_TEXT_BYTES);

        if expect_symbols_released {
            assert!(table.retained_capacity() <= MAX_SYMBOLS);
        } else {
            assert_eq!(table.retained_capacity(), symbol_capacity);
        }
        if expect_text_released {
            assert!(table.retained_text_capacity() <= MAX_TEXT_BYTES);
        } else {
            assert_eq!(table.retained_text_capacity(), text_capacity);
        }
        assert_eq!(table.sid_for("$ion"), Some(1));
        assert_eq!(table.len(), 10);
        assert_eq!(table.get_or_add("foo"), 10);
    }
}
