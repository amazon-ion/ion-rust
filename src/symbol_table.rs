use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Range;

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
    /// more than once, returns the highest ID. User symbols with unknown text match `""`.
    ///
    /// This is a linear scan; readers resolve symbols by ID, not by text.
    pub fn sid_for<A: AsRef<str>>(&self, text: A) -> Option<SymbolId> {
        let text = text.as_ref();
        self.symbols_by_id
            .iter()
            .enumerate()
            .skip(1) // $0 is never resolved by text
            .rev()
            .find(|(_, symbol)| symbol.text().unwrap_or("") == text)
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

/// Resolves a writer symbol ID using the static system table or the user-symbol arena.
fn writer_text_for<'a>(
    system_symbols: &'static SystemSymbolTable,
    text_arena: &'a str,
    text_ranges: &'a [Range<usize>],
    sid: SymbolId,
) -> Option<&'a str> {
    if sid == 0 {
        return None;
    }
    if sid < system_symbols.len() {
        return system_symbols.text_for_address(sid);
    }
    let range = text_ranges.get(sid - system_symbols.len())?;
    Some(&text_arena[range.clone()])
}

/// Like [`writer_text_for`], but returns bytes, which skips the UTF-8 boundary checks of `str`
/// slicing on the lookup hot path. SIDs without text yield no bytes; they are never indexed.
fn writer_bytes_for<'a>(
    system_symbols: &'static SystemSymbolTable,
    text_arena: &'a str,
    text_ranges: &'a [Range<usize>],
    sid: SymbolId,
) -> &'a [u8] {
    if sid == 0 {
        return &[];
    }
    if sid < system_symbols.len() {
        return system_symbols
            .text_for_address(sid)
            .map_or(&[], str::as_bytes);
    }
    text_ranges
        .get(sid - system_symbols.len())
        .and_then(|range| text_arena.as_bytes().get(range.clone()))
        .unwrap_or(&[])
}

/// Rehashes an SID already in the index. Only `seed_system_symbols` and `get_or_add` insert into
/// the index, and both insert SIDs that have text, so the empty-text fallback is never taken.
fn indexed_sid_hash(
    system_symbols: &'static SystemSymbolTable,
    text_arena: &str,
    text_ranges: &[Range<usize>],
    sid: SymbolId,
) -> u64 {
    symbol_text_hash(writer_text_for(system_symbols, text_arena, text_ranges, sid).unwrap_or(""))
}

/// The symbol table a writer uses to assign symbol IDs to text.
// Like `SymbolTable`, this always contains the system symbols, so it is never empty.
#[allow(clippy::len_without_is_empty)]
pub struct WriterSymbolTable {
    ion_version: IonVersion,
    text_arena: String,
    text_ranges: Vec<Range<usize>>,
    ids_by_text: HashTable<SymbolId>,
    num_pending: usize,
}

impl WriterSymbolTable {
    const INITIAL_USER_SYMBOL_CAPACITY: usize = 32;
    const INITIAL_TEXT_CAPACITY: usize = 256;

    pub(crate) fn new(ion_version: IonVersion) -> Self {
        let system_symbol_count = ion_version.system_symbol_table().len();
        let mut table = Self {
            ion_version,
            text_arena: String::with_capacity(Self::INITIAL_TEXT_CAPACITY),
            text_ranges: Vec::with_capacity(Self::INITIAL_USER_SYMBOL_CAPACITY),
            ids_by_text: HashTable::with_capacity(
                system_symbol_count + Self::INITIAL_USER_SYMBOL_CAPACITY,
            ),
            num_pending: 0,
        };
        table.seed_system_symbols();
        table
    }

    fn seed_system_symbols(&mut self) {
        let system_symbols = self.ion_version.system_symbol_table();
        // SID 0 has unknown text, so it is valid but is not part of the text lookup index.
        for (index, text) in system_symbols.symbols_by_address.iter().enumerate() {
            self.ids_by_text
                .insert_unique(symbol_text_hash(text), index + 1, |sid| {
                    indexed_sid_hash(system_symbols, "", &[], *sid)
                });
        }
    }

    /// Returns the existing SID for `text`, or interns the text and assigns it a new SID.
    pub(crate) fn get_or_add(&mut self, text: impl AsRef<str>) -> SymbolId {
        let text = text.as_ref();
        let hash = symbol_text_hash(text);
        let system_symbols = self.ion_version.system_symbol_table();

        let text_arena = self.text_arena.as_str();
        let text_ranges = self.text_ranges.as_slice();
        if let Some(sid) = self.ids_by_text.find(hash, |sid| {
            writer_bytes_for(system_symbols, text_arena, text_ranges, *sid) == text.as_bytes()
        }) {
            return *sid;
        }

        let start = self.text_arena.len();
        self.text_arena.push_str(text);
        let end = self.text_arena.len();
        self.text_ranges.push(start..end);
        let sid = system_symbols.len() + self.text_ranges.len() - 1;
        let (text_arena, text_ranges) = (self.text_arena.as_str(), self.text_ranges.as_slice());
        // Reuses `hash`, so the new text is not hashed a second time.
        self.ids_by_text.insert_unique(hash, sid, |sid| {
            indexed_sid_hash(system_symbols, text_arena, text_ranges, *sid)
        });
        self.num_pending += 1;
        sid
    }

    /// If defined, returns the Symbol ID associated with the provided text.
    pub fn sid_for(&self, text: impl AsRef<str>) -> Option<SymbolId> {
        let text = text.as_ref();
        let hash = symbol_text_hash(text);
        let system_symbols = self.ion_version.system_symbol_table();
        self.ids_by_text
            .find(hash, |sid| {
                writer_bytes_for(system_symbols, &self.text_arena, &self.text_ranges, *sid)
                    == text.as_bytes()
            })
            .copied()
    }

    /// If defined, returns the text associated with the provided Symbol ID.
    #[cfg_attr(not(feature = "experimental-reader-writer"), allow(dead_code))]
    pub fn text_for(&self, sid: SymbolId) -> Option<&str> {
        writer_text_for(
            self.ion_version.system_symbol_table(),
            self.text_arena.as_str(),
            self.text_ranges.as_slice(),
            sid,
        )
    }

    /// Returns true if `sid` is in the range defined by this table.
    pub fn sid_is_valid(&self, sid: SymbolId) -> bool {
        sid < self.len()
    }

    /// Returns the number of symbol addresses defined by this table, including SID 0.
    pub fn len(&self) -> usize {
        self.ion_version.system_symbol_table().len() + self.text_ranges.len()
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
        debug_assert!(self.num_pending <= self.text_ranges.len());
        let first_pending = self.text_ranges.len() - self.num_pending;
        self.text_ranges[first_pending..]
            .iter()
            .map(|range| &self.text_arena[range.clone()])
    }

    /// Clears all user symbols while retaining ordinary working capacity and the system index.
    /// Oversized entry storage and text storage are capped independently.
    pub(crate) fn reset_for_reuse(
        &mut self,
        max_retained_symbols: usize,
        max_retained_text_bytes: usize,
    ) {
        self.text_arena.clear();
        self.text_ranges.clear();
        self.num_pending = 0;

        if self.text_arena.capacity() > max_retained_text_bytes {
            self.text_arena = String::with_capacity(Self::INITIAL_TEXT_CAPACITY);
        }
        if self.text_ranges.capacity() > max_retained_symbols {
            self.text_ranges = Vec::with_capacity(Self::INITIAL_USER_SYMBOL_CAPACITY);
        }

        let system_symbol_count = self.ion_version.system_symbol_table().len();
        if self.ids_by_text.capacity() > max_retained_symbols {
            self.ids_by_text =
                HashTable::with_capacity(system_symbol_count + Self::INITIAL_USER_SYMBOL_CAPACITY);
            self.seed_system_symbols();
        } else {
            self.ids_by_text.retain(|sid| *sid < system_symbol_count);
        }
    }

    /// The number of symbol entries this table can retain without reallocating.
    #[cfg(test)]
    pub(crate) fn retained_capacity(&self) -> usize {
        self.text_ranges.capacity().max(self.ids_by_text.capacity())
    }

    /// The number of symbol-text bytes this table can retain without reallocating.
    #[cfg(test)]
    pub(crate) fn retained_text_capacity(&self) -> usize {
        self.text_arena.capacity()
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
    fn sid_for_returns_the_last_matching_sid() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        table.add_symbol(Symbol::owned("foo"));
        table.add_symbol(Symbol::owned("name"));
        table.add_symbol(Symbol::owned("foo"));

        assert_eq!(table.sid_for("$ion"), Some(1));
        assert_eq!(table.sid_for("name"), Some(11));
        assert_eq!(table.sid_for("foo"), Some(12));
        assert_eq!(table.sid_for("bar"), None);
    }

    #[test]
    fn sid_for_empty_text_skips_sid_zero() {
        let table = SymbolTable::new(IonVersion::v1_0);
        assert_eq!(table.sid_for(""), None);
    }

    #[test]
    fn sid_for_empty_text_matches_unknown_and_empty_symbols() {
        let mut table = SymbolTable::new(IonVersion::v1_0);
        table.add_symbol(Symbol::unknown_text());
        assert_eq!(table.sid_for(""), Some(10));

        table.add_symbol(Symbol::owned(""));
        assert_eq!(table.sid_for(""), Some(11));

        table.add_symbol(Symbol::unknown_text());
        assert_eq!(table.sid_for(""), Some(12));
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
        assert_eq!(table.text_arena, "foobar");
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
