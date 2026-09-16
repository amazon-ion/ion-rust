use crate::element::builders::StructBuilder;
use crate::element::Element;
use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::symbol_ref::AsSymbolRef;
use crate::text::text_formatter::FmtValueFormatter;
use crate::Symbol;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use rustc_hash::FxHasher;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::OnceLock;

/// Field counts at or below this length are served by a linear scan over `slots`; above it, `get()`
/// lazily builds and probes a hash index. The default is a benchmark-derived tuning value, not a
/// contract; revisit if `Element`/`Symbol` size or real `get()` access patterns change.
///
/// Chosen on aarch64 / Graviton2 against a happy-path (hit-dominated) workload: the linear-vs-hash
/// crossover measured at ~10 fields for 2 lookups/field, ~19 for 1×, and ~28 for 0.5×, and the cost
/// of setting the threshold too high (linear's O(n²) tail) dwarfs setting it too low (one bounded
/// ~140 ns + ~14 ns/field index build). Erring low, 16 covers the ≥1×/field cases and stays cheap
/// for the sparser ones.
///
/// The default (16) can be overridden at build time by setting the
/// `ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD` environment variable to a base-10 integer, e.g.
/// `ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD=32 cargo build`. This is a tuning/experimentation knob, not
/// a stability guarantee; a malformed value is a compile error. `rustc` records the read, so the
/// crate is rebuilt when the value changes.
const LINEAR_SCAN_THRESHOLD: usize = match option_env!("ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD") {
    None => 16,
    Some(text) => parse_threshold(text),
};

/// Parses the `ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD` override in const context. A non-empty run of
/// ASCII digits only; anything else is a compile error, and const evaluation traps on overflow.
const fn parse_threshold(text: &str) -> usize {
    let bytes = text.as_bytes();
    assert!(
        !bytes.is_empty(),
        "ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD must not be empty"
    );
    let mut value: usize = 0;
    let mut i = 0;
    while i < bytes.len() {
        let digit = bytes[i];
        assert!(
            digit >= b'0' && digit <= b'9',
            "ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD must be a base-10 integer"
        );
        value = value * 10 + (digit - b'0') as usize;
        i += 1;
    }
    value
}

/// One entry in the lazily built hash lookup index. Stores the cached field-name hash (so probes
/// don't rehash the stored name) and the index of the corresponding pair in [`Fields::slots`].
/// Every slot is indexed, including unknown-text (`$0`) fields (see [`symbol_name_hash`]).
#[derive(Debug, Clone, Copy)]
struct HashIndex {
    hash: u64,
    slot_index: u32,
}

/// Lazily built auxiliary indexes over [`Fields::slots`]. Boxed behind a single `OnceLock` so an
/// iterate-only struct never allocates either index, and so `Fields` itself stays pointer-small.
#[derive(Debug, Clone, Default)]
struct FieldsAux {
    /// Hash lookup index over all fields, built on the first large-struct `get()`.
    table: OnceLock<Box<HashTable<HashIndex>>>,
    /// Slot indices sorted into canonical Ion field order, built on the first
    /// equality / ordering / hashing operation. Covers **all** slots, including unknown-text ones.
    by_field: OnceLock<Box<[u32]>>,
}

// The struct's storage, split into its own type so `Struct` stays a thin wrapper.
#[derive(Debug, Clone)]
struct Fields {
    /// Every (name, value) pair in insertion order. The single source of truth for the struct's
    /// contents — a boxed slice rather than a `Vec` because a struct is immutable once built, so the
    /// capacity word is dead weight.
    slots: Box<[(Symbol, Element)]>,
    /// Lazily allocated indexes; absent until the first operation that needs one.
    aux: OnceLock<Box<FieldsAux>>,
}

/// Hashes a field name's text with the portable hasher the lookup index is built against. `get()`
/// must hash probes the same way the index was populated, so this is the one place the choice lives.
fn field_name_hash(text: &str) -> u64 {
    let mut hasher = FxHasher::default();
    text.hash(&mut hasher);
    hasher.finish()
}

/// The hash a text-less field name (`$0`, unknown text) is indexed and probed under. `$0` has no
/// text to feed [`field_name_hash`], so it gets a fixed sentinel. Correctness does not depend on
/// the value — the `find` predicate disambiguates any collision, exactly as it does for two
/// known-text names that hash alike — and a known-text field is no likelier to hash here than to
/// any other fixed value. Every `$0` field shares this one hash, but the index dedups by name (see
/// [`Fields::table`]), so many `$0` fields cost one entry, not a single overloaded bucket.
const UNKNOWN_TEXT_HASH: u64 = 0;

/// The hash a field name is indexed and probed under: its `text` hashed with [`field_name_hash`],
/// or [`UNKNOWN_TEXT_HASH`] when the name has unknown text (`$0`, `text == None`). This is the one
/// place the index build and every probe agree on the mapping, so they cannot drift.
fn name_hash(text: Option<&str>) -> u64 {
    match text {
        Some(text) => field_name_hash(text),
        None => UNKNOWN_TEXT_HASH,
    }
}

impl Fields {
    fn aux(&self) -> &FieldsAux {
        self.aux
            .get_or_init(|| Box::new(FieldsAux::default()))
            .as_ref()
    }

    /// Returns the hash lookup index, building it on first use. Indexes the first slot of each
    /// distinct field name, keyed under [`name_hash`], so both known-text and unknown-text (`$0`)
    /// fields are probeable.
    ///
    /// Only the *first* occurrence of a name is stored: `get()` needs a single match and `get_all()`
    /// scans `slots` directly, so a later duplicate adds nothing to the index. Skipping duplicates
    /// also keeps the build linear — indexing every occurrence would pile all N repeats of a name
    /// (and all `$0` fields, which share one hash) into a single bucket, making the build O(N²).
    fn table(&self) -> &HashTable<HashIndex> {
        self.aux()
            .table
            .get_or_init(|| {
                // Slot indices are stored as `u32`; a struct with >4B fields is unsupported (and
                // would need hundreds of GB of live data). The cast below is checked here.
                debug_assert!(
                    self.slots.len() <= u32::MAX as usize,
                    "slot index must fit in u32"
                );
                let mut table = HashTable::with_capacity(self.slots.len());
                for (i, (name, _)) in self.slots.iter().enumerate() {
                    let hash = name_hash(name.text());
                    if let Entry::Vacant(vacant) = table.entry(
                        hash,
                        |entry: &HashIndex| {
                            self.slots[entry.slot_index as usize].0.text() == name.text()
                        },
                        |entry| entry.hash,
                    ) {
                        vacant.insert(HashIndex {
                            hash,
                            slot_index: i as u32,
                        });
                    }
                }
                Box::new(table)
            })
            .as_ref()
    }

    /// Returns slot indices in canonical Ion field order, building the ordering on first use.
    /// Used by equality, ordering, and hashing, all of which treat a struct as an unordered
    /// multiset of (name, value) pairs.
    fn by_field(&self) -> &[u32] {
        self.aux()
            .by_field
            .get_or_init(|| {
                debug_assert!(
                    self.slots.len() <= u32::MAX as usize,
                    "slot index must fit in u32"
                );
                let mut order: Vec<u32> = (0..self.slots.len() as u32).collect();
                // Unstable is fine: `ion_cmp_field` only reports `Equal` for slots that are fully
                // interchangeable for every `by_field` consumer, so their relative order is
                // irrelevant.
                order.sort_unstable_by(|&a, &b| {
                    ion_cmp_field(&self.slots[a as usize], &self.slots[b as usize])
                });
                order.into_boxed_slice()
            })
            .as_ref()
    }

    /// Returns *a* value associated with the given field name, or `None` if there is none.
    ///
    /// The Ion data model views a struct as an unordered bag of (name, value) pairs, so when a name
    /// appears more than once this returns an arbitrary match. The choice is consistent within a
    /// single struct instance but is otherwise unspecified. Applications that repeat field names
    /// should use [`get_all`](Self::get_all).
    fn get<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.get_matching(field_name.as_symbol_ref().text())
    }

    /// Looks up a field name by its `text` (`None` is the unknown-text `$0` name): a linear scan for
    /// small structs, a hash probe for large ones. The hash is derived from `text` via [`name_hash`]
    /// only on the probe path, so a small-struct lookup never hashes. When a name repeats, both
    /// regimes return the value at its *first* slot — the linear scan finds it first, and the index
    /// stores only that first slot (see [`table`](Self::table)) — so the two agree regardless of
    /// struct size. Callers must still treat the choice among duplicates as unspecified.
    fn get_matching(&self, text: Option<&str>) -> Option<&Element> {
        if self.slots.len() <= LINEAR_SCAN_THRESHOLD {
            self.slots
                .iter()
                .find(|(name, _)| name.text() == text)
                .map(|(_, value)| value)
        } else {
            self.table()
                .find(name_hash(text), |entry| {
                    self.slots[entry.slot_index as usize].0.text() == text
                })
                .map(|entry| &self.slots[entry.slot_index as usize].1)
        }
    }

    /// Iterates over all values associated with the given field name.
    ///
    /// This is a scan over `slots` regardless of struct size: duplicate field names are uncommon,
    /// so the hash index is not maintained per-name and this path does not consult it. Values are
    /// yielded in the order the pairs sit in `slots`, but a struct is an unordered bag so that
    /// order is an implementation artifact, not a guarantee to callers.
    fn get_all<A: AsSymbolRef>(&self, field_name: A) -> FieldValuesIterator<'_> {
        // The probe borrows from `field_name`, a by-value argument, so the target text cannot be
        // borrowed into the returned iterator. Copy it (cold path — see above) or record that an
        // unknown-text name was requested.
        let target = match field_name.as_symbol_ref().text() {
            Some(text) => FieldNameMatch::Text(text.to_owned()),
            None => FieldNameMatch::UnknownText,
        };
        FieldValuesIterator {
            slots: &self.slots,
            pos: 0,
            target,
        }
    }

    /// Iterates over all of the (field name, field value) pairs in the struct.
    fn iter(&self) -> impl Iterator<Item = &(Symbol, Element)> {
        self.slots.iter()
    }
}

/// Iterates over the (field name, field value) pairs in a Struct.
pub struct FieldIterator<'a> {
    values: Option<std::slice::Iter<'a, (Symbol, Element)>>,
}

impl<'a> FieldIterator<'a> {
    fn new(data: &'a [(Symbol, Element)]) -> Self {
        FieldIterator {
            values: Some(data.iter()),
        }
    }
}

impl<'a> Iterator for FieldIterator<'a> {
    type Item = (&'a Symbol, &'a Element);

    fn next(&mut self) -> Option<Self::Item> {
        self.values
            .as_mut()
            // Get the next &(name, value) and convert it to (&name, &value)
            .and_then(|iter| iter.next().map(|field| (&field.0, &field.1)))
    }
}

/// Iterates over the (field name, field value) pairs in a Struct.
pub struct OwnedFieldIterator {
    fields: VecDeque<(Symbol, Element)>,
}

impl OwnedFieldIterator {
    fn new(data: Vec<(Symbol, Element)>) -> Self {
        OwnedFieldIterator {
            fields: data.into(),
        }
    }
}

impl Iterator for OwnedFieldIterator {
    type Item = (Symbol, Element);

    fn next(&mut self) -> Option<Self::Item> {
        self.fields.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.fields.len();
        (len, Some(len))
    }
}

/// The field name a [`FieldValuesIterator`] matches against. Owned so the iterator can outlive the
/// by-value probe argument it was built from.
enum FieldNameMatch {
    UnknownText,
    Text(String),
}

/// Iterates over the values associated with a given field name in a Struct.
pub(crate) struct FieldValuesIterator<'a> {
    slots: &'a [(Symbol, Element)],
    pos: usize,
    target: FieldNameMatch,
}

impl<'a> Iterator for FieldValuesIterator<'a> {
    type Item = &'a Element;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((name, value)) = self.slots.get(self.pos) {
            self.pos += 1;
            let matches = match &self.target {
                FieldNameMatch::UnknownText => name.text().is_none(),
                FieldNameMatch::Text(text) => name.text() == Some(text.as_str()),
            };
            if matches {
                return Some(value);
            }
        }
        None
    }
}

/// An in-memory representation of an Ion Struct
/// ```
/// use ion_rs::{Element, ion_struct};
/// # use ion_rs::IonResult;
/// # fn main() -> IonResult<()> {
/// let struct_ = ion_struct! {
///   "foo": 1,
///   "bar": true,
///   "baz": "hello"
/// };
/// assert_eq!(struct_.len(), 3);
/// assert_eq!(struct_.get("baz"), Some(&Element::string("hello")));
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Struct {
    fields: Fields,
}

impl Display for Struct {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = FmtValueFormatter { output: f };
        ivf.format_struct(self).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl Struct {
    pub fn builder() -> StructBuilder {
        StructBuilder::new()
    }

    pub fn clone_builder(&self) -> StructBuilder {
        StructBuilder::with_initial_fields(&self.fields.slots)
    }

    /// Returns an iterator over the field name/value pairs in this Struct.
    #[allow(clippy::map_identity)]
    // ^-- This is a temporary workaround for a bug in Clippy that should be fixed in the next release.
    // See: https://github.com/rust-lang/rust-clippy/issues/9280
    pub fn fields(&self) -> impl Iterator<Item = (&Symbol, &Element)> {
        self.fields
            .iter()
            // Here we convert from &(name, value) to (&name, &value).
            // The former makes a stronger assertion about how the data is being stored. We don't
            // want that to be a mandatory part of the public API.
            .map(|(name, element)| (name, element))
    }

    /// Compares two structs as unordered multisets of (name, value) pairs.
    ///
    /// Each side's slots are visited in canonical Ion field order (via `by_field`) and compared
    /// positionally. This is valid even though `eq` may be coarser than Ion's total `ion_cmp`
    /// order — `PartialEq` treats `-0e0 == 0e0`, numeric-equal decimals such as `0d0`/`0d3` as
    /// equal, and timestamps as equal by instant — because `ion_cmp` orders each such
    /// `eq`-equivalence class as a **contiguous run**: the tie-breaks it adds (e.g. decimal
    /// exponent, timestamp precision/offset) only reorder values that are already `eq`-equal, so no
    /// `eq`-*unequal* value ever sorts between two `eq`-equal ones. Sorting both sides by `ion_cmp`
    /// and pairing positionally therefore cannot mis-pair slots. A future `eq` that merged two
    /// values with an `eq`-unequal value ordered between them would break this invariant and would
    /// instead need a greedy bipartite match over each repeated name's values.
    fn fields_eq(&self, other: &Self, eq: impl Fn(&Element, &Element) -> bool) -> bool {
        let these = self.fields.by_field();
        let those = other.fields.by_field();
        // Callers guarantee equal length before reaching here.
        debug_assert_eq!(these.len(), those.len());
        for (&this_i, &that_i) in these.iter().zip(those.iter()) {
            let (this_name, this_value) = &self.fields.slots[this_i as usize];
            let (that_name, that_value) = &other.fields.slots[that_i as usize];
            // Only name equality matters here (`by_field` already put both sides in the same
            // order); `ion_eq` can short-circuit on the first differing byte, where `ion_cmp` would
            // compute a full ordering.
            if !this_name.ion_eq(that_name) {
                return false;
            }
            if !eq(this_value, that_value) {
                return false;
            }
        }
        true
    }

    /// Returns the number of fields in this Struct.
    pub fn len(&self) -> usize {
        self.fields.slots.len()
    }

    /// Returns `true` if this struct has zero fields.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> FieldIterator<'_> {
        FieldIterator::new(&self.fields.slots)
    }

    /// Returns a value associated with the specified field name.
    ///
    /// The Ion data model views a struct as an unordered bag of (name, value) pairs. If more than
    /// one field has the given name, this returns an arbitrary one; the choice is consistent within
    /// a single struct instance but is otherwise unspecified. To access every value for a repeated
    /// name, see [`get_all`](Self::get_all).
    pub fn get<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.fields.get(field_name)
    }

    /// Returns an iterator over all of the values associated with the specified field name.
    pub fn get_all<A: AsSymbolRef>(&self, field_name: A) -> impl Iterator<Item = &Element> {
        self.fields.get_all(field_name)
    }
}

// Allows `for (name, value) in &my_struct {...}` syntax
impl<'a> IntoIterator for &'a Struct {
    type Item = (&'a Symbol, &'a Element);
    type IntoIter = FieldIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// Allows `for (name, value) in my_struct {...}` syntax
impl IntoIterator for Struct {
    type Item = (Symbol, Element);
    type IntoIter = OwnedFieldIterator;

    fn into_iter(self) -> Self::IntoIter {
        // `into_vec` reuses the boxed slice's allocation, so this does not copy the elements.
        OwnedFieldIterator::new(self.fields.slots.into_vec())
    }
}

impl<K, V> FromIterator<(K, V)> for Struct
where
    K: Into<Symbol>,
    V: Into<Element>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let slots: Box<[(Symbol, Element)]> = iter
            .into_iter()
            .map(|(name, value)| (name.into(), value.into()))
            .collect();
        let fields = Fields {
            slots,
            aux: OnceLock::new(),
        };
        Self { fields }
    }
}

impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.fields_eq(other, |a, b| a == b)
    }
}

impl IonEq for Struct {
    fn ion_eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.fields_eq(other, |a, b| a.ion_eq(b))
    }
}

impl IonDataOrd for Struct {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        let these = self.fields.by_field();
        let those = other.fields.by_field();
        let mut i0 = these.iter();
        let mut i1 = those.iter();
        loop {
            match [i0.next(), i1.next()] {
                [None, Some(_)] => return Ordering::Less,
                [None, None] => return Ordering::Equal,
                [Some(_), None] => return Ordering::Greater,
                [Some(&a), Some(&b)] => {
                    let ord = ion_cmp_field(
                        &self.fields.slots[a as usize],
                        &other.fields.slots[b as usize],
                    );
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
            }
        }
    }
}

fn ion_cmp_field(this: &(Symbol, Element), that: &(Symbol, Element)) -> Ordering {
    let ord = this.0.ion_cmp(&that.0);
    if !ord.is_eq() {
        return ord;
    }
    IonDataOrd::ion_cmp(&this.1, &that.1)
}

impl IonDataHash for Struct {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        for &i in self.fields.by_field() {
            let (name, value) = &self.fields.slots[i as usize];
            name.ion_data_hash(state);
            value.ion_data_hash(state);
        }
    }
}

// `Struct` is one variant of the `Value` enum embedded in `Element`. Keeping its footprint within
// the per-variant budget is what lets `Element` fit in a single 64-byte cache line on a 64-bit
// target; a later field addition that busts this budget fails to compile here rather than silently
// growing `Element`. The byte counts are a 64-bit-target claim (see the 32-bit counterpart below).
#[cfg(target_pointer_width = "64")]
const _: () = {
    assert!(std::mem::size_of::<Struct>() <= 32);
    assert!(std::mem::align_of::<Struct>() == 8);
};

// The 32-bit counterpart, so `wasm32`/`i686` check something rather than skipping. `Fields` is
// entirely pointer-shaped (a boxed slice plus a `OnceLock<Box<_>>`), so it halves on a 32-bit
// target: two words for `slots`, two for `aux`.
#[cfg(target_pointer_width = "32")]
const _: () = {
    assert!(std::mem::size_of::<Struct>() <= 16);
    assert!(std::mem::align_of::<Struct>() == 4);
};

#[cfg(test)]
mod tests {
    use crate::element::Element;
    use crate::ion_data::IonEq;
    use crate::{ion_struct, Struct, Symbol};

    // Field count that forces `get()` onto the hash-index path (> LINEAR_SCAN_THRESHOLD). Derived
    // from the threshold so a build-time `ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD` override can't
    // silently drop these cases back onto the linear path and void the hash-index coverage.
    const ABOVE_THRESHOLD: usize = super::LINEAR_SCAN_THRESHOLD * 4 + 1;

    /// Builds a struct with `n` distinct fields named `f0..fn`, plus any `extra` (name, value)
    /// pairs appended after them. Used to exercise both the linear-scan and hash-index regimes.
    fn struct_with(n: usize, extra: &[(&str, i64)]) -> Struct {
        let mut builder = Struct::builder();
        for i in 0..n {
            builder = builder.with_field(format!("f{i}"), Element::int(i as i64));
        }
        for (name, value) in extra {
            builder = builder.with_field(*name, Element::int(*value));
        }
        builder.build()
    }

    #[test]
    fn get_all_preserves_duplicates_and_order() {
        // A name repeated three times yields all three, in insertion order.
        let s = ion_struct! { "a": 1, "a": 2, "a": 3, "b": 9 };
        let all: Vec<_> = s.get_all("a").collect();
        assert_eq!(
            all,
            vec![&Element::int(1), &Element::int(2), &Element::int(3)]
        );
        // A unique name yields exactly one.
        assert_eq!(s.get_all("b").collect::<Vec<_>>(), vec![&Element::int(9)]);
        // An absent name yields none.
        assert_eq!(s.get_all("z").count(), 0);
    }

    #[test]
    fn get_all_scans_in_both_regimes() {
        // Above the threshold, get_all still scans slots rather than consulting the index.
        let s = struct_with(ABOVE_THRESHOLD, &[("dup", 1), ("dup", 2), ("dup", 3)]);
        assert_eq!(
            s.get_all("dup").collect::<Vec<_>>(),
            vec![&Element::int(1), &Element::int(2), &Element::int(3)]
        );
        assert_eq!(s.get_all("f0").collect::<Vec<_>>(), vec![&Element::int(0)]);
    }

    #[rstest::rstest]
    #[case::below(4)]
    #[case::above(ABOVE_THRESHOLD)]
    fn get_matches_str_symbol_and_symbol_ref(#[case] n: usize) {
        // The struct's own fields land in slots f0..fn; append a known target after them.
        let s = struct_with(n, &[("target", 42)]);
        let expected = Some(&Element::int(42));

        // &str probe
        assert_eq!(s.get("target"), expected);
        // &Symbol probe
        let sym = Symbol::owned("target");
        assert_eq!(s.get(&sym), expected);
        // owned Symbol probe
        assert_eq!(s.get(Symbol::owned("target")), expected);
    }

    #[rstest::rstest]
    #[case::below(4)]
    #[case::above(ABOVE_THRESHOLD)]
    fn get_and_get_all_find_unknown_text(#[case] n: usize) {
        // Build with an unknown-text ($0) field among known ones.
        let mut builder = Struct::builder();
        for i in 0..n {
            builder = builder.with_field(format!("f{i}"), Element::int(i as i64));
        }
        let s = builder
            .with_field(Symbol::unknown_text(), Element::int(7))
            .build();

        assert_eq!(s.get(Symbol::unknown_text()), Some(&Element::int(7)));
        assert_eq!(
            s.get_all(Symbol::unknown_text()).collect::<Vec<_>>(),
            vec![&Element::int(7)]
        );
    }

    #[rstest::rstest]
    #[case::below(4)]
    #[case::above(ABOVE_THRESHOLD)]
    fn repeated_unknown_text_fields(#[case] n: usize) {
        // Multiple $0 fields all key under UNKNOWN_TEXT_HASH, so above the threshold the hash index
        // holds several entries in one bucket and a probe must walk them. A $0 placed non-terminally
        // (first here) also guards against the lookup only ever finding a trailing text-less slot.
        let mut builder = Struct::builder().with_field(Symbol::unknown_text(), Element::int(1));
        for i in 0..n {
            builder = builder.with_field(format!("f{i}"), Element::int(i as i64));
        }
        let s = builder
            .with_field(Symbol::unknown_text(), Element::int(2))
            .with_field(Symbol::owned(""), Element::int(3))
            .build();

        // get() returns *a* $0 value (which one is unspecified per its contract), never the ""
        // value — the point is that a text-less probe resolves to a text-less slot.
        let got = s.get(Symbol::unknown_text());
        assert!(got == Some(&Element::int(1)) || got == Some(&Element::int(2)));
        // get_all() yields every $0 value in slot order and excludes the "" field.
        assert_eq!(
            s.get_all(Symbol::unknown_text()).collect::<Vec<_>>(),
            vec![&Element::int(1), &Element::int(2)]
        );
        // The "" field and known-text fields remain independently resolvable.
        assert_eq!(s.get(""), Some(&Element::int(3)));
        if n > 0 {
            assert_eq!(s.get("f0"), Some(&Element::int(0)));
        }
    }

    #[rstest::rstest]
    #[case::below(4)]
    #[case::above(ABOVE_THRESHOLD)]
    fn unknown_text_and_empty_text_do_not_collide(#[case] n: usize) {
        // The unknown-text ($0) name and the empty-text ("") name are distinct field names that
        // must resolve independently. `name_hash` keys them under different hashes, so above the
        // threshold each probe walks its own bucket; below it, the linear scan compares full names.
        // Either way, collapsing the two — or letting one shadow the other in the index — would
        // return the wrong value, and adding both to the index must not disturb known-text lookups.
        let mut builder = struct_with(n, &[]).clone_builder();
        builder = builder
            .with_field(Symbol::unknown_text(), Element::int(100))
            .with_field(Symbol::owned(""), Element::int(200));
        let s = builder.build();

        assert_eq!(s.get(Symbol::unknown_text()), Some(&Element::int(100)));
        assert_eq!(s.get(Symbol::owned("")), Some(&Element::int(200)));
        assert_eq!(s.get(""), Some(&Element::int(200)));
        // Known-text fields still resolve with the text-less entries present in the index.
        if n > 0 {
            assert_eq!(s.get("f0"), Some(&Element::int(0)));
            let last = format!("f{}", n - 1);
            assert_eq!(s.get(last.as_str()), Some(&Element::int((n - 1) as i64)));
        }
    }

    #[rstest::rstest]
    #[case::below(4)]
    #[case::above(ABOVE_THRESHOLD)]
    fn get_absent_name_is_none(#[case] n: usize) {
        let s = struct_with(n, &[]);
        assert_eq!(s.get("not-a-field"), None);
        assert_eq!(s.get(Symbol::unknown_text()), None);
    }

    #[test]
    fn empty_struct() {
        let s = Struct::builder().build();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
        assert_eq!(s.get("anything"), None);
        assert_eq!(s.get_all("anything").count(), 0);
        assert_eq!(s, Struct::builder().build());
    }

    #[rstest::rstest]
    #[case(crate::types::r#struct::LINEAR_SCAN_THRESHOLD)]
    #[case(crate::types::r#struct::LINEAR_SCAN_THRESHOLD + 1)]
    fn threshold_boundary_lookup(#[case] n: usize) {
        // Off-by-one at the regime crossover: the last field must be findable at both N and N+1.
        let s = struct_with(n, &[]);
        let last = format!("f{}", n - 1);
        assert_eq!(s.get(last.as_str()), Some(&Element::int((n - 1) as i64)));
        assert_eq!(s.get("f0"), Some(&Element::int(0)));
    }

    #[test]
    fn duplicate_field_values_not_equal() {
        let s1 = ion_struct! { "a": 1, "a": 1, "a": 2 };
        let s2 = ion_struct! { "a": 1, "a": 2, "a": 2 };
        assert_ne!(s1, s2);
        assert!(!s1.ion_eq(&s2));
    }

    #[test]
    fn same_multiset_different_order_is_equal() {
        let s1 = ion_struct! { "a": 1, "a": 2, "b": 3 };
        let s2 = ion_struct! { "b": 3, "a": 2, "a": 1 };
        assert_eq!(s1, s2);
        assert!(s1.ion_eq(&s2));
    }

    #[test]
    fn equal_length_differing_repeat_counts_not_equal() {
        // Same length, same names present, but different multiplicities.
        let s1 = ion_struct! { "a": 1, "a": 2, "b": 3 };
        let s2 = ion_struct! { "a": 1, "b": 2, "b": 3 };
        assert_ne!(s1, s2);
        assert!(!s1.ion_eq(&s2));
    }

    #[test]
    fn all_identical_names_equal_as_multiset() {
        let s1 = ion_struct! { "a": 1, "a": 2, "a": 3 };
        let s2 = ion_struct! { "a": 3, "a": 1, "a": 2 };
        assert_eq!(s1, s2);
        assert!(s1.ion_eq(&s2));
    }

    #[rstest::rstest]
    // `pad` distinct filler fields (f0..f{pad}) precede the class-defining fields on both sides, so
    // the same struct lands below the threshold (pad=0, linear regime) or above it (hash regime).
    // Equality routes through `by_field`, which does not branch on the threshold, so every class
    // must resolve identically in both regimes.
    #[case::below(0)]
    #[case::above(ABOVE_THRESHOLD)]
    fn multiset_equality_classes(#[case] pad: usize) {
        let mk = |extra: &[(&str, i64)]| struct_with(pad, extra);
        // no duplicates, different order
        assert_eq!(mk(&[("a", 1), ("b", 2)]), mk(&[("b", 2), ("a", 1)]));
        // one name twice
        assert_eq!(mk(&[("a", 1), ("a", 2)]), mk(&[("a", 2), ("a", 1)]));
        assert!(mk(&[("a", 1), ("a", 2)]).ion_eq(&mk(&[("a", 2), ("a", 1)])));
        // all names identical
        assert_eq!(
            mk(&[("a", 1), ("a", 2), ("a", 3)]),
            mk(&[("a", 3), ("a", 1), ("a", 2)])
        );
        // equal length, same names present, differing repeat counts -> not equal
        assert_ne!(
            mk(&[("a", 1), ("a", 2), ("b", 3)]),
            mk(&[("a", 1), ("b", 2), ("b", 3)])
        );
        // differing values under a repeated name -> not equal (and not ion_eq)
        let s1 = mk(&[("a", 1), ("a", 2)]);
        let s2 = mk(&[("a", 1), ("a", 3)]);
        assert_ne!(s1, s2);
        assert!(!s1.ion_eq(&s2));
    }

    #[test]
    fn rebuild_changing_duplicate_shape_stays_equal() {
        // A struct rebuilt through the builder — introducing then removing a duplicate — must
        // compare equal to a direct build under both PartialEq and IonEq. This guards against an
        // index (here, `by_field`) that was somehow derived from a stale pair list.
        let direct = ion_struct! { "a": 1, "b": 2 };
        let rebuilt = direct
            .clone_builder()
            .with_field("b", Element::int(99)) // introduce a duplicate "b"
            .remove_field("b") // remove the first "b"
            .build();
        // rebuilt is now { a: 1, b: 99 }; not equal to the original, but a well-formed struct.
        assert_eq!(rebuilt, ion_struct! { "a": 1, "b": 99 });
        assert!(rebuilt.ion_eq(&ion_struct! { "a": 1, "b": 99 }));
    }

    #[test]
    fn nan_partial_eq_vs_ion_eq() {
        let s1 = ion_struct! { "x": f64::NAN };
        let s2 = ion_struct! { "x": f64::NAN };
        // PartialEq uses standard f64 semantics: NaN != NaN
        assert_ne!(s1, s2);
        // IonEq treats NaN as equivalent
        assert!(s1.ion_eq(&s2));
    }

    #[test]
    fn signed_zero_partial_eq_vs_ion_eq() {
        let s1 = ion_struct! { "x": 0.0f64 };
        let s2 = ion_struct! { "x": -0.0f64 };
        // PartialEq uses standard f64 semantics: 0.0 == -0.0
        assert_eq!(s1, s2);
        // IonEq distinguishes signed zeros
        assert!(!s1.ion_eq(&s2));
    }

    #[test]
    fn rebuild_last_duplicate_survives_removal() {
        // `remove_field` removes the FIRST matching field, so from {a:1, b:2, b:3} it leaves the
        // last "b". The lazy indexes must be rebuilt from the post-removal pair list: `get`/
        // `get_all` must see 3 (the survivor), never a stale 2.
        let rebuilt = ion_struct! { "a": 1, "b": 2, "b": 3 }
            .clone_builder()
            .remove_field("b")
            .build();
        let expected = ion_struct! { "a": 1, "b": 3 };
        assert_eq!(rebuilt, expected);
        assert!(rebuilt.ion_eq(&expected));
        assert_eq!(rebuilt.get("b"), Some(&Element::int(3)));
        assert_eq!(
            rebuilt.get_all("b").collect::<Vec<_>>(),
            vec![&Element::int(3)]
        );
    }

    #[rstest::rstest]
    #[case::below(4)]
    #[case::above(ABOVE_THRESHOLD)]
    fn get_all_across_probe_forms_and_absent(#[case] n: usize) {
        let s = struct_with(n, &[("target", 42), ("target", 43)]);
        let want = vec![Element::int(42), Element::int(43)];
        let sym = Symbol::owned("target");
        // &str, &Symbol, and owned Symbol probes all yield every value in insertion order.
        assert_eq!(s.get_all("target").cloned().collect::<Vec<_>>(), want);
        assert_eq!(s.get_all(&sym).cloned().collect::<Vec<_>>(), want);
        assert_eq!(
            s.get_all(Symbol::owned("target"))
                .cloned()
                .collect::<Vec<_>>(),
            want
        );
        // An absent name yields nothing in both regimes.
        assert_eq!(s.get_all("absent").count(), 0);
    }

    #[test]
    fn get_agrees_before_and_after_index_build() {
        // A large struct clone taken *before* the lazy hash index is built must answer lookups the
        // same as the original does after building it.
        let s = struct_with(ABOVE_THRESHOLD, &[("target", 5)]);
        let clone_before = s.clone();
        // First get triggers the lazy table build; the second reads the built table.
        assert_eq!(s.get("target"), Some(&Element::int(5)));
        assert_eq!(s.get("target"), Some(&Element::int(5)));
        // The pre-build clone builds its own index independently and agrees.
        assert_eq!(clone_before.get("target"), Some(&Element::int(5)));
        assert_eq!(clone_before, s);
    }

    #[test]
    fn concurrent_get_agrees() {
        use std::sync::Arc;
        // Racing threads on the first get() of a large struct all race the same OnceLock table
        // build; every thread must observe the correct value regardless of which one initializes.
        let s = Arc::new(struct_with(ABOVE_THRESHOLD, &[("target", 5)]));
        let handles: Vec<_> = (0..8)
            .map(|_| {
                let s = Arc::clone(&s);
                std::thread::spawn(move || s.get("target").cloned())
            })
            .collect();
        for handle in handles {
            assert_eq!(handle.join().unwrap(), Some(Element::int(5)));
        }
    }

    #[test]
    fn struct_is_send_sync() {
        // The lazy OnceLock-backed indexes must not cost `Struct` its `Send`/`Sync`.
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Struct>();
    }

    #[test]
    fn clone_agrees_with_original() {
        // Cloning after the lazy indexes are built must preserve lookup answers.
        let s = struct_with(ABOVE_THRESHOLD, &[("target", 5)]);
        let _ = s.get("target"); // force the hash index to build
        let cloned = s.clone();
        assert_eq!(cloned.get("target"), Some(&Element::int(5)));
        assert_eq!(cloned, s);
    }

    #[test]
    fn for_field_in_struct() {
        // Simple example to exercise Struct's implementation of IntoIterator
        let s = ion_struct! { "foo": 1, "bar": 2, "baz": 3};
        let _fields = s.clone().iter().collect::<Vec<_>>(); // exercises `size_hint`
        let mut baz_value = None;
        for (name, value) in &s {
            if *name == "baz" {
                baz_value = Some(value);
            }
        }
        assert_eq!(baz_value, Some(&Element::int(3)));
    }

    #[test]
    fn for_field_in_owned_struct() {
        // Simple example to exercise Struct's implementation of IntoIterator
        let s = ion_struct! { "foo": 1, "bar": 2, "baz": 3};
        let _fields = s.clone().into_iter().collect::<Vec<_>>(); // exercises `size_hint`
        let mut baz_value = None;
        for (name, value) in s {
            if name == "baz" {
                baz_value = Some(value);
            }
        }
        assert_eq!(baz_value, Some(Element::int(3)));
    }
}
