use crate::raw_symbol_ref::{AsRawSymbolRef, RawSymbolRef};
use crate::result::IonFailure;
use crate::{IonResult, Str, Symbol};
use std::borrow::Borrow;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

/// A reference to a fully resolved symbol. Like `Symbol` (a fully resolved symbol with a
/// static lifetime), a `SymbolRef` may have known or undefined text (i.e. `$0`).
#[derive(Eq, Clone, Copy)]
pub struct SymbolRef<'a> {
    text: Option<&'a str>,
    // `true` if this symbol is a placeholder for a symbol ID in a shared symbol table import
    // that could not be resolved. See `SymbolText::UnknownImport`. This flag does not
    // participate in equality, ordering, or hashing: a placeholder is equivalent to `$0`
    // everywhere except during transcription (the `WriteAsIon` implementations used when
    // writing an `Element`, `Value`, `LazyValue`, `SymbolRef`, or `Symbol`), which refuses
    // to encode it. Conversions to `RawSymbolRef` (used by the value writer APIs for symbol
    // values, struct field names, and annotations) are infallible and intentionally lossy:
    // they discard this flag and map the placeholder to `$0` (symbol ID 0).
    //
    // TODO: absorb into the symbol table representation (tracked SID ranges of unresolved
    //       imports) when symbol tables move to a slab/Vec<Arc<SymbolTable>> design; that
    //       also enables import-location preservation for round-trip.
    is_unknown_import_placeholder: bool,
}

// `is_unknown_import_placeholder` is intentionally not part of equality.
impl PartialEq<Self> for SymbolRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.text == other.text
    }
}

// `is_unknown_import_placeholder` is intentionally not part of ordering.
impl PartialOrd<Self> for SymbolRef<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// `is_unknown_import_placeholder` is intentionally not part of ordering.
impl Ord for SymbolRef<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.text.cmp(&other.text)
    }
}

impl Debug for SymbolRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.text() {
            Some(text) => write!(f, "{text}"),
            // Debug output (unlike `Display`, which renders Ion text and must remain `$0`)
            // distinguishes a placeholder for an unresolvable shared symbol table import
            // from a genuine `$0`.
            None if self.is_unknown_import_placeholder => write!(f, "$0 (unresolved import)"),
            None => write!(f, "$0"),
        }
    }
}

impl<'a> SymbolRef<'a> {
    /// If this symbol has known text, returns `Some(&str)`. Otherwise, returns `None`.
    pub fn text(&self) -> Option<&'a str> {
        self.text
    }

    /// Constructs a `SymbolRef` with unknown text.
    pub fn with_unknown_text() -> Self {
        SymbolRef {
            text: None,
            is_unknown_import_placeholder: false,
        }
    }

    /// Constructs a `SymbolRef` with the specified text.
    pub fn with_text(text: &'a str) -> SymbolRef<'a> {
        SymbolRef {
            text: Some(text),
            is_unknown_import_placeholder: false,
        }
    }

    /// Returns `true` if this symbol is a placeholder for a symbol ID in a shared symbol
    /// table import that could not be resolved. See `SymbolText::UnknownImport`.
    pub(crate) fn is_unknown_import_placeholder(&self) -> bool {
        self.is_unknown_import_placeholder
    }

    pub fn to_owned(self) -> Symbol {
        match self.text {
            None if self.is_unknown_import_placeholder => Symbol::unknown_import_placeholder(),
            None => Symbol::unknown_text(),
            Some(text) => Symbol::owned(Str::from(text)),
        }
    }

    pub fn expect_text(&self) -> IonResult<&'a str> {
        match self.text() {
            Some(text) => Ok(text),
            None => IonResult::decoding_error("symbol has unknown text"),
        }
    }
}

impl<A> PartialEq<A> for SymbolRef<'_>
where
    A: AsSymbolRef,
{
    fn eq(&self, other: &A) -> bool {
        let other_symbol_ref = other.as_symbol_ref();
        self == &other_symbol_ref
    }
}

/// Allows a `SymbolRef` to be constructed from a source value. This enables non-symbol types to be
/// viewed as a symbol with little to no runtime overhead.
pub trait AsSymbolRef {
    fn as_symbol_ref(&self) -> SymbolRef<'_>;
}

// All text types can be viewed as a `SymbolRef`.
impl<A: AsRef<str>> AsSymbolRef for A {
    fn as_symbol_ref(&self) -> SymbolRef<'_> {
        SymbolRef {
            text: Some(self.as_ref()),
            is_unknown_import_placeholder: false,
        }
    }
}

// `is_unknown_import_placeholder` is intentionally not part of hashing.
impl Hash for SymbolRef<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.text() {
            None => 0.hash(state),
            Some(text) => text.hash(state),
        }
    }
}

impl<'a> From<&'a str> for SymbolRef<'a> {
    fn from(text: &'a str) -> Self {
        Self {
            text: Some(text),
            is_unknown_import_placeholder: false,
        }
    }
}

impl<'a> From<&'a Symbol> for SymbolRef<'a> {
    fn from(symbol: &'a Symbol) -> Self {
        Self {
            text: symbol.text(),
            is_unknown_import_placeholder: symbol.is_unknown_import_placeholder(),
        }
    }
}

// Note that this method panics if the SymbolRef has unknown text! This is unfortunate but is required
// in order to allow a HashMap<SymbolRef, _> to do lookups with a &str instead of a &SymbolRef
impl Borrow<str> for SymbolRef<'_> {
    fn borrow(&self) -> &str {
        self.text()
            .expect("cannot borrow a &str from a SymbolRef with unknown text")
    }
}

// Owned `Symbol` values can be viewed as a `SymbolRef`. Due to lifetime conflicts in the
// trait definitions, this cannot be achieved with `AsRef` or `Borrow`.
impl AsSymbolRef for Symbol {
    fn as_symbol_ref(&self) -> SymbolRef<'_> {
        SymbolRef::from(self)
    }
}

impl AsSymbolRef for &Symbol {
    fn as_symbol_ref(&self) -> SymbolRef<'_> {
        SymbolRef::from(*self)
    }
}

// This conversion is infallible and therefore intentionally lossy: a `SymbolRef` that is a
// placeholder for a symbol ID in an unresolvable shared symbol table import (see
// `SymbolText::UnknownImport`) is mapped to `$0` (symbol ID 0), discarding the placeholder
// flag. Raw-level writers legitimately emit `$0`; only the typed transcription layer
// (`WriteAsIon`/`Element`) refuses to encode placeholders.
//
// Reachability on the default-features API: the writer APIs that consume this conversion
// (`Writer`, `ValueWriter`, `StructWriter`, etc.) are only public with the
// `experimental-reader-writer` feature, and the default-features encoding entry points
// (`Element::encode_as`/`encode_to`) go through `WriteAsIon` and refuse placeholders.
// However, the `Display` impls for `Element`/`Value` (Ion text rendering) also use this
// conversion and are available on default features; they render placeholders as `$0`.
impl AsRawSymbolRef for SymbolRef<'_> {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_> {
        match &self.text {
            None => RawSymbolRef::SymbolId(0),
            Some(text) => RawSymbolRef::Text(text),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_ref_size_regression() {
        // A `SymbolRef` is an `Option<&str>` (16 bytes, thanks to the niche optimization)
        // plus the one-byte `is_unknown_import_placeholder` flag, padded to the pointer
        // alignment of `&str`: 24 bytes total. Before the flag was added it was 16 bytes.
        // `ValueRef` (see the size regression test in `value_ref.rs`) absorbed the growth
        // because its size is dominated by larger variants. If this assertion fails, the
        // type has changed size; check whether `ValueRef` (and other containing types)
        // grew with it.
        assert_eq!(std::mem::size_of::<SymbolRef<'_>>(), 24);
    }

    #[test]
    fn symbol_ref_with_text() {
        let symbol_ref = SymbolRef::with_text("foo");
        assert_eq!(Some("foo"), symbol_ref.text());
    }

    #[test]
    fn symbol_ref_with_unknown_text() {
        let symbol_ref = SymbolRef::with_unknown_text();
        assert_eq!(None, symbol_ref.text());
    }

    #[test]
    fn str_as_symbol_ref() {
        let symbol_ref: SymbolRef<'_> = "foo".as_symbol_ref();
        assert_eq!(Some("foo"), symbol_ref.text());
    }

    #[test]
    fn symbol_as_symbol_ref() {
        let symbol = Symbol::owned("foo");
        let symbol_ref: SymbolRef<'_> = symbol.as_symbol_ref();
        assert_eq!(Some("foo"), symbol_ref.text());
    }

    #[test]
    fn symbol_with_unknown_text_as_symbol_ref() {
        let symbol = Symbol::unknown_text();
        let symbol_ref: SymbolRef<'_> = symbol.as_symbol_ref();
        assert_eq!(None, symbol_ref.text());
    }
}
