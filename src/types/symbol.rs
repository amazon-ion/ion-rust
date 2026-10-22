use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::IonFailure;
use crate::{IonResult, SymbolRef};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Stores or points to the text of a given [Symbol].
#[derive(Debug, Eq)]
pub(crate) enum SymbolText {
    // This Symbol refers to a string in the active symbol table
    Shared(Arc<str>),
    // This Symbol owns its own text
    // TODO: Turn this into a Box<str>.
    //       Symbols are read-only, so there's no chance we'll add data to the `String`. Using
    //       a `Box<str>` shrinks this value from 24 bytes to 8 bytes.
    Owned(String),
    // This symbol has text that is statically defined (e.g. system symbol table text)
    Static(&'static str),
    // This Symbol is equivalent to SID zero (`$0`)
    Unknown,
    // This Symbol is a placeholder for a symbol ID in a shared symbol table import that could
    // not be resolved. Like `Unknown`, it has no text and is equivalent to `$0` when read
    // (it compares equal to `Unknown`). The typed transcription layer -- the `WriteAsIon`
    // implementations for `Element`, `Value`, `Symbol`, `SymbolRef`, and the lazy value types
    // -- refuses to encode it (whether it appears in value position, as a struct field name,
    // or as an annotation): emitting it as `$0` would silently and irreversibly discard the
    // fact that the symbol had text in the (unavailable) shared table. However, the infallible
    // conversions to `RawSymbolRef` used by the value writer APIs (e.g. `write_symbol`,
    // `field_writer`, `with_annotations`) are an intentional lossy escape hatch: they map the
    // placeholder to `$0` (symbol ID 0).
    UnknownImport,
}

impl SymbolText {
    fn text(&self) -> Option<&str> {
        let text = match self {
            SymbolText::Shared(s) => s.as_ref(),
            SymbolText::Owned(s) => s.as_str(),
            SymbolText::Static(s) => s,
            SymbolText::Unknown | SymbolText::UnknownImport => return None,
        };
        Some(text)
    }
}

impl Hash for SymbolText {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let text = self.text().unwrap_or("");
        text.hash(state)
    }
}

impl Clone for SymbolText {
    fn clone(&self) -> Self {
        match self {
            SymbolText::Owned(text) => SymbolText::Owned(text.to_owned()),
            SymbolText::Shared(text) => SymbolText::Shared(Arc::clone(text)),
            SymbolText::Static(text) => SymbolText::Static(text),
            SymbolText::Unknown => SymbolText::Unknown,
            SymbolText::UnknownImport => SymbolText::UnknownImport,
        }
    }
}

impl PartialEq<Self> for SymbolText {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd<Self> for SymbolText {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymbolText {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.text(), other.text()) {
            // If both Symbols have known text, delegate the comparison to their text.
            (Some(s1), Some(s2)) => s1.cmp(s2),
            // Otherwise, $0 (unknown text) is treated as 'less than' known text
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}

/// The text of a fully resolved field name, annotation, or symbol value. If the symbol has known
/// text (that is: the symbol is not `$0`), it will be stored as either a `String` or a shared
/// reference to text in a symbol table.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Symbol {
    pub(crate) text: SymbolText,
}

impl Symbol {
    pub fn owned<I: Into<String>>(text: I) -> Symbol {
        Symbol {
            text: SymbolText::Owned(text.into()),
        }
    }

    pub fn shared(text: Arc<str>) -> Symbol {
        Symbol {
            text: SymbolText::Shared(text),
        }
    }

    pub const fn static_text(text: &'static str) -> Symbol {
        Symbol {
            text: SymbolText::Static(text),
        }
    }

    pub fn unknown_text() -> Symbol {
        Symbol {
            text: SymbolText::Unknown,
        }
    }

    /// Constructs a `Symbol` that stands in for a symbol ID in a shared symbol table import
    /// that could not be resolved. Like [`Symbol::unknown_text`], the resulting symbol has no
    /// text and is equivalent to `$0` when read, but the typed transcription layer
    /// (`WriteAsIon`/`Element`) refuses to encode it. See [`SymbolText::UnknownImport`] for
    /// details, including the lossy raw-level escape hatch.
    pub(crate) fn unknown_import_placeholder() -> Symbol {
        Symbol {
            text: SymbolText::UnknownImport,
        }
    }

    /// Returns `true` if this symbol is a placeholder for a symbol ID in a shared symbol
    /// table import that could not be resolved. See [`SymbolText::UnknownImport`].
    pub(crate) fn is_unknown_import_placeholder(&self) -> bool {
        matches!(self.text, SymbolText::UnknownImport)
    }

    pub fn text(&self) -> Option<&str> {
        self.text.text()
    }

    pub fn expect_text(&self) -> IonResult<&str> {
        match self.text() {
            Some(text) => Ok(text),
            None => IonResult::decoding_error("symbol has unknown text"),
        }
    }
}

impl IonEq for Symbol {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonDataOrd for Symbol {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

impl IonDataHash for Symbol {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.hash(state)
    }
}

// We cannot use a blanket impl for AsRef<str> as that would prevent us from
// optimizing the From<String> case, a conversion which can be performed
// without cloning.

impl From<&str> for Symbol {
    fn from(text: &str) -> Self {
        Symbol::owned(text)
    }
}

impl From<String> for Symbol {
    fn from(text: String) -> Self {
        Symbol::owned(text)
    }
}

impl From<&String> for Symbol {
    fn from(text: &String) -> Self {
        text.as_str().into()
    }
}

impl<'a> From<&'a Symbol> for Symbol {
    fn from(text: &'a Symbol) -> Self {
        text.clone()
    }
}

impl<'a> From<SymbolRef<'a>> for Symbol {
    fn from(symbol_ref: SymbolRef<'a>) -> Self {
        symbol_ref.to_owned()
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.text() {
            None => write!(f, "$0"),
            Some(text) => write!(f, "'{text}'"),
        }
    }
}

impl<A: AsRef<str>> PartialEq<A> for Symbol {
    fn eq(&self, other: &A) -> bool {
        self.text()
            // If the symbol has known text, compare it to the provide text
            .map(|t| t == other.as_ref())
            // If there's no text, it's definitely not equivalent to the provided text
            .unwrap_or(false)
    }
}

impl PartialEq<Symbol> for String {
    fn eq(&self, other: &Symbol) -> bool {
        other.text().map(|t| t == self.as_str()).unwrap_or(false)
    }
}

impl PartialEq<Symbol> for &str {
    fn eq(&self, other: &Symbol) -> bool {
        other.text().map(|t| &t == self).unwrap_or(false)
    }
}

// Note that if the Symbol has no text, this will return the empty string. This is unfortunate,
// but implementing this trait is necessary to allow `Symbol` to be used as a HashMap key.
// See issue https://github.com/amazon-ion/ion-rust/issues/444 for more information.
impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        // If the
        self.text().unwrap_or("")
    }
}

#[cfg(test)]
mod symbol_tests {
    use super::*;

    /// This is a test to ensure that the static_text function is const.
    const TEST_STATIC_TEXT_IS_CONST: Symbol = Symbol::static_text("foo");

    #[test]
    fn test_static_text_is_const() {
        // Uses the above `const` to prevent it from being considered dead code.
        assert_eq!(TEST_STATIC_TEXT_IS_CONST, "foo")
    }

    #[test]
    fn ordering_and_eq() {
        let mut symbols = vec![
            Symbol::owned("foo"),
            Symbol::shared(Arc::from("bar")),
            Symbol::shared(Arc::from("baz")),
            Symbol::owned("quux"),
        ];
        // Sort the list to demonstrate that our Ord implementation works.
        symbols.as_mut_slice().sort();
        // Equality testing doesn't depend on what kind of Symbol it is, just the text.
        // We can compare the sorted version of the vec above to this one and it will
        // be considered equal.
        let expected = vec![
            Symbol::owned("bar"),
            Symbol::owned("baz"),
            Symbol::owned("foo"),
            Symbol::owned("quux"),
        ];
        assert_eq!(symbols, expected)
    }

    #[test]
    fn partial_eq_str() {
        let symbols = vec![
            Symbol::shared(Arc::from("bar")),
            Symbol::shared(Arc::from("baz")),
            Symbol::owned("foo"),
            Symbol::owned("quux"),
        ];
        // Equality testing for a rust str with symbol
        let expected = vec!["bar", "baz", "foo", "quux"];
        assert_eq!(symbols, expected)
    }

    #[test]
    fn unknown_import_placeholder_is_equivalent_to_unknown_text() {
        // A placeholder for an unresolvable shared symbol table import has no text; for the
        // purposes of equality, ordering, hashing, and Ion data equivalence it is
        // indistinguishable from a genuine `$0`. (Only the writer treats them differently.)
        let placeholder = Symbol::unknown_import_placeholder();
        let unknown = Symbol::unknown_text();
        assert_eq!(placeholder, unknown);
        assert!(placeholder.ion_eq(&unknown));
        assert_eq!(placeholder.cmp(&unknown), Ordering::Equal);
        assert_eq!(placeholder.text(), None);
        assert!(placeholder.is_unknown_import_placeholder());
        assert!(!unknown.is_unknown_import_placeholder());
        // Cloning preserves the placeholder marker.
        assert!(placeholder.clone().is_unknown_import_placeholder());
    }
}
