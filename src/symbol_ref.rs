use crate::Symbol;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

/// A reference to a fully resolved symbol. Like `Symbol` (a fully resolved symbol with a
/// static lifetime), a `SymbolRef` may have known or undefined text.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct SymbolRef<'a> {
    text: Option<&'a str>,
}

impl<'a> SymbolRef<'a> {
    /// If this symbol has known text, returns `Some(&str)`. Otherwise, returns `None`.
    pub fn text(&self) -> Option<&str> {
        self.text
    }

    /// Constructs a `SymbolRef` with unknown text.
    pub fn with_unknown_text() -> Self {
        SymbolRef { text: None }
    }

    /// Constructs a `SymbolRef` with the specified text.
    pub fn with_text(text: &str) -> SymbolRef {
        SymbolRef { text: Some(text) }
    }
}

/// Allows a `SymbolRef` to be constructed from a source value. This enables non-symbol types to be
/// viewed as a symbol with little to no runtime overhead.
pub trait AsSymbolRef {
    fn as_symbol_ref(&self) -> SymbolRef;
}

// All text types can be viewed as a `SymbolRef`.
impl<'a, A: AsRef<str> + 'a> AsSymbolRef for A {
    fn as_symbol_ref(&self) -> SymbolRef {
        SymbolRef {
            text: Some(self.as_ref()),
        }
    }
}

impl<'a> Hash for SymbolRef<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.text {
            None => 0.hash(state),
            Some(text) => text.hash(state),
        }
    }
}

impl<'a> From<&'a str> for SymbolRef<'a> {
    fn from(text: &'a str) -> Self {
        Self { text: Some(text) }
    }
}

// Note that this method panics if the SymbolRef has unknown text! This is unfortunate but is required
// in order to allow a HashMap<SymbolRef, _> to do lookups with a &str instead of a &SymbolRef
impl<'a> Borrow<str> for SymbolRef<'a> {
    fn borrow(&self) -> &str {
        self.text()
            .expect("cannot borrow a &str from a SymbolRef with unknown text")
    }
}

// Owned `Symbol` values can be viewed as a `SymbolRef`. Due to lifetime conflicts in the
// trait definitions, this cannot be achieved with `AsRef` or `Borrow`.
impl AsSymbolRef for Symbol {
    fn as_symbol_ref(&self) -> SymbolRef {
        self.text()
            .map(SymbolRef::with_text)
            .unwrap_or_else(SymbolRef::with_unknown_text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let symbol_ref: SymbolRef = "foo".as_symbol_ref();
        assert_eq!(Some("foo"), symbol_ref.text());
    }

    #[test]
    fn symbol_as_symbol_ref() {
        let symbol = Symbol::owned("foo");
        let symbol_ref: SymbolRef = symbol.as_symbol_ref();
        assert_eq!(Some("foo"), symbol_ref.text());
    }

    #[test]
    fn symbol_with_unknown_text_as_symbol_ref() {
        let symbol = Symbol::unknown_text();
        let symbol_ref: SymbolRef = symbol.as_symbol_ref();
        assert_eq!(None, symbol_ref.text());
    }
}
