use crate::raw_symbol_ref::{AsRawSymbolRef, RawSymbolRef};
use crate::result::IonFailure;
use crate::{IonResult, Str, Symbol};
use std::borrow::Borrow;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

/// A reference to a fully resolved symbol. Like `Symbol` (a fully resolved symbol with a
/// static lifetime), a `SymbolRef` may have known or undefined text (i.e. `$0`).
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct SymbolRef<'a> {
    text: Option<&'a str>,
}

impl Debug for SymbolRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.text().unwrap_or("$0"))
    }
}

impl<'a> SymbolRef<'a> {
    /// If this symbol has known text, returns `Some(&str)`. Otherwise, returns `None`.
    pub fn text(&self) -> Option<&'a str> {
        self.text
    }

    /// Constructs a `SymbolRef` with unknown text.
    pub fn with_unknown_text() -> Self {
        SymbolRef { text: None }
    }

    /// Constructs a `SymbolRef` with the specified text.
    pub fn with_text(text: &'a str) -> SymbolRef<'a> {
        SymbolRef { text: Some(text) }
    }

    pub fn to_owned(self) -> Symbol {
        match self.text {
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
        }
    }
}

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
        Self { text: Some(text) }
    }
}

impl<'a> From<&'a Symbol> for SymbolRef<'a> {
    fn from(symbol: &'a Symbol) -> Self {
        Self {
            text: symbol.text(),
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
        self.text()
            .map(SymbolRef::with_text)
            .unwrap_or_else(SymbolRef::with_unknown_text)
    }
}

impl AsSymbolRef for &Symbol {
    fn as_symbol_ref(&self) -> SymbolRef<'_> {
        self.text()
            .map(SymbolRef::with_text)
            .unwrap_or_else(SymbolRef::with_unknown_text)
    }
}

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
