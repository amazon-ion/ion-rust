use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

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

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.text.as_ref())
    }
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

impl<A: AsRef<str>> PartialOrd<A> for Symbol {
    fn partial_cmp(&self, other: &A) -> Option<Ordering> {
        self.text.as_ref().partial_cmp(other.as_ref())
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> Ordering {
        self.text.as_ref().cmp(other.as_ref())
    }
}

#[cfg(test)]
mod symbol_tests {
    use super::*;

    #[test]
    fn ordering_and_eq() {
        let mut symbols = vec![
            Symbol::owned("foo".to_owned()),
            Symbol::shared(Rc::from("bar")),
            Symbol::shared(Rc::from("baz")),
            Symbol::owned("quux".to_owned()),
        ];
        // Sort the list to demonstrate that our Ord implementation works.
        symbols.as_mut_slice().sort();
        // Equality testing doesn't depend on what kind of Symbol it is, just the text.
        // We can compare the sorted version of the vec above to this one and it will
        // be considered equal.
        let expected = vec![
            Symbol::owned("bar".to_owned()),
            Symbol::owned("baz".to_owned()),
            Symbol::owned("foo".to_owned()),
            Symbol::owned("quux".to_owned()),
        ];
        assert_eq!(symbols, expected)
    }
}
