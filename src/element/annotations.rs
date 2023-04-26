use crate::element::iterators::{AnnotationsIntoIter, SymbolsIterator};
use crate::ion_data::IonOrd;
use crate::Symbol;
use std::cmp::Ordering;

/// An ordered sequence of symbols that convey additional, application-specific information about
/// their associated Ion value.
///
/// The [`IntoAnnotations`] trait is a convenient way to convert collections of symbol convertible
/// things (including [`&str`] and [`String`]) into this sequence.
///
/// ```
/// use ion_rs::element::{Annotations, IntoAnnotations};
/// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
/// for annotation in &annotations {
///     assert_eq!(annotation.text().map(|s| s.len()), Some(3));
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotations {
    symbols: Vec<Symbol>,
}

impl Annotations {
    // This is limited to crate visibility to allow us to change `Vec<_>` to something
    // else (`thinvec`?) in the future. Users are unlikely to need to construct an `Annotations`
    // themselves, but can use a `From` impl if necessary.
    pub(crate) fn new(symbols: Vec<Symbol>) -> Self {
        Annotations { symbols }
    }

    /// Constructs an Annotations object representing an empty symbol sequence
    pub fn empty() -> Self {
        Annotations {
            symbols: Vec::new(),
        }
    }

    /// Returns an [`Iterator`] that yields each of the [`Symbol`]s in this annotations
    /// sequence in order.
    pub fn iter(&self) -> SymbolsIterator {
        SymbolsIterator::new(self.symbols.as_slice())
    }

    /// Returns the number of annotations in this sequence.
    /// ```
    /// use ion_rs::element::{Annotations, IntoAnnotations};
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert_eq!(annotations.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Returns `true` if this sequence contains zero annotations. Otherwise, returns `false`.
    /// ```
    /// use ion_rs::element::{Annotations, IntoAnnotations};
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert!(!annotations.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.symbols.len() == 0
    }

    /// Returns `true` if any symbol in this annotations sequence is equal to the provided text.
    /// Otherwise, returns `false`.
    /// ```
    /// use ion_rs::element::{Annotations, IntoAnnotations};
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert!(annotations.contains("foo"));
    /// assert!(annotations.contains("bar"));
    /// assert!(annotations.contains("baz"));
    ///
    /// assert!(!annotations.contains("quux"));
    /// assert!(!annotations.contains("quuz"));
    /// ```
    pub fn contains<S: AsRef<str>>(&self, query: S) -> bool {
        let query: &str = query.as_ref();
        self.iter().any(|symbol| symbol.text() == Some(query))
    }

    /// Returns the text of the first annotation in this sequence.
    ///
    /// If the sequence is empty, returns `None`.
    /// If the first annotation in the sequence is `$0` (symbol ID 0), returns `None`.
    /// Otherwise, returns a `Some(&str)` containing the text.
    ///
    /// To view the first annotation as a [Symbol] rather than a `&str`, use
    /// `annotations.iter().next()`.
    /// ```
    /// use ion_rs::element::{Annotations, IntoAnnotations};
    /// use ion_rs::Symbol;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert_eq!(annotations.first(), Some("foo"));
    ///
    /// let empty_sequence: Vec<&str> = vec![];
    /// let annotations: Annotations = empty_sequence.into_annotations();
    /// assert_eq!(annotations.first(), None);
    ///
    /// let annotations: Annotations = [Symbol::unknown_text()].into_annotations();
    /// assert_eq!(annotations.first(), None)
    /// ```
    pub fn first(&self) -> Option<&str> {
        self.iter().next().and_then(|a| a.text())
    }
}

impl From<Vec<Symbol>> for Annotations {
    fn from(value: Vec<Symbol>) -> Self {
        Annotations::new(value)
    }
}

impl<S: Into<Symbol>> FromIterator<S> for Annotations {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        iter.into_annotations()
    }
}

impl<'a> IntoIterator for &'a Annotations {
    type Item = &'a Symbol;
    type IntoIter = SymbolsIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        SymbolsIterator::new(self.symbols.as_slice())
    }
}

impl IntoIterator for Annotations {
    type Item = Symbol;
    type IntoIter = AnnotationsIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        AnnotationsIntoIter::new(self.symbols.into_iter())
    }
}

impl IonOrd for Annotations {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.symbols.ion_cmp(&other.symbols)
    }
}

/// Defines conversion into [`Annotations`].
///
/// This trait allows us to have a blanket implementations that can cover many type combinations
/// without conflicting in ways that blanket [`From`] implementations can.
///
/// With this we can convert for some `T` that is string-like (`&str`, `String`, `Symbol`, etc...)
/// we can convert from collections of that type like `[T]`, `[T; n]`, `Vec<T>`, and
/// iterators of `T` generically.
pub trait IntoAnnotations {
    fn into_annotations(self) -> Annotations;
}

impl<S, I> IntoAnnotations for I
where
    S: Into<Symbol>,
    I: IntoIterator<Item = S>,
{
    fn into_annotations(self) -> Annotations {
        let symbols: Vec<Symbol> = self.into_iter().map(|a| a.into()).collect();
        Annotations::new(symbols)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_into_iter() {
        let expected = vec!["a", "b", "c"].into_annotations();
        let collect: Annotations = expected.clone().into_iter().collect();
        assert_eq!(expected, collect);
    }

    #[test]
    fn test_from_vec() {
        let expected = vec!["d", "e", "f"].into_annotations();
        let symbols: Vec<_> = expected.clone().into_iter().collect();
        let from: Annotations = symbols.into();
        assert_eq!(expected, from);
    }
}
