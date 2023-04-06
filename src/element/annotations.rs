use crate::element::iterators::SymbolsIterator;
use crate::Symbol;

/// An ordered sequence of symbols that convey additional, application-specific information about
/// their associated Ion value.
/// ```
/// use ion_rs::element::Annotations;
/// let annotations: Annotations = ["foo", "bar", "baz"].into();
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
    // else (`thinvec`?) in the future.
    pub(crate) fn new(symbols: Vec<Symbol>) -> Self {
        Annotations { symbols }
    }

    /// Returns the number of annotations in this sequence.
    /// ```
    /// use ion_rs::element::Annotations;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into();
    /// assert_eq!(annotations.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Returns `true` if this sequence contains zero annotations. Otherwise, returns `false`.
    /// ```
    /// use ion_rs::element::Annotations;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into();
    /// assert!(!annotations.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.symbols.len() == 0
    }

    /// Returns `true` if any symbol in this annotations sequence is equal to the provided text.
    /// Otherwise, returns `false`.
    /// ```
    /// use ion_rs::element::Annotations;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into();
    /// assert!(annotations.contains("foo"));
    /// assert!(annotations.contains("bar"));
    /// assert!(annotations.contains("baz"));
    ///
    /// assert!(!annotations.contains("quux"));
    /// assert!(!annotations.contains("quuz"));
    /// ```
    pub fn contains<S: AsRef<str>>(&self, query: S) -> bool {
        let query: &str = query.as_ref();
        self.into_iter().any(|symbol| symbol.text() == Some(query))
    }

    /// Determines whether this annotations sequence begins with the specified sequence of text
    /// values.
    /// ```
    /// use ion_rs::element::Annotations;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into();
    /// assert!(annotations.starts_with(["foo"]));
    /// assert!(annotations.starts_with(["foo", "bar"]));
    /// assert!(annotations.starts_with(["foo", "bar", "baz"]));
    ///
    /// assert!(!annotations.starts_with(["quux"]));
    /// assert!(!annotations.starts_with(["foo", "bar", "baz", "quux"]));
    /// ```
    pub fn starts_with<S: AsRef<str>, I: IntoIterator<Item = S>>(&self, sequence: I) -> bool {
        let mut annotations = self.into_iter();
        for query_annotation in sequence.into_iter() {
            let query_str: &str = query_annotation.as_ref();
            if let Some(actual_annotation) = annotations.next() {
                if Some(query_str) == actual_annotation.text() {
                    continue;
                }
            }
            return false;
        }

        true
    }
}

// NB: This blanket implementation covers a LOT of type combinations:
//
//     A {slice, array, Vec...} of {&str, String, Symbol, ...}
//
// Unfortunately, it also prevents us from having special cases for Vec<Symbol>
// (which would otherwise be able to be converted directly to an `Annotations` without cloning)
// or for a single value that could be turned into a `Symbol`. If we need that ability in the
// future, consider defining a custom `IntoAnnotations` trait.
impl<S: Into<Symbol>, I: IntoIterator<Item = S>> From<I> for Annotations {
    fn from(annotations: I) -> Self {
        let symbols: Vec<Symbol> = annotations.into_iter().map(|a| a.into()).collect();
        Annotations::new(symbols)
    }
}

impl<'a> IntoIterator for &'a Annotations {
    type Item = &'a Symbol;
    type IntoIter = SymbolsIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        SymbolsIterator::new(self.symbols.as_slice())
    }
}
