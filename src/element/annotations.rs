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

    /// Returns a [SymbolsIterator] that yields each of the [Symbol]s in this annotations sequence
    /// in order.
    pub fn iter(&self) -> SymbolsIterator {
        self.into_iter()
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
    /// use ion_rs::element::Annotations;
    /// use ion_rs::Symbol;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into();
    /// assert_eq!(annotations.first(), Some("foo"));
    ///
    /// let empty_sequence: Vec<&str> = vec![];
    /// let annotations: Annotations = empty_sequence.into();
    /// assert_eq!(annotations.first(), None);
    ///
    /// let annotations: Annotations = [Symbol::unknown_text()].into();
    /// assert_eq!(annotations.first(), None)
    /// ```
    pub fn first(&self) -> Option<&str> {
        self.iter().next().and_then(|a| a.text())
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
