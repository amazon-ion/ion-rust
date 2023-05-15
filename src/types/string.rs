use crate::ion_data::{IonEq, IonOrd};
use crate::text::text_formatter::IonValueFormatter;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

/// An owned, immutable in-memory representation of an Ion `string`.
///
/// ```
/// use ion_rs::Str;
/// let s: Str = "hello!".into();
/// assert_eq!(s, "hello!");
/// ```
#[derive(Eq, Ord, PartialOrd, Debug, Clone, Hash)]
pub struct Str {
    // For the time being, the `Str` type is an opaque wrapper around the standard Rust `String`
    // type. Having this opaque wrapper means that we can swap out its implementation without a
    // breaking change, allowing us to offer string interning, stack-allocated small strings, or
    // other optimizations as needed.
    text: String,
}

impl Str {
    /// Returns the number of UTF-8 encoded bytes in this string.
    ///
    /// ```
    /// use ion_rs::Str;
    /// let s: Str = "hello!".into();
    /// assert_eq!(s.len(), 6);
    /// // Note that the length returned is a number of UTF-8 bytes, not codepoints or graphemes.
    /// let s: Str = "🚀🚀🚀".into();
    /// assert_eq!(s.len(), 12);
    /// ```
    pub fn len(&self) -> usize {
        self.text.len()
    }

    /// Returns `true` if this is the empty string (`""`); otherwise, returns `false`.
    ///
    /// ```
    /// use ion_rs::Str;
    /// let s: Str = "".into();
    /// assert!(s.is_empty());
    /// let s: Str = "hello!".into();
    /// assert!(!s.is_empty());
    /// ```
    // This method is largely here because clippy complains if you provide a `len()` method but not
    // an accompanying `is_empty()` method.
    pub fn is_empty(&self) -> bool {
        self.text.is_empty()
    }

    /// Returns a `&str` representation of this string's text.
    ///
    /// ```
    /// use ion_rs::Str;
    /// let s: Str = "hello, world!".into();
    /// assert!(s.text().contains("world"));
    /// assert!(s.text().is_ascii());
    /// ```
    pub fn text(&self) -> &str {
        self.text.as_str()
    }
}

impl Display for Str {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut formatter = IonValueFormatter { output: f };
        formatter
            .format_string(self.as_ref())
            .map_err(|_| std::fmt::Error)
    }
}

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        Str {
            text: value.to_string(),
        }
    }
}

impl From<String> for Str {
    fn from(value: String) -> Self {
        Str { text: value }
    }
}

impl AsRef<str> for Str {
    fn as_ref(&self) -> &str {
        self.text()
    }
}

impl<S> PartialEq<S> for Str
where
    S: AsRef<str>,
{
    fn eq(&self, other: &S) -> bool {
        let other_text: &str = other.as_ref();
        self.text() == other_text
    }
}

impl PartialEq<Str> for &str {
    fn eq(&self, other: &Str) -> bool {
        self.eq(&other.text())
    }
}

impl PartialEq<Str> for String {
    fn eq(&self, other: &Str) -> bool {
        let self_text: &str = self.as_str();
        self_text.eq(other.text())
    }
}

impl IonEq for Str {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonOrd for Str {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}
