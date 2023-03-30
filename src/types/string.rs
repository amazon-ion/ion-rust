use crate::text::text_formatter::IonValueFormatter;
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
    // For the time being, the `Text` type is an opaque wrapper around the standard Rust `String`
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
        self.text.as_ref()
    }
}

impl<S> PartialEq<S> for Str
where
    S: AsRef<str>,
{
    fn eq(&self, other: &S) -> bool {
        let this_text: &str = self.as_ref();
        let other_text: &str = other.as_ref();
        this_text == other_text
    }
}

impl PartialEq<Str> for &str {
    fn eq(&self, other: &Str) -> bool {
        self.eq(&other.as_ref())
    }
}

impl PartialEq<Str> for String {
    fn eq(&self, other: &Str) -> bool {
        let self_text: &str = self.as_str();
        self_text.eq(other.as_ref())
    }
}
