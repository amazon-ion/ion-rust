use crate::lazy::bytes_ref::BytesRef;
use crate::text::text_formatter::FmtValueFormatter;
use crate::{RawSymbolRef, Str};
use std::fmt::{Display, Formatter};
use std::ops::Deref;

/// A reference to an immutable in-memory representation of an Ion string. To get an owned [`Str`]
/// instead, see [`StrRef::to_owned`].
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct StrRef<'data> {
    text: &'data str,
}

impl<'data> StrRef<'data> {
    pub fn to_owned(self) -> Str {
        Str::from(self.text)
    }

    pub fn into_owned(self) -> Str {
        Str::from(self)
    }

    pub fn text(&self) -> &'data str {
        self.text
    }
}

impl Deref for StrRef<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.text
    }
}

impl PartialEq<str> for StrRef<'_> {
    fn eq(&self, other: &str) -> bool {
        self.text() == other
    }
}

impl PartialEq<&str> for StrRef<'_> {
    fn eq(&self, other: &&str) -> bool {
        self.text() == *other
    }
}

impl<'data> PartialEq<StrRef<'data>> for str {
    fn eq(&self, other: &StrRef<'data>) -> bool {
        self == other.text()
    }
}

impl Display for StrRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut formatter = FmtValueFormatter { output: f };
        formatter
            .format_string(self.text())
            .map_err(|_| std::fmt::Error)
    }
}

impl<'a> From<&'a str> for StrRef<'a> {
    fn from(value: &'a str) -> Self {
        StrRef { text: value }
    }
}

impl<'data> From<StrRef<'data>> for Str {
    fn from(str_ref: StrRef<'data>) -> Self {
        let text: String = str_ref.text.to_owned();
        Str::from(text)
    }
}

impl<'data> From<StrRef<'data>> for BytesRef<'data> {
    fn from(value: StrRef<'data>) -> Self {
        value.text.into()
    }
}

impl<'data> From<StrRef<'data>> for RawSymbolRef<'data> {
    fn from(value: StrRef<'data>) -> Self {
        RawSymbolRef::Text(value.text)
    }
}
