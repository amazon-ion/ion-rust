use crate::lazy::bytes_ref::BytesRef;
use crate::text::text_formatter::IonValueFormatter;
use crate::Str;
use nom::AsBytes;
use std::borrow::Cow;
use std::fmt::{Display, Formatter};
use std::ops::Deref;

#[derive(Clone, PartialEq, Debug)]
pub struct StrRef<'data> {
    text: Cow<'data, str>,
}

impl<'data> StrRef<'data> {
    pub fn to_owned(&self) -> Str {
        Str::from(self.as_ref())
    }

    pub fn into_owned(self) -> Str {
        Str::from(self)
    }

    pub fn text(&self) -> &str {
        self.as_ref()
    }
}

impl<'data> Deref for StrRef<'data> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.text.as_ref()
    }
}

impl<'data> PartialEq<str> for StrRef<'data> {
    fn eq(&self, other: &str) -> bool {
        self.text() == other
    }
}

impl<'data> PartialEq<&str> for StrRef<'data> {
    fn eq(&self, other: &&str) -> bool {
        self.text() == *other
    }
}

impl<'data> PartialEq<StrRef<'data>> for str {
    fn eq(&self, other: &StrRef<'data>) -> bool {
        self == other.text()
    }
}

impl<'data> Display for StrRef<'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut formatter = IonValueFormatter { output: f };
        formatter
            .format_string(self.text())
            .map_err(|_| std::fmt::Error)
    }
}

impl<'a> From<&'a str> for StrRef<'a> {
    fn from(value: &'a str) -> Self {
        StrRef {
            text: Cow::from(value),
        }
    }
}

impl<'a> From<String> for StrRef<'a> {
    fn from(value: String) -> Self {
        StrRef {
            text: Cow::from(value),
        }
    }
}

impl<'data> From<StrRef<'data>> for Str {
    fn from(str_ref: StrRef<'data>) -> Self {
        let text: String = str_ref.text.into_owned();
        Str::from(text)
    }
}

impl<'data> From<StrRef<'data>> for BytesRef<'data> {
    fn from(value: StrRef<'data>) -> Self {
        match value.text {
            Cow::Borrowed(text) => text.as_bytes().into(),
            Cow::Owned(text) => Vec::from(text).into(),
        }
    }
}
