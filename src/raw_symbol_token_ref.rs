use crate::raw_symbol_token::RawSymbolToken;
use crate::{Symbol, SymbolId};
use std::borrow::Cow;

/// Like RawSymbolToken, but the Text variant holds a borrowed reference instead of a String.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawSymbolTokenRef<'a> {
    SymbolId(SymbolId),
    Text(Cow<'a, str>),
}

impl<'a> RawSymbolTokenRef<'a> {
    /// Returns `true` if this token matches either the specified symbol ID or text value.
    /// This is useful for comparing tokens that represent system symbol values of an unknown
    /// encoding.
    pub fn matches_sid_or_text(&self, symbol_id: SymbolId, symbol_text: &str) -> bool {
        match self {
            RawSymbolTokenRef::SymbolId(sid) => symbol_id == *sid,
            RawSymbolTokenRef::Text(text) => symbol_text == text,
        }
    }
}

/// Implemented by types that can be viewed as a [RawSymbolTokenRef] without allocations.
pub trait AsRawSymbolTokenRef {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef;
}

impl<'a> AsRawSymbolTokenRef for RawSymbolTokenRef<'a> {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        self.clone()
    }
}

impl AsRawSymbolTokenRef for SymbolId {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        RawSymbolTokenRef::SymbolId(*self)
    }
}

impl AsRawSymbolTokenRef for String {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        RawSymbolTokenRef::Text(Cow::from(self.as_str()))
    }
}

impl AsRawSymbolTokenRef for &str {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        RawSymbolTokenRef::Text(Cow::from(*self))
    }
}

impl AsRawSymbolTokenRef for Symbol {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        match self.text() {
            Some(text) => RawSymbolTokenRef::Text(Cow::from(text)),
            None => RawSymbolTokenRef::SymbolId(0),
        }
    }
}

impl<T> AsRawSymbolTokenRef for &T
where
    T: AsRawSymbolTokenRef,
{
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        (*self).as_raw_symbol_token_ref()
    }
}

impl AsRawSymbolTokenRef for RawSymbolToken {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolTokenRef {
        match self {
            RawSymbolToken::SymbolId(sid) => RawSymbolTokenRef::SymbolId(*sid),
            RawSymbolToken::Text(text) => RawSymbolTokenRef::Text(Cow::from(text.as_str())),
        }
    }
}

impl<'a> From<&'a RawSymbolToken> for RawSymbolTokenRef<'a> {
    fn from(value: &'a RawSymbolToken) -> Self {
        value.as_raw_symbol_token_ref()
    }
}

impl<'a, 'b> From<&'a RawSymbolTokenRef<'b>> for RawSymbolTokenRef<'b> {
    fn from(value: &'a RawSymbolTokenRef<'b>) -> Self {
        value.clone()
    }
}

impl<'a> From<&'a str> for RawSymbolTokenRef<'a> {
    fn from(value: &'a str) -> Self {
        RawSymbolTokenRef::Text(Cow::Borrowed(value))
    }
}

impl<'a> From<SymbolId> for RawSymbolTokenRef<'a> {
    fn from(value: SymbolId) -> Self {
        RawSymbolTokenRef::SymbolId(value)
    }
}

impl<'a> From<&'a Symbol> for RawSymbolTokenRef<'a> {
    fn from(value: &'a Symbol) -> Self {
        value.as_raw_symbol_token_ref()
    }
}
