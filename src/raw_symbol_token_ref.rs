use crate::raw_symbol_token::RawSymbolToken;
use crate::{Symbol, SymbolId};
use std::borrow::Cow;

/// Like RawSymbolToken, but the Text variant holds a borrowed reference instead of a String.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawSymbolTokenRef<'a> {
    SymbolId(SymbolId),
    Text(Cow<'a, str>),
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
