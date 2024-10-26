use crate::lazy::expanded::EncodingContextRef;
use crate::result::IonFailure;
use crate::{IonError, IonResult, Symbol, SymbolId, SymbolRef};

/// A raw symbol token found in the input stream.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RawSymbolRef<'a> {
    // Ion 1.0 has a consolidated symbol table with both user and system symbols.
    // Ion 1.1 has a user table (that may optionally contain system symbols) and a system table
    // (which is always available and only contains system symbols).
    //
    // In Ion 1.0, all symbol ID tokens are represented using the `SymbolId` variant.
    // In Ion 1.1, all user symbol ID tokens are represented using the `SymbolId` variant,
    // while system symbol ID tokens are resolved to text in the system table and returned
    // as a `Text` variant.
    //
    // This was done to minimize the changes needed to add a second address space.
    // If there is call for it in the future, we could add a `SystemSymbolId` variant
    // and modify Ion 1.0 to return that for SIDs < $10.
    SymbolId(SymbolId),
    Text(&'a str),
}

impl<'a> RawSymbolRef<'a> {
    /// Returns `true` if this token matches either the specified symbol ID or text value.
    /// This is useful for comparing tokens that represent system symbol values of an unknown
    /// encoding.
    pub fn matches_sid_or_text(&self, symbol_id: SymbolId, symbol_text: &str) -> bool {
        match self {
            RawSymbolRef::SymbolId(sid) => symbol_id == *sid,
            RawSymbolRef::Text(text) => symbol_text == *text,
        }
    }

    pub fn resolve(self, context: EncodingContextRef<'a>) -> IonResult<SymbolRef<'a>> {
        let symbol = match self {
            RawSymbolRef::SymbolId(sid) => context
                .symbol_table()
                .symbol_for(sid)
                .ok_or_else(
                    #[inline(never)]
                    || {
                        IonError::decoding_error(format!(
                            "found a symbol ID (${}) that was not in the symbol table",
                            sid
                        ))
                    },
                )?
                .into(),
            RawSymbolRef::Text(text) => text.into(),
        };
        Ok(symbol)
    }
}

/// Implemented by types that can be viewed as a [RawSymbolRef] without allocations.
pub trait AsRawSymbolRef {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolRef;
}

impl<'a> AsRawSymbolRef for RawSymbolRef<'a> {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolRef {
        *self
    }
}

impl AsRawSymbolRef for SymbolId {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolRef {
        RawSymbolRef::SymbolId(*self)
    }
}

impl AsRawSymbolRef for &str {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolRef {
        RawSymbolRef::Text(self)
    }
}

impl AsRawSymbolRef for Symbol {
    fn as_raw_symbol_token_ref(&self) -> RawSymbolRef {
        match self.text() {
            Some(text) => RawSymbolRef::Text(text),
            None => RawSymbolRef::SymbolId(0),
        }
    }
}

impl<T> AsRawSymbolRef for &T
where
    T: AsRawSymbolRef,
{
    fn as_raw_symbol_token_ref(&self) -> RawSymbolRef {
        (*self).as_raw_symbol_token_ref()
    }
}

impl<'a, 'b> From<&'a RawSymbolRef<'b>> for RawSymbolRef<'a> {
    fn from(value: &'a RawSymbolRef<'b>) -> Self {
        *value
    }
}

impl<'a> From<&'a str> for RawSymbolRef<'a> {
    fn from(value: &'a str) -> Self {
        RawSymbolRef::Text(value)
    }
}

impl<'a> From<&'a &str> for RawSymbolRef<'a> {
    fn from(value: &'a &str) -> Self {
        RawSymbolRef::Text(value)
    }
}

impl<'a> From<SymbolId> for RawSymbolRef<'a> {
    fn from(value: SymbolId) -> Self {
        RawSymbolRef::SymbolId(value)
    }
}

impl<'a> From<&'a SymbolId> for RawSymbolRef<'a> {
    fn from(value: &'a SymbolId) -> Self {
        RawSymbolRef::SymbolId(*value)
    }
}

impl<'a> From<SymbolRef<'a>> for RawSymbolRef<'a> {
    fn from(value: SymbolRef<'a>) -> Self {
        match value.text() {
            None => RawSymbolRef::SymbolId(0),
            Some(text) => RawSymbolRef::Text(text),
        }
    }
}

impl<'a> From<&'a Symbol> for RawSymbolRef<'a> {
    fn from(value: &'a Symbol) -> Self {
        value.as_raw_symbol_token_ref()
    }
}
