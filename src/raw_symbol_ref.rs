use crate::lazy::expanded::EncodingContextRef;
use crate::result::IonFailure;
use crate::{IonError, IonResult, Symbol, SymbolId, SymbolRef};

/// A raw symbol token found in the input stream.
#[derive(Debug, Copy, Clone, Eq)]
pub enum RawSymbolRef<'a> {
    /// A symbol address in the active symbol table.
    ///
    /// In Ion 1.0, the system symbol table is a permanent prefix to the active symbol table.
    /// System symbols are encoded using an address in the active symbol table just like
    /// application symbols, they just have an address lower than `$10`.
    SymbolId(SymbolId),
    /// A text literal.
    Text(&'a str),
}

impl PartialEq for RawSymbolRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        use RawSymbolRef::*;
        match (self, other) {
            (SymbolId(sid1), SymbolId(sid2)) => sid1 == sid2,
            (Text(text1), Text(text2)) => text1 == text2,
            _ => false,
        }
    }
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

    pub fn is_unknown_text(&self) -> bool {
        self.is_symbol_id(0)
    }

    pub fn is_symbol_id(&self, symbol_id: SymbolId) -> bool {
        matches!(self, RawSymbolRef::SymbolId(s) if *s == symbol_id)
    }

    pub fn resolve(
        self,
        label: &'static str,
        context: EncodingContextRef<'a>,
    ) -> IonResult<SymbolRef<'a>> {
        let symbol = match self {
            RawSymbolRef::SymbolId(sid) => context
                .symbol_table()
                .symbol_for(sid)
                .ok_or_else(
                    #[inline(never)]
                    || {
                        IonError::decoding_error(format!(
                            "found {label} symbol ID (${}) that was not in the symbol table (len={})",
                            sid,
                            context.symbol_table().len()
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
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_>;
}

impl AsRawSymbolRef for RawSymbolRef<'_> {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_> {
        *self
    }
}

impl AsRawSymbolRef for SymbolId {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_> {
        RawSymbolRef::SymbolId(*self)
    }
}

impl AsRawSymbolRef for &str {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_> {
        RawSymbolRef::Text(self)
    }
}

impl AsRawSymbolRef for Symbol {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_> {
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
    fn as_raw_symbol_ref(&self) -> RawSymbolRef<'_> {
        (*self).as_raw_symbol_ref()
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

impl From<SymbolId> for RawSymbolRef<'_> {
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
        value.as_raw_symbol_ref()
    }
}
