use crate::types::SymbolId;

/// A symbol token encountered in a text or binary Ion stream.
/// [RawSymbolToken]s do not store import source information for the token encountered. Similarly,
/// a [RawSymbolToken] cannot store both a symbol ID _and_ text, which means that it is not suitable
/// for representing a resolved symbol.
#[derive(Debug, Clone, PartialEq)]
pub enum RawSymbolToken {
    SymbolId(SymbolId),
    Text(String),
}

impl RawSymbolToken {
    pub fn matches(&self, sid: SymbolId, text: &str) -> bool {
        match self {
            RawSymbolToken::SymbolId(s) if *s == sid => true,
            RawSymbolToken::Text(t) if t == text => true,
            _ => false,
        }
    }

    pub fn local_sid(&self) -> Option<SymbolId> {
        match self {
            RawSymbolToken::SymbolId(s) => Some(*s),
            RawSymbolToken::Text(_t) => None,
        }
    }

    pub fn text(&self) -> Option<&str> {
        match self {
            RawSymbolToken::SymbolId(_s) => None,
            RawSymbolToken::Text(t) => Some(t.as_str()),
        }
    }
}

/// Constructs an [`OwnedSymbolToken`] with unknown text and a local ID.
/// A common case for binary parsing (though technically relevant in text).
#[inline]
pub fn local_sid_token(local_sid: SymbolId) -> RawSymbolToken {
    RawSymbolToken::SymbolId(local_sid)
}

/// Constructs an [`OwnedSymbolToken`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token<T: Into<String>>(text: T) -> RawSymbolToken {
    RawSymbolToken::Text(text.into())
}

impl From<SymbolId> for RawSymbolToken {
    fn from(value: SymbolId) -> Self {
        local_sid_token(value)
    }
}

impl From<String> for RawSymbolToken {
    fn from(value: String) -> Self {
        text_token(value)
    }
}

impl From<&str> for RawSymbolToken {
    fn from(value: &str) -> Self {
        text_token(value.to_string())
    }
}
