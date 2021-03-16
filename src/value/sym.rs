// Copyright Amazon.com, Inc. or its affiliates.

use crate::types::SymbolId;

// TODO refactor the symbol types into a more general place.

/// The shared symbol table source of a given [`SymbolToken`].
pub trait ImportSource {
    /// The name of the shared symbol table that the token is from.
    fn table(&self) -> &str;

    /// The ID within the shared symbol table that the token is positioned in.
    fn sid(&self) -> SymbolId;
}

/// A view of a symbolic token.
/// This can be either a symbol value itself, an annotation, or an field name.
/// A token may have `text`, a symbol `id`, or both.
pub trait SymbolToken {
    type ImportSourceType: ImportSource;

    /// The text of the token, which may be `None` if no text is associated with the token
    /// (e.g. lack of a shared symbol table import for a given SID).
    fn text(&self) -> Option<&str>;

    /// The ID of the token, which may be `None` if no ID is associated with the token
    /// (e.g. Ion text symbols).
    fn local_sid(&self) -> Option<SymbolId>;

    /// The source of this token, which may be `None` if the symbol is locally defined.
    fn source(&self) -> Option<&Self::ImportSourceType>;
}

/// A simple implementation of  [`ImportSource`].
pub struct BasicImportSource {
    table: String,
    sid: SymbolId,
}

impl ImportSource for BasicImportSource {
    fn table(&self) -> &str {
        &self.table
    }

    fn sid(&self) -> usize {
        self.sid
    }
}

/// A simple, owned implementation of [`SymbolToken`].
pub struct BasicSymbolToken {
    text: Option<String>,
    local_sid: Option<SymbolId>,
    source: Option<BasicImportSource>,
}

impl SymbolToken for BasicSymbolToken {
    type ImportSourceType = BasicImportSource;

    fn text(&self) -> Option<&str> {
        self.text.as_ref().map(String::as_str)
    }

    fn local_sid(&self) -> Option<usize> {
        self.local_sid
    }

    fn source(&self) -> Option<&Self::ImportSourceType> {
        self.source.as_ref()
    }
}
