// Copyright Amazon.com, Inc. or its affiliates.

use super::{ImportSource, SymbolToken};
use crate::types::SymbolId;

/// A simple, owned implementation of  [`ImportSource`].
#[derive(Debug, Clone)]
pub struct OwnedImportSource {
    table: String,
    sid: SymbolId,
}

impl ImportSource for OwnedImportSource {
    fn table(&self) -> &str {
        &self.table
    }

    fn sid(&self) -> usize {
        self.sid
    }
}

/// A simple, owned implementation of [`SymbolToken`].
#[derive(Debug, Clone)]
pub struct OwnedSymbolToken {
    text: Option<String>,
    local_sid: Option<SymbolId>,
    source: Option<OwnedImportSource>,
}

impl SymbolToken for OwnedSymbolToken {
    type ImportSourceType = OwnedImportSource;

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
