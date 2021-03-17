// Copyright Amazon.com, Inc. or its affiliates.

use super::{ImportSource, SymbolToken};
use crate::types::SymbolId;

/// A simple, borrowed implementation of [`ImportSource`].
#[derive(Debug, Copy, Clone)]
pub struct BorrowedImportSource<'a> {
    table: &'a str,
    sid: SymbolId,
}

impl<'a> ImportSource for BorrowedImportSource<'a> {
    fn table(&self) -> &str {
        self.table
    }

    fn sid(&self) -> usize {
        self.sid
    }
}

/// A simple, borrowed implementation of [`SymbolToken`].
#[derive(Debug, Copy, Clone)]
pub struct BorrowedSymbolToken<'a> {
    text: Option<&'a str>,
    local_sid: Option<SymbolId>,
    source: Option<BorrowedImportSource<'a>>,
}

impl<'a> SymbolToken for BorrowedSymbolToken<'a> {
    type ImportSource = BorrowedImportSource<'a>;

    fn text(&self) -> Option<&str> {
        self.text
    }

    fn local_sid(&self) -> Option<usize> {
        self.local_sid
    }

    fn source(&self) -> Option<&Self::ImportSource> {
        self.source.as_ref()
    }
}
