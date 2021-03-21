// Copyright Amazon.com, Inc. or its affiliates.

use super::{Element, ImportSource, SymbolToken};
use crate::types::SymbolId;
use crate::IonType;

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

#[derive(Debug, Copy, Clone)]
pub enum BorrowedValue<'a> {
    Null(IonType),
    String(&'a str),
    Symbol(BorrowedSymbolToken<'a>),
    // TODO fill this in with the rest...
}

#[derive(Debug, Clone)]
pub struct BorrowedElement<'a> {
    annotations: Vec<BorrowedSymbolToken<'a>>,
    value: BorrowedValue<'a>,
}

impl<'a> BorrowedElement<'a> {
    /// Constructs a new borrowed element from its constituent components.
    fn new(annotations: Vec<BorrowedSymbolToken<'a>>, value: BorrowedValue<'a>) -> Self {
        BorrowedElement { annotations, value }
    }
}

impl<'a> Element for BorrowedElement<'a> {
    type SymbolToken = BorrowedSymbolToken<'a>;
    type Sequence = ();
    type Struct = ();

    fn ion_type(&self) -> IonType {
        use BorrowedValue::*;
        match &self.value {
            Null(t) => *t,
            String(_) => IonType::String,
            Symbol(_) => IonType::Symbol,
        }
    }

    fn annotations<'b>(&'b self) -> Box<dyn Iterator<Item = &'b Self::SymbolToken> + 'b> {
        Box::new(self.annotations.iter())
    }

    fn is_null(&self) -> bool {
        match &self.value {
            BorrowedValue::Null(_) => true,
            _ => false,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match &self.value {
            BorrowedValue::String(text) => Some(*text),
            BorrowedValue::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    fn as_sym(&self) -> Option<&Self::SymbolToken> {
        match &self.value {
            BorrowedValue::Symbol(sym) => Some(sym),
            _ => None,
        }
    }
}
