// Copyright Amazon.com, Inc. or its affiliates.

use super::{Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::SymbolId;
use crate::IonType;

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
    type ImportSource = OwnedImportSource;

    fn text(&self) -> Option<&str> {
        self.text.as_ref().map(String::as_str)
    }

    fn local_sid(&self) -> Option<usize> {
        self.local_sid
    }

    fn source(&self) -> Option<&Self::ImportSource> {
        self.source.as_ref()
    }
}

#[derive(Debug, Clone)]
pub enum OwnedValue {
    Null(IonType),
    String(String),
    // TODO fill this in with the rest of the value types...
}

#[derive(Debug, Clone)]
pub struct OwnedElement {
    annotations: Vec<OwnedSymbolToken>,
    value: OwnedValue,
}

impl OwnedElement {
    /// Constructs a new owned element from its constituent components.
    fn new(annotations: Vec<OwnedSymbolToken>, value: OwnedValue) -> Self {
        OwnedElement { annotations, value }
    }
}

impl Element for OwnedElement {
    type SymbolToken = OwnedSymbolToken;
    type Sequence = ();
    type Struct = ();

    fn ion_type(&self) -> IonType {
        use OwnedValue::*;

        match &self.value {
            Null(t) => *t,
            String(_) => IonType::String,
        }
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::SymbolToken> + 'a> {
        Box::new(self.annotations.iter())
    }

    fn is_null(&self) -> bool {
        match &self.value {
            OwnedValue::Null(_) => true,
            _ => false,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match &self.value {
            OwnedValue::String(s) => Some(s),
            _ => None,
        }
    }
}
