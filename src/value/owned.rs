// Copyright Amazon.com, Inc. or its affiliates.

use super::{AnyInt, Element, ImportSource, Sequence, SymbolToken};
use crate::types::SymbolId;
use crate::IonType;

/// A simple, owned implementation of  [`ImportSource`].
#[derive(Debug, Clone)]
pub struct OwnedImportSource {
    table: String,
    sid: SymbolId,
}

impl OwnedImportSource {
    fn new(table: String, sid: SymbolId) -> Self {
        Self { table, sid }
    }
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

impl OwnedSymbolToken {
    fn new(
        text: Option<String>,
        local_sid: Option<SymbolId>,
        source: Option<OwnedImportSource>,
    ) -> Self {
        Self {
            text,
            local_sid,
            source,
        }
    }

    /// Constructs a token that contains only text.
    fn new_text(text: String) -> Self {
        Self::new(Some(text), None, None)
    }
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
pub struct OwnedSequence {
    children: Vec<OwnedElement>,
}

impl OwnedSequence {
    fn new(children: Vec<OwnedElement>) -> Self {
        Self { children }
    }
}

impl Sequence for OwnedSequence {
    type Element = OwnedElement;

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(self.children.iter())
    }
}

#[derive(Debug, Clone)]
pub enum OwnedValue {
    Null(IonType),
    Integer(AnyInt),
    String(String),
    Symbol(OwnedSymbolToken),
    SExpression(OwnedSequence),
    List(OwnedSequence),
    // TODO fill this in with the rest of the value types...
}

#[derive(Debug, Clone)]
pub struct OwnedElement {
    annotations: Vec<OwnedSymbolToken>,
    value: OwnedValue,
}

impl OwnedElement {
    fn new(annotations: Vec<OwnedSymbolToken>, value: OwnedValue) -> Self {
        Self { annotations, value }
    }
}

impl Element for OwnedElement {
    type SymbolToken = OwnedSymbolToken;
    type Sequence = OwnedSequence;
    type Struct = ();

    fn ion_type(&self) -> IonType {
        use OwnedValue::*;

        match &self.value {
            Null(t) => *t,
            Integer(_) => IonType::Integer,
            String(_) => IonType::String,
            Symbol(_) => IonType::Symbol,
            SExpression(_) => IonType::SExpression,
            List(_) => IonType::List,
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

    fn as_any_int(&self) -> Option<&AnyInt> {
        match &self.value {
            OwnedValue::Integer(i) => Some(i),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match &self.value {
            OwnedValue::String(text) => Some(text),
            OwnedValue::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    fn as_sym(&self) -> Option<&Self::SymbolToken> {
        match &self.value {
            OwnedValue::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    fn as_sequence(&self) -> Option<&Self::Sequence> {
        match &self.value {
            OwnedValue::SExpression(seq) | OwnedValue::List(seq) => Some(seq),
            _ => None,
        }
    }
}
