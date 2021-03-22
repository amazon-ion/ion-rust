// Copyright Amazon.com, Inc. or its affiliates.

use super::{Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::SymbolId;
use crate::value::AnyInt;
use crate::IonType;

/// A simple, borrowed implementation of [`ImportSource`].
#[derive(Debug, Copy, Clone)]
pub struct BorrowedImportSource<'a> {
    table: &'a str,
    sid: SymbolId,
}

impl<'a> BorrowedImportSource<'a> {
    fn new(table: &'a str, sid: SymbolId) -> Self {
        Self { table, sid }
    }
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

impl<'a> BorrowedSymbolToken<'a> {
    fn new(
        text: Option<&'a str>,
        local_sid: Option<SymbolId>,
        source: Option<BorrowedImportSource<'a>>,
    ) -> Self {
        Self {
            text,
            local_sid,
            source,
        }
    }

    /// Constructs a token that contains only text.
    fn new_text(text: &'a str) -> Self {
        Self::new(Some(text), None, None)
    }
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

#[derive(Debug, Clone)]
pub struct BorrowedSequence<'a> {
    children: Vec<BorrowedElement<'a>>,
}

impl<'a> BorrowedSequence<'a> {
    fn new(children: Vec<BorrowedElement<'a>>) -> Self {
        Self { children }
    }
}

impl<'a> Sequence for BorrowedSequence<'a> {
    type Element = BorrowedElement<'a>;

    fn iter<'b>(&'b self) -> Box<dyn Iterator<Item = &'b Self::Element> + 'b> {
        Box::new(self.children.iter())
    }
}

#[derive(Debug, Clone)]
pub struct BorrowedStruct<'a> {
    // TODO model actual map indexing for the struct (maybe as a variant type)
    //      otherwise struct field lookup will be O(N)
    fields: Vec<(BorrowedSymbolToken<'a>, BorrowedElement<'a>)>,
}

impl<'a> BorrowedStruct<'a> {
    fn new(fields: Vec<(BorrowedSymbolToken<'a>, BorrowedElement<'a>)>) -> Self {
        Self { fields }
    }
}

impl<'a> Struct for BorrowedStruct<'a> {
    type FieldName = BorrowedSymbolToken<'a>;
    type Element = BorrowedElement<'a>;

    fn iter<'b>(
        &'b self,
    ) -> Box<dyn Iterator<Item = (&'b Self::FieldName, &'b Self::Element)> + 'b> {
        // convert &(k, v) -> (&k, &v)
        Box::new(self.fields.iter().map(|kv| match &kv {
            (k, v) => (k, v),
        }))
    }
}

// TODO replace the references with `Cow` and bridge to the owned APIs for mutability

#[derive(Debug, Clone)]
pub enum BorrowedValue<'a> {
    Null(IonType),
    Integer(AnyInt),
    String(&'a str),
    Symbol(BorrowedSymbolToken<'a>),
    SExpression(BorrowedSequence<'a>),
    List(BorrowedSequence<'a>),
    Struct(BorrowedStruct<'a>),
    // TODO fill this in with the rest...
}

#[derive(Debug, Clone)]
pub struct BorrowedElement<'a> {
    annotations: Vec<BorrowedSymbolToken<'a>>,
    value: BorrowedValue<'a>,
}

impl<'a> BorrowedElement<'a> {
    fn new(annotations: Vec<BorrowedSymbolToken<'a>>, value: BorrowedValue<'a>) -> Self {
        Self { annotations, value }
    }
}

impl<'a> Element for BorrowedElement<'a> {
    type SymbolToken = BorrowedSymbolToken<'a>;
    type Sequence = BorrowedSequence<'a>;
    type Struct = BorrowedStruct<'a>;

    fn ion_type(&self) -> IonType {
        use BorrowedValue::*;
        match &self.value {
            Null(t) => *t,
            Integer(_) => IonType::Integer,
            String(_) => IonType::String,
            Symbol(_) => IonType::Symbol,
            SExpression(_) => IonType::SExpression,
            List(_) => IonType::List,
            Struct(_) => IonType::Struct,
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

    fn as_any_int(&self) -> Option<&AnyInt> {
        match &self.value {
            BorrowedValue::Integer(i) => Some(i),
            _ => None,
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

    fn as_sequence(&self) -> Option<&Self::Sequence> {
        match &self.value {
            BorrowedValue::SExpression(seq) | BorrowedValue::List(seq) => Some(seq),
            _ => None,
        }
    }

    fn as_struct(&self) -> Option<&Self::Struct> {
        match &self.value {
            BorrowedValue::Struct(structure) => Some(structure),
            _ => None,
        }
    }
}
