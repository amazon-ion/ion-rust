// Copyright Amazon.com, Inc. or its affiliates.

//! Provides borrowed implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! Specifically, all implementations are tied to some particular lifetime, generally linked
//! to a parser implementation of some sort or some context from which the borrow can occur.
//! For simple values, the values are inlined (see [`BorrowedValue`]), but for things that are
//! backed by octets or string data, `&[u8]` and `&str` are used.

use super::{Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::SymbolId;
use crate::value::AnyInt;
use crate::IonType;
use std::collections::HashMap;

/// A borrowed implementation of [`ImportSource`].
#[derive(Debug, Copy, Clone)]
pub struct BorrowedImportSource<'val> {
    table: &'val str,
    sid: SymbolId,
}

impl<'val> BorrowedImportSource<'val> {
    pub fn new(table: &'val str, sid: SymbolId) -> Self {
        Self { table, sid }
    }
}

impl<'val> ImportSource for BorrowedImportSource<'val> {
    fn table(&self) -> &str {
        self.table
    }

    fn sid(&self) -> usize {
        self.sid
    }
}

/// A borrowed implementation of [`SymbolToken`].
#[derive(Debug, Copy, Clone)]
pub struct BorrowedSymbolToken<'val> {
    text: Option<&'val str>,
    local_sid: Option<SymbolId>,
    source: Option<BorrowedImportSource<'val>>,
}

impl<'val> BorrowedSymbolToken<'val> {
    pub fn new(
        text: Option<&'val str>,
        local_sid: Option<SymbolId>,
        source: Option<BorrowedImportSource<'val>>,
    ) -> Self {
        Self {
            text,
            local_sid,
            source,
        }
    }
}

impl<'val> From<&'val str> for BorrowedSymbolToken<'val> {
    fn from(text: &'val str) -> Self {
        Self::new(Some(text), None, None)
    }
}

impl<'val> SymbolToken for BorrowedSymbolToken<'val> {
    type ImportSource = BorrowedImportSource<'val>;

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

/// A borrowed implementation of [`Sequence`].
#[derive(Debug, Clone)]
pub struct BorrowedSequence<'val> {
    children: Vec<BorrowedElement<'val>>,
}

impl<'val> BorrowedSequence<'val> {
    pub fn new(children: Vec<BorrowedElement<'val>>) -> Self {
        Self { children }
    }
}

impl<'val> Sequence for BorrowedSequence<'val> {
    type Element = BorrowedElement<'val>;

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(self.children.iter())
    }

    fn get(&self, index: usize) -> Option<&Self::Element> {
        if index > self.children.len() {
            None
        } else {
            Some(&self.children[index])
        }
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    fn is_empty(&self) -> bool {
        self.children.len() == 0
    }

    // TODO Add these mutable methods on Sequence
    /*fn pop(&mut self) -> Self::Element {
        self.children.pop().unwrap()
    }

    fn push(&mut self, e: Self::Element) {
        self.children.push(e)
    }*/
}

/// A borrowed implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct BorrowedStruct<'val> {
    fields_with_text_key: HashMap<String, Vec<(BorrowedSymbolToken<'val>, BorrowedElement<'val>)>>,
    fields_with_no_text_key: Vec<(BorrowedSymbolToken<'val>, BorrowedElement<'val>)>,
}

impl<'val> BorrowedStruct<'val> {
    // TODO remove constructor and instead add from_iter function to HashMap and Vec from iterator
    fn new(
        fields_with_text: HashMap<
            std::string::String,
            Vec<(BorrowedSymbolToken<'val>, BorrowedElement<'val>)>,
        >,
        fields_with_no_text: Vec<(BorrowedSymbolToken<'val>, BorrowedElement<'val>)>,
    ) -> Self {
        Self {
            fields_with_text_key: fields_with_text,
            fields_with_no_text_key: fields_with_no_text,
        }
    }
}

impl<'val> Struct for BorrowedStruct<'val> {
    type FieldName = BorrowedSymbolToken<'val>;
    type Element = BorrowedElement<'val>;

    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a> {
        // convert (&k, &v[0..n]) -> (&k, &v[0])
        // flattens the fields_with_text_key HashMap and chains with fields_with_no_text_key
        // to return all fields with iterator
        let all_fields_vec: Vec<&(BorrowedSymbolToken, BorrowedElement)> = self
            .fields_with_text_key
            .values()
            .flat_map(|v| v)
            .into_iter()
            .chain(self.fields_with_no_text_key.iter())
            .collect();
        Box::new(all_fields_vec.into_iter().map(|kv| match &kv {
            (k, v) => (k, v),
        }))
    }

    fn get(&self, field_name: &String) -> Option<&Self::Element> {
        match self.fields_with_text_key.get(field_name)?.last() {
            None => None,
            Some(value) => Some(&value.1),
        }
    }

    fn get_all<'a>(
        &'a self,
        field_name: &'a String,
    ) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(
            self.fields_with_text_key
                .get(field_name)
                .into_iter()
                .flat_map(|v| v.iter())
                .map(|kv| match &kv {
                    (_k, v) => v,
                }),
        )
    }
}

// TODO replace the references with `Cow` and bridge to the owned APIs for mutability

/// Variants for all borrowed version _values_ within an [`Element`].
#[derive(Debug, Clone)]
pub enum BorrowedValue<'val> {
    Null(IonType),
    Integer(AnyInt),
    String(&'val str),
    Symbol(BorrowedSymbolToken<'val>),
    SExpression(BorrowedSequence<'val>),
    List(BorrowedSequence<'val>),
    Struct(BorrowedStruct<'val>),
    // TODO fill this in with the rest...
}

/// A borrowed implementation of [`Element`]
#[derive(Debug, Clone)]
pub struct BorrowedElement<'val> {
    annotations: Vec<BorrowedSymbolToken<'val>>,
    value: BorrowedValue<'val>,
}

impl<'val> BorrowedElement<'val> {
    pub fn new(annotations: Vec<BorrowedSymbolToken<'val>>, value: BorrowedValue<'val>) -> Self {
        Self { annotations, value }
    }
}

impl<'val> From<BorrowedValue<'val>> for BorrowedElement<'val> {
    /// Constructs a [`BorrowedElement`] without annotations from this value.
    fn from(val: BorrowedValue<'val>) -> Self {
        Self::new(vec![], val)
    }
}

impl<'val> Element for BorrowedElement<'val> {
    type SymbolToken = BorrowedSymbolToken<'val>;
    type Sequence = BorrowedSequence<'val>;
    type Struct = BorrowedStruct<'val>;

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

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::SymbolToken> + 'a> {
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
