// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{AnyInt, Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::SymbolId;
use crate::IonType;
use std::collections::HashMap;

/// An owned implementation of  [`ImportSource`].
#[derive(Debug, Clone)]
pub struct OwnedImportSource {
    table: String,
    sid: SymbolId,
}

impl OwnedImportSource {
    pub fn new<T: Into<String>>(table: T, sid: SymbolId) -> Self {
        Self {
            table: table.into(),
            sid,
        }
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

/// An owned implementation of [`SymbolToken`].
#[derive(Debug, Clone)]
pub struct OwnedSymbolToken {
    text: Option<String>,
    local_sid: Option<SymbolId>,
    source: Option<OwnedImportSource>,
}

impl OwnedSymbolToken {
    pub fn new(
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
}

impl<T: Into<String>> From<T> for OwnedSymbolToken {
    /// Constructs an owned token that has only text.
    fn from(text: T) -> Self {
        Self::new(Some(text.into()), None, None)
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

/// An owned implementation of [`Sequence`]
#[derive(Debug, Clone)]
pub struct OwnedSequence {
    children: Vec<OwnedElement>,
}

impl OwnedSequence {
    pub fn new(children: Vec<OwnedElement>) -> Self {
        Self { children }
    }
}

impl Sequence for OwnedSequence {
    type Element = OwnedElement;

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
        self.len() == 0
    }

    // TODO Add these mutable methods on Sequence
    /*fn pop(&mut self) -> Self::Element {
        self.children.pop().unwrap()
    }

    fn push(&mut self, e: Self::Element) {
        self.children.push(e)
    }*/
}

/// An owned implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct OwnedStruct {
    // TODO model actual map indexing for the struct (maybe as a variant type)
    //      otherwise struct field lookup will be O(N)
    fields_with_text_key: HashMap<String, Vec<(OwnedSymbolToken, OwnedElement)>>,
    fields_with_no_text_key: Vec<(OwnedSymbolToken, OwnedElement)>,
}

impl OwnedStruct {
    // TODO remove constructor and instead add from_iter function to HashMap and Vec from iterator
    fn new(
        fields_with_text: HashMap<String, Vec<(OwnedSymbolToken, OwnedElement)>>,
        fields_with_no_text: Vec<(OwnedSymbolToken, OwnedElement)>,
    ) -> Self {
        Self {
            fields_with_text_key: fields_with_text,
            fields_with_no_text_key: fields_with_no_text,
        }
    }
}

impl Struct for OwnedStruct {
    type FieldName = OwnedSymbolToken;
    type Element = OwnedElement;

    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a> {
        // convert &(k, v) -> (&k, &v)
        // flattens the fields_with_text_key HashMap and chains with fields_with_no_text_key
        // to return all fields with iterator
        let all_fields_vec: Vec<&(OwnedSymbolToken, OwnedElement)> = self
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
                    (k, v) => v,
                }),
        )
    }
}

/// Variants for all owned version _values_ within an [`Element`].
#[derive(Debug, Clone)]
pub enum OwnedValue {
    Null(IonType),
    Integer(AnyInt),
    String(String),
    Symbol(OwnedSymbolToken),
    SExpression(OwnedSequence),
    List(OwnedSequence),
    Struct(OwnedStruct),
    // TODO fill this in with the rest of the value types...
}

/// An owned implementation of [`Element`]
#[derive(Debug, Clone)]
pub struct OwnedElement {
    annotations: Vec<OwnedSymbolToken>,
    value: OwnedValue,
}

impl OwnedElement {
    pub fn new(annotations: Vec<OwnedSymbolToken>, value: OwnedValue) -> Self {
        Self { annotations, value }
    }
}

impl From<OwnedValue> for OwnedElement {
    fn from(val: OwnedValue) -> Self {
        Self::new(vec![], val)
    }
}

impl Element for OwnedElement {
    type SymbolToken = OwnedSymbolToken;
    type Sequence = OwnedSequence;
    type Struct = OwnedStruct;

    fn ion_type(&self) -> IonType {
        use OwnedValue::*;

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

    fn as_struct(&self) -> Option<&Self::Struct> {
        match &self.value {
            OwnedValue::Struct(structure) => Some(structure),
            _ => None,
        }
    }
}
