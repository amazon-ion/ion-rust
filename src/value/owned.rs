// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{AnyInt, Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::SymbolId;
use crate::IonType;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::rc::Rc;

/// An owned implementation of  [`ImportSource`].
#[derive(Debug, Clone)]
pub struct OwnedImportSource {
    table: Rc<str>,
    sid: SymbolId,
}

impl OwnedImportSource {
    pub fn new<T: Into<Rc<str>>>(table: T, sid: SymbolId) -> Self {
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
    text: Option<Rc<str>>,
    local_sid: Option<SymbolId>,
    source: Option<OwnedImportSource>,
}

impl OwnedSymbolToken {
    pub fn new(
        text: Option<Rc<str>>,
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

impl<T: Into<Rc<str>>> From<T> for OwnedSymbolToken {
    /// Constructs an owned token that has only text.
    fn from(text: T) -> Self {
        Self::new(Some(text.into()), None, None)
    }
}

impl SymbolToken for OwnedSymbolToken {
    type ImportSource = OwnedImportSource;

    fn text(&self) -> Option<&str> {
        self.text.as_ref().map(|s| s.as_ref())
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
}

/// An owned implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct OwnedStruct {
    text_fields: HashMap<Rc<str>, Vec<(OwnedSymbolToken, OwnedElement)>>,
    no_text_fields: Vec<(OwnedSymbolToken, OwnedElement)>,
}

impl<K, V> FromIterator<(K, V)> for OwnedStruct
where
    K: Into<OwnedSymbolToken>,
    V: Into<OwnedElement>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut text_fields: HashMap<Rc<str>, Vec<(OwnedSymbolToken, OwnedElement)>> =
            HashMap::new();
        let mut no_text_fields: Vec<(OwnedSymbolToken, OwnedElement)> = Vec::new();

        for (k, v) in iter {
            let key = k.into();
            let val = v.into();

            match key.text() {
                Some(text) => {
                    let vals = text_fields.entry(text.into()).or_insert(Vec::new());
                    vals.push((key, val));
                }
                None => {
                    no_text_fields.push((key, val));
                }
            }
        }

        Self {
            text_fields,
            no_text_fields,
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
        Box::new(
            self.text_fields
                .values()
                .flat_map(|v| v)
                .into_iter()
                .chain(self.no_text_fields.iter())
                .map(|(k, v)| (k, v)),
        )
    }

    fn get<T: AsRef<str>>(&self, field_name: T) -> Option<&Self::Element> {
        self.text_fields
            .get(field_name.as_ref())?
            .last()
            .map(|(_s, v)| v)
    }

    fn get_all<'a, T: AsRef<str>>(
        &'a self,
        field_name: T,
    ) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(
            self.text_fields
                .get(field_name.as_ref())
                .into_iter()
                .flat_map(|v| v.iter())
                .map(|(_s, v)| v),
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
