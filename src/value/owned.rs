// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::ion_eq::IonEq;
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::value::Builder;
use crate::IonType;
use num_bigint::BigInt;
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

impl PartialEq for OwnedImportSource {
    fn eq(&self, other: &Self) -> bool {
        self.table == other.table && self.sid == other.sid
    }
}

impl Eq for OwnedImportSource {}

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
    fn new(
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

/// Constructs an [`OwnedSymbolToken`] with unknown text and a local ID.
/// A common case for binary parsing (though technically relevant in text).
#[inline]
pub fn local_sid_token(local_sid: SymbolId) -> OwnedSymbolToken {
    OwnedSymbolToken::new(None, Some(local_sid), None)
}

/// Constructs an [`OwnedSymbolToken`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token<T: Into<Rc<str>>>(text: T) -> OwnedSymbolToken {
    OwnedSymbolToken::new(Some(text.into()), None, None)
}

impl PartialEq for OwnedSymbolToken {
    fn eq(&self, other: &Self) -> bool {
        if other.text != None || self.text != None {
            // if either side has text, we only compare text
            other.text == self.text
        } else {
            // no text--so the sources must be the same (all local symbols with no source are the same)
            other.source == self.source
        }
    }
}

impl Eq for OwnedSymbolToken {}

impl<T: Into<Rc<str>>> From<T> for OwnedSymbolToken {
    /// Constructs an owned token that has only text.
    fn from(text: T) -> Self {
        text_token(text)
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

    fn with_text(self, text: &'static str) -> Self {
        OwnedSymbolToken::new(Some(Rc::from(text)), self.local_sid, self.source)
    }

    fn with_local_sid(self, local_sid: SymbolId) -> Self {
        OwnedSymbolToken::new(self.text, Some(local_sid), self.source)
    }

    fn with_source(self, table: &'static str, sid: SymbolId) -> Self {
        OwnedSymbolToken::new(
            self.text,
            self.local_sid,
            Some(OwnedImportSource::new(table, sid)),
        )
    }

    fn text_token(text: &'static str) -> Self {
        OwnedSymbolToken::new(Some(Rc::from(text)), None, None)
    }

    fn local_sid_token(local_sid: usize) -> Self {
        OwnedSymbolToken::new(None, Some(local_sid), None)
    }
}

/// An owned implementation of [`Builder`].
impl Builder for OwnedElement {
    type Element = OwnedElement;
    type SymbolToken = OwnedSymbolToken;
    type Sequence = OwnedSequence;
    type Struct = OwnedStruct;
    type ImportSource = OwnedImportSource;

    fn new_null(e_type: IonType) -> Self::Element {
        OwnedValue::Null(e_type).into()
    }

    fn new_bool(bool: bool) -> Self::Element {
        OwnedValue::Boolean(bool).into()
    }

    fn new_string(str: &'static str) -> Self::Element {
        OwnedValue::String(str.into()).into()
    }

    fn new_symbol(sym: Self::SymbolToken) -> Self::Element {
        OwnedValue::Symbol(sym).into()
    }

    fn new_i64(int: i64) -> Self::Element {
        OwnedValue::Integer(Integer::I64(int)).into()
    }

    fn new_big_int(big_int: BigInt) -> Self::Element {
        OwnedValue::Integer(Integer::BigInt(big_int)).into()
    }

    fn new_decimal(decimal: Decimal) -> Self::Element {
        OwnedValue::Decimal(decimal).into()
    }

    fn new_timestamp(timestamp: Timestamp) -> Self::Element {
        OwnedValue::Timestamp(timestamp).into()
    }

    fn new_f64(float: f64) -> Self::Element {
        OwnedValue::Float(float).into()
    }

    fn new_clob(bytes: &[u8]) -> Self::Element {
        OwnedValue::Clob(bytes.into()).into()
    }

    fn new_blob(bytes: &[u8]) -> Self::Element {
        OwnedValue::Blob(bytes.into()).into()
    }

    fn new_list<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        OwnedValue::List(seq.into_iter().collect()).into()
    }

    fn new_sexp<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        OwnedValue::SExpression(seq.into_iter().collect()).into()
    }

    fn new_struct<
        K: Into<Self::SymbolToken>,
        V: Into<Self::Element>,
        I: IntoIterator<Item = (K, V)>,
    >(
        structure: I,
    ) -> Self::Element {
        OwnedValue::Struct(structure.into_iter().collect()).into()
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

impl FromIterator<OwnedElement> for OwnedSequence {
    /// Returns an owned sequence from the given iterator of elements.
    fn from_iter<I: IntoIterator<Item = OwnedElement>>(iter: I) -> Self {
        let mut children: Vec<OwnedElement> = Vec::new();
        for elem in iter {
            children.push(elem);
        }
        Self { children }
    }
}

impl Sequence for OwnedSequence {
    type Element = OwnedElement;

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(self.children.iter())
    }

    fn get(&self, index: usize) -> Option<&Self::Element> {
        self.children.get(index)
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl PartialEq for OwnedSequence {
    fn eq(&self, other: &Self) -> bool {
        self.children == other.children
    }
}

impl Eq for OwnedSequence {}

/// An owned implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct OwnedStruct {
    text_fields: HashMap<Rc<str>, Vec<(OwnedSymbolToken, OwnedElement)>>,
    no_text_fields: Vec<(OwnedSymbolToken, OwnedElement)>,
}

impl OwnedStruct {
    fn eq_text_fields(&self, other: &Self) -> bool {
        // check if both the text_fields have same (field_name,value) pairs
        self.text_fields.iter().all(|(key, value)| {
            value
                .iter()
                .all(|(_my_s, my_v)| other.get_all(key).any(|other_v| my_v.ion_eq(other_v)))
                && value.len() == other.get_all(key).count()
        })
    }

    fn eq_no_text_fields(&self, other: &Self) -> bool {
        // check if both the no_text_fields are same values
        self.no_text_fields.iter().all(|(my_k, my_v)| {
            other
                .no_text_fields
                .iter()
                .any(|(other_k, other_v)| my_k == other_k && my_v.ion_eq(other_v))
        })
    }
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
                    let vals = text_fields.entry(text.into()).or_insert_with(Vec::new);
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
                .flatten()
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

impl PartialEq for OwnedStruct {
    fn eq(&self, other: &Self) -> bool {
        // check if both text_fields and no_text_fields have same length
        self.text_fields.len() == other.text_fields.len() && self.no_text_fields.len() == other.no_text_fields.len()
            // check if text_fields and no_text_fields are equal
            // we need to test equality in both directions for both text_fields and no_text_fields
            // A good example for this is annotated vs not annotated values in struct
            //  { a:4, a:4 } vs. { a:4, a:a::4 } // returns true
            //  { a:4, a:a::4 } vs. { a:4, a:4 } // returns false
            && self.eq_text_fields(other) && other.eq_text_fields(self)
            && self.eq_no_text_fields(other) && other.eq_no_text_fields(self)
    }
}

impl Eq for OwnedStruct {}

impl IonEq for OwnedSequence {
    fn ion_eq(&self, other: &Self) -> bool {
        self.children.ion_eq(&other.children)
    }
}

impl IonEq for OwnedValue {
    fn ion_eq(&self, other: &Self) -> bool {
        use OwnedValue::*;
        match (self, other) {
            (Float(f1), Float(f2)) => return f1.ion_eq(f2),
            (Decimal(d1), Decimal(d2)) => return d1.ion_eq(d2),
            (Timestamp(t1), Timestamp(t2)) => return t1.ion_eq(t2),
            (List(seq1), List(seq2)) => return seq1.ion_eq(seq2),
            (SExpression(seq1), SExpression(seq2)) => return seq1.ion_eq(seq2),
            _ => {}
        };
        // For any other case, fall back to vanilla equality
        self == other
    }
}

impl IonEq for OwnedElement {
    fn ion_eq(&self, other: &Self) -> bool {
        self.annotations == other.annotations && self.value.ion_eq(&other.value)
    }
}

impl IonEq for Vec<OwnedElement> {
    fn ion_eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (v1, v2) in self.iter().zip(other.iter()) {
            if !v1.ion_eq(v2) {
                return false;
            }
        }
        true
    }
}

/// Variants for all owned version _values_ within an [`Element`].
#[derive(Debug, Clone, PartialEq)]
pub enum OwnedValue {
    Null(IonType),
    Integer(Integer),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(String),
    Symbol(OwnedSymbolToken),
    Boolean(bool),
    Blob(Vec<u8>),
    Clob(Vec<u8>),
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

impl PartialEq for OwnedElement {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.annotations == other.annotations
    }
}

impl Eq for OwnedElement {}

impl From<OwnedValue> for OwnedElement {
    fn from(val: OwnedValue) -> Self {
        Self::new(vec![], val)
    }
}

impl From<IonType> for OwnedElement {
    fn from(ion_type: IonType) -> Self {
        OwnedValue::Null(ion_type).into()
    }
}

impl From<i64> for OwnedElement {
    fn from(i64_val: i64) -> Self {
        OwnedValue::Integer(Integer::I64(i64_val)).into()
    }
}

impl From<BigInt> for OwnedElement {
    fn from(big_int_val: BigInt) -> Self {
        OwnedValue::Integer(Integer::BigInt(big_int_val)).into()
    }
}

impl From<f64> for OwnedElement {
    fn from(f64_val: f64) -> Self {
        OwnedValue::Float(f64_val).into()
    }
}

impl From<Decimal> for OwnedElement {
    fn from(decimal_val: Decimal) -> Self {
        OwnedValue::Decimal(decimal_val).into()
    }
}

impl From<Timestamp> for OwnedElement {
    fn from(timestamp_val: Timestamp) -> Self {
        OwnedValue::Timestamp(timestamp_val).into()
    }
}

impl From<bool> for OwnedElement {
    fn from(bool_val: bool) -> Self {
        OwnedValue::Boolean(bool_val).into()
    }
}

impl From<String> for OwnedElement {
    fn from(string_val: String) -> Self {
        OwnedValue::String(string_val).into()
    }
}

impl From<OwnedSymbolToken> for OwnedElement {
    fn from(sym_val: OwnedSymbolToken) -> Self {
        OwnedValue::Symbol(sym_val).into()
    }
}

impl From<OwnedStruct> for OwnedElement {
    fn from(struct_val: OwnedStruct) -> Self {
        OwnedValue::Struct(struct_val).into()
    }
}

impl Element for OwnedElement {
    type SymbolToken = OwnedSymbolToken;
    type Sequence = OwnedSequence;
    type Struct = OwnedStruct;
    type Builder = OwnedElement;

    fn ion_type(&self) -> IonType {
        use OwnedValue::*;

        match &self.value {
            Null(t) => *t,
            Integer(_) => IonType::Integer,
            Float(_) => IonType::Float,
            Decimal(_) => IonType::Decimal,
            Timestamp(_) => IonType::Timestamp,
            String(_) => IonType::String,
            Symbol(_) => IonType::Symbol,
            Boolean(_) => IonType::Boolean,
            Blob(_) => IonType::Blob,
            Clob(_) => IonType::Clob,
            SExpression(_) => IonType::SExpression,
            List(_) => IonType::List,
            Struct(_) => IonType::Struct,
        }
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::SymbolToken> + 'a> {
        Box::new(self.annotations.iter())
    }

    fn with_annotations<I: IntoIterator<Item = Self::SymbolToken>>(self, annotations: I) -> Self {
        OwnedElement::new(annotations.into_iter().collect(), self.value)
    }

    fn is_null(&self) -> bool {
        matches!(&self.value, OwnedValue::Null(_))
    }

    fn as_integer(&self) -> Option<&Integer> {
        match &self.value {
            OwnedValue::Integer(i) => Some(i),
            _ => None,
        }
    }

    fn as_f64(&self) -> Option<f64> {
        match &self.value {
            OwnedValue::Float(f) => Some(*f),
            _ => None,
        }
    }

    fn as_decimal(&self) -> Option<&Decimal> {
        match &self.value {
            OwnedValue::Decimal(d) => Some(d),
            _ => None,
        }
    }

    fn as_timestamp(&self) -> Option<&Timestamp> {
        match &self.value {
            OwnedValue::Timestamp(t) => Some(t),
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

    fn as_bool(&self) -> Option<bool> {
        match &self.value {
            OwnedValue::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    fn as_bytes(&self) -> Option<&[u8]> {
        match &self.value {
            OwnedValue::Blob(bytes) | OwnedValue::Clob(bytes) => Some(bytes),
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

#[cfg(test)]
mod value_tests {
    use super::*;
    use rstest::*;

    #[rstest(
        elem1,elem2,
        case::str(
            OwnedElement::new_string("hello"),
            "hello".to_string().into()
        ),
        case::sym_with_text(
            OwnedElement::new_symbol(text_token("hello")),
            text_token("hello").into()
        ),
    case::struct_(
            OwnedElement::new_struct(vec![("greetings", OwnedElement::from(OwnedValue::String("hello".into())))].into_iter()),
            OwnedStruct::from_iter(vec![("greetings", OwnedElement::from(OwnedValue::String("hello".into())))].into_iter()).into()
        ),
    )]
    fn owned_element_accessors(elem1: OwnedElement, elem2: OwnedElement) {
        // assert if both the element construction creates the same element
        assert_eq!(elem1, elem2);
    }
}
