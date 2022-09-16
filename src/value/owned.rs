// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{ImportSource, IonElement, IonSequence, IonStruct, IonSymbolToken};
use crate::ion_eq::IonEq;
use crate::text::text_formatter::IonValueFormatter;
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::value::Builder;
use crate::IonType;
use num_bigint::BigInt;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
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
pub struct SymbolToken {
    text: Option<Rc<str>>,
    local_sid: Option<SymbolId>,
    source: Option<OwnedImportSource>,
}

impl SymbolToken {
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
pub fn local_sid_token(local_sid: SymbolId) -> SymbolToken {
    SymbolToken::new(None, Some(local_sid), None)
}

/// Constructs an [`OwnedSymbolToken`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token<T: Into<Rc<str>>>(text: T) -> SymbolToken {
    SymbolToken::new(Some(text.into()), None, None)
}

impl PartialEq for SymbolToken {
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

impl Eq for SymbolToken {}

impl<T: Into<Rc<str>>> From<T> for SymbolToken {
    /// Constructs an owned token that has only text.
    fn from(text: T) -> Self {
        text_token(text)
    }
}

impl IonSymbolToken for SymbolToken {
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
        SymbolToken::new(Some(Rc::from(text)), self.local_sid, self.source)
    }

    fn with_local_sid(self, local_sid: SymbolId) -> Self {
        SymbolToken::new(self.text, Some(local_sid), self.source)
    }

    fn with_source(self, table: &'static str, sid: SymbolId) -> Self {
        SymbolToken::new(
            self.text,
            self.local_sid,
            Some(OwnedImportSource::new(table, sid)),
        )
    }

    fn text_token(text: &'static str) -> Self {
        SymbolToken::new(Some(Rc::from(text)), None, None)
    }

    fn local_sid_token(local_sid: usize) -> Self {
        SymbolToken::new(None, Some(local_sid), None)
    }
}

/// An owned implementation of [`Builder`].
impl Builder for Element {
    type Element = Element;
    type SymbolToken = SymbolToken;
    type Sequence = Sequence;
    type Struct = Struct;
    type ImportSource = OwnedImportSource;

    fn new_null(e_type: IonType) -> Self::Element {
        Value::Null(e_type).into()
    }

    fn new_bool(bool: bool) -> Self::Element {
        Value::Boolean(bool).into()
    }

    fn new_string(str: &'static str) -> Self::Element {
        Value::String(str.into()).into()
    }

    fn new_symbol(sym: Self::SymbolToken) -> Self::Element {
        Value::Symbol(sym).into()
    }

    fn new_i64(int: i64) -> Self::Element {
        Value::Integer(Integer::I64(int)).into()
    }

    fn new_big_int(big_int: BigInt) -> Self::Element {
        Value::Integer(Integer::BigInt(big_int)).into()
    }

    fn new_decimal(decimal: Decimal) -> Self::Element {
        Value::Decimal(decimal).into()
    }

    fn new_timestamp(timestamp: Timestamp) -> Self::Element {
        Value::Timestamp(timestamp).into()
    }

    fn new_f64(float: f64) -> Self::Element {
        Value::Float(float).into()
    }

    fn new_clob(bytes: &[u8]) -> Self::Element {
        Value::Clob(bytes.into()).into()
    }

    fn new_blob(bytes: &[u8]) -> Self::Element {
        Value::Blob(bytes.into()).into()
    }

    fn new_list<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        Value::List(seq.into_iter().collect()).into()
    }

    fn new_sexp<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        Value::SExpression(seq.into_iter().collect()).into()
    }

    fn new_struct<
        K: Into<Self::SymbolToken>,
        V: Into<Self::Element>,
        I: IntoIterator<Item = (K, V)>,
    >(
        structure: I,
    ) -> Self::Element {
        Value::Struct(structure.into_iter().collect()).into()
    }
}

/// An owned implementation of [`Sequence`]
#[derive(Debug, Clone)]
pub struct Sequence {
    children: Vec<Element>,
}

impl Sequence {
    pub fn new(children: Vec<Element>) -> Self {
        Self { children }
    }
}

impl FromIterator<Element> for Sequence {
    /// Returns an owned sequence from the given iterator of elements.
    fn from_iter<I: IntoIterator<Item = Element>>(iter: I) -> Self {
        let mut children: Vec<Element> = Vec::new();
        for elem in iter {
            children.push(elem);
        }
        Self { children }
    }
}

impl IonSequence for Sequence {
    type Element = Element;

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

impl PartialEq for Sequence {
    fn eq(&self, other: &Self) -> bool {
        self.children == other.children
    }
}

impl Eq for Sequence {}

/// An owned implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct Struct {
    text_fields: HashMap<Rc<str>, Vec<(SymbolToken, Element)>>,
    no_text_fields: Vec<(SymbolToken, Element)>,
}

impl Struct {
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

impl<K, V> FromIterator<(K, V)> for Struct
where
    K: Into<SymbolToken>,
    V: Into<Element>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut text_fields: HashMap<Rc<str>, Vec<(SymbolToken, Element)>> = HashMap::new();
        let mut no_text_fields: Vec<(SymbolToken, Element)> = Vec::new();

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

impl IonStruct for Struct {
    type FieldName = SymbolToken;
    type Element = Element;

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

impl PartialEq for Struct {
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

impl Eq for Struct {}

impl IonEq for Sequence {
    fn ion_eq(&self, other: &Self) -> bool {
        self.children.ion_eq(&other.children)
    }
}

impl IonEq for Value {
    fn ion_eq(&self, other: &Self) -> bool {
        use Value::*;
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

impl IonEq for Element {
    fn ion_eq(&self, other: &Self) -> bool {
        self.annotations == other.annotations && self.value.ion_eq(&other.value)
    }
}

impl IonEq for Vec<Element> {
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
pub enum Value {
    Null(IonType),
    Integer(Integer),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(String),
    Symbol(SymbolToken),
    Boolean(bool),
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    SExpression(Sequence),
    List(Sequence),
    Struct(Struct),
    // TODO fill this in with the rest of the value types...
}

/// An owned implementation of [`Element`]
#[derive(Debug, Clone)]
pub struct Element {
    annotations: Vec<SymbolToken>,
    value: Value,
}

impl Element {
    pub fn new(annotations: Vec<SymbolToken>, value: Value) -> Self {
        Self { annotations, value }
    }
}

impl Display for Element {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let mut ivf = IonValueFormatter { output: f };

        // display for annotations of this owned_element
        ivf.format_annotations(&self.annotations)
            .map_err(|_| std::fmt::Error)?;

        match self.ion_type() {
            IonType::Null => ivf.format_null(IonType::Null),
            IonType::Boolean => ivf.format_bool(self.as_bool().unwrap()),
            IonType::Integer => ivf.format_integer(self.as_integer().unwrap()),
            IonType::Float => ivf.format_float(self.as_f64().unwrap()),
            IonType::Decimal => ivf.format_decimal(self.as_decimal().unwrap()),
            IonType::Timestamp => ivf.format_timestamp(self.as_timestamp().unwrap()),
            IonType::Symbol => ivf.format_symbol(self.as_str().unwrap()),
            IonType::String => ivf.format_string(self.as_str().unwrap()),
            IonType::Clob => ivf.format_clob(self.as_bytes().unwrap()),
            IonType::Blob => ivf.format_blob(self.as_bytes().unwrap()),
            IonType::Struct => ivf.format_struct(self.as_struct().unwrap()),
            IonType::SExpression => ivf.format_sexp(self.as_sequence().unwrap()),
            IonType::List => ivf.format_list(self.as_sequence().unwrap()),
        }
        .map_err(|_| std::fmt::Error)?;

        Ok(())
    }
}

impl PartialEq for Element {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.annotations == other.annotations
    }
}

impl Eq for Element {}

impl From<Value> for Element {
    fn from(val: Value) -> Self {
        Self::new(vec![], val)
    }
}

impl From<IonType> for Element {
    fn from(ion_type: IonType) -> Self {
        Value::Null(ion_type).into()
    }
}

impl From<i64> for Element {
    fn from(i64_val: i64) -> Self {
        Value::Integer(Integer::I64(i64_val)).into()
    }
}

impl From<BigInt> for Element {
    fn from(big_int_val: BigInt) -> Self {
        Value::Integer(Integer::BigInt(big_int_val)).into()
    }
}

impl From<f64> for Element {
    fn from(f64_val: f64) -> Self {
        Value::Float(f64_val).into()
    }
}

impl From<Decimal> for Element {
    fn from(decimal_val: Decimal) -> Self {
        Value::Decimal(decimal_val).into()
    }
}

impl From<Timestamp> for Element {
    fn from(timestamp_val: Timestamp) -> Self {
        Value::Timestamp(timestamp_val).into()
    }
}

impl From<bool> for Element {
    fn from(bool_val: bool) -> Self {
        Value::Boolean(bool_val).into()
    }
}

impl From<String> for Element {
    fn from(string_val: String) -> Self {
        Value::String(string_val).into()
    }
}

impl From<SymbolToken> for Element {
    fn from(sym_val: SymbolToken) -> Self {
        Value::Symbol(sym_val).into()
    }
}

impl From<Struct> for Element {
    fn from(struct_val: Struct) -> Self {
        Value::Struct(struct_val).into()
    }
}

impl IonElement for Element {
    type SymbolToken = SymbolToken;
    type Sequence = Sequence;
    type Struct = Struct;
    type Builder = Element;

    fn ion_type(&self) -> IonType {
        use Value::*;

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
        Element::new(annotations.into_iter().collect(), self.value)
    }

    fn has_annotation(&self, annotation: &str) -> bool {
        self.annotations
            .iter()
            .any(|a| a.text() == Some(annotation))
    }

    fn is_null(&self) -> bool {
        matches!(&self.value, Value::Null(_))
    }

    fn as_integer(&self) -> Option<&Integer> {
        match &self.value {
            Value::Integer(i) => Some(i),
            _ => None,
        }
    }

    fn as_f64(&self) -> Option<f64> {
        match &self.value {
            Value::Float(f) => Some(*f),
            _ => None,
        }
    }

    fn as_decimal(&self) -> Option<&Decimal> {
        match &self.value {
            Value::Decimal(d) => Some(d),
            _ => None,
        }
    }

    fn as_timestamp(&self) -> Option<&Timestamp> {
        match &self.value {
            Value::Timestamp(t) => Some(t),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match &self.value {
            Value::String(text) => Some(text),
            Value::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    fn as_sym(&self) -> Option<&Self::SymbolToken> {
        match &self.value {
            Value::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match &self.value {
            Value::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    fn as_bytes(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) | Value::Clob(bytes) => Some(bytes),
            _ => None,
        }
    }

    fn as_sequence(&self) -> Option<&Self::Sequence> {
        match &self.value {
            Value::SExpression(seq) | Value::List(seq) => Some(seq),
            _ => None,
        }
    }

    fn as_struct(&self) -> Option<&Self::Struct> {
        match &self.value {
            Value::Struct(structure) => Some(structure),
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
            Element::new_string("hello"),
            "hello".to_string().into()
        ),
        case::sym_with_text(
            Element::new_symbol(text_token("hello")),
            text_token("hello").into()
        ),
    case::struct_(
            Element::new_struct(vec![("greetings", Element::from(Value::String("hello".into())))].into_iter()),
            Struct::from_iter(vec![("greetings", Element::from(Value::String("hello".into())))].into_iter()).into()
        ),
    )]
    fn owned_element_accessors(elem1: Element, elem2: Element) {
        // assert if both the element construction creates the same element
        assert_eq!(elem1, elem2);
    }
}
