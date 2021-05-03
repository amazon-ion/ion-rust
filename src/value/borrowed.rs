// Copyright Amazon.com, Inc. or its affiliates.

//! Provides borrowed implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! Specifically, all implementations are tied to some particular lifetime, generally linked
//! to a parser implementation of some sort or some context from which the borrow can occur.
//! For simple values, the values are inlined (see [`BorrowedValue`]), but for things that are
//! backed by octets or string data, `&[u8]` and `&str` are used.

use super::{Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::value::{AnyInt, Builder};
use crate::IonType;
use num_bigint::BigInt;
use std::collections::HashMap;
use std::iter::FromIterator;

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

impl<'val> PartialEq for BorrowedImportSource<'val> {
    fn eq(&self, other: &Self) -> bool {
        self.table == other.table && self.sid == other.sid
    }
}

impl<'val> Eq for BorrowedImportSource<'val> {}

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
    fn new(
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

/// Constructs an [`BorrowedSymbolToken`] with unknown text and a local ID.
/// A common case for binary parsing (though technically relevant in text).
#[inline]
pub fn local_sid_token<'val>(local_sid: SymbolId) -> BorrowedSymbolToken<'val> {
    BorrowedSymbolToken::new(None, Some(local_sid), None)
}

/// Constructs an [`BorrowedSymbolToken`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token(text: &str) -> BorrowedSymbolToken {
    BorrowedSymbolToken::new(Some(text), None, None)
}

impl<'val> PartialEq for BorrowedSymbolToken<'val> {
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

impl<'val> Eq for BorrowedSymbolToken<'val> {}

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

    fn with_text(self, text: &'static str) -> Self {
        BorrowedSymbolToken::new(Some(text), self.local_sid, self.source)
    }

    fn with_local_sid(self, local_sid: SymbolId) -> Self {
        BorrowedSymbolToken::new(self.text, Some(local_sid), self.source)
    }

    fn with_source(self, table: &'static str, sid: SymbolId) -> Self {
        BorrowedSymbolToken::new(
            self.text,
            self.local_sid,
            Some(BorrowedImportSource::new(table, sid)),
        )
    }

    fn text_token(text: &'static str) -> Self {
        BorrowedSymbolToken::new(Some(text), None, None)
    }

    fn local_sid_token(local_sid: usize) -> Self {
        BorrowedSymbolToken::new(None, Some(local_sid), None)
    }
}

/// A borrowed implementation of [`Builder`].
impl<'val> Builder for BorrowedElement<'val> {
    type Element = BorrowedElement<'val>;
    type SymbolToken = BorrowedSymbolToken<'val>;
    type Sequence = BorrowedSequence<'val>;
    type Struct = BorrowedStruct<'val>;
    type ImportSource = BorrowedImportSource<'val>;

    fn new_null(e_type: IonType) -> Self::Element {
        BorrowedValue::Null(e_type).into()
    }

    fn new_bool(bool: bool) -> Self::Element {
        BorrowedValue::Boolean(bool).into()
    }

    fn new_string(str: &'static str) -> Self::Element {
        BorrowedValue::String(str).into()
    }

    fn new_symbol(sym: Self::SymbolToken) -> Self::Element {
        BorrowedValue::Symbol(sym).into()
    }

    fn new_i64(int: i64) -> Self::Element {
        BorrowedValue::Integer(AnyInt::I64(int)).into()
    }

    fn new_big_int(big_int: BigInt) -> Self::Element {
        BorrowedValue::Integer(AnyInt::BigInt(big_int)).into()
    }

    fn new_decimal(decimal: Decimal) -> Self::Element {
        BorrowedValue::Decimal(decimal).into()
    }

    fn new_timestamp(timestamp: Timestamp) -> Self::Element {
        BorrowedValue::Timestamp(timestamp).into()
    }

    fn new_f64(float: f64) -> Self::Element {
        BorrowedValue::Float(float).into()
    }

    fn new_clob(bytes: &'static [u8]) -> Self::Element {
        BorrowedValue::Clob(bytes).into()
    }

    fn new_blob(bytes: &'static [u8]) -> Self::Element {
        BorrowedValue::Blob(bytes).into()
    }

    fn new_list<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        BorrowedValue::List(seq.into_iter().collect()).into()
    }

    fn new_sexp<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        BorrowedValue::SExpression(seq.into_iter().collect()).into()
    }

    fn new_struct<
        K: Into<Self::SymbolToken>,
        V: Into<Self::Element>,
        I: IntoIterator<Item = (K, V)>,
    >(
        structure: I,
    ) -> Self::Element {
        BorrowedValue::Struct(structure.into_iter().collect()).into()
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

impl<'val> FromIterator<BorrowedElement<'val>> for BorrowedSequence<'val> {
    /// Returns an borrowed sequence from the given iterator of elements.
    fn from_iter<I: IntoIterator<Item = BorrowedElement<'val>>>(iter: I) -> Self {
        let mut children: Vec<BorrowedElement> = Vec::new();
        for elem in iter {
            children.push(elem);
        }
        Self { children }
    }
}

impl<'val> Sequence for BorrowedSequence<'val> {
    type Element = BorrowedElement<'val>;

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
        self.children.len() == 0
    }
}

impl<'val> PartialEq for BorrowedSequence<'val> {
    fn eq(&self, other: &Self) -> bool {
        self.children == other.children
    }
}

impl<'val> Eq for BorrowedSequence<'val> {}

/// A borrowed implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct BorrowedStruct<'val> {
    text_fields: HashMap<String, Vec<(BorrowedSymbolToken<'val>, BorrowedElement<'val>)>>,
    no_text_fields: Vec<(BorrowedSymbolToken<'val>, BorrowedElement<'val>)>,
}

impl<'val> BorrowedStruct<'val> {
    fn eq_text_fields(&self, other: &Self) -> bool {
        // check if both the text_fields have same (field_name,value) pairs
        self.text_fields.iter().all(|(key, value)| {
            value.iter().all(|(_my_s, my_v)| {
                other
                    .get_all(key)
                    .find(|other_v| my_v == *other_v)
                    .is_some()
            }) && value.len() == other.get_all(key).count()
        })
    }

    fn eq_no_text_fields(&self, other: &Self) -> bool {
        // check if both the no_text_fields are same values
        self.no_text_fields.iter().all(|(my_k, my_v)| {
            other
                .no_text_fields
                .iter()
                .find(|(other_k, other_v)| my_k == other_k && my_v == other_v)
                .is_some()
        })
    }
}

impl<'val, K, V> FromIterator<(K, V)> for BorrowedStruct<'val>
where
    K: Into<BorrowedSymbolToken<'val>>,
    V: Into<BorrowedElement<'val>>,
{
    /// Returns a borrowed struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut text_fields: HashMap<String, Vec<(BorrowedSymbolToken, BorrowedElement)>> =
            HashMap::new();
        let mut no_text_fields: Vec<(BorrowedSymbolToken, BorrowedElement)> = Vec::new();

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

impl<'val> Struct for BorrowedStruct<'val> {
    type FieldName = BorrowedSymbolToken<'val>;
    type Element = BorrowedElement<'val>;

    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a> {
        // flattens the text_fields HashMap and chains with no_text_fields
        // to return all fields with iterator
        Box::new(
            self.text_fields
                .values()
                .flat_map(|v| v)
                .into_iter()
                .chain(self.no_text_fields.iter())
                .map(|(s, v)| (s, v)),
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

impl<'val> PartialEq for BorrowedStruct<'val> {
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

impl<'val> Eq for BorrowedStruct<'val> {}

// TODO replace the references with `Cow` and bridge to the owned APIs for mutability

/// Variants for all borrowed version _values_ within an [`Element`].
#[derive(Debug, Clone, PartialEq)]
pub enum BorrowedValue<'val> {
    Null(IonType),
    Integer(AnyInt),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(&'val str),
    Symbol(BorrowedSymbolToken<'val>),
    Boolean(bool),
    Blob(&'val [u8]),
    Clob(&'val [u8]),
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

impl<'val> PartialEq for BorrowedElement<'val> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.annotations == other.annotations
    }
}

impl<'val> Eq for BorrowedElement<'val> {}

impl<'val> From<BorrowedValue<'val>> for BorrowedElement<'val> {
    /// Constructs a [`BorrowedElement`] without annotations from this value.
    fn from(val: BorrowedValue<'val>) -> Self {
        Self::new(vec![], val)
    }
}

impl<'val> From<IonType> for BorrowedElement<'val> {
    fn from(ion_type: IonType) -> Self {
        BorrowedValue::Null(ion_type).into()
    }
}

impl<'val> From<i64> for BorrowedElement<'val> {
    fn from(i64_val: i64) -> Self {
        BorrowedValue::Integer(AnyInt::I64(i64_val)).into()
    }
}

impl<'val> From<BigInt> for BorrowedElement<'val> {
    fn from(big_int_val: BigInt) -> Self {
        BorrowedValue::Integer(AnyInt::BigInt(big_int_val)).into()
    }
}

impl<'val> From<f64> for BorrowedElement<'val> {
    fn from(f64_val: f64) -> Self {
        BorrowedValue::Float(f64_val).into()
    }
}

impl<'val> From<Decimal> for BorrowedElement<'val> {
    fn from(decimal_val: Decimal) -> Self {
        BorrowedValue::Decimal(decimal_val).into()
    }
}

impl<'val> From<Timestamp> for BorrowedElement<'val> {
    fn from(timestamp_val: Timestamp) -> Self {
        BorrowedValue::Timestamp(timestamp_val).into()
    }
}

impl<'val> From<bool> for BorrowedElement<'val> {
    fn from(bool_val: bool) -> Self {
        BorrowedValue::Boolean(bool_val).into()
    }
}

impl<'val> From<&'val str> for BorrowedElement<'val> {
    fn from(string_val: &'val str) -> Self {
        BorrowedValue::String(string_val).into()
    }
}

impl<'val> From<BorrowedSymbolToken<'val>> for BorrowedElement<'val> {
    fn from(sym_val: BorrowedSymbolToken<'val>) -> Self {
        BorrowedValue::Symbol(sym_val).into()
    }
}

impl<'val> From<BorrowedStruct<'val>> for BorrowedElement<'val> {
    fn from(struct_val: BorrowedStruct<'val>) -> Self {
        BorrowedValue::Struct(struct_val).into()
    }
}

impl<'val> Element for BorrowedElement<'val> {
    type SymbolToken = BorrowedSymbolToken<'val>;
    type Sequence = BorrowedSequence<'val>;
    type Struct = BorrowedStruct<'val>;
    type Builder = BorrowedElement<'val>;

    fn ion_type(&self) -> IonType {
        use BorrowedValue::*;
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
        BorrowedElement::new(annotations.into_iter().collect(), self.value)
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

    fn as_f64(&self) -> Option<f64> {
        match &self.value {
            BorrowedValue::Float(f) => Some(*f),
            _ => None,
        }
    }

    fn as_decimal(&self) -> Option<&Decimal> {
        match &self.value {
            BorrowedValue::Decimal(d) => Some(d),
            _ => None,
        }
    }

    fn as_timestamp(&self) -> Option<&Timestamp> {
        match &self.value {
            BorrowedValue::Timestamp(t) => Some(t),
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

    fn as_bool(&self) -> Option<bool> {
        match &self.value {
            BorrowedValue::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    fn as_bytes(&self) -> Option<&[u8]> {
        match &self.value {
            BorrowedValue::Blob(bytes) | BorrowedValue::Clob(bytes) => Some(bytes),
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

#[cfg(test)]
mod borrowed_value_tests {
    use super::*;
    use rstest::*;

    #[rstest(
    elem1,elem2,
        case::str(
            BorrowedElement::new_string("hello"),
            "hello".into()
        ),
        case::sym_with_text(
            BorrowedElement::new_symbol(text_token("hello")),
            text_token("hello").into()
        ),
        case::struct_(
            BorrowedElement::new_struct(vec![("greetings", BorrowedElement::from(BorrowedValue::String("hello".into())))].into_iter()),
            BorrowedStruct::from_iter(vec![("greetings", BorrowedElement::from(BorrowedValue::String("hello".into())))].into_iter()).into()
        ),
    )]
    fn owned_element_accessors(elem1: BorrowedElement, elem2: BorrowedElement) {
        // assert if both the element construction creates the same element
        assert_eq!(elem1, elem2);
    }
}
