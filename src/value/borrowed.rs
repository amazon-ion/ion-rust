// Copyright Amazon.com, Inc. or its affiliates.

//! Provides borrowed implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! Specifically, all implementations are tied to some particular lifetime, generally linked
//! to a parser implementation of some sort or some context from which the borrow can occur.
//! For simple values, the values are inlined (see [`ValueRef`]), but for things that are
//! backed by octets or string data, `&[u8]` and `&str` are used.

use super::{IonElement, IonSequence, IonStruct, IonSymbolToken};
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::value::Builder;
use crate::IonType;
use num_bigint::BigInt;
use std::collections::HashMap;
use std::iter::FromIterator;

/// A borrowed implementation of [`SymbolToken`].
#[derive(Debug, Copy, Clone)]
pub struct SymbolTokenRef<'val> {
    text: Option<&'val str>,
    local_sid: Option<SymbolId>,
}

impl<'val> SymbolTokenRef<'val> {
    fn new(text: Option<&'val str>, local_sid: Option<SymbolId>) -> Self {
        Self { text, local_sid }
    }
}

/// Constructs a [`SymbolTokenRef`] with unknown text and a local ID.
/// A common case for binary parsing (though technically relevant in text).
#[inline]
pub fn local_sid_token<'val>(local_sid: SymbolId) -> SymbolTokenRef<'val> {
    SymbolTokenRef::new(None, Some(local_sid))
}

/// Constructs a [`SymbolTokenRef`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token(text: &str) -> SymbolTokenRef {
    SymbolTokenRef::new(Some(text), None)
}

impl<'val> PartialEq for SymbolTokenRef<'val> {
    fn eq(&self, other: &Self) -> bool {
        match (self.text(), other.text()) {
            // SymbolTokenRef is a resolved symbol; if there's no text, it's because the symbol
            // explicitly has undefined text.
            (Some(text), Some(other_text)) => text == other_text,
            (None, None) => true,
            _ => false,
        }
    }
}

impl<'val> Eq for SymbolTokenRef<'val> {}

impl<'val> From<&'val str> for SymbolTokenRef<'val> {
    fn from(text: &'val str) -> Self {
        Self::new(Some(text), None)
    }
}

impl<'val> IonSymbolToken for SymbolTokenRef<'val> {
    fn text(&self) -> Option<&str> {
        self.text
    }

    fn symbol_id(&self) -> Option<usize> {
        self.local_sid
    }

    fn with_text(self, text: &'static str) -> Self {
        SymbolTokenRef::new(Some(text), self.local_sid)
    }

    fn with_symbol_id(self, local_sid: SymbolId) -> Self {
        SymbolTokenRef::new(self.text, Some(local_sid))
    }

    fn text_token(text: &'static str) -> Self {
        SymbolTokenRef::new(Some(text), None)
    }

    fn symbol_id_token(local_sid: usize) -> Self {
        SymbolTokenRef::new(None, Some(local_sid))
    }
}

/// A borrowed implementation of [`Builder`].
impl<'val> Builder for ElementRef<'val> {
    type Element = ElementRef<'val>;
    type SymbolToken = SymbolTokenRef<'val>;
    type Sequence = SequenceRef<'val>;
    type Struct = StructRef<'val>;

    fn new_null(e_type: IonType) -> Self::Element {
        ValueRef::Null(e_type).into()
    }

    fn new_bool(bool: bool) -> Self::Element {
        ValueRef::Boolean(bool).into()
    }

    fn new_string(str: &'static str) -> Self::Element {
        ValueRef::String(str).into()
    }

    fn new_symbol(sym: Self::SymbolToken) -> Self::Element {
        ValueRef::Symbol(sym).into()
    }

    fn new_i64(int: i64) -> Self::Element {
        ValueRef::Integer(Integer::I64(int)).into()
    }

    fn new_big_int(big_int: BigInt) -> Self::Element {
        ValueRef::Integer(Integer::BigInt(big_int)).into()
    }

    fn new_decimal(decimal: Decimal) -> Self::Element {
        ValueRef::Decimal(decimal).into()
    }

    fn new_timestamp(timestamp: Timestamp) -> Self::Element {
        ValueRef::Timestamp(timestamp).into()
    }

    fn new_f64(float: f64) -> Self::Element {
        ValueRef::Float(float).into()
    }

    fn new_clob(bytes: &'static [u8]) -> Self::Element {
        ValueRef::Clob(bytes).into()
    }

    fn new_blob(bytes: &'static [u8]) -> Self::Element {
        ValueRef::Blob(bytes).into()
    }

    fn new_list<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        ValueRef::List(seq.into_iter().collect()).into()
    }

    fn new_sexp<I: IntoIterator<Item = Self::Element>>(seq: I) -> Self::Element {
        ValueRef::SExpression(seq.into_iter().collect()).into()
    }

    fn new_struct<
        K: Into<Self::SymbolToken>,
        V: Into<Self::Element>,
        I: IntoIterator<Item = (K, V)>,
    >(
        structure: I,
    ) -> Self::Element {
        ValueRef::Struct(structure.into_iter().collect()).into()
    }
}

/// A borrowed implementation of [`Sequence`].
#[derive(Debug, Clone)]
pub struct SequenceRef<'val> {
    children: Vec<ElementRef<'val>>,
}

impl<'val> SequenceRef<'val> {
    pub fn new(children: Vec<ElementRef<'val>>) -> Self {
        Self { children }
    }
}

impl<'val> FromIterator<ElementRef<'val>> for SequenceRef<'val> {
    /// Returns an borrowed sequence from the given iterator of elements.
    fn from_iter<I: IntoIterator<Item = ElementRef<'val>>>(iter: I) -> Self {
        let mut children: Vec<ElementRef> = Vec::new();
        for elem in iter {
            children.push(elem);
        }
        Self { children }
    }
}

impl<'val> IonSequence for SequenceRef<'val> {
    type Element = ElementRef<'val>;

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

impl<'val> PartialEq for SequenceRef<'val> {
    fn eq(&self, other: &Self) -> bool {
        self.children == other.children
    }
}

impl<'val> Eq for SequenceRef<'val> {}

/// A borrowed implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct StructRef<'val> {
    text_fields: HashMap<String, Vec<(SymbolTokenRef<'val>, ElementRef<'val>)>>,
    no_text_fields: Vec<(SymbolTokenRef<'val>, ElementRef<'val>)>,
}

impl<'val> StructRef<'val> {
    fn eq_text_fields(&self, other: &Self) -> bool {
        // check if both the text_fields have same (field_name,value) pairs
        self.text_fields.iter().all(|(key, value)| {
            value
                .iter()
                .all(|(_my_s, my_v)| other.get_all(key).any(|other_v| my_v == other_v))
                && value.len() == other.get_all(key).count()
        })
    }

    fn eq_no_text_fields(&self, other: &Self) -> bool {
        // check if both the no_text_fields are same values
        self.no_text_fields.iter().all(|(my_k, my_v)| {
            other
                .no_text_fields
                .iter()
                .any(|(other_k, other_v)| my_k == other_k && my_v == other_v)
        })
    }
}

impl<'val, K, V> FromIterator<(K, V)> for StructRef<'val>
where
    K: Into<SymbolTokenRef<'val>>,
    V: Into<ElementRef<'val>>,
{
    /// Returns a borrowed struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut text_fields: HashMap<String, Vec<(SymbolTokenRef, ElementRef)>> = HashMap::new();
        let mut no_text_fields: Vec<(SymbolTokenRef, ElementRef)> = Vec::new();

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

impl<'val> IonStruct for StructRef<'val> {
    type FieldName = SymbolTokenRef<'val>;
    type Element = ElementRef<'val>;

    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a> {
        // flattens the text_fields HashMap and chains with no_text_fields
        // to return all fields with iterator
        Box::new(
            self.text_fields
                .values()
                .flatten()
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

impl<'val> PartialEq for StructRef<'val> {
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

impl<'val> Eq for StructRef<'val> {}

// TODO replace the references with `Cow` and bridge to the owned APIs for mutability

/// Variants for all borrowed version _values_ within an [`Element`].
#[derive(Debug, Clone, PartialEq)]
pub enum ValueRef<'val> {
    Null(IonType),
    Integer(Integer),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(&'val str),
    Symbol(SymbolTokenRef<'val>),
    Boolean(bool),
    Blob(&'val [u8]),
    Clob(&'val [u8]),
    SExpression(SequenceRef<'val>),
    List(SequenceRef<'val>),
    Struct(StructRef<'val>),
    // TODO fill this in with the rest...
}

/// A borrowed implementation of [`Element`]
#[derive(Debug, Clone)]
pub struct ElementRef<'val> {
    annotations: Vec<SymbolTokenRef<'val>>,
    value: ValueRef<'val>,
}

impl<'val> ElementRef<'val> {
    pub fn new(annotations: Vec<SymbolTokenRef<'val>>, value: ValueRef<'val>) -> Self {
        Self { annotations, value }
    }
}

impl<'val> PartialEq for ElementRef<'val> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.annotations == other.annotations
    }
}

impl<'val> Eq for ElementRef<'val> {}

impl<'val> From<ValueRef<'val>> for ElementRef<'val> {
    /// Constructs an [`ElementRef`] without annotations from this value.
    fn from(val: ValueRef<'val>) -> Self {
        Self::new(vec![], val)
    }
}

impl<'val> From<IonType> for ElementRef<'val> {
    fn from(ion_type: IonType) -> Self {
        ValueRef::Null(ion_type).into()
    }
}

impl<'val> From<i64> for ElementRef<'val> {
    fn from(i64_val: i64) -> Self {
        ValueRef::Integer(Integer::I64(i64_val)).into()
    }
}

impl<'val> From<BigInt> for ElementRef<'val> {
    fn from(big_int_val: BigInt) -> Self {
        ValueRef::Integer(Integer::BigInt(big_int_val)).into()
    }
}

impl<'val> From<f64> for ElementRef<'val> {
    fn from(f64_val: f64) -> Self {
        ValueRef::Float(f64_val).into()
    }
}

impl<'val> From<Decimal> for ElementRef<'val> {
    fn from(decimal_val: Decimal) -> Self {
        ValueRef::Decimal(decimal_val).into()
    }
}

impl<'val> From<Timestamp> for ElementRef<'val> {
    fn from(timestamp_val: Timestamp) -> Self {
        ValueRef::Timestamp(timestamp_val).into()
    }
}

impl<'val> From<bool> for ElementRef<'val> {
    fn from(bool_val: bool) -> Self {
        ValueRef::Boolean(bool_val).into()
    }
}

impl<'val> From<&'val str> for ElementRef<'val> {
    fn from(string_val: &'val str) -> Self {
        ValueRef::String(string_val).into()
    }
}

impl<'val> From<SymbolTokenRef<'val>> for ElementRef<'val> {
    fn from(sym_val: SymbolTokenRef<'val>) -> Self {
        ValueRef::Symbol(sym_val).into()
    }
}

impl<'val> From<StructRef<'val>> for ElementRef<'val> {
    fn from(struct_val: StructRef<'val>) -> Self {
        ValueRef::Struct(struct_val).into()
    }
}

impl<'val> IonElement for ElementRef<'val> {
    type SymbolToken = SymbolTokenRef<'val>;
    type Sequence = SequenceRef<'val>;
    type Struct = StructRef<'val>;
    type Builder = ElementRef<'val>;

    fn ion_type(&self) -> IonType {
        use ValueRef::*;
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
        ElementRef::new(annotations.into_iter().collect(), self.value)
    }

    fn has_annotation(&self, annotation: &str) -> bool {
        self.annotations
            .iter()
            .any(|a| a.text() == Some(annotation))
    }

    fn is_null(&self) -> bool {
        matches!(&self.value, ValueRef::Null(_))
    }

    fn as_integer(&self) -> Option<&Integer> {
        match &self.value {
            ValueRef::Integer(i) => Some(i),
            _ => None,
        }
    }

    fn as_f64(&self) -> Option<f64> {
        match &self.value {
            ValueRef::Float(f) => Some(*f),
            _ => None,
        }
    }

    fn as_decimal(&self) -> Option<&Decimal> {
        match &self.value {
            ValueRef::Decimal(d) => Some(d),
            _ => None,
        }
    }

    fn as_timestamp(&self) -> Option<&Timestamp> {
        match &self.value {
            ValueRef::Timestamp(t) => Some(t),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match &self.value {
            ValueRef::String(text) => Some(*text),
            ValueRef::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    fn as_sym(&self) -> Option<&Self::SymbolToken> {
        match &self.value {
            ValueRef::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match &self.value {
            ValueRef::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    fn as_bytes(&self) -> Option<&[u8]> {
        match &self.value {
            ValueRef::Blob(bytes) | ValueRef::Clob(bytes) => Some(bytes),
            _ => None,
        }
    }

    fn as_sequence(&self) -> Option<&Self::Sequence> {
        match &self.value {
            ValueRef::SExpression(seq) | ValueRef::List(seq) => Some(seq),
            _ => None,
        }
    }

    fn as_struct(&self) -> Option<&Self::Struct> {
        match &self.value {
            ValueRef::Struct(structure) => Some(structure),
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
            ElementRef::new_string("hello"),
            "hello".into()
        ),
        case::sym_with_text(
            ElementRef::new_symbol(text_token("hello")),
            text_token("hello").into()
        ),
        case::struct_(
            ElementRef::new_struct(vec![("greetings", ElementRef::from(ValueRef::String("hello")))].into_iter()),
            StructRef::from_iter(vec![("greetings", ElementRef::from(ValueRef::String("hello")))].into_iter()).into()
        ),
    )]
    fn owned_element_accessors(elem1: ElementRef, elem2: ElementRef) {
        // assert if both the element construction creates the same element
        assert_eq!(elem1, elem2);
    }
}
