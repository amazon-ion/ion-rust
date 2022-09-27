// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{IonElement, IonSequence, IonStruct, IonSymbolToken};
use crate::ion_eq::IonEq;
use crate::text::text_formatter::IonValueFormatter;
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::value::Builder;
use crate::{IonType, Symbol};
use hashlink::LinkedHashMap;
use num_bigint::BigInt;
use std::fmt::{Display, Formatter};
use std::iter::FromIterator;

use crate::symbol_ref::AsSymbolRef;
use smallvec::SmallVec;

impl IonSymbolToken for Symbol {
    fn text(&self) -> Option<&str> {
        self.text()
    }

    fn symbol_id(&self) -> Option<SymbolId> {
        match self.text() {
            Some(_) => None,
            None => Some(0),
        }
    }

    fn with_text(self, text: &'static str) -> Self {
        Symbol::owned(text)
    }

    fn with_symbol_id(self, _local_sid: SymbolId) -> Self {
        // Because `Symbol` represents a fully resolved symbol...
        if self.text().is_some() {
            // ...if we already have text, we can discard the symbol ID.
            return self;
        }
        // Otherwise, the text is unknown.
        Symbol::unknown_text()
    }

    fn text_token(text: &'static str) -> Self {
        Symbol::owned(text)
    }

    fn symbol_id_token(_local_sid: SymbolId) -> Self {
        // Because `Symbol` represents a fully resolved symbol, constructing one from a symbol ID
        // alone means that it has no defined text and is therefore equivalent to SID 0.
        Symbol::unknown_text()
    }
}

/// Constructs a [`SymbolTokenRef`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token(text: &str) -> Symbol {
    Symbol::owned(text)
}

/// An owned implementation of [`Builder`].
impl Builder for Element {
    type Element = Element;
    type SymbolToken = Symbol;
    type Sequence = Sequence;
    type Struct = Struct;

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

/// An owned implementation of [`IonStruct`]
#[derive(Debug, Clone)]
pub struct Struct {
    // A mapping of field name to any values associated with that name.
    // If a field name is repeated, each value will be in the associated SmallVec.
    // Since repeated field names are not common, we store the values in a SmallVec;
    // the first value will be stored directly in the map while additional values will
    // be stored elsewhere on the heap.
    fields: LinkedHashMap<Symbol, SmallVec<[Element; 1]>>,
    // `fields.len()` will only tell us the number of *distinct* field names. If the struct
    // contains any repeated field names, it will be an under-count. Therefore, we track the number
    // of fields separately.
    number_of_fields: usize,
}

impl Struct {
    /// Returns an iterator over the field name/value pairs in this Struct.
    pub fn fields(&self) -> impl Iterator<Item = (&Symbol, &Element)> {
        self.fields
            .iter()
            .flat_map(|(name, values)| values.iter().map(move |value| (name, value)))
    }

    fn fields_eq(&self, other: &Self) -> bool {
        // For each (field name, field value list) in `self`...
        for (field_name, field_values) in &self.fields {
            // ...get the corresponding field value list from `other`.
            let other_values = match other.fields.get(field_name) {
                // If there's no such list, they're not equal.
                None => return false,
                Some(values) => values,
            };

            // If `other` has a corresponding list but it's a different length, they're not equal.
            if field_values.len() != other_values.len() {
                return false;
            }

            // If any of the values in `self`'s value list are not also in `other`'s value list,
            // they're not equal.
            if field_values.iter().any(|value| {
                other_values
                    .iter()
                    .all(|other_value| !value.ion_eq(other_value))
            }) {
                return false;
            }
        }

        // If all of the above conditions hold, the two structs are equal.
        true
    }

    /// Returns the number of fields in this Struct.
    pub fn len(&self) -> usize {
        self.number_of_fields
    }

    /// Returns `true` if this struct has zero fields.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K, V> FromIterator<(K, V)> for Struct
where
    K: Into<Symbol>,
    V: Into<Element>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut fields: LinkedHashMap<Symbol, SmallVec<[Element; 1]>> = LinkedHashMap::new();
        let mut number_of_fields: usize = 0;

        for (field_name, field_value) in iter {
            let field_name = field_name.into();
            let field_value = field_value.into();

            fields
                .entry(field_name)
                .or_insert_with(SmallVec::new)
                .push(field_value);

            number_of_fields += 1;
        }

        Self {
            fields,
            number_of_fields,
        }
    }
}

impl IonStruct for Struct {
    type FieldName = Symbol;
    type Element = Element;

    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a> {
        Box::new(self.fields())
    }

    fn get<A: AsSymbolRef>(&self, field_name: A) -> Option<&Self::Element> {
        match field_name.as_symbol_ref().text() {
            None => {
                // Build a cheap, stack-allocated `Symbol` that represents unknown text
                let symbol = Symbol::unknown_text();
                // Use the unknown text symbol to look up matching field values
                self.fields.get(&symbol)?.last()
            }
            Some(text) => {
                // Otherwise, look it up by text
                self.fields.get(text)?.last()
            }
        }
    }

    fn get_all<'a, A: AsSymbolRef>(
        &'a self,
        field_name: A,
    ) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        // TODO: This method has to box its return value, which is why we're not re-using it
        //       for the implementation of the `get` method. Once we remove the `Box`
        //       (via GATs or RPITIT?) we can have `get` call `get_all`.
        let values = match field_name.as_symbol_ref().text() {
            None => {
                // Build a cheap, stack-allocated `Symbol` that represents unknown text
                let symbol = Symbol::unknown_text();
                self.fields.get(&symbol)
            }
            Some(text) => {
                // Otherwise, look it up by text
                self.fields.get(text)
            }
        };

        match values {
            Some(values) => Box::new(values.iter()),
            None => Box::new(None.iter()), // An empty iterator
        }
    }
}

impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        // check if both text_fields and no_text_fields have same length
        self.len() == other.len()
            // we need to test equality in both directions for both text_fields and no_text_fields
            // A good example for this is annotated vs not annotated values in struct
            //  { a:4, a:4 } vs. { a:4, a:a::4 } // returns true
            //  { a:4, a:a::4 } vs. { a:4, a:4 } // returns false
            && self.fields_eq(other) && other.fields_eq(self)
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
    Symbol(Symbol),
    Boolean(bool),
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    SExpression(Sequence),
    List(Sequence),
    Struct(Struct),
}

/// An owned implementation of [`Element`]
#[derive(Debug, Clone)]
pub struct Element {
    annotations: Vec<Symbol>,
    value: Value,
}

impl Element {
    pub fn new(annotations: Vec<Symbol>, value: Value) -> Self {
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

impl From<Symbol> for Element {
    fn from(sym_val: Symbol) -> Self {
        Value::Symbol(sym_val).into()
    }
}

impl From<Struct> for Element {
    fn from(struct_val: Struct) -> Self {
        Value::Struct(struct_val).into()
    }
}

impl IonElement for Element {
    type SymbolToken = Symbol;
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
            Element::new_symbol(Symbol::owned("hello")),
            Symbol::owned("hello").into()
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

    #[rstest(
        container, length,
        case::struct_(
            Element::new_struct(
                vec![
                    ("greetings", Element::from(Value::String("hello".into()))),
                    ("name", Element::from(Value::String("Ion".into())))
                ].into_iter()
            ),
            2
        ),
        case::list(
            Element::new_list(
                vec![
                    Element::from("greetings".to_owned()),
                    Element::from(5),
                    Element::from(true)
                ].into_iter()
            ),
            3
        ),
        case::sexp(
            Element::new_sexp(vec![Element::from(5), Element::from(true)].into_iter()),
            2
        ),
    )]
    fn owned_container_len_test(container: Element, length: usize) {
        match container.ion_type() {
            IonType::List | IonType::SExpression => {
                // check length for given sequence value
                assert_eq!(container.as_sequence().unwrap().len(), length);
            }
            IonType::Struct => {
                // check length for given struct value
                assert_eq!(container.as_struct().unwrap().len(), length);
            }
            _ => {
                unreachable!("This test is only for container type elements")
            }
        }
    }

    #[rstest(
        container, is_empty,
        case::struct_(
                Element::new_struct(
                vec![
                    ("greetings", Element::from(Value::String("hello".into()))),
                    ("name", Element::from(Value::String("Ion".into())))
                ].into_iter()
            ),
            false
        ),
        case::list(
            Element::new_list(
                vec![
                    Element::from("greetings".to_owned()),
                    Element::from(5),
                    Element::from(true)
                ].into_iter()
            ),
            false
        ),
        case::list_empty(
            Element::new_list(vec![].into_iter()),
            true
        ),
        case::sexp(
            Element::new_sexp(vec![Element::from(5), Element::from(true)].into_iter()),
            false
        ),
        case::sexp_empty(
            Element::new_sexp(vec![].into_iter()),
            true
        ),
    )]
    fn owned_container_is_empty_test(container: Element, is_empty: bool) {
        match container.ion_type() {
            IonType::List | IonType::SExpression => {
                // check length for given sequence value
                assert_eq!(container.as_sequence().unwrap().is_empty(), is_empty);
            }
            IonType::Struct => {
                // check length for given struct value
                assert_eq!(container.as_struct().unwrap().is_empty(), is_empty);
            }
            _ => {
                unreachable!("This test is only for container type elements")
            }
        }
    }
}
