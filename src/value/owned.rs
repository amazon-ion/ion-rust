// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`IonSymbolToken`], [`IonElement`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use crate::ion_eq::IonEq;
use crate::text::text_formatter::IonValueFormatter;
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::{IonType, Symbol};
use num_bigint::BigInt;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::iter::FromIterator;
use std::rc::Rc;

use crate::symbol_ref::AsSymbolRef;
use crate::value::iterators::{
    ElementsIterator, FieldIterator, FieldValuesIterator, IndexVec, SymbolsIterator,
};

impl Symbol {
    pub fn symbol_id(&self) -> Option<SymbolId> {
        match self.text() {
            Some(_) => None,
            None => Some(0),
        }
    }

    pub fn with_text(self, text: &'static str) -> Self {
        Symbol::owned(text)
    }

    pub fn with_symbol_id(self, _local_sid: SymbolId) -> Self {
        // Because `Symbol` represents a fully resolved symbol...
        if self.text().is_some() {
            // ...if we already have text, we can discard the symbol ID.
            return self;
        }
        // Otherwise, the text is unknown.
        Symbol::unknown_text()
    }

    pub fn text_token(text: &'static str) -> Self {
        Symbol::owned(text)
    }

    pub fn symbol_id_token(_local_sid: SymbolId) -> Self {
        // Because `Symbol` represents a fully resolved symbol, constructing one from a symbol ID
        // alone means that it has no defined text and is therefore equivalent to SID 0.
        Symbol::unknown_text()
    }
}

/// Constructs a [`Symbol`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token(text: &str) -> Symbol {
    Symbol::owned(text)
}

/// An owned implementation of [`Builder`].
impl Element {
    fn new_null(e_type: IonType) -> Element {
        Value::Null(e_type).into()
    }

    fn new_bool(bool: bool) -> Element {
        Value::Boolean(bool).into()
    }

    fn new_string<A: AsRef<str>>(str: A) -> Element {
        Value::String(str.as_ref().to_owned()).into()
    }

    fn new_symbol(symbol: Symbol) -> Element {
        Value::Symbol(symbol).into()
    }

    fn new_i64(integer: i64) -> Element {
        Value::Integer(Integer::I64(integer)).into()
    }

    fn new_big_int(big_int: BigInt) -> Element {
        Value::Integer(Integer::BigInt(big_int)).into()
    }

    fn new_decimal(decimal: Decimal) -> Element {
        Value::Decimal(decimal).into()
    }

    fn new_timestamp(timestamp: Timestamp) -> Element {
        Value::Timestamp(timestamp).into()
    }

    fn new_f64(float: f64) -> Element {
        Value::Float(float).into()
    }

    fn new_clob(bytes: &[u8]) -> Element {
        Value::Clob(bytes.into()).into()
    }

    fn new_blob(bytes: &[u8]) -> Element {
        Value::Blob(bytes.into()).into()
    }

    fn new_list<I: IntoIterator<Item = Element>>(seq: I) -> Element {
        Value::List(seq.into_iter().collect()).into()
    }

    fn new_sexp<I: IntoIterator<Item = Element>>(seq: I) -> Element {
        Value::SExpression(seq.into_iter().collect()).into()
    }

    fn new_struct<K: Into<Symbol>, V: Into<Element>, I: IntoIterator<Item = (K, V)>>(
        structure: I,
    ) -> Element {
        Value::Struct(structure.into_iter().collect()).into()
    }
}

/// An owned implementation of [`IonSequence`]
#[derive(Debug, Clone)]
pub struct Sequence {
    // TODO: Since we've moved the elements Vec to the heap, we could consider replacing it with a
    //       SmallVec that can store some number of elements (4? 8?) inline. We'd need to benchmark.
    children: Rc<Vec<Element>>,
}

impl Sequence {
    pub fn new(children: Vec<Element>) -> Self {
        Self {
            children: Rc::new(children),
        }
    }
}

impl FromIterator<Element> for Sequence {
    /// Returns an owned sequence from the given iterator of elements.
    fn from_iter<I: IntoIterator<Item = Element>>(iter: I) -> Self {
        let mut children: Vec<Element> = Vec::new();
        for elem in iter {
            children.push(elem);
        }
        Self {
            children: Rc::new(children),
        }
    }
}

impl Sequence {
    pub fn iter(&self) -> ElementsIterator<'_> {
        ElementsIterator::new(&self.children)
    }

    pub fn get(&self, index: usize) -> Option<&Element> {
        self.children.get(index)
    }

    pub fn len(&self) -> usize {
        self.children.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl PartialEq for Sequence {
    fn eq(&self, other: &Self) -> bool {
        self.children == other.children
    }
}

impl Eq for Sequence {}

// This collection is broken out into its own type to allow instances of it to be shared with Rc.
#[derive(Debug)]
struct Fields {
    // Key/value pairs in the order they were inserted
    by_index: Vec<(Symbol, Element)>,
    // Maps symbols to a list of indexes where values may be found in `by_index` above
    by_name: HashMap<Symbol, IndexVec>,
}

impl Fields {
    /// Gets all of the indexes that contain a value associated with the given field name.
    fn get_indexes<A: AsSymbolRef>(&self, field_name: A) -> Option<&IndexVec> {
        field_name
            .as_symbol_ref()
            .text()
            .map(|text| {
                // If the symbol has defined text, look it up by &str
                self.by_name.get(text)
            })
            .unwrap_or_else(|| {
                // Otherwise, construct a (cheap, stack-allocated) Symbol with unknown text...
                let symbol = Symbol::unknown_text();
                // ...and use the unknown text symbol to look up matching field values
                self.by_name.get(&symbol)
            })
    }

    /// Iterates over the values found at the specified indexes.
    fn get_values_at_indexes<'a>(&'a self, indexes: &'a IndexVec) -> FieldValuesIterator<'a> {
        FieldValuesIterator {
            current: 0,
            indexes: Some(indexes),
            by_index: &self.by_index,
        }
    }

    /// Gets the last value in the Struct that is associated with the specified field name.
    ///
    /// Note that the Ion data model views a struct as a bag of (name, value) pairs and does not
    /// have a notion of field ordering. In most use cases, field names are distinct and the last
    /// appearance of a field in the struct's serialized form will have been the _only_ appearance.
    /// If a field name appears more than once, this method makes the arbitrary decision to return
    /// the value associated with the last appearance. If your application uses structs that repeat
    /// field names, you are encouraged to use [get_all] instead.
    fn get_last<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.get_indexes(field_name)
            .and_then(|indexes| indexes.last())
            .and_then(|index| self.by_index.get(*index))
            .map(|(_name, value)| value)
    }

    /// Iterates over all of the values associated with the given field name.
    fn get_all<A: AsSymbolRef>(&self, field_name: A) -> FieldValuesIterator {
        let indexes = self.get_indexes(field_name);
        FieldValuesIterator {
            current: 0,
            indexes,
            by_index: &self.by_index,
        }
    }

    /// Iterates over all of the (field name, field value) pairs in the struct.
    fn iter(&self) -> impl Iterator<Item = &(Symbol, Element)> {
        self.by_index.iter()
    }
}

/// An owned implementation of [`IonStruct`]
#[derive(Debug, Clone)]
pub struct Struct {
    fields: Rc<Fields>,
}

impl Struct {
    /// Returns an iterator over the field name/value pairs in this Struct.
    pub fn fields(&self) -> impl Iterator<Item = (&Symbol, &Element)> {
        self.fields
            .iter()
            // Here we convert from &(name, value) to (&name, &value).
            // The former makes a stronger assertion about how the data is being stored. We don't
            // want that to be a mandatory part of the public API.
            .map(|(name, element)| (name, element))
    }

    fn fields_eq(&self, other: &Self) -> bool {
        // For each field name in `self`, get the list of indexes that contain a value with that name.
        for (field_name, field_value_indexes) in &self.fields.by_name {
            let other_value_indexes = match other.fields.get_indexes(field_name) {
                Some(indexes) => indexes,
                // The other struct doesn't have a field with this name so they're not equal.
                None => return false,
            };

            if field_value_indexes.len() != other_value_indexes.len() {
                // The other struct has fields with the same name, but a different number of them.
                return false;
            }

            for field_value in self.fields.get_values_at_indexes(field_value_indexes) {
                if other
                    .fields
                    .get_values_at_indexes(other_value_indexes)
                    .all(|other_value| !field_value.ion_eq(other_value))
                {
                    // Couldn't find an equivalent field in the other struct
                    return false;
                }
            }
        }

        // If all of the above conditions hold, the two structs are equal.
        true
    }

    /// Returns the number of fields in this Struct.
    pub fn len(&self) -> usize {
        self.fields.by_index.len()
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
        let mut by_index: Vec<(Symbol, Element)> = Vec::new();
        let mut by_name: HashMap<Symbol, IndexVec> = HashMap::new();
        for (field_name, field_value) in iter {
            let field_name = field_name.into();
            let field_value = field_value.into();

            by_name
                .entry(field_name.clone())
                .or_insert_with(IndexVec::new)
                .push(by_index.len());
            by_index.push((field_name, field_value));
        }

        let fields = Rc::new(Fields { by_index, by_name });
        Self { fields }
    }
}

impl Struct {
    pub fn iter(&self) -> FieldIterator<'_> {
        FieldIterator::new(&self.fields.by_index)
    }

    pub fn get<A: AsSymbolRef>(&self, field_name: A) -> Option<&Element> {
        self.fields.get_last(field_name)
    }

    pub fn get_all<A: AsSymbolRef>(&self, field_name: A) -> FieldValuesIterator<'_> {
        self.fields.get_all(field_name)
    }
}

impl PartialEq for Struct {
    fn eq(&self, other: &Self) -> bool {
        // check if both fields have same length
        self.len() == other.len()
            // we need to test equality in both directions for both fields
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

/// Variants for all owned version _values_ within an [`IonElement`].
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

/// An owned implementation of [`IonElement`]
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

        match &self.value {
            Value::Null(ion_type) => ivf.format_null(*ion_type),
            Value::Boolean(bool) => ivf.format_bool(*bool),
            Value::Integer(integer) => ivf.format_integer(integer),
            Value::Float(float) => ivf.format_float(*float),
            Value::Decimal(decimal) => ivf.format_decimal(decimal),
            Value::Timestamp(timestamp) => ivf.format_timestamp(timestamp),
            Value::Symbol(symbol) => ivf.format_symbol(symbol),
            Value::String(string) => ivf.format_string(string),
            Value::Clob(clob) => ivf.format_clob(clob),
            Value::Blob(blob) => ivf.format_blob(blob),
            Value::Struct(struct_) => ivf.format_struct(struct_),
            Value::SExpression(sexp) => ivf.format_sexp(sexp),
            Value::List(list) => ivf.format_list(list),
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

impl From<Integer> for Element {
    fn from(integer_val: Integer) -> Self {
        match integer_val {
            Integer::I64(i64_int) => i64_int.into(),
            Integer::BigInt(big_int) => big_int.into(),
        }
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

impl From<&str> for Element {
    fn from(string_val: &str) -> Self {
        Value::String(string_val.to_owned()).into()
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

// TODO: explain motivation (static Rc no good)
// TODO: better name?
// Wraps a standard library slice iterator in an `Option`.
struct ElementDataIterator<'a, T: 'a> {
    values: Option<std::slice::Iter<'a, T>>,
}

impl<'a, T: 'a> ElementDataIterator<'a, T> {
    fn new<'f, V: 'f>(data: &'f [V]) -> ElementDataIterator<'f, V> {
        ElementDataIterator {
            values: Some(data.iter()),
        }
    }

    fn empty() -> Self {
        ElementDataIterator { values: None }
    }
}

impl<'a, T: 'a> Iterator for ElementDataIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.values.as_mut().and_then(|iter| iter.next())
    }
}

impl Element {
    pub fn ion_type(&self) -> IonType {
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

    pub fn annotations(&self) -> SymbolsIterator<'_> {
        SymbolsIterator::new(&self.annotations)
    }

    pub fn with_annotations<S: Into<Symbol>, I: IntoIterator<Item = S>>(
        self,
        annotations: I,
    ) -> Self {
        let annotations: Vec<Symbol> = annotations.into_iter().map(|i| i.into()).collect();
        Element::new(annotations, self.value)
    }

    pub fn has_annotation(&self, annotation: &str) -> bool {
        self.annotations
            .iter()
            .any(|a| a.text() == Some(annotation))
    }

    pub fn is_null(&self) -> bool {
        matches!(&self.value, Value::Null(_))
    }

    pub fn as_integer(&self) -> Option<&Integer> {
        match &self.value {
            Value::Integer(i) => Some(i),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<f64> {
        match &self.value {
            Value::Float(f) => Some(*f),
            _ => None,
        }
    }

    pub fn as_decimal(&self) -> Option<&Decimal> {
        match &self.value {
            Value::Decimal(d) => Some(d),
            _ => None,
        }
    }

    pub fn as_timestamp(&self) -> Option<&Timestamp> {
        match &self.value {
            Value::Timestamp(t) => Some(t),
            _ => None,
        }
    }

    pub fn as_text(&self) -> Option<&str> {
        match &self.value {
            Value::String(text) => Some(text),
            Value::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match &self.value {
            Value::String(text) => Some(text),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<&Symbol> {
        match &self.value {
            Value::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    pub fn as_boolean(&self) -> Option<bool> {
        match &self.value {
            Value::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_lob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) | Value::Clob(bytes) => Some(bytes),
            _ => None,
        }
    }

    pub fn as_blob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) => Some(bytes),
            _ => None,
        }
    }

    pub fn as_clob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Clob(bytes) => Some(bytes),
            _ => None,
        }
    }

    pub fn as_sequence(&self) -> Option<&Sequence> {
        match &self.value {
            Value::SExpression(seq) | Value::List(seq) => Some(seq),
            _ => None,
        }
    }

    pub fn as_struct(&self) -> Option<&Struct> {
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
