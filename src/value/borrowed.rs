// Copyright Amazon.com, Inc. or its affiliates.

//! Provides borrowed implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! Specifically, all implementations are tied to some particular lifetime, generally linked
//! to a parser implementation of some sort or some context from which the borrow can occur.
//! For simple values, the values are inlined (see [`ValueRef`]), but for things that are
//! backed by octets or string data, `&[u8]` and `&str` are used.

use super::{IonElement, IonSequence, IonStruct, IonSymbolToken};
use crate::ion_eq::IonEq;
use crate::symbol_ref::{AsSymbolRef, SymbolRef};
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
use crate::value::iterators::{
    ElementRefIterator, FieldRefIterator, FieldValueRefsIterator, IndexVec, SymbolRefIterator,
};
use crate::value::Builder;
use crate::IonType;
use num_bigint::BigInt;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::rc::Rc;

impl<'a> IonSymbolToken for SymbolRef<'a> {
    fn text(&self) -> Option<&str> {
        self.text()
    }

    fn symbol_id(&self) -> Option<usize> {
        match self.text() {
            Some(_) => None,
            None => Some(0), // unknown text is represented with $0
        }
    }

    fn with_text(self, text: &'static str) -> Self {
        SymbolRef::with_text(text)
    }

    fn with_symbol_id(self, _symbol_id: usize) -> Self {
        // Because `SymbolRef` represents a fully resolved symbol...
        if self.text().is_some() {
            // ...if we already have text, we can discard the symbol ID.
            return self;
        }
        // Otherwise, the text is unknown.
        SymbolRef::with_unknown_text()
    }

    fn text_token(text: &'static str) -> Self {
        SymbolRef::with_text(text)
    }

    fn symbol_id_token(_symbol_id: usize) -> Self {
        // Because `SymbolRef` represents a fully resolved symbol, constructing one from a symbol ID
        // alone means that it has no defined text and is therefore equivalent to SID 0.
        SymbolRef::with_unknown_text()
    }
}

/// Constructs a [`SymbolRef`] with just text.
/// A common case for text and synthesizing tokens.
#[inline]
pub fn text_token(text: &str) -> SymbolRef {
    SymbolRef::with_text(text)
}

/// A borrowed implementation of [`Builder`].
impl<'val> Builder for ElementRef<'val> {
    type Element = ElementRef<'val>;
    type SymbolToken = SymbolRef<'val>;
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
    // TODO: Since we've moved the elements Vec to the heap, we could consider replacing it with a
    //       SmallVec that can store some number of elements (4? 8?) inline. We'd need to benchmark.
    children: Rc<Vec<ElementRef<'val>>>,
}

impl<'val> SequenceRef<'val> {
    pub fn new(children: Vec<ElementRef<'val>>) -> Self {
        Self {
            children: Rc::new(children),
        }
    }
}

impl<'val> FromIterator<ElementRef<'val>> for SequenceRef<'val> {
    /// Returns an borrowed sequence from the given iterator of elements.
    fn from_iter<I: IntoIterator<Item = ElementRef<'val>>>(iter: I) -> Self {
        let mut children: Vec<ElementRef> = Vec::new();
        for elem in iter {
            children.push(elem);
        }
        Self {
            children: Rc::new(children),
        }
    }
}

impl<'val> IonSequence for SequenceRef<'val> {
    type Element = ElementRef<'val>;
    type ElementsIterator<'a> = ElementRefIterator<'a, 'val> where 'val: 'a;

    fn iter(&self) -> Self::ElementsIterator<'_> {
        ElementRefIterator::new(&self.children)
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
    fields: Rc<FieldRefs<'val>>,
}

impl<'val> StructRef<'val> {
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

impl<'val, K, V> FromIterator<(K, V)> for StructRef<'val>
where
    K: Into<SymbolRef<'val>>,
    V: Into<ElementRef<'val>>,
{
    /// Returns a borrowed struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut by_index = Vec::new();
        let mut by_name = HashMap::new();
        for (field_name, field_value) in iter {
            let field_name = field_name.into();
            let field_value = field_value.into();

            by_name
                .entry(field_name.clone())
                .or_insert_with(IndexVec::new)
                .push(by_index.len());
            by_index.push((field_name, field_value));
        }

        let fields = Rc::new(FieldRefs { by_index, by_name });
        Self { fields }
    }
}

// This collection is broken out into its own type to allow instances of it to be shared with Rc.
#[derive(Debug)]
struct FieldRefs<'a> {
    // Key/value pairs in the order they were inserted
    by_index: Vec<(SymbolRef<'a>, ElementRef<'a>)>,
    // Maps symbols to a list of indexes where values may be found in `by_index` above
    by_name: HashMap<SymbolRef<'a>, IndexVec>,
}

impl<'data> FieldRefs<'data> {
    /// Gets all of the indexes that contain a value associated with the given field name.
    fn get_indexes<A: AsSymbolRef>(&self, field_name: A) -> Option<&IndexVec> {
        match field_name.as_symbol_ref().text() {
            // If the provided field name symbol has undefined text...
            None => {
                // ...then build a cheap, stack-allocated `Symbol` that represents unknown text
                let symbol = SymbolRef::with_unknown_text();
                // ...and use the unknown text symbol to look up matching field values
                self.by_name.get(&symbol)
            }
            Some(text) => {
                // Otherwise, look it up by text
                self.by_name.get(text)
            }
        }
    }

    /// Iterates over the values found at the specified indexes.
    fn get_values_at_indexes<'iter>(
        &'iter self,
        indexes: &'iter IndexVec,
    ) -> FieldValueRefsIterator<'iter, 'data> {
        FieldValueRefsIterator {
            current: 0,
            indexes: Some(indexes),
            fields: &self.by_index,
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
    fn get_last<'iter, A: AsSymbolRef>(
        &'iter self,
        field_name: A,
    ) -> Option<&'iter ElementRef<'data>> {
        self.get_indexes(field_name)
            .and_then(|indexes| indexes.last())
            .and_then(|index| self.by_index.get(*index))
            .map(|(_name, value)| value)
    }

    /// Iterates over all of the values associated with the given field name.
    fn get_all<'iter, A: AsSymbolRef>(
        &'iter self,
        field_name: A,
    ) -> FieldValueRefsIterator<'iter, 'data> {
        let indexes = self.get_indexes(field_name);
        FieldValueRefsIterator {
            current: 0,
            indexes,
            fields: &self.by_index,
        }
    }

    /// Iterates over all of the (field name, field value) pairs in the struct.
    fn iter<'iter>(
        &'iter self,
    ) -> impl Iterator<Item = &'iter (SymbolRef<'data>, ElementRef<'data>)> {
        self.by_index.iter()
    }
}

impl<'val> IonStruct for StructRef<'val> {
    type FieldName = SymbolRef<'val>;
    type Element = ElementRef<'val>;
    type FieldsIterator<'a> = FieldRefIterator<'a, 'val> where 'val: 'a;
    type ValuesIterator<'a> = FieldValueRefsIterator<'a, 'val> where 'val: 'a;

    fn iter<'a>(&'a self) -> FieldRefIterator<'a, 'val> {
        // flattens the fields map
        FieldRefIterator::new(&self.fields.by_index)
    }

    fn get<T: AsSymbolRef>(&self, field_name: T) -> Option<&Self::Element> {
        self.fields.get_last(field_name)
    }

    fn get_all<'a, T: AsSymbolRef>(&'a self, field_name: T) -> FieldValueRefsIterator<'a, 'val> {
        self.fields.get_all(field_name)
    }
}

impl<'val> PartialEq for StructRef<'val> {
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

impl<'val> Eq for StructRef<'val> {}

// TODO replace the references with `Cow` and bridge to the owned APIs for mutability

impl<'val> IonEq for SequenceRef<'val> {
    fn ion_eq(&self, other: &Self) -> bool {
        self.children.ion_eq(&other.children)
    }
}

impl<'val> IonEq for ValueRef<'val> {
    fn ion_eq(&self, other: &Self) -> bool {
        use ValueRef::*;
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

impl<'val> IonEq for ElementRef<'val> {
    fn ion_eq(&self, other: &Self) -> bool {
        self.annotations == other.annotations && self.value.ion_eq(&other.value)
    }
}

impl<'val> IonEq for Vec<ElementRef<'val>> {
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

/// Variants for all borrowed version _values_ within an [`Element`].
#[derive(Debug, Clone, PartialEq)]
pub enum ValueRef<'val> {
    Null(IonType),
    Integer(Integer),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(&'val str),
    Symbol(SymbolRef<'val>),
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
    annotations: Vec<SymbolRef<'val>>,
    value: ValueRef<'val>,
}

impl<'val> ElementRef<'val> {
    pub fn new(annotations: Vec<SymbolRef<'val>>, value: ValueRef<'val>) -> Self {
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

impl<'val> From<SymbolRef<'val>> for ElementRef<'val> {
    fn from(sym_val: SymbolRef<'val>) -> Self {
        ValueRef::Symbol(sym_val).into()
    }
}

impl<'val> From<StructRef<'val>> for ElementRef<'val> {
    fn from(struct_val: StructRef<'val>) -> Self {
        ValueRef::Struct(struct_val).into()
    }
}

impl<'val> IonElement for ElementRef<'val> {
    type SymbolToken = SymbolRef<'val>;
    type Sequence = SequenceRef<'val>;
    type Struct = StructRef<'val>;
    type Builder = ElementRef<'val>;
    type AnnotationsIterator<'a> = SymbolRefIterator<'a, 'val> where 'val: 'a;

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

    fn annotations<'a>(&'a self) -> SymbolRefIterator<'a, 'val> {
        SymbolRefIterator::new(&self.annotations)
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
    fn owned_element_accessors<'a>(elem1: ElementRef<'a>, elem2: ElementRef<'a>) {
        // assert if both the element construction creates the same element
        assert_eq!(elem1, elem2);
    }

    #[rstest(
    container, length,
    case::struct_(
        ElementRef::new_struct(
            vec![
                ("greetings", ElementRef::from(ValueRef::String("hello".into()))),
                ("name", ElementRef::from(ValueRef::String("Ion".into())))
            ].into_iter()
        ),
        2
    ),
    case::list(
        ElementRef::new_list(
            vec![
                ElementRef::from("greetings"),
                ElementRef::from(5),
                ElementRef::from(true)
            ].into_iter()
        ),
        3
    ),
        case::sexp(
            ElementRef::new_sexp(vec![ElementRef::from(5), ElementRef::from(true)].into_iter()),
        2
    ),
    )]
    fn borrowed_container_len_test(container: ElementRef, length: usize) {
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
        ElementRef::new_struct(
            vec![
                ("greetings", ElementRef::from(ValueRef::String("hello"))),
                ("name", ElementRef::from(ValueRef::String("Ion")))
            ].into_iter()
        ),
        false
    ),
    case::list(
        ElementRef::new_list(
            vec![
                ElementRef::from("greetings"),
                ElementRef::from(5),
                ElementRef::from(true)
            ].into_iter()
        ),
        false
    ),
    case::list_empty(
        ElementRef::new_list(vec![].into_iter()),
        true
    ),
    case::sexp(
        ElementRef::new_sexp(vec![ElementRef::from(5), ElementRef::from(true)].into_iter()),
        false
    ),
    case::sexp_empty(
        ElementRef::new_sexp(vec![].into_iter()),
        true
    ),
    )]
    fn borrowed_container_is_empty_test(container: ElementRef, is_empty: bool) {
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
