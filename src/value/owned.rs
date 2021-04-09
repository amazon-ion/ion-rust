// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{AnyInt, Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
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

    /// Decorates the [`OwnedSymbolToken`] with text.
    pub fn with_text<T: Into<Rc<str>>>(mut self, text: T) -> Self {
        self.text = Some(text.into());
        self
    }

    /// Decorates the [`OwnedSymbolToken`] with a local ID.
    pub fn with_local_sid(mut self, local_sid: SymbolId) -> Self {
        self.local_sid = Some(local_sid);
        self
    }

    /// Decorates the [`OwnedSymbolToken`] with an [`OwnedImportSource`].
    pub fn with_source<T: Into<Rc<str>>>(mut self, table: T, sid: SymbolId) -> Self {
        self.source = Some(OwnedImportSource::new(table, sid));
        self
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
        if other.text != None && self.text != None {
            other.text == self.text
        } else {
            self.source == other.source
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

impl PartialEq for OwnedStruct {
    fn eq(&self, other: &Self) -> bool {
        for (key, value) in &self.text_fields {
            if other.get_all(key).ne(value.iter().map(|(_s, v)| v)) {
                return false;
            }
        }
        true
    }
}

impl Eq for OwnedStruct {}

/// Variants for all owned version _values_ within an [`Element`].
#[derive(Debug, Clone, PartialEq)]
pub enum OwnedValue {
    Null(IonType),
    Integer(AnyInt),
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

impl Element for OwnedElement {
    type SymbolToken = OwnedSymbolToken;
    type Sequence = OwnedSequence;
    type Struct = OwnedStruct;

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
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::value::{AnyInt, Element, IntAccess, SymbolToken};
    use crate::IonType;
    use chrono::*;
    use rstest::*;
    use std::iter::{once, Once};

    /// Makes a timestamp from an RFC-3339 string and panics if it can't
    fn make_timestamp<T: AsRef<str>>(text: T) -> Timestamp {
        DateTime::parse_from_rfc3339(text.as_ref()).unwrap().into()
    }

    // TODO consider refactoring in a common generic form for the `borrowed` module.

    /// Models the operations on `Element` that we want to test.
    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    enum ElemOp {
        IsNull,
        AsBool,
        AsAnyInt,
        AsF64,
        AsDecimal,
        AsTimestamp,
        AsStr,
        AsSym,
        AsBytes,
        AsSequence,
        AsStruct,
    }

    impl IntoIterator for ElemOp {
        type Item = ElemOp;
        type IntoIter = <Once<ElemOp> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            once(self)
        }
    }

    use std::collections::HashSet;
    use ElemOp::*;

    type ElemAssertFunc = dyn Fn(&OwnedElement) -> ();

    #[rstest]
    #[case::annotations_with_elem(OwnedElement::new(["foo","bar","baz"].iter().map(|s| (*s).into()).collect(), OwnedValue::Boolean(true)), vec![OwnedSymbolToken::from("foo"), OwnedSymbolToken::from("bar"), OwnedSymbolToken::from("baz")])]
    #[case::annotations_with_elem(OwnedValue::Boolean(true).into(), vec![])]
    fn annotations_with_element(
        #[case] elem: OwnedElement,
        #[case] annotations: Vec<OwnedSymbolToken>,
    ) {
        let actual: Vec<&OwnedSymbolToken> = elem.annotations().map(|tok| tok).collect();
        let expected: Vec<&OwnedSymbolToken> = annotations.iter().collect();
        assert_eq!(actual, expected);
    }

    #[rstest(
        val, ion_type, valid_ops_iter, op_assert,
        case::null(
            OwnedValue::Null(IonType::Null),
            IonType::Null,
            IsNull,
            &|e: &OwnedElement| assert_eq!(true, e.is_null())
        ),
        // TODO more null testing (probably its own fixture)
        case::bool(
            OwnedValue::Boolean(true),
            IonType::Boolean,
            AsBool,
            &|e: &OwnedElement| assert_eq!(Some(true), e.as_bool())
        ),
        case::i64(
            OwnedValue::Integer(AnyInt::I64(100)),
            IonType::Integer,
            AsAnyInt,
            &|e: &OwnedElement| {
                assert_eq!(Some(&AnyInt::I64(100)), e.as_any_int());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(None, e.as_big_int());
            }
        ),
        // TODO a BigInt test case
        case::f64(
            OwnedValue::Float(16.0),
            IonType::Float,
            AsF64,
            &|e: &OwnedElement| assert_eq!(Some(16.0), e.as_f64())
        ),
        case::decimal(
            OwnedValue::Decimal(Decimal::new(8, 3)),
            IonType::Decimal,
            AsDecimal,
            &|e: &OwnedElement| assert_eq!(Some(&Decimal::new(80, 2)), e.as_decimal())
        ),
        case::timestamp(
            OwnedValue::Timestamp(make_timestamp("2014-10-16T12:01:00-00:00")),
            IonType::Timestamp,
            AsTimestamp,
            &|e: &OwnedElement| {
                assert_eq!(Some(&make_timestamp("2014-10-16T12:01:00+00:00")), e.as_timestamp());
            }
        ),
        case::str(
            OwnedValue::String("hello".into()),
            IonType::String,
            AsStr,
            &|e: &OwnedElement| assert_eq!(Some("hello"), e.as_str())
        ),
        case::sym_text(
            OwnedValue::Symbol("hello".into()),
            IonType::Symbol,
            vec![AsStr, AsSym],
            &|e: &OwnedElement| {
                assert_eq!(Some("hello"), e.as_str());
                assert_eq!(Some("hello"), e.as_sym().unwrap().text());
            }
        ),
        case::sym_no_text(
            OwnedValue::Symbol(OwnedSymbolToken::new(None, Some(10), Some(OwnedImportSource::new("greetings", 1)))),
            IonType::Symbol,
            vec![AsSym],
            &|e: &OwnedElement| {
                assert_eq!(Some(10), e.as_sym().unwrap().local_sid());
                assert_eq!(Some(&OwnedImportSource::new("greetings", 1)), e.as_sym().unwrap().source());
            }
        ),
        case::blob(
            OwnedValue::Blob("world".as_bytes().into()),
            IonType::Blob,
            AsBytes,
            &|e: &OwnedElement| {
                assert_eq!(Some("world".as_bytes()), e.as_bytes());
            }
        ),
        case::clob(
            OwnedValue::Clob("goodbye".as_bytes().into()),
            IonType::Clob,
            AsBytes,
            &|e: &OwnedElement| {
                assert_eq!(Some("goodbye".as_bytes()), e.as_bytes());
            }
        ),
        case::list(
            OwnedValue::List(vec![OwnedValue::Boolean(true), OwnedValue::Boolean(false)].into_iter().map(|v| v.into()).collect()),
            IonType::List,
            AsSequence,
            &|e: &OwnedElement| {
                assert_eq!(Some(&vec![OwnedValue::Boolean(true), OwnedValue::Boolean(false)].into_iter().map(|v| v.into()).collect()), e.as_sequence());
            }
        ),
        case::sexp(
            OwnedValue::SExpression(vec![OwnedValue::Boolean(true), OwnedValue::Boolean(false)].into_iter().map(|v| v.into()).collect()),
            IonType::SExpression,
            AsSequence,
            &|e: &OwnedElement| {
                assert_eq!(Some(&vec![OwnedValue::Boolean(true), OwnedValue::Boolean(false)].into_iter().map(|v| v.into()).collect()), e.as_sequence());
            }
        ),
        case::struct_(
            OwnedValue::Struct(vec![("greetings", OwnedElement::from(OwnedValue::String("hello".into())))].into_iter().collect()),
            IonType::Struct,
            AsStruct,
            &|e: &OwnedElement| {
                assert_eq!(Some(&vec![("greetings", OwnedElement::from(OwnedValue::String("hello".into())))].into_iter().collect()), e.as_struct());
            }
        ),
        // TODO consider factoring this out of the value tests to make it more contained
        // TODO consider adding non-equivs for this (really symbol token tests are probably better for this)
        eq_annotations => [
            // trivially empty is equivalent to another empty
            vec![vec![], vec![]],
            // tokens with text
            vec![
                vec![text_token("hello"), text_token("world")],
                // containing local sids only
                vec![
                    text_token("hello").with_local_sid(20),
                    local_sid_token(21).with_text("world"),
                ],
                // mix of local sid, but all with sources
                vec![
                    text_token("hello").with_source("hello_table", 2),
                    text_token("world").with_local_sid(59).with_source("world_table", 200)
                ]
            ],
            // tokens without text
            vec![
                vec![
                    // local sid only with no text are all $0 equivalent
                    local_sid_token(21),
                    // source import table is the comparator for unknown cases
                    local_sid_token(22).with_source("hello_table", 2)
                ],
                vec![
                    local_sid_token(0),
                    local_sid_token(400).with_source("hello_table", 2),
                ],
                vec![
                    local_sid_token(200),
                    text_token("hello").with_source("hello_table", 2),
                ],
                vec![
                    local_sid_token(99),
                    text_token("hello").with_local_sid(500).with_source("hello_table", 2),
                ],
            ],
        ]
    )]
    fn owned_element_accessors<O: IntoIterator<Item = ElemOp>>(
        val: OwnedValue,
        ion_type: IonType,
        valid_ops_iter: O,
        op_assert: &ElemAssertFunc,
        eq_annotations: Vec<Vec<OwnedSymbolToken>>,
    ) {
        // table of negative assertions for each operation
        let neg_table: Vec<(ElemOp, &ElemAssertFunc)> = vec![
            (IsNull, &|e| assert_eq!(false, e.is_null())),
            (AsBool, &|e| assert_eq!(None, e.as_bool())),
            (AsAnyInt, &|e| {
                assert_eq!(None, e.as_any_int());
                assert_eq!(None, e.as_i64());
                assert_eq!(None, e.as_big_int());
            }),
            (AsF64, &|e| assert_eq!(None, e.as_f64())),
            (AsDecimal, &|e| assert_eq!(None, e.as_decimal())),
            (AsTimestamp, &|e| assert_eq!(None, e.as_timestamp())),
            (AsStr, &|e| assert_eq!(None, e.as_str())),
            (AsSym, &|e| assert_eq!(None, e.as_sym())),
            (AsBytes, &|e| assert_eq!(None, e.as_bytes())),
            (AsSequence, &|e| assert_eq!(None, e.as_sequence())),
            (AsStruct, &|e| assert_eq!(None, e.as_struct())),
        ];

        // produce the table of assertions to operate on, replacing the one specified by
        // the test case
        let valid_ops: HashSet<ElemOp> = valid_ops_iter.into_iter().collect();
        let op_assertions: Vec<&ElemAssertFunc> = neg_table
            .into_iter()
            .filter(|(op, _)| !valid_ops.contains(op))
            .map(|(_, neg_assert)| neg_assert)
            .chain(once(op_assert))
            .collect();

        // construct an element to test
        let elem: OwnedElement = val.into();
        assert_eq!(ion_type, elem.ion_type());

        for assert in op_assertions {
            assert(&elem);
        }

        // assert that a value element as-is is equal to itself
        assert_eq!(elem, elem);

        // use the base value to make annotated versions
        let eq_elems: Vec<OwnedElement> = eq_annotations
            .into_iter()
            .map(|annotations| OwnedElement::new(annotations, elem.value.clone()))
            .collect();

        for left_elem in eq_elems.iter() {
            for right_elem in eq_elems.iter() {
                assert_eq!(left_elem, right_elem);
            }
        }
    }
}
