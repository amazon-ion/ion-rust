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

    /// Decorates the [`BorrowedSymbolToken`] with text.
    pub fn with_text(mut self, text: &'val str) -> Self {
        self.text = Some(text);
        self
    }

    /// Decorates the [`BorrowedSymbolToken`] with a local ID.
    pub fn with_local_sid(mut self, local_sid: SymbolId) -> Self {
        self.local_sid = Some(local_sid);
        self
    }

    /// Decorates the [`BorrowedSymbolToken`] with an [`BorrowedImportSource`].
    pub fn with_source(mut self, table: &'val str, sid: SymbolId) -> Self {
        self.source = Some(BorrowedImportSource::new(table, sid));
        self
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
}

/// An borrowed implementation of [`Builder`].
impl<'val> Builder for BorrowedValue<'val> {
    type Element = BorrowedElement<'val>;
    type Sequence = BorrowedSequence<'val>;

    fn new_null(e_type: IonType) -> Self {
        BorrowedValue::Null(e_type)
    }

    fn new_clob(bytes: &'static [u8]) -> Self {
        BorrowedValue::Clob(bytes)
    }

    fn new_blob(bytes: &'static [u8]) -> Self {
        BorrowedValue::Blob(bytes)
    }

    fn new_list(seq: Self::Sequence) -> Self {
        BorrowedValue::List(seq)
    }

    fn new_sexp(seq: Self::Sequence) -> Self {
        BorrowedValue::SExpression(seq)
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
        // check if both the text_fields have same (field_name,value) pairs
        self.text_fields.iter().all(|(key, value)| {
            value.iter().all(|(_my_s, my_v)| {
                other
                    .get_all(key)
                    .find(|other_v| my_v == *other_v)
                    .is_some()
            })
        }) && self.no_text_fields.iter().all(|(my_k, my_v)| {
            // check if both the no_text_fields have same values
            other
                .no_text_fields
                .iter()
                .find(|(other_k, other_v)| my_k == other_k && my_v == other_v)
                .is_some()
        })
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
    type Builder = BorrowedValue<'val>;

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
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::value::{AnyInt, Element, IntAccess, SymbolToken};
    use crate::IonType;
    use chrono::*;
    use rstest::*;
    use std::iter::{once, Once};
    use std::str::FromStr;

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

    type ElemAssertFunc = dyn Fn(&BorrowedElement) -> ();

    #[rstest]
    #[case::annotations_with_elem(BorrowedElement::new(["foo","bar","baz"].iter().map(|s| (*s).into()).collect(), BorrowedValue::Boolean(true)), vec![BorrowedSymbolToken::from("foo"), BorrowedSymbolToken::from("bar"), BorrowedSymbolToken::from("baz")])]
    #[case::annotations_with_elem(BorrowedValue::Boolean(true).into(), vec![])]
    fn annotations_with_element(
        #[case] elem: BorrowedElement,
        #[case] annotations: Vec<BorrowedSymbolToken>,
    ) {
        let actual: Vec<&BorrowedSymbolToken> = elem.annotations().map(|tok| tok).collect();
        let expected: Vec<&BorrowedSymbolToken> = annotations.iter().collect();
        assert_eq!(actual, expected);
    }

    /// Each case is a set of tokens that are the same, and a set of tokens that are not ever equal to the first.
    /// This should test symmetry/transitivity/commutativity
    #[rstest(
        // SymbolTokens with same text are equivalent
        case::sym_text(
            vec![
                text_token("foo"),
                text_token("foo").with_local_sid(10),
                text_token("foo").with_local_sid(10).with_source("greetings", 2)
            ],
            vec![
                text_token("bar"),
                local_sid_token(10).with_source("greetings", 1),
                local_sid_token(10).with_source("hello_table", 2),
                local_sid_token(10)
            ]
        ),
        case::sym_local_sid(
            // local sids with no text are equivalent to each other and to SID $0
            vec![
                local_sid_token(200),
                local_sid_token(100)
            ],
            vec![
                local_sid_token(200).with_source("greetings", 2),
                text_token("foo").with_local_sid(200)
            ]
        ),
        // SymbolTokens with no text are equivalent only if their source is equivalent
        case::sym_source(
            vec![
                local_sid_token(200).with_source("greetings", 1),
                local_sid_token(100).with_source("greetings", 1)
            ],
            vec![
                local_sid_token(200).with_source("greetings", 2),
                local_sid_token(200).with_source("hello_table", 1),
                local_sid_token(200),
                text_token("greetings"),
                // due to the transitivity rule this is not equivalent to any member from above vector,
                // even though it has the same import source
                local_sid_token(100).with_source("greetings", 1).with_text("foo")
            ]
        )
    )]
    fn borrowed_symbol_token_eq(
        #[case] equivalent: Vec<BorrowedSymbolToken>,
        #[case] non_equivalent: Vec<BorrowedSymbolToken>,
    ) {
        // check if equivalent vector contains set of tokens that are all equal
        for eq_this_token in &equivalent {
            for eq_other_token in &equivalent {
                assert_eq!(eq_this_token, eq_other_token);
            }
        }

        // check if non_equivalent vector contains a set of tokens that are not ever equal
        // to the equivalent set tokens.
        for eq_token in &equivalent {
            for non_eq_token in &non_equivalent {
                assert_ne!(eq_token, non_eq_token);
            }
        }
    }

    #[rstest(
        elem, ion_type, valid_ops_iter, op_assert,
        case::null(
            IonType::Null.into(),
            IonType::Null,
            IsNull,
            &|e: &BorrowedElement| assert_eq!(true, e.is_null())
        ),
        // TODO more null testing (probably its own fixture)
        case::bool(
            true.into(),
            IonType::Boolean,
            AsBool,
            &|e: &BorrowedElement| assert_eq!(Some(true), e.as_bool())
        ),
        case::i64(
            100.into(),
            IonType::Integer,
            AsAnyInt,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&AnyInt::I64(100)), e.as_any_int());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(None, e.as_big_int());
            }
        ),
        case::big_int(
            BigInt::from(100).into(),
            IonType::Integer,
            AsAnyInt,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&AnyInt::BigInt(BigInt::from(100))), e.as_any_int());
                assert_eq!(BigInt::from_str("100").unwrap(), *e.as_big_int().unwrap());
            }
        ),
        case::f64(
            16.0.into(),
            IonType::Float,
            AsF64,
            &|e: &BorrowedElement| assert_eq!(Some(16.0), e.as_f64())
        ),
        case::decimal(
            Decimal::new(8, 3).into(),
            IonType::Decimal,
            AsDecimal,
            &|e: &BorrowedElement| assert_eq!(Some(&Decimal::new(80, 2)), e.as_decimal())
        ),
        case::timestamp(
            make_timestamp("2014-10-16T12:01:00-00:00").into(),
            IonType::Timestamp,
            AsTimestamp,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&make_timestamp("2014-10-16T12:01:00+00:00")), e.as_timestamp());
            }
        ),
        case::str(
            "hello".into(),
            IonType::String,
            AsStr,
            &|e: &BorrowedElement| assert_eq!(Some("hello"), e.as_str())
        ),
        case::sym_with_text(
            text_token("hello").into(),
            IonType::Symbol,
            vec![AsStr, AsSym],
            &|e: &BorrowedElement| {
                assert_eq!(Some("hello"), e.as_str());
                assert_eq!(Some("hello"), e.as_sym().unwrap().text());
            }
        ),
        case::sym_with_local_sid_source(
            local_sid_token(10).with_source("greetings", 1).into(),
            IonType::Symbol,
            vec![AsSym],
            &|e: &BorrowedElement| {
                assert_eq!(Some(10), e.as_sym().unwrap().local_sid());
                assert_eq!(Some(&BorrowedImportSource::new("greetings", 1)), e.as_sym().unwrap().source());
            }
        ),
        case::sym_with_text_local_sid_source(
            local_sid_token(10).with_source("greetings", 1).with_text("foo").into(),
            IonType::Symbol,
            vec![AsSym, AsStr],
            &|e: &BorrowedElement| {
                assert_eq!(Some("foo"), e.as_str());
                assert_eq!(Some("foo"), e.as_sym().unwrap().text());
                assert_eq!(Some(10), e.as_sym().unwrap().local_sid());
                assert_eq!(Some(&BorrowedImportSource::new("greetings", 1)), e.as_sym().unwrap().source());
            }
        ),
        case::blob(
            BorrowedValue::new_blob(b"world").into(),
            IonType::Blob,
            AsBytes,
            &|e: &BorrowedElement| {
                assert_eq!(Some("world".as_bytes()), e.as_bytes());
            }
        ),
        case::clob(
            BorrowedValue::new_clob(b"goodbye").into(),
            IonType::Clob,
            AsBytes,
            &|e: &BorrowedElement| {
                assert_eq!(Some("goodbye".as_bytes()), e.as_bytes());
            }
        ),
        case::list(
            BorrowedValue::new_list(vec![true.into(), false.into()].into_iter().collect()).into(),
            IonType::List,
            AsSequence,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&vec![BorrowedValue::Boolean(true), BorrowedValue::Boolean(false)].into_iter().map(|v| v.into()).collect()), e.as_sequence());
            }
        ),
        case::sexp(
            BorrowedValue::new_sexp(vec![true.into(), false.into()].into_iter().collect()).into(),
            IonType::SExpression,
            AsSequence,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&vec![BorrowedValue::Boolean(true), BorrowedValue::Boolean(false)].into_iter().map(|v| v.into()).collect()), e.as_sequence());
            }
        ),
        case::struct_(
            BorrowedStruct::from_iter(vec![("greetings", BorrowedElement::from(BorrowedValue::String("hello".into())))].into_iter()).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&vec![("greetings", BorrowedElement::from(BorrowedValue::String("hello".into())))].into_iter().collect()), e.as_struct());
            }
        ),
        case::struct_not_equal(
            BorrowedStruct::from_iter(vec![("greetings", BorrowedElement::from(BorrowedValue::String("hello".into())))].into_iter()).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_ne!(Some(&vec![("name", BorrowedElement::from(BorrowedValue::String("Ion".into())))].into_iter().collect()), e.as_struct());
            }
        ),
        case::struct_with_local_sid(
            BorrowedStruct::from_iter(vec![(local_sid_token(21), BorrowedValue::String("hello".into()))].into_iter()).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&vec![(local_sid_token(21), BorrowedValue::String("hello".into()))].into_iter().collect()), e.as_struct());
            }
        ),
        // SymbolToken with local SID and no text are equivalent to each other and to SID $0 
        case::struct_with_different_local_sids(
            BorrowedStruct::from_iter(vec![(local_sid_token(21), BorrowedValue::String("hello".into()))].into_iter()).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&vec![(local_sid_token(22), BorrowedValue::String("hello".into()))].into_iter().collect()), e.as_struct());
            }
        ),
        case::struct_with_import_source(
            BorrowedStruct::from_iter(vec![(local_sid_token(21).with_source("hello_table", 2), BorrowedValue::String("hello".into()))].into_iter()).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(Some(&vec![(local_sid_token(21).with_source("hello_table", 2), BorrowedValue::String("hello".into()))].into_iter().collect()), e.as_struct());
            }
        ),
        case::struct_with_import_source_not_equal(
            BorrowedStruct::from_iter(vec![(local_sid_token(21).with_source("hello_table", 2), BorrowedValue::String("hello".into()))].into_iter()).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_ne!(Some(&vec![(local_sid_token(21).with_source("hey_table", 2), BorrowedValue::String("hello".into()))].into_iter().collect()), e.as_struct());
            }
        ),
        case::struct_with_multiple_fields(
            BorrowedStruct::from_iter(
                vec![
                    ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                    ("name", BorrowedElement::from(BorrowedValue::String("Ion".into()))),
                ].into_iter()
            ).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(
                    Some(
                        &vec![
                            ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                            ("name", BorrowedElement::from(BorrowedValue::String("Ion".into()))),
                        ].into_iter().collect()
                    ),
                    e.as_struct()
                );
            }
        ),
        case::struct_with_multiple_fields_not_equal(
            BorrowedStruct::from_iter(
                vec![
                    ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                    ("name", BorrowedElement::from(BorrowedValue::String("Ion".into()))),
                ].into_iter()
            ).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_ne!(
                    Some(
                        &vec![
                            ("greetings", BorrowedElement::from(BorrowedValue::String("world".into()))),
                            ("name", BorrowedElement::from(BorrowedValue::String("Ion".into()))),
                        ].into_iter().collect()
                    ),
                    e.as_struct()
                );
            }
        ),
        case::struct_with_multiple_unordred_fields(
            BorrowedStruct::from_iter(
                vec![
                    ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                    ("name", BorrowedElement::from(BorrowedValue::String("Ion".into()))),
                ].into_iter()
            ).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(
                    Some(
                        &vec![
                            ("name", BorrowedElement::from(BorrowedValue::String("Ion".into()))),
                            ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                        ].into_iter().collect()
                    ),
                    e.as_struct()
                );
            }
        ),
        case::struct_with_text_and_duplicates(
        BorrowedStruct::from_iter(
            vec![
                ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                ("greetings", BorrowedElement::from(BorrowedValue::String("world".into()))),
            ].into_iter()
        ).into(),
        IonType::Struct,
        AsStruct,
        &|e: &BorrowedElement| {
            assert_eq!(
                Some(
                    &vec![
                            ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                            ("greetings", BorrowedElement::from(BorrowedValue::String("world".into()))),
                        ].into_iter().collect()
                    ),
                    e.as_struct()
                );
            }
        ),
        case::struct_with_text_and_unordered_duplicates(
        BorrowedStruct::from_iter(
            vec![
                ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                ("greetings", BorrowedElement::from(BorrowedValue::String("world".into()))),
            ].into_iter()
        ).into(),
        IonType::Struct,
        AsStruct,
        &|e: &BorrowedElement| {
                assert_eq!(
                    Some(
                        &vec![
                                ("greetings", BorrowedElement::from(BorrowedValue::String("world".into()))),
                                ("greetings", BorrowedElement::from(BorrowedValue::String("hello".into()))),
                        ].into_iter().collect()
                    ),
                    e.as_struct()
                );
            }
        ),
        case::struct_with_no_text_and_unordered_duplicates(
            BorrowedStruct::from_iter(
                vec![
                    (local_sid_token(21), BorrowedElement::from(BorrowedValue::String("hello".into()))),
                    (local_sid_token(21), BorrowedElement::from(BorrowedValue::String("world".into()))),
                ].into_iter()
            ).into(),
            IonType::Struct,
            AsStruct,
            &|e: &BorrowedElement| {
                assert_eq!(
                    Some(
                        &vec![
                            (local_sid_token(21), BorrowedElement::from(BorrowedValue::String("world".into()))),
                            (local_sid_token(21), BorrowedElement::from(BorrowedValue::String("hello".into()))),
                        ].into_iter().collect()
                    ),
                    e.as_struct()
                );
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
                ]
            ],
        ]
    )]
    fn borrowed_element_accessors<O: IntoIterator<Item = ElemOp>>(
        elem: BorrowedElement,
        ion_type: IonType,
        valid_ops_iter: O,
        op_assert: &ElemAssertFunc,
        eq_annotations: Vec<Vec<BorrowedSymbolToken>>,
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
        assert_eq!(ion_type, elem.ion_type());

        for assert in op_assertions {
            assert(&elem);
        }

        // assert that a value element as-is is equal to itself
        assert_eq!(elem, elem);

        // use the base value to make annotated versions
        let eq_elems: Vec<BorrowedElement> = eq_annotations
            .into_iter()
            .map(|annotations| BorrowedElement::new(annotations, elem.value.clone()))
            .collect();

        for left_elem in eq_elems.iter() {
            for right_elem in eq_elems.iter() {
                assert_eq!(left_elem, right_elem);
            }
        }
    }
}
