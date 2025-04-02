// Copyright Amazon.com, Inc. or its affiliates.

// Disabled for this file because `Element`'s `try_into_<x>` methods return
// `ConversionOperationError<Element, <X>>` which embeds an `Element`. `Element` itself is 128 bytes.
// This trips `clippy::result_large_err`. However, most usages of this type are expected to be
// converted or destructured immediately.
//
// Cf. https://rust-lang.github.io/rust-clippy/master/index.html#result_large_err
#![allow(clippy::result_large_err)]

//! Provides a dynamically typed, materialized representation of an Ion value.
//!
//! An [Element] represents an `(annotations, value)` pair, where a `value` is
//! an Ion `integer`, `float`, `list`, `struct`, etc.
//!
//! For reference here are a couple other _value_ style APIs for JSON:
//! * [`simd_json`'s `Value` API][simd-json-value]
//! * [`serde_json`'s `Value` API][serde-json-value]
//!
//! [simd-json-value]: https://docs.rs/simd-json/latest/simd_json/value/index.html
//! [serde-json-value]: https://docs.serde.rs/serde_json/value/enum.Value.html

pub use annotations::{Annotations, IntoAnnotations};
pub use sequence::{OwnedSequenceIterator, Sequence};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::Hasher;
use std::io;

use crate::{ion_data, Decimal, Int, IonResult, IonType, Str, Symbol, SymbolRef, Timestamp};
use crate::{Blob, Bytes, Clob, List, SExp, Struct};
// Re-export the Value variant types and traits so they can be accessed directly from this module.
use crate::element::builders::{SequenceBuilder, StructBuilder};
use crate::element::reader::ElementReader;
use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::lazy::any_encoding::AnyEncoding;
use crate::lazy::encoding::Encoding;
use crate::lazy::reader::Reader;
use crate::lazy::streaming_raw_reader::{IonInput, IonSlice};
use crate::location::SourceLocation;
use crate::result::{
    ConversionOperationError, ConversionOperationResult, IonTypeExpectation, TypeExpectation,
};
use crate::text::text_formatter::FmtValueFormatter;
use crate::types::symbol::SymbolText;
use crate::write_config::WriteConfig;

mod annotations;
pub(crate) mod iterators;

pub mod builders;
pub mod element_writer;
pub mod reader;
mod sequence;

impl IonEq for Value {
    fn ion_eq(&self, other: &Self) -> bool {
        use Value::*;
        match (self, other) {
            (Null(this), Null(that)) => this == that,
            (Bool(this), Bool(that)) => ion_data::ion_eq_bool(this, that),
            (Int(this), Int(that)) => this.ion_eq(that),
            (Float(this), Float(that)) => ion_data::ion_eq_f64(this, that),
            (Decimal(this), Decimal(that)) => this.ion_eq(that),
            (Timestamp(this), Timestamp(that)) => this.ion_eq(that),
            (Symbol(this), Symbol(that)) => this.ion_eq(that),
            (String(this), String(that)) => this.ion_eq(that),
            (Clob(this), Clob(that)) => this.ion_eq(that),
            (Blob(this), Blob(that)) => this.ion_eq(that),
            (List(this), List(that)) => this.ion_eq(that),
            (SExp(this), SExp(that)) => this.ion_eq(that),
            (Struct(this), Struct(that)) => this.ion_eq(that),
            _ => false,
        }
    }
}

impl IonDataOrd for Value {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        use Value::*;

        // First compare Ion types
        let ord = self.ion_type().ion_cmp(&other.ion_type());
        if !ord.is_eq() {
            return ord;
        }

        macro_rules! compare {
            ($p:pat => $e:expr) => {
                match other {
                    $p => $e,
                    Null(_) => Ordering::Greater,
                    _ => unreachable!("We already checked the Ion Type!"),
                }
            };
        }

        match self {
            Null(_) => {
                if let Null(_) = other {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            }
            Bool(this) => compare!(Bool(that) => ion_data::ion_cmp_bool(this, that)),
            Int(this) => compare!(Int(that) => this.ion_cmp(that)),
            Float(this) => compare!(Float(that) => ion_data::ion_cmp_f64(this, that)),
            Decimal(this) => compare!(Decimal(that) => this.ion_cmp(that)),
            Timestamp(this) => compare!(Timestamp(that) => this.ion_cmp(that)),
            Symbol(this) => compare!(Symbol(that) => this.ion_cmp(that)),
            String(this) => compare!(String(that) => this.ion_cmp(that)),
            Clob(this) => compare!(Clob(that) => this.ion_cmp(that)),
            Blob(this) => compare!(Blob(that) => this.ion_cmp(that)),
            List(this) => compare!(List(that) => this.ion_cmp(that)),
            SExp(this) => compare!(SExp(that) => this.ion_cmp(that)),
            Struct(this) => compare!(Struct(that) => this.ion_cmp(that)),
        }
    }
}

impl IonDataHash for Value {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        use Value::*;
        self.ion_type().ion_data_hash(state);
        match self {
            Null(_) => state.write_u8(0),
            Bool(this) => ion_data::ion_data_hash_bool(*this, state),
            Int(this) => this.ion_data_hash(state),
            Float(this) => ion_data::ion_data_hash_f64(*this, state),
            Decimal(this) => this.ion_data_hash(state),
            Timestamp(this) => this.ion_data_hash(state),
            Symbol(this) => this.ion_data_hash(state),
            String(this) => this.ion_data_hash(state),
            Clob(this) => this.ion_data_hash(state),
            Blob(this) => this.ion_data_hash(state),
            List(this) => this.ion_data_hash(state),
            SExp(this) => this.ion_data_hash(state),
            Struct(this) => this.ion_data_hash(state),
        }
    }
}

/// Variants for all _values_ within an [`Element`].
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    Symbol(Symbol),
    String(Str),
    Clob(Bytes),
    Blob(Bytes),
    List(Sequence),
    SExp(Sequence),
    Struct(Struct),
}

impl Value {
    pub fn ion_type(&self) -> IonType {
        use Value::*;

        match self {
            Null(t) => *t,
            Bool(_) => IonType::Bool,
            Int(_) => IonType::Int,
            Float(_) => IonType::Float,
            Decimal(_) => IonType::Decimal,
            Timestamp(_) => IonType::Timestamp,
            Symbol(_) => IonType::Symbol,
            String(_) => IonType::String,
            Clob(_) => IonType::Clob,
            Blob(_) => IonType::Blob,
            List(_) => IonType::List,
            SExp(_) => IonType::SExp,
            Struct(_) => IonType::Struct,
        }
    }
}

impl IonTypeExpectation for Value {
    fn ion_type(&self) -> IonType {
        self.ion_type()
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = FmtValueFormatter { output: f };
        match &self {
            Value::Null(ion_type) => ivf.format_null(*ion_type),
            Value::Bool(bool) => ivf.format_bool(*bool),
            Value::Int(integer) => ivf.format_integer(integer),
            Value::Float(float) => ivf.format_float(*float),
            Value::Decimal(decimal) => ivf.format_decimal(decimal),
            Value::Timestamp(timestamp) => ivf.format_timestamp(timestamp),
            Value::Symbol(symbol) => ivf.format_symbol(symbol),
            Value::String(string) => ivf.format_string(string),
            Value::Clob(clob) => ivf.format_clob(clob),
            Value::Blob(blob) => ivf.format_blob(blob),
            Value::List(sequence) => ivf.format_list(sequence),
            Value::SExp(sequence) => ivf.format_sexp(sequence),
            Value::Struct(struct_) => ivf.format_struct(struct_),
        }
        .map_err(|_| std::fmt::Error)?;

        Ok(())
    }
}

impl From<IonType> for Value {
    fn from(ion_type: IonType) -> Self {
        Value::Null(ion_type)
    }
}

// Provides Into<Value> for all int types, both signed and unsigned.
// Those types can also use the blanket Into<Element> impl that exists for T: Into<Value>.
impl<I: Into<Int>> From<I> for Value {
    fn from(value: I) -> Self {
        let int: Int = value.into();
        Value::Int(int)
    }
}

impl From<f64> for Value {
    fn from(f64_val: f64) -> Self {
        Value::Float(f64_val)
    }
}

impl From<Decimal> for Value {
    fn from(decimal_val: Decimal) -> Self {
        Value::Decimal(decimal_val)
    }
}

impl From<Timestamp> for Value {
    fn from(timestamp_val: Timestamp) -> Self {
        Value::Timestamp(timestamp_val)
    }
}

impl From<bool> for Value {
    fn from(bool_val: bool) -> Self {
        Value::Bool(bool_val)
    }
}

impl From<&str> for Value {
    fn from(string_val: &str) -> Self {
        Value::String(string_val.into())
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        let s: Str = value.into();
        Value::String(s)
    }
}

impl From<Str> for Value {
    fn from(string_val: Str) -> Self {
        Value::String(string_val)
    }
}

impl From<Symbol> for Value {
    fn from(sym_val: Symbol) -> Self {
        Value::Symbol(sym_val)
    }
}

impl From<SymbolRef<'_>> for Value {
    fn from(sym_val: SymbolRef<'_>) -> Self {
        Value::Symbol(sym_val.to_owned())
    }
}

impl From<&[u8]> for Value {
    fn from(value: &[u8]) -> Self {
        Value::Blob(value.into())
    }
}

impl From<Vec<u8>> for Value {
    fn from(value: Vec<u8>) -> Self {
        Value::Blob(value.into())
    }
}

impl From<Blob> for Value {
    fn from(blob: Blob) -> Self {
        let bytes: Bytes = blob.into();
        Value::Blob(bytes)
    }
}

impl From<Clob> for Value {
    fn from(clob: Clob) -> Self {
        let bytes: Bytes = clob.into();
        Value::Clob(bytes)
    }
}

impl From<List> for Value {
    fn from(list: List) -> Self {
        Value::List(list.into())
    }
}

impl From<SExp> for Value {
    fn from(s_expr: SExp) -> Self {
        Value::SExp(s_expr.into())
    }
}

impl From<Struct> for Value {
    fn from(struct_val: Struct) -> Self {
        Value::Struct(struct_val)
    }
}

/// Allows types that can be converted into an Ion [Value] to also specify annotations, producing
/// an [Element].
///
/// ```
/// use ion_rs::{Element, IntoAnnotatedElement, Value};
///
/// // Explicit ConversionResult of a Rust bool (`true`) into a `Value`...
/// let boolean_value: Value = true.into();
/// // and then into an `Element`...
/// let mut boolean_element: Element = boolean_value.into();
/// // and then adding annotations to the `Element`.
/// let boolean_element = boolean_element.with_annotations(["foo", "bar"]);
///
/// // Much more concise equivalent leveraging the `IntoAnnotatedElement` trait.
/// let boolean_element = true.with_annotations(["foo", "bar"]);
/// ```
pub trait IntoAnnotatedElement: Into<Value> {
    /// Converts the value into an [Element] with the specified annotations.
    fn with_annotations<I: IntoAnnotations>(self, annotations: I) -> Element {
        Element::new(annotations.into_annotations(), self.into())
    }
}

impl<V> IntoAnnotatedElement for V where V: Into<Value> {}

impl IonEq for Element {
    fn ion_eq(&self, other: &Self) -> bool {
        self.annotations == other.annotations && self.value.ion_eq(&other.value)
    }
}

// Ordering is done as follows:
// 1. Ion type -- It is a logical way to group Ion values, and it is the cheapest comparison
// 2. Annotations -- the vast majority of Ion values have few annotations, so this should usually be cheap
// 3. Value -- compared using IonOrd
impl IonDataOrd for Element {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        let ord = self.ion_type().ion_cmp(&other.ion_type());
        if !ord.is_eq() {
            return ord;
        }

        let a1 = self.annotations();
        let a2 = other.annotations();

        let ord = a1.ion_cmp(a2);
        if !ord.is_eq() {
            return ord;
        }

        let v1 = self.value();
        let v2 = other.value();
        v1.ion_cmp(v2)
    }
}

impl IonDataHash for Element {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.annotations.ion_data_hash(state);
        self.value.ion_data_hash(state);
    }
}

/// An `(annotations, value)` pair representing an Ion value.
#[derive(Clone)]
pub struct Element {
    annotations: Annotations,
    value: Value,
    // Represents the source location metadata (row, column).
    location: SourceLocation
}

impl std::fmt::Debug for Element {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        <Element as Display>::fmt(self, f)
    }
}

macro_rules! impl_try_from_element {
    ($to_type:ident, $to_fn:ident) => {
        impl TryFrom<Element> for $to_type {
            type Error = ConversionOperationError<Element, $to_type>;

            fn try_from(element: Element) -> ConversionOperationResult<Element, $to_type> {
                element.$to_fn().into()
            }
        }
    };
}

impl_try_from_element!(f64, try_into_float);
impl_try_from_element!(Decimal, try_into_decimal);
impl_try_from_element!(Timestamp, try_into_timestamp);
impl_try_from_element!(String, try_into_text);
impl_try_from_element!(Str, try_into_string);
impl_try_from_element!(Symbol, try_into_symbol);
impl_try_from_element!(bool, try_into_bool);
impl_try_from_element!(Bytes, try_into_lob);
impl_try_from_element!(Sequence, try_into_sequence);
impl_try_from_element!(Struct, try_into_struct);

impl Element {
    pub(crate) fn new(annotations: Annotations, value: impl Into<Value>) -> Self {
        Self {
            annotations,
            value: value.into(),
            location: SourceLocation::empty(),
        }
    }

    pub(crate) fn with_location(self, location: SourceLocation) -> Self {
        Self {
            annotations: self.annotations,
            value: self.value,
            location,
        }
    }

    fn expected<ToType>(&self, maybe: Option<ToType>) -> IonResult<ToType>
    where
        ToType: TypeExpectation,
    {
        Ok(maybe.ok_or_else(|| ConversionOperationError::<&Element, ToType>::new(self))?)
    }

    /// Returns a reference to this [Element]'s [Value].
    ///
    /// ```
    /// use ion_rs::{Element, Value};
    /// let element: Element = true.into();
    /// if let Value::Bool(b) = element.value() {
    ///     println!("It was a boolean: {b}");
    /// } else {
    ///     println!("It was something else.");
    /// }
    /// ```
    pub fn value(&self) -> &Value {
        &self.value
    }

    /// Returns the source location (row, column) of this element in the original Ion text.
    ///
    /// The location metadata is primarily intended for error reporting and debugging purposes,
    /// helping applications provide meaningful feedback to users about the source of issues.
    ///
    /// # Returns
    /// * `Some((row, column))` - Position where this element was found in the source text
    /// * `None` - Location information is not available
    ///
    /// # Important
    /// Location information is best-effort and may not be available in all cases:
    /// * Elements created programmatically won't have locations
    /// * Some parsing scenarios might not preserve location data
    /// * Binary Ion data does not contain location information
    ///
    /// Do not rely on this metadata for programmatic manipulation of Ion data.
    pub fn location(&self) -> &SourceLocation {
        &self.location
    }

    /// Consumes self and returns this [Element]'s [Value].
    pub fn into_value(self) -> Value {
        self.value
    }

    /// Consumes self and returns this [Element]'s [Annotations].
    pub fn into_annotations(self) -> Annotations {
        self.annotations
    }

    /// Consumes self and returns this [Element]'s [Annotations] and [Value].
    pub fn into_parts(self) -> (Annotations, Value) {
        (self.annotations, self.value)
    }

    pub fn null(null_type: IonType) -> Element {
        null_type.into()
    }

    pub fn boolean(value: bool) -> Element {
        value.into()
    }

    pub fn string<I: Into<Str>>(str: I) -> Element {
        let text: Str = str.into();
        text.into()
    }

    pub fn symbol<I: Into<Symbol>>(symbol: I) -> Element {
        let symbol: Symbol = symbol.into();
        symbol.into()
    }

    pub fn int<I: Into<Int>>(integer: I) -> Element {
        let integer: Int = integer.into();
        integer.into()
    }

    pub fn decimal(decimal: Decimal) -> Element {
        decimal.into()
    }

    pub fn timestamp(timestamp: Timestamp) -> Element {
        timestamp.into()
    }

    pub fn float(float: f64) -> Element {
        float.into()
    }

    pub fn clob<A: AsRef<[u8]>>(bytes: A) -> Element {
        let bytes: &[u8] = bytes.as_ref();
        Value::Clob(bytes.into()).into()
    }

    pub fn blob<A: AsRef<[u8]>>(bytes: A) -> Element {
        let bytes: &[u8] = bytes.as_ref();
        Value::Blob(bytes.into()).into()
    }

    pub fn sequence_builder() -> SequenceBuilder {
        Sequence::builder()
    }

    pub fn struct_builder() -> StructBuilder {
        Struct::builder()
    }

    pub fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub fn annotations(&self) -> &Annotations {
        &self.annotations
    }

    pub fn with_annotations<I: IntoAnnotations>(self, annotations: I) -> Self {
        Element::new(annotations.into_annotations(), self.value)
    }

    pub fn is_null(&self) -> bool {
        matches!(&self.value, Value::Null(_))
    }

    pub fn as_int(&self) -> Option<&Int> {
        match &self.value {
            Value::Int(i) => Some(i),
            _ => None,
        }
    }

    pub fn expect_int(&self) -> IonResult<&Int> {
        self.expected(self.as_int())
    }

    pub fn try_into_int(self) -> ConversionOperationResult<Element, Int> {
        match self.value {
            Value::Int(i) => Ok(i),
            _ => Err(self.into()),
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        match &self.value {
            Value::Int(i) => i.as_i64(),
            _ => None,
        }
    }

    pub fn expect_i64(&self) -> IonResult<i64> {
        self.expected(self.as_i64())
    }

    pub fn try_into_i64(self) -> ConversionOperationResult<Element, i64> {
        match self.value {
            Value::Int(i) if i.as_i64().is_some() => Ok(i.as_i64().unwrap()),
            _ => Err(self.into()),
        }
    }

    pub fn as_usize(&self) -> Option<usize> {
        match &self.value {
            Value::Int(i) => i.as_usize(),
            _ => None,
        }
    }

    pub fn expect_usize(&self) -> IonResult<usize> {
        self.expected(self.as_usize())
    }

    pub fn try_into_usize(self) -> ConversionOperationResult<Element, usize> {
        self.as_usize().ok_or_else(|| self.into())
    }

    pub fn as_float(&self) -> Option<f64> {
        match &self.value {
            Value::Float(f) => Some(*f),
            _ => None,
        }
    }

    pub fn expect_float(&self) -> IonResult<f64> {
        self.expected(self.as_float())
    }

    pub fn try_into_float(self) -> ConversionOperationResult<Element, f64> {
        match self.value {
            Value::Float(f) => Ok(f),
            _ => Err(self.into()),
        }
    }

    pub fn as_decimal(&self) -> Option<Decimal> {
        match &self.value {
            Value::Decimal(d) => Some(*d),
            _ => None,
        }
    }

    pub fn expect_decimal(&self) -> IonResult<Decimal> {
        self.expected(self.as_decimal())
    }

    pub fn try_into_decimal(self) -> ConversionOperationResult<Element, Decimal> {
        match self.value {
            Value::Decimal(d) => Ok(d),
            _ => Err(self.into()),
        }
    }

    pub fn as_timestamp(&self) -> Option<Timestamp> {
        match &self.value {
            Value::Timestamp(t) => Some(*t),
            _ => None,
        }
    }

    pub fn expect_timestamp(&self) -> IonResult<Timestamp> {
        self.expected(self.as_timestamp())
    }

    pub fn try_into_timestamp(self) -> ConversionOperationResult<Element, Timestamp> {
        match self.value {
            Value::Timestamp(t) => Ok(t),
            _ => Err(self.into()),
        }
    }

    pub fn as_text(&self) -> Option<&str> {
        match &self.value {
            Value::String(text) => Some(text.as_ref()),
            Value::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    pub fn expect_text(&self) -> IonResult<&str> {
        self.expected(self.as_text())
    }

    pub fn try_into_text(self) -> ConversionOperationResult<Element, String> {
        let Self { value, annotations, location } = self;
        match value {
            Value::String(text) => Ok(text.to_string()),
            Value::Symbol(sym) => match sym.text {
                SymbolText::Shared(shared) => Ok((*shared).to_string()),
                SymbolText::Owned(owned) => Ok(owned),
                SymbolText::Unknown => {
                    let sym = Self {
                        value: Value::Symbol(Symbol::unknown_text()),
                        annotations,
                        location,
                    };
                    Err(ConversionOperationError::new(sym))
                }
                SymbolText::Static(static_str) => Ok((*static_str).to_string()),
            },
            _ => {
                let sym = Self { value, annotations, location };
                Err(ConversionOperationError::new(sym))
            }
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match &self.value {
            Value::String(text) => Some(text.as_ref()),
            _ => None,
        }
    }

    pub fn expect_string(&self) -> IonResult<&str> {
        self.expected(self.as_string())
    }

    pub fn try_into_string(self) -> ConversionOperationResult<Element, Str> {
        match self.value {
            Value::String(text) => Ok(text),
            _ => Err(self.into()),
        }
    }

    pub fn as_symbol(&self) -> Option<&Symbol> {
        match &self.value {
            Value::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    pub fn expect_symbol(&self) -> IonResult<&Symbol> {
        self.expected(self.as_symbol())
    }

    pub fn try_into_symbol(self) -> ConversionOperationResult<Element, Symbol> {
        match self.value {
            Value::Symbol(sym) => Ok(sym),
            _ => Err(self.into()),
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match &self.value {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn expect_bool(&self) -> IonResult<bool> {
        self.expected(self.as_bool())
    }

    pub fn try_into_bool(self) -> ConversionOperationResult<Element, bool> {
        match self.value {
            Value::Bool(b) => Ok(b),
            _ => Err(self.into()),
        }
    }

    pub fn as_lob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) | Value::Clob(bytes) => Some(bytes.as_ref()),
            _ => None,
        }
    }

    pub fn expect_lob(&self) -> IonResult<&[u8]> {
        self.expected(self.as_lob())
    }

    pub fn try_into_lob(self) -> ConversionOperationResult<Element, Bytes> {
        match self.value {
            Value::Blob(bytes) | Value::Clob(bytes) => Ok(bytes),
            _ => Err(self.into()),
        }
    }

    pub fn as_blob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) => Some(bytes.as_ref()),
            _ => None,
        }
    }

    pub fn expect_blob(&self) -> IonResult<&[u8]> {
        self.expected(self.as_blob())
    }

    pub fn try_into_blob(self) -> ConversionOperationResult<Element, Bytes> {
        match self.value {
            Value::Blob(bytes) => Ok(bytes),
            _ => Err(self.into()),
        }
    }

    pub fn as_clob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Clob(bytes) => Some(bytes.as_ref()),
            _ => None,
        }
    }

    pub fn expect_clob(&self) -> IonResult<&[u8]> {
        self.expected(self.as_clob())
    }

    pub fn try_into_clob(self) -> ConversionOperationResult<Element, Bytes> {
        match self.value {
            Value::Clob(bytes) => Ok(bytes),
            _ => Err(self.into()),
        }
    }

    pub fn as_sequence(&self) -> Option<&Sequence> {
        match &self.value {
            Value::SExp(s) | Value::List(s) => Some(s),
            _ => None,
        }
    }

    pub fn expect_sequence(&self) -> IonResult<&Sequence> {
        self.expected(self.as_sequence())
    }

    pub fn try_into_sequence(self) -> ConversionOperationResult<Element, Sequence> {
        match self.value {
            Value::SExp(s) | Value::List(s) => Ok(s),
            _ => Err(self.into()),
        }
    }

    pub fn as_list(&self) -> Option<&Sequence> {
        match &self.value {
            Value::List(s) => Some(s),
            _ => None,
        }
    }

    pub fn expect_list(&self) -> IonResult<&Sequence> {
        self.expected(self.as_list())
    }

    pub fn try_into_list(self) -> ConversionOperationResult<Element, Sequence> {
        match self.value {
            Value::List(s) => Ok(s),
            _ => Err(self.into()),
        }
    }

    pub fn as_sexp(&self) -> Option<&Sequence> {
        match &self.value {
            Value::SExp(s) => Some(s),
            _ => None,
        }
    }

    pub fn expect_sexp(&self) -> IonResult<&Sequence> {
        self.expected(self.as_sexp())
    }

    pub fn try_into_sexp(self) -> ConversionOperationResult<Element, Sequence> {
        match self.value {
            Value::SExp(s) => Ok(s),
            _ => Err(self.into()),
        }
    }

    pub fn as_struct(&self) -> Option<&Struct> {
        match &self.value {
            Value::Struct(structure) => Some(structure),
            _ => None,
        }
    }

    pub fn expect_struct(&self) -> IonResult<&Struct> {
        self.expected(self.as_struct())
    }

    pub fn try_into_struct(self) -> ConversionOperationResult<Element, Struct> {
        match self.value {
            Value::Struct(structure) => Ok(structure),
            _ => Err(self.into()),
        }
    }

    /// Reads a single Ion [`Element`] from the provided data source.
    ///
    /// If the data source is empty, returns `Ok(None)`.
    /// If the data source has at least one value, returns `Ok(Some(Element))`.
    /// If the data source has invalid data, returns `Err`.
    pub fn read_first<A: AsRef<[u8]>>(data: A) -> IonResult<Option<Element>> {
        let mut reader = Reader::new(AnyEncoding, IonSlice::new(data))?;
        reader.read_next_element()
    }

    /// Reads a single Ion [`Element`] from the provided data source. If the input has invalid
    /// data or does not contain at exactly one Ion value, returns `Err(IonError)`.
    pub fn read_one<A: AsRef<[u8]>>(data: A) -> IonResult<Element> {
        let mut reader = Reader::new(AnyEncoding, IonSlice::new(data))?;
        reader.read_one_element()
    }

    /// Reads all available [`Element`]s from the provided data source.
    ///
    /// If the input has valid data, returns `Ok(Sequence)`.
    /// If the input has invalid data, returns `Err(IonError)`.
    pub fn read_all<A: AsRef<[u8]>>(data: A) -> IonResult<Sequence> {
        Ok(Reader::new(AnyEncoding, IonSlice::new(data))?
            .into_elements()
            .collect::<IonResult<Vec<_>>>()?
            .into())
    }

    /// Returns an iterator over the Elements in the provided Ion data source.
    /// If the data source cannot be read or contains invalid Ion data, this method
    /// will return an `Err`.
    pub fn iter<'a, I: IonInput + 'a>(
        source: I,
    ) -> IonResult<impl Iterator<Item = IonResult<Element>> + 'a> {
        Ok(Reader::new(AnyEncoding, source)?.into_elements())
    }

    /// Encodes this element as an Ion stream with itself as the only top-level value.
    /// If the stream's encoding is binary Ion, returns a `Vec<u8>` containing the encoded bytes.
    /// If the stream's encoding is text Ion, returns a `String` containing the UTF-8 encoded text.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::Element;
    /// use ion_rs::v1_0::Binary;
    ///
    /// let ion_data = r#"{foo: "hello", bar: quux::5, baz: null, bar: false}"#;
    /// let element_before = Element::read_one(ion_data)?;
    ///
    /// // Encode the element as a binary Ion stream
    /// let ion_bytes: Vec<u8> = element_before.encode_as(Binary)?;
    /// // Read the element back from the binary stream
    /// let element_after = Element::read_one(ion_bytes)?;
    ///
    /// // Confirm that the value we read back is identical to the one we serialized
    /// assert_eq!(element_before, element_after);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn encode_as<E: Encoding, C: Into<WriteConfig<E>>>(
        &self,
        config: C,
    ) -> IonResult<E::Output> {
        config.into().encode(self)
    }

    /// Encodes this element as an Ion stream with itself as the only top-level value.
    /// The encoded bytes are written to the provided [`io::Write`] implementation.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::Element;
    /// use ion_rs::v1_0::Binary;
    ///
    /// let ion_data = r#"{foo: "hello", bar: quux::5, baz: null, bar: false}"#;
    /// let element_before = Element::read_one(ion_data)?;
    ///
    /// // Encode the element as a binary Ion stream. The bytes will be written to the provided
    /// //  Vec<u8>, and the Vec<u8> will be returned when encoding is complete.
    /// let ion_bytes: Vec<u8> = element_before.encode_to(Vec::new(), Binary)?;
    /// // Read the element back from the binary stream
    /// let element_after = Element::read_one(ion_bytes)?;
    ///
    /// // Confirm that the value we read back is identical to the one we serialized
    /// assert_eq!(element_before, element_after);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn encode_to<E: Encoding, C: Into<WriteConfig<E>>, W: io::Write>(
        &self,
        output: W,
        config: C,
    ) -> IonResult<W> {
        config.into().encode_to(self, output)
    }
}

impl IonTypeExpectation for Element {
    fn ion_type(&self) -> IonType {
        Element::ion_type(self)
    }
}

impl IonTypeExpectation for &Element {
    fn ion_type(&self) -> IonType {
        Element::ion_type(self)
    }
}

impl Display for Element {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let mut ivf = FmtValueFormatter { output: f };

        // display for annotations of this element
        ivf.format_annotations(&self.annotations)
            .map_err(|_| std::fmt::Error)?;

        self.value.fmt(f)
    }
}

impl PartialEq for Element {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.annotations == other.annotations
    }
}

impl Eq for Element {}

// This implementation allows APIs that require an Into<Element> to accept references to an existing
// Element.
impl<'a> From<&'a Element> for Element {
    fn from(element: &'a Element) -> Self {
        element.clone()
    }
}

// Anything that can be turned into a `Value` can then be turned into an `Element`
// by associating it with an empty annotations sequence.
impl<T> From<T> for Element
where
    T: Into<Value>,
{
    fn from(value: T) -> Self {
        Element::new(Annotations::empty(), value.into())
    }
}

impl AsRef<Element> for Element {
    fn as_ref(&self) -> &Element {
        self
    }
}

#[cfg(test)]
mod tests {
    use chrono::*;
    use rstest::*;
    use std::collections::HashSet;
    use std::iter::{once, Once};

    use ElemOp::*;

    use crate::element::annotations::IntoAnnotations;
    use crate::{ion_list, ion_sexp, ion_struct, Decimal, Int, IonType, Symbol, Timestamp, Value};
    use crate::{Annotations, Element, IntoAnnotatedElement, Struct};

    /// Makes a timestamp from an RFC-3339 string and panics if it can't
    fn make_timestamp<T: AsRef<str>>(text: T) -> Timestamp {
        DateTime::parse_from_rfc3339(text.as_ref()).unwrap().into()
    }

    struct CaseAnnotations {
        elem: Element,
        annotations: Annotations,
    }

    fn annotations_text_case() -> CaseAnnotations {
        CaseAnnotations {
            elem: 10i64.with_annotations(["foo", "bar", "baz"]),
            annotations: ["foo", "bar", "baz"].into_annotations(),
        }
    }

    fn no_annotations_case() -> CaseAnnotations {
        CaseAnnotations {
            elem: 10i64.into(),
            annotations: Annotations::empty(),
        }
    }

    #[rstest]
    #[case::annotations_text(annotations_text_case())]
    #[case::no_annotations(no_annotations_case())]
    fn annotations_with_element(#[case] input: CaseAnnotations) {
        let actual: &Annotations = input.elem.annotations();
        let expected: &Annotations = &input.annotations;
        assert_eq!(actual, expected);
    }

    struct CaseSym {
        eq_annotations: Vec<Symbol>,
        ne_annotations: Vec<Symbol>,
    }

    fn sym_text_case() -> CaseSym {
        // SymbolTokens with same text are equivalent
        CaseSym {
            eq_annotations: vec![Symbol::owned("foo"), Symbol::owned("foo")],
            // These are not equal to any of the ones in `eq_annotations` above
            ne_annotations: vec![Symbol::owned("bar"), Symbol::owned("baz")],
        }
    }

    /// Each case is a set of tokens that are the same, and a set of tokens that are not ever equal to the first.
    /// This should test symmetry/transitivity/commutativity
    #[rstest]
    #[case::owned_sym_text(sym_text_case())]
    fn symbol_token_eq(#[case] input: CaseSym) {
        // check if equivalent vector contains set of tokens that are all equal
        for eq_this_token in &input.eq_annotations {
            for eq_other_token in &input.eq_annotations {
                assert_eq!(eq_this_token, eq_other_token);
            }
        }

        // check if non_equivalent vector contains a set of tokens that are not ever equal
        // to the equivalent set tokens.
        for eq_token in &input.eq_annotations {
            for non_eq_token in &input.ne_annotations {
                assert_ne!(eq_token, non_eq_token);
            }
        }
    }

    /// A struct that defines input case for `struct_accessors` method
    struct CaseStruct {
        /// set of struct elements that are the same
        eq_elements: Vec<Element>,
        /// set of struct elements that are never equal to `eq_annotations`
        ne_elements: Vec<Element>,
    }

    /// A convenience method for constructing a Vec<Element> from a collection of
    /// homogeneously typed values that implement Into<Element>.
    fn ion_vec<E: Into<Element>, I: IntoIterator<Item = E>>(values: I) -> Vec<Element> {
        values.into_iter().map(|v| v.into()).collect()
    }

    fn struct_with_multiple_fields_case() -> CaseStruct {
        CaseStruct {
            eq_elements: ion_vec([
                // structs with different order of fields
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion"
                },
                ion_struct! {
                    "name": "Ion",
                    "greetings": "hello"
                },
            ]),
            ne_elements: ion_vec([
                // structs with different length and duplicates
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion",
                    "greetings": "hello"
                },
                // structs with different fields length and duplicates
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion",
                    "greetings": "bye"
                },
                // structs with different fields length
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion",
                    "message": "bye"
                },
            ]),
        }
    }

    fn struct_with_duplicates_in_multiple_fields_case() -> CaseStruct {
        CaseStruct {
            // Structs are bags of (field, value) pairs, order is irrelevant
            eq_elements: ion_vec([
                ion_struct! {
                    "a" : 2i64,
                    "a" : 2i64,
                    "a" : 1i64
                },
                ion_struct! {
                    "a" : 2i64,
                    "a" : 1i64,
                    "a" : 2i64
                },
                ion_struct! {
                    "a" : 1i64,
                    "a" : 2i64,
                    "a" : 2i64
                },
            ]),
            ne_elements: ion_vec([
                // structs with different length
                ion_struct! {
                    "a" : 1i64,
                    "a" : 2i64
                },
                // structs with annotated values
                ion_struct! {
                    "a" : 2i64,
                    "a" : 1i64.with_annotations(["a"]),
                    "a" : 2i64
                },
                // structs with different value for duplicates
                ion_struct! {
                    "a" : 2i64,
                    "a" : 3i64,
                    "a" : 2i64
                },
            ]),
        }
    }

    fn struct_with_duplicate_fieldnames_case() -> CaseStruct {
        CaseStruct {
            eq_elements: ion_vec([
                // structs with unordered fields
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello"
                },
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello"
                },
            ]),
            ne_elements: ion_vec([
                // structs with different length and duplicates
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello",
                    "greetings" : "hey"
                },
                // structs with annotated values
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello".with_annotations(["foo"])
                },
                // structs with different length
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello",
                    "name" : "hello"
                },
            ]),
        }
    }

    #[rstest]
    #[case::owned_struct_with_multiple_fields(struct_with_multiple_fields_case())]
    #[case::owned_struct_with_duplicates_in_multiple_fields(
        struct_with_duplicates_in_multiple_fields_case()
    )]
    #[case::owned_struct_with_duplicate_fieldnames(struct_with_duplicate_fieldnames_case())]
    fn struct_accessors(#[case] input: CaseStruct) {
        // check if equivalent vector contains set of structs that are all equal
        for eq_this_struct in &input.eq_elements {
            for eq_other_struct in &input.eq_elements {
                assert_eq!(eq_this_struct, eq_other_struct);
            }
        }

        // check if non_equivalent vector contains a set of structs that are not ever equal
        // to the equivalent set structs.
        for eq_struct in &input.eq_elements {
            for non_eq_struct in &input.ne_elements {
                assert_ne!(eq_struct, non_eq_struct);
            }
        }
    }

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
        TryIntoInt,
        TryIntoI64,
        TryIntoF64,
        TryIntoDecimal,
        TryIntoTimestamp,
        TryIntoText,
        TryIntoString,
        TryIntoSymbol,
        TryIntoBool,
        TryIntoLob,
        TryIntoBlob,
        TryIntoClob,
        TryIntoSequence,
        TryIntoList,
        TryIntoSexp,
        TryIntoStruct,
    }

    impl IntoIterator for ElemOp {
        type Item = ElemOp;
        type IntoIter = <Once<ElemOp> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            once(self)
        }
    }

    type ElemAssertFn = Box<dyn FnOnce(&Element)>;
    type OwnedElemAssertFn = Box<dyn FnOnce(Element)>;

    macro_rules! assert_pass_try_into {
        ($f:ident) => {
            Box::new(|e: Element| assert!(e.$f().is_ok()))
        };
    }

    macro_rules! assert_fail_try_into {
        ($f:ident) => {
            Box::new(|e: Element| assert!(e.$f().is_err()))
        };
    }

    struct Case {
        elem: Element,
        ion_type: IonType,
        ops: Vec<ElemOp>,
        op_assert: ElemAssertFn,
        owned_asserts: Vec<OwnedElemAssertFn>,
    }

    fn null_case() -> Case {
        Case {
            elem: Element::from(IonType::Null), // null.null
            ion_type: IonType::Null,
            ops: vec![IsNull],
            op_assert: Box::new(|e: &Element| assert!(e.is_null())),
            owned_asserts: vec![],
        }
    }

    fn bool_case() -> Case {
        Case {
            elem: true.into(),
            ion_type: IonType::Bool,
            ops: vec![AsBool, TryIntoBool],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_bool().expect("expected bool");
                let expected = Element::from(true);
                assert_eq!(Some(true), e.as_bool());
                assert_eq!(&expected, e);
            }),
            owned_asserts: vec![Box::new(|e: Element| assert!(e.try_into_bool().is_ok()))],
        }
    }

    fn i64_case() -> Case {
        Case {
            elem: 100.into(),
            ion_type: IonType::Int,
            ops: vec![AsAnyInt, TryIntoInt, TryIntoI64],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_i64().expect("expected i64");
                let _ = e.expect_int().expect("expected int");
                let expected: Element = 100i64.into();
                assert_eq!(Some(&Int::from(100i64)), e.as_int());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(&expected, e);
            }),
            owned_asserts: vec![
                assert_pass_try_into!(try_into_i64),
                assert_pass_try_into!(try_into_int),
            ],
        }
    }

    fn big_int_case() -> Case {
        Case {
            elem: ((i64::MAX as i128) + 1).into(),
            ion_type: IonType::Int,
            ops: vec![AsAnyInt, TryIntoInt],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_int().expect("expected int");
                let expected: Element = 9223372036854775808i128.into();
                assert_eq!(Some(&Int::from(9223372036854775808i128)), e.as_int());
                assert_eq!(&expected, e);
            }),
            owned_asserts: vec![assert_pass_try_into!(try_into_int)],
        }
    }

    fn f64_case() -> Case {
        Case {
            elem: 16.0.into(),
            ion_type: IonType::Float,
            ops: vec![AsF64, TryIntoF64],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_float().expect("expected float");
                let expected = Element::from(16.0f64);
                assert_eq!(Some(16.0), e.as_float());
                assert_eq!(&expected, e);
            }),
            owned_asserts: vec![assert_pass_try_into!(try_into_float)],
        }
    }

    fn timestamp_case() -> Case {
        Case {
            elem: make_timestamp("2014-10-16T12:01:00-00:00").into(),
            ion_type: IonType::Timestamp,
            ops: vec![AsTimestamp, TryIntoTimestamp],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_timestamp().expect("expected timestamp");
                let expected: Element = make_timestamp("2014-10-16T12:01:00+00:00").into();
                assert_eq!(
                    Some(make_timestamp("2014-10-16T12:01:00+00:00")),
                    e.as_timestamp()
                );
                assert_eq!(&expected, e);
            }),
            owned_asserts: vec![assert_pass_try_into!(try_into_timestamp)],
        }
    }

    fn decimal_case() -> Case {
        Case {
            elem: Decimal::new(8, 3).into(),
            ion_type: IonType::Decimal,
            ops: vec![AsDecimal, TryIntoDecimal],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_decimal().expect("expected decimal");
                let expected: Element = Decimal::new(8, 3).into();
                assert_eq!(Some(Decimal::new(80, 2)), e.as_decimal());
                assert_eq!(&expected, e);
            }),
            owned_asserts: vec![assert_pass_try_into!(try_into_decimal)],
        }
    }

    fn string_case() -> Case {
        Case {
            elem: "hello".into(),
            ion_type: IonType::String,
            ops: vec![AsStr, TryIntoText, TryIntoString],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_text().expect("expected text");
                let _ = e.expect_string().expect("expected string");
                assert_eq!(Some("hello"), e.as_text())
            }),
            owned_asserts: vec![
                assert_pass_try_into!(try_into_text),
                assert_pass_try_into!(try_into_string),
            ],
        }
    }

    fn symbol_case() -> Case {
        Case {
            elem: Symbol::owned("foo").into(),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr, TryIntoText, TryIntoSymbol],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_text().expect("expected text");
                let _ = e.expect_symbol().expect("expected symbol");
                assert_eq!(Some("foo"), e.as_symbol().unwrap().text());
                assert_eq!(Some("foo"), e.as_text());
            }),
            owned_asserts: vec![assert_pass_try_into!(try_into_symbol)],
        }
    }

    fn blob_case() -> Case {
        Case {
            elem: Element::blob(b"hello"),
            ion_type: IonType::Blob,
            ops: vec![AsBytes, TryIntoLob, TryIntoBlob],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_lob().expect("expected lob");
                let _ = e.expect_blob().expect("expected blob");
                assert_eq!(Some("hello".as_bytes()), e.as_lob())
            }),
            owned_asserts: vec![
                assert_pass_try_into!(try_into_lob),
                assert_pass_try_into!(try_into_blob),
                Box::new(|e: Element| {
                    if let Value::Blob(bytes) = e.into_value() {
                        let data: Vec<_> = bytes.into();
                        assert_eq!(b"hello", data.as_slice());
                    } else {
                        panic!("expected blob");
                    }
                }),
            ],
        }
    }

    fn clob_case() -> Case {
        Case {
            elem: Element::clob(b"goodbye"),
            ion_type: IonType::Clob,
            ops: vec![AsBytes, TryIntoLob, TryIntoClob],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_lob().expect("expected lob");
                let _ = e.expect_clob().expect("expected clob");
                assert_eq!(Some("goodbye".as_bytes()), e.as_lob())
            }),
            owned_asserts: vec![
                assert_pass_try_into!(try_into_lob),
                assert_pass_try_into!(try_into_clob),
                Box::new(|e: Element| {
                    if let Value::Clob(bytes) = e.into_value() {
                        let data: Vec<_> = bytes.into();
                        assert_eq!(b"goodbye", data.as_slice());
                    } else {
                        panic!("expected clob");
                    }
                }),
            ],
        }
    }

    fn list_case() -> Case {
        Case {
            elem: ion_list![true, false].into(),
            ion_type: IonType::List,
            ops: vec![AsSequence, TryIntoList, TryIntoSequence],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_list().expect("expected list");
                let _ = e.expect_sequence().expect("expected sequence");
                let actual = e.as_sequence().unwrap();
                let expected: Vec<Element> = ion_vec([true, false]);
                // assert the length of list
                assert_eq!(2, actual.len());
                for (i, actual_item) in actual.elements().enumerate() {
                    // assert the list elements one-by-one
                    assert_eq!(&expected[i], actual_item);
                }
                assert!(!actual.is_empty());
            }),
            owned_asserts: vec![
                assert_pass_try_into!(try_into_list),
                assert_pass_try_into!(try_into_sequence),
            ],
        }
    }

    fn sexp_case() -> Case {
        Case {
            elem: ion_sexp!(true false).into(),
            ion_type: IonType::SExp,
            ops: vec![AsSequence, TryIntoSexp, TryIntoSequence],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_sexp().expect("expected sexp");
                let _ = e.expect_sequence().expect("expected sequence");
                let actual = e.as_sequence().unwrap();
                let expected: Vec<Element> = ion_vec([true, false]);
                // assert the length of s-expression
                assert_eq!(2, actual.len());
                for (i, actual_item) in actual.elements().enumerate() {
                    // assert the s-expression elements one-by-one
                    assert_eq!(&expected[i], actual_item);
                }
            }),
            owned_asserts: vec![
                assert_pass_try_into!(try_into_sexp),
                assert_pass_try_into!(try_into_sequence),
            ],
        }
    }

    fn struct_case() -> Case {
        Case {
            elem: ion_struct! {"greetings": "hello", "name": "ion"}.into(),
            ion_type: IonType::Struct,
            ops: vec![AsStruct, TryIntoStruct],
            op_assert: Box::new(|e: &Element| {
                let _ = e.expect_struct().expect("expected struct");
                let actual: &Struct = e.as_struct().unwrap();

                // verify that the field order is maintained when creating Struct
                assert_eq!(
                    actual.iter().next(),
                    Some((&"greetings".into(), &"hello".into()))
                );

                assert_eq!(actual.get("greetings"), Some(&"hello".into()));
            }),
            owned_asserts: vec![assert_pass_try_into!(try_into_struct)],
        }
    }
    // TODO add more tests to remove the separate Owned/Borrowed tests and only keep generic tests

    #[rstest]
    #[case::owned_null(null_case())]
    #[case::owned_bool(bool_case())]
    #[case::owned_i64(i64_case())]
    #[case::owned_big_int(big_int_case())]
    #[case::owned_f64(f64_case())]
    #[case::owned_decimal(decimal_case())]
    #[case::owned_timestamp(timestamp_case())]
    #[case::owned_string(string_case())]
    #[case::owned_blob(blob_case())]
    #[case::owned_clob(clob_case())]
    #[case::owned_list(list_case())]
    #[case::owned_sexp(sexp_case())]
    #[case::owned_struct(struct_case())]
    #[case::owned_symbol(symbol_case())]
    fn element_accessors(#[case] input_case: Case) {
        // table of negative assertions for each operation
        let neg_table: Vec<(ElemOp, ElemAssertFn)> = vec![
            (IsNull, Box::new(|e| assert!(!e.is_null()))),
            (AsBool, Box::new(|e| assert_eq!(None, e.as_bool()))),
            (
                AsAnyInt,
                Box::new(|e| {
                    assert_eq!(None, e.as_int());
                    assert_eq!(None, e.as_i64());
                }),
            ),
            (AsF64, Box::new(|e| assert_eq!(None, e.as_float()))),
            (AsDecimal, Box::new(|e| assert_eq!(None, e.as_decimal()))),
            (
                AsTimestamp,
                Box::new(|e| assert_eq!(None, e.as_timestamp())),
            ),
            (AsStr, Box::new(|e| assert_eq!(None, e.as_text()))),
            (AsSym, Box::new(|e| assert_eq!(None, e.as_symbol()))),
            (AsBytes, Box::new(|e| assert_eq!(None, e.as_lob()))),
            (AsSequence, Box::new(|e| assert!(e.as_sequence().is_none()))),
            (AsStruct, Box::new(|e| assert_eq!(None, e.as_struct()))),
        ];

        let owned_neg_table: Vec<(ElemOp, OwnedElemAssertFn)> = vec![
            (TryIntoInt, assert_fail_try_into!(try_into_int)),
            (TryIntoI64, assert_fail_try_into!(try_into_i64)),
            (TryIntoF64, assert_fail_try_into!(try_into_float)),
            (TryIntoDecimal, assert_fail_try_into!(try_into_decimal)),
            (TryIntoTimestamp, assert_fail_try_into!(try_into_timestamp)),
            (TryIntoText, assert_fail_try_into!(try_into_text)),
            (TryIntoString, assert_fail_try_into!(try_into_string)),
            (TryIntoSymbol, assert_fail_try_into!(try_into_symbol)),
            (TryIntoBool, assert_fail_try_into!(try_into_bool)),
            (TryIntoLob, assert_fail_try_into!(try_into_lob)),
            (TryIntoBlob, assert_fail_try_into!(try_into_blob)),
            (TryIntoClob, assert_fail_try_into!(try_into_clob)),
            (TryIntoSequence, assert_fail_try_into!(try_into_sequence)),
            (TryIntoList, assert_fail_try_into!(try_into_list)),
            (TryIntoSexp, assert_fail_try_into!(try_into_sexp)),
            (TryIntoStruct, assert_fail_try_into!(try_into_struct)),
        ];

        // produce the table of assertions to operate on, replacing the one specified by
        // the test case
        let valid_ops: HashSet<ElemOp> = input_case.ops.into_iter().collect();
        let borrowed_pos = once(input_case.op_assert);
        let owned_pos = input_case.owned_asserts.into_iter();
        let borrowed_neg = neg_table
            .into_iter()
            .filter_map(|(op, f)| (!valid_ops.contains(&op)).then_some(f));
        let owned_neg = owned_neg_table
            .into_iter()
            .filter_map(|(op, f)| (!valid_ops.contains(&op)).then_some(f));
        let borrowed = borrowed_pos.chain(borrowed_neg);
        let owned = owned_pos
            .chain(owned_neg)
            .map(|owned_fn| Box::new(|e: &Element| owned_fn(e.clone())) as ElemAssertFn);
        let op_assertions: Vec<ElemAssertFn> = borrowed.chain(owned).collect();

        // construct an element to test
        assert_eq!(input_case.ion_type, input_case.elem.ion_type());

        // assert value & annotation accessors
        let val_ref = input_case.elem.value();
        let ann_ref = input_case.elem.annotations();
        let val_owned = input_case.elem.clone().into_value();
        let ann_owned = input_case.elem.clone().into_annotations();
        let (ann_owned2, val_owned2) = input_case.elem.clone().into_parts();
        assert_eq!(val_ref, &val_owned);
        assert_eq!(val_owned, val_owned2);
        assert_eq!(ann_ref, &ann_owned);
        assert_eq!(ann_owned, ann_owned2);

        // assert element operations
        for assert in op_assertions {
            assert(&input_case.elem);
        }

        // assert that an element as-is is equal to itself
        // Creating an alias here bypasses clippy's objection to comparing any literal to itself.
        let itself = &input_case.elem;
        assert_eq!(&input_case.elem, itself);
    }
}

#[cfg(test)]
mod value_tests {
    use std::fmt::Debug;

    use rstest::*;

    use crate::element::*;
    use crate::ion_data::IonEq;
    use crate::types::UInt;
    use crate::{ion_list, ion_sexp, ion_struct, IonType};

    #[test]
    fn demonstrate_element_implements_send() {
        use std::thread;
        // The Element type must implement `Send` in order for values to be
        // moved between threads. If changes are made to the `Element` type
        // or its nested field types (like the `Value` enum and its variants)
        // which accidentally cause it not to implement `Send`, then this test
        // will fail to compile.
        let list: Element = ion_list![1, 2, 3].into();
        thread::scope(|_| {
            // Move `list` into this scope, demonstrating `Send`
            let elements = [list];
            // Trivial assertion to use `elements`
            assert_eq!(elements.len(), 1);
        });
    }

    #[rstest]
    #[case::strings(
        Element::from("hello"), // An explicitly constructed String Element
        "hello"                 // A Rust &str, which implements Into<Element>
    )]
    #[case::symbols(
        Element::from(Symbol::owned("hello")), // An explicitly constructed Symbol Element
        Symbol::owned("hello")                 // A Symbol, which implements Into<Element>
    )]
    #[case::struct_(
        ion_struct!{"greetings": "hello"},
        Element::read_one(r#"{greetings: "hello"}"#).unwrap()
    )]
    #[case::strings(
        Element::from("hello"), // An explicitly constructed String Element
        "hello"                 // A Rust &str, which implements Into<Element>
    )]
    #[case::symbols(
        Element::from(Symbol::owned("hello")), // An explicitly constructed Symbol Element
        Symbol::owned("hello")                 // A Symbol, which implements Into<Element>
    )]
    #[case::struct_(
        ion_struct!{"greetings": "hello"},
        Element::read_one(r#"{greetings: "hello"}"#).unwrap()
    )]
    fn owned_element_accessors<E1, E2>(#[case] e1: E1, #[case] e2: E2)
    where
        E1: Into<Element>,
        E2: Into<Element>,
    {
        // assert that both element construction methods create the same element
        assert_eq!(e1.into(), e2.into());
    }

    #[rstest]
    #[case::struct_(ion_struct!{"greetings": "hello", "name": "Ion"}, 2)]
    #[case::list(ion_list!["greetings", 5, true], 3)]
    #[case::sexp(ion_sexp!(5 true), 2)]
    fn owned_container_len_test<I: Into<Element>>(#[case] container: I, #[case] length: usize) {
        let container = container.into();
        match container.ion_type() {
            IonType::List | IonType::SExp => {
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

    #[rstest]
    #[case::struct_(ion_struct!{"greetings": "hello", "name": "Ion"}, false)]
    #[case::list(ion_list!["greetings", 5, true], false)]
    #[case::list_empty(ion_list![], true)]
    #[case::sexp(ion_sexp!(5 true), false)]
    #[case::sexp_empty(ion_sexp!(), true)]
    fn owned_container_is_empty_test<I: Into<Element>>(
        #[case] container: I,
        #[case] is_empty: bool,
    ) {
        let container = container.into();
        match container.ion_type() {
            IonType::List | IonType::SExp => {
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

    #[test]
    fn list_display_roundtrip() {
        let list = ion_list![1, 2, 3, true, false];

        // Use the Display impl to serialize the list to text
        let text_list = format!("{list}");
        // Parse the result and make sure it represents the same data
        let expected_element: Element = list.into();
        let actual_element = Element::read_one(text_list).unwrap();
        assert!(expected_element.ion_eq(&actual_element));
    }

    #[test]
    fn sexp_display_roundtrip() {
        let sexp = ion_sexp! (1 2 3 true false);

        // Use the Display impl to serialize the sexp to text
        let text_sexp = format!("{sexp}");
        // Parse the result and make sure it represents the same data
        let expected_element: Element = sexp.into();
        let actual_element = Element::read_one(text_sexp).unwrap();
        assert!(expected_element.ion_eq(&actual_element));
    }

    #[test]
    fn struct_display_roundtrip() {
        let struct_ = ion_struct! {"foo": 1, "bar": 2, "baz": ion_list! [true, false]};

        // Use the Display impl to serialize the struct to text
        let text_struct = format!("{struct_}");
        // Parse the result and make sure it represents the same data
        let expected_element: Element = struct_.into();
        let actual_element = Element::read_one(text_struct).unwrap();
        assert!(expected_element.ion_eq(&actual_element));
    }

    #[rstest]
    #[case::i8(42i8)]
    #[case::i8_neg(-42i8)]
    #[case::i16(42i16)]
    #[case::i16_neg(-42i16)]
    #[case::i32(42i32)]
    #[case::i32_neg(-42i32)]
    #[case::i64(42i64)]
    #[case::i64_neg(-42i64)]
    #[case::i128(42i128)]
    #[case::i128_neg(-42i128)]
    #[case::isize(42isize)]
    #[case::isize_neg(-42isize)]
    #[case::int(Int::from(42i64))]
    #[case::int_neg(Int::from(-42i64))]
    #[case::u8(42u8)]
    #[case::u16(42u16)]
    #[case::u32(42u32)]
    #[case::u64(42u64)]
    #[case::u128(42u128)]
    #[case::usize(42usize)]
    #[case::uint(UInt::from(42u64))]
    fn element_from_int<I, E>(#[case] source_int: I)
    where
        E: Debug,
        I: TryInto<Int, Error = E>,
    {
        let int: Int = source_int.try_into().unwrap();
        let element: Element = int.into();
        assert_eq!(element.expect_i64(), int.expect_i64())
    }

    #[rstest]
    fn read_a_symbol_terminated_by_end_of_input(
        #[values(
        "a","b","c","d","e","f","g","h","i","j",
        "k","l","m","n","o","p","q","r","s","t",
        // These are all things that look like they _could_
        // be an incomplete value (or IVM).
        "fa", "fal", "fals",
        "na", "nu", "nul",
        "tr", "tru",
        "$ion_",
        "$ion_1",
        "$ion_1_",
        )]
        input: &str,
    ) -> IonResult<()> {
        let value = Element::read_one(input)?;
        let actual_text = value.as_symbol().unwrap().text().unwrap();
        assert_eq!(actual_text, input);
        Ok(())
    }
}
