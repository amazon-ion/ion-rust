// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a dynamically typed, materialized representation of an Ion value.
//!
//! An [Element](Element) represents an `(annotations, value)` pair, where a `value` is
//! an Ion `integer`, `float`, `list`, `struct`, etc.
//!
//! For reference here are a couple other _value_ style APIs for JSON:
//! * [`simd_json`'s `Value` API][simd-json-value]
//! * [`serde_json`'s `Value` API][serde-json-value]
//!
//! [simd-json-value]: https://docs.rs/simd-json/latest/simd_json/value/index.html
//! [serde-json-value]: https://docs.serde.rs/serde_json/value/enum.Value.html

use crate::binary::binary_writer::BinaryWriterBuilder;
use crate::element::builders::{SequenceBuilder, StructBuilder};
use crate::element::reader::ElementReader;
use crate::ion_data::{IonEq, IonOrd};
use crate::ion_writer::IonWriter;
use crate::text::text_formatter::IonValueFormatter;
use crate::text::text_writer::TextWriterBuilder;
use crate::{ion_data, Decimal, Format, Int, IonResult, IonType, Str, Symbol, TextKind, Timestamp};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::io;

mod annotations;
pub mod builders;
pub mod element_stream_reader;
pub mod element_stream_writer;
pub(crate) mod iterators;
pub mod reader;
pub mod writer;

// Re-export the Value variant types and traits so they can be accessed directly from this module.
use crate::data_source::IonDataSource;
use crate::element::writer::ElementWriter;
use crate::reader::ReaderBuilder;
pub use crate::types::{Blob, Bytes, Clob};
pub use annotations::{Annotations, IntoAnnotations};

pub use crate::types::{List, SExp, Sequence, Struct};

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

impl IonOrd for Value {
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

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ivf = IonValueFormatter { output: f };
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

#[cfg(feature = "experimental-streaming")]
impl From<crate::tokens::ScalarValue> for Value {
    fn from(value: crate::tokens::ScalarValue) -> Self {
        use crate::tokens::ScalarValue;
        match value {
            ScalarValue::Bool(bool) => Value::Bool(bool),
            ScalarValue::Int(int) => Value::Int(int),
            ScalarValue::Float(float) => Value::Float(float),
            ScalarValue::Decimal(decimal) => Value::Decimal(decimal),
            ScalarValue::Timestamp(timestamp) => Value::Timestamp(timestamp),
            ScalarValue::String(text) => Value::String(text),
            ScalarValue::Symbol(symbol) => Value::Symbol(symbol),
            ScalarValue::Blob(bytes) => Value::Blob(bytes),
            ScalarValue::Clob(bytes) => Value::Clob(bytes),
        }
    }
}

/// Allows types that can be converted into an Ion [Value] to also specify annotations, producing
/// an [Element].
///
/// ```
/// use ion_rs::element::{Element, IntoAnnotatedElement, Value};
///
/// // Explicit conversion of a Rust bool (`true`) into a `Value`...
/// let boolean_value: Value = true.into();
/// // and then into an `Element`...
/// let mut boolean_element: Element = boolean_value.into();
/// // and then adding annotations to the `Element`.
/// boolean_element = boolean_element.with_annotations(["foo", "bar"]);
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
impl IonOrd for Element {
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

/// An `(annotations, value)` pair representing an Ion value.
#[derive(Debug, Clone)]
pub struct Element {
    annotations: Annotations,
    value: Value,
}

impl Element {
    pub(crate) fn new(annotations: Annotations, value: impl Into<Value>) -> Self {
        Self {
            annotations,
            value: value.into(),
        }
    }

    /// Returns a reference to this [Element]'s [Value].
    ///
    /// ```
    /// use ion_rs::element::{Element, Value};
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

    pub fn integer<I: Into<Int>>(integer: I) -> Element {
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
            Value::String(text) => Some(text.as_ref()),
            Value::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match &self.value {
            Value::String(text) => Some(text.as_ref()),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<&Symbol> {
        match &self.value {
            Value::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match &self.value {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_lob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) | Value::Clob(bytes) => Some(bytes.as_ref()),
            _ => None,
        }
    }

    pub fn as_blob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Blob(bytes) => Some(bytes.as_ref()),
            _ => None,
        }
    }

    pub fn as_clob(&self) -> Option<&[u8]> {
        match &self.value {
            Value::Clob(bytes) => Some(bytes.as_ref()),
            _ => None,
        }
    }

    pub fn as_sequence(&self) -> Option<&Sequence> {
        match &self.value {
            Value::SExp(s) | Value::List(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_struct(&self) -> Option<&Struct> {
        match &self.value {
            Value::Struct(structure) => Some(structure),
            _ => None,
        }
    }

    /// Reads a single Ion [`Element`] from the provided data source.
    ///
    /// If the data source is empty, returns `Ok(None)`.
    /// If the data source has at least one value, returns `Ok(Some(Element))`.
    /// If the data source has invalid data, returns `Err`.
    pub fn read_first<A: AsRef<[u8]>>(data: A) -> IonResult<Option<Element>> {
        let bytes: &[u8] = data.as_ref();
        // Create an iterator over the Elements in the data
        let mut reader = ReaderBuilder::default().build(bytes)?;
        reader.read_next_element()
    }

    /// Reads a single Ion [`Element`] from the provided data source. If the input has invalid
    /// data or does not contain at exactly one Ion value, returns `Err(IonError)`.
    pub fn read_one<A: AsRef<[u8]>>(data: A) -> IonResult<Element> {
        let bytes: &[u8] = data.as_ref();
        // Create an iterator over the Elements in the data
        let mut reader = ReaderBuilder::default().build(bytes)?;
        reader.read_one_element()
    }

    /// Reads all available [`Element`]s from the provided data source.
    ///
    /// If the input has valid data, returns `Ok(Vec<Element>)`.
    /// If the input has invalid data, returns `Err(IonError)`.
    pub fn read_all<A: AsRef<[u8]>>(data: A) -> IonResult<Sequence> {
        Element::iter(data.as_ref())?.collect()
    }

    /// Returns an iterator over the Elements in the provided Ion data source.
    /// If the data source cannot be read or contains invalid Ion data, this method
    /// will return an `Err`.
    pub fn iter<'a, I: IonDataSource + 'a>(
        source: I,
    ) -> IonResult<impl Iterator<Item = IonResult<Element>> + 'a> {
        Ok(ReaderBuilder::default().build(source)?.into_elements())
    }

    /// Serializes this element to the provided writer.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::element::Element;
    /// use ion_rs::{ion_list, IonWriter, TextWriterBuilder};
    ///
    /// // Construct an Element
    /// let element_before: Element = ion_list! [1, 2, 3].into();
    ///
    /// // Serialize the Element to a writer
    /// let mut writer = TextWriterBuilder::default().build(Vec::new())?;
    /// element_before.write_to(&mut writer)?;
    /// writer.flush()?;
    ///
    /// // Read the Element back from the serialized form
    /// let element_after = Element::read_one(writer.output())?;
    ///
    /// // Confirm that no data was lost
    /// assert_eq!(element_before, element_after);
    ///# Ok(())
    ///# }
    /// ```
    #[cfg(feature = "experimental-writer")]
    pub fn write_to<W: ElementWriter>(&self, writer: &mut W) -> IonResult<()> {
        Self::write_element_to(self, writer)
    }

    // This method performs the logic of the `write_to` method above, but is always limited to
    // crate visibility. The `write_to` method can be exposed publicly by enabling the
    // "experimental-writer" feature.
    pub(crate) fn write_element_to<W: ElementWriter>(&self, writer: &mut W) -> IonResult<()> {
        writer.write_element(self)?;
        Ok(())
    }

    #[doc = r##"
Serializes this [`Element`] as Ion, writing the resulting bytes to the provided [`io::Write`].
The caller must verify that `output` is either empty or only contains Ion of the same
format (text or binary) before writing begins.

This method constructs a new writer for each invocation, which means that there will only be a single
top level value in the output stream. Writing several values to the same stream is preferable to
maximize encoding efficiency."##]
    #[cfg_attr(
        feature = "experimental-writer",
        doc = r##"
To reuse a writer and have greater control over resource
management, see [`Element::write_to`].
```
# use ion_rs::{Format, IonResult, TextKind};
# fn main() -> IonResult<()> {
use ion_rs::element::Element;
use ion_rs::ion_list;

// Construct an Element
let element_before: Element = ion_list! [1, 2, 3].into();

// Write the Element to a buffer using a specified format
let mut buffer = Vec::new();
element_before.write_as(Format::Text(TextKind::Pretty), &mut buffer)?;

// Read the Element back from the serialized form
let element_after = Element::read_one(&buffer)?;

// Confirm that no data was lost
assert_eq!(element_before, element_after);
# Ok(())
# }
```
"##
    )]
    pub fn write_as<W: io::Write>(&self, format: Format, output: W) -> IonResult<()> {
        match format {
            Format::Text(text_kind) => {
                let mut text_writer = TextWriterBuilder::new(text_kind).build(output)?;
                Element::write_element_to(self, &mut text_writer)?;
                text_writer.flush()
            }
            Format::Binary => {
                let mut binary_writer = BinaryWriterBuilder::default().build(output)?;
                Element::write_element_to(self, &mut binary_writer)?;
                binary_writer.flush()
            }
        }
    }

    #[doc = r##"
Serializes this [`Element`] as binary Ion, returning the output as a `Vec<u8>`.
"##]
    #[cfg_attr(
        feature = "experimental-writer",
        doc = r##"
This is a convenience method; it is less efficient than [`Element::write_to`] because:
1. It must allocate a new `Vec<u8>` to fill and return.
2. It encodes this [`Element`] as its own binary Ion stream, limiting the benefit of the
   symbol table.
"##
    )]
    #[doc = r##"
```
# use ion_rs::IonResult;
# fn main() -> IonResult<()> {
use ion_rs::element::Element;
use ion_rs::ion_list;

// Construct an Element
let element_before: Element = ion_list! [1, 2, 3].into();

// Write the Element to a buffer as binary Ion
let binary_ion: Vec<u8> = element_before.to_binary()?;

// Read the Element back from the serialized form
let element_after = Element::read_one(&binary_ion)?;

// Confirm that no data was lost
assert_eq!(element_before, element_after);
# Ok(())
# }
```
"##]
    pub fn to_binary(&self) -> IonResult<Vec<u8>> {
        let mut buffer = Vec::new();
        self.write_as(Format::Binary, &mut buffer)?;
        Ok(buffer)
    }

    #[doc = r##"
Serializes this [`Element`] as text Ion using the requested [`TextKind`] and returning the
output as a `String`.
"##]
    #[cfg_attr(
        feature = "experimental-writer",
        doc = r##"
This is a convenience method; to provide your own buffer instead of allocating a `String`
on each call, see [`Element::write_as`]. To provide your own writer instead of constructing
a new `String` and writer on each call, see [`Element::write_to`].
    "##
    )]
    ///

    #[doc = r##"
```
# use ion_rs::IonResult;
# fn main() -> IonResult<()> {
use ion_rs::ion_list;
use ion_rs::element::Element;
use ion_rs::TextKind;

// Construct an Element
let element_before: Element = ion_list! [1, 2, 3].into();

let text_ion: String = element_before.to_text(TextKind::Pretty)?;

// Read the Element back from the serialized form
let element_after = Element::read_one(&text_ion)?;

// Confirm that no data was lost
assert_eq!(element_before, element_after);
# Ok(())
# }
```
    "##]
    pub fn to_text(&self, text_kind: TextKind) -> IonResult<String> {
        let mut buffer = Vec::new();
        self.write_as(Format::Text(text_kind), &mut buffer)?;
        Ok(std::str::from_utf8(&buffer)
            .expect("writer produced invalid utf-8")
            .to_string())
    }
}

impl Display for Element {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let mut ivf = IonValueFormatter { output: f };

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

#[cfg(test)]
mod tests {
    use crate::element::annotations::IntoAnnotations;
    use crate::{ion_list, ion_sexp, ion_struct, Decimal, Int, IonType, Symbol, Timestamp};
    use chrono::*;
    use rstest::*;
    use std::iter::{once, Once};

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
    }

    impl IntoIterator for ElemOp {
        type Item = ElemOp;
        type IntoIter = <Once<ElemOp> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            once(self)
        }
    }

    use crate::element::{Annotations, Element, IntoAnnotatedElement, Struct};
    use crate::types::IntAccess;
    use num_bigint::BigInt;
    use std::collections::HashSet;
    use std::str::FromStr;
    use ElemOp::*;

    type ElemAssertFn = Box<dyn FnOnce(&Element)>;

    struct Case {
        elem: Element,
        ion_type: IonType,
        ops: Vec<ElemOp>,
        op_assert: ElemAssertFn,
    }

    fn null_case() -> Case {
        Case {
            elem: Element::from(IonType::Null), // null.null
            ion_type: IonType::Null,
            ops: vec![IsNull],
            op_assert: Box::new(|e: &Element| assert!(e.is_null())),
        }
    }

    fn bool_case() -> Case {
        Case {
            elem: true.into(),
            ion_type: IonType::Bool,
            ops: vec![AsBool],
            op_assert: Box::new(|e: &Element| {
                let expected = Element::from(true);
                assert_eq!(Some(true), e.as_bool());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn i64_case() -> Case {
        Case {
            elem: 100.into(),
            ion_type: IonType::Int,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = 100i64.into();
                assert_eq!(Some(&Int::from(100i64)), e.as_int());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(None, e.as_big_int());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn big_int_case() -> Case {
        Case {
            elem: BigInt::from(100).into(),
            ion_type: IonType::Int,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = BigInt::from(100).into();
                assert_eq!(Some(&Int::from(BigInt::from(100))), e.as_int());
                assert_eq!(BigInt::from_str("100").unwrap(), *e.as_big_int().unwrap());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn f64_case() -> Case {
        Case {
            elem: 16.0.into(),
            ion_type: IonType::Float,
            ops: vec![AsF64],
            op_assert: Box::new(|e: &Element| {
                let expected = Element::from(16.0f64);
                assert_eq!(Some(16.0), e.as_float());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn timestamp_case() -> Case {
        Case {
            elem: make_timestamp("2014-10-16T12:01:00-00:00").into(),
            ion_type: IonType::Timestamp,
            ops: vec![AsTimestamp],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = make_timestamp("2014-10-16T12:01:00+00:00").into();
                assert_eq!(
                    Some(&make_timestamp("2014-10-16T12:01:00+00:00")),
                    e.as_timestamp()
                );
                assert_eq!(&expected, e);
            }),
        }
    }

    fn decimal_case() -> Case {
        Case {
            elem: Decimal::new(8, 3).into(),
            ion_type: IonType::Decimal,
            ops: vec![AsDecimal],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = Decimal::new(8, 3).into();
                assert_eq!(Some(&Decimal::new(80, 2)), e.as_decimal());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn string_case() -> Case {
        Case {
            elem: "hello".into(),
            ion_type: IonType::String,
            ops: vec![AsStr],
            op_assert: Box::new(|e: &Element| assert_eq!(Some("hello"), e.as_text())),
        }
    }

    fn symbol_case() -> Case {
        Case {
            elem: Symbol::owned("foo").into(),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &Element| {
                assert_eq!(Some("foo"), e.as_symbol().unwrap().text());
                assert_eq!(Some("foo"), e.as_text());
            }),
        }
    }

    fn blob_case() -> Case {
        Case {
            elem: Element::blob(b"hello"),
            ion_type: IonType::Blob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &Element| assert_eq!(Some("hello".as_bytes()), e.as_lob())),
        }
    }

    fn clob_case() -> Case {
        Case {
            elem: Element::clob(b"goodbye"),
            ion_type: IonType::Clob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &Element| assert_eq!(Some("goodbye".as_bytes()), e.as_lob())),
        }
    }

    fn list_case() -> Case {
        Case {
            elem: ion_list![true, false].into(),
            ion_type: IonType::List,
            ops: vec![AsSequence],
            op_assert: Box::new(|e: &Element| {
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
        }
    }

    fn sexp_case() -> Case {
        Case {
            elem: ion_sexp!(true false).into(),
            ion_type: IonType::SExp,
            ops: vec![AsSequence],
            op_assert: Box::new(|e: &Element| {
                let actual = e.as_sequence().unwrap();
                let expected: Vec<Element> = ion_vec([true, false]);
                // assert the length of s-expression
                assert_eq!(2, actual.len());
                for (i, actual_item) in actual.elements().enumerate() {
                    // assert the s-expression elements one-by-one
                    assert_eq!(&expected[i], actual_item);
                }
            }),
        }
    }

    fn struct_case() -> Case {
        Case {
            elem: ion_struct! {"greetings": "hello", "name": "ion"}.into(),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &Element| {
                let actual: &Struct = e.as_struct().unwrap();

                // verify that the field order is maintained when creating Struct
                assert_eq!(
                    actual.iter().next(),
                    Some((&"greetings".into(), &"hello".into()))
                );

                assert_eq!(actual.get("greetings"), Some(&"hello".into()));
            }),
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
                    assert_eq!(None, e.as_big_int());
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

        // produce the table of assertions to operate on, replacing the one specified by
        // the test case
        let valid_ops: HashSet<ElemOp> = input_case.ops.into_iter().collect();
        let op_assertions: Vec<ElemAssertFn> = neg_table
            .into_iter()
            .filter(|(op, _)| !valid_ops.contains(op))
            .map(|(_, neg_assert)| neg_assert)
            .chain(once(input_case.op_assert))
            .collect();

        // construct an element to test
        assert_eq!(input_case.ion_type, input_case.elem.ion_type());

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
    use crate::element::*;
    use crate::ion_data::IonEq;
    use crate::types::UInt;
    use crate::{ion_list, ion_sexp, ion_struct, IonType};
    use rstest::*;

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
            let elements = vec![list];
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
    fn element_from_int(#[case] source_int: impl Into<Int>) {
        let int: Int = source_int.into();
        let element: Element = int.clone().into();
        assert_eq!(element.as_int().unwrap().expect_i64(), int.expect_i64())
    }
}
