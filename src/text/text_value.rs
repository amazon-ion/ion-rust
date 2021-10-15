use crate::raw_symbol_token::{local_sid_token, text_token, RawSymbolToken};
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::IonType;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AnnotatedTextValue {
    annotations: Vec<RawSymbolToken>,
    value: TextValue,
}

impl AnnotatedTextValue {
    pub(crate) fn new(annotations: Vec<RawSymbolToken>, value: TextValue) -> Self {
        AnnotatedTextValue { annotations, value }
    }

    pub(crate) fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    pub(crate) fn value(&self) -> &TextValue {
        &self.value
    }

    pub(crate) fn annotations(&self) -> &[RawSymbolToken] {
        &self.annotations
    }
}

impl PartialEq<TextValue> for AnnotatedTextValue {
    fn eq(&self, other: &TextValue) -> bool {
        if self.annotations.len() > 0 {
            return false;
        }
        *self.value() == *other
    }
}

/// Represents a single value encountered in a text Ion stream. The enum includes variants for each
/// scalar type as well as variants for the beginning of each container type.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TextValue {
    Null(IonType),
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    // TODO: String(&str) will be possible if/when we add reusable buffers to the TextReader.
    String(String),
    Symbol(RawSymbolToken),
    // TODO: [BC]lob(&[u8]) will be possible if/when we add reusable buffers to the TextReader.
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    ListStart,
    SExpressionStart,
    StructStart,
}

impl TextValue {
    /// Returns the IonType associated with the TextValue in question.
    pub fn ion_type(&self) -> IonType {
        match self {
            TextValue::Null(ion_type) => *ion_type,
            TextValue::Boolean(_) => IonType::Boolean,
            TextValue::Integer(_) => IonType::Integer,
            TextValue::Float(_) => IonType::Float,
            TextValue::Decimal(_) => IonType::Decimal,
            TextValue::Timestamp(_) => IonType::Timestamp,
            TextValue::String(_) => IonType::String,
            TextValue::Symbol(_) => IonType::Symbol,
            TextValue::Blob(_) => IonType::Blob,
            TextValue::Clob(_) => IonType::Clob,
            TextValue::ListStart => IonType::List,
            TextValue::SExpressionStart => IonType::SExpression,
            TextValue::StructStart => IonType::Struct,
        }
    }

    /// Converts this [TextValue] into an [AnnotatedTextValue] with the specified annotations.
    pub fn with_annotations<I: IntoAnnotations>(self, annotations: I) -> AnnotatedTextValue {
        AnnotatedTextValue::new(annotations.into_annotations(), self)
    }

    /// Converts this [TextValue] into an [AnnotatedTextValue] with no annotations.
    pub fn without_annotations(self) -> AnnotatedTextValue {
        // Vec::new() doesn't perform heap allocations
        AnnotatedTextValue::new(Vec::new(), self)
    }
}

/// Converts a given type into a `Vec<OwnedSymbolToken>`.
pub trait IntoAnnotations {
    fn into_annotations(self) -> Vec<RawSymbolToken>;
}

impl IntoAnnotations for Vec<RawSymbolToken> {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self
    }
}

impl IntoAnnotations for &[RawSymbolToken] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self.iter().map(|token| token.clone()).collect()
    }
}

impl<const N: usize> IntoAnnotations for &[RawSymbolToken; N] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self.iter().map(|token| token.clone()).collect()
    }
}

impl IntoAnnotations for &[&str] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self.iter().map(|text| text_token(*text)).collect()
    }
}

impl<const N: usize> IntoAnnotations for &[&str; N] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self.iter().map(|text| text_token(*text)).collect()
    }
}

impl IntoAnnotations for &[SymbolId] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self.iter().map(|token| local_sid_token(*token)).collect()
    }
}

impl<const N: usize> IntoAnnotations for &[SymbolId; N] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        self.iter().map(|token| local_sid_token(*token)).collect()
    }
}

impl IntoAnnotations for &str {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        vec![text_token(self)]
    }
}

impl IntoAnnotations for SymbolId {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        vec![local_sid_token(self)]
    }
}

impl IntoAnnotations for RawSymbolToken {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        vec![self]
    }
}
