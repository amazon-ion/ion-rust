use crate::raw_symbol_token::RawSymbolToken;
use crate::types::decimal::Decimal;
use crate::types::integer::Integer;
use crate::types::timestamp::Timestamp;
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

    pub(crate) fn is_null(&self) -> bool {
        matches!(self.value(), TextValue::Null(_))
    }

    pub(crate) fn annotations(&self) -> &[RawSymbolToken] {
        &self.annotations
    }
}

impl PartialEq<TextValue> for AnnotatedTextValue {
    fn eq(&self, other: &TextValue) -> bool {
        if !self.annotations.is_empty() {
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
    Integer(Integer),
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

/// Converts a given type into a `Vec<RawSymbolToken>`.
pub trait IntoAnnotations {
    fn into_annotations(self) -> Vec<RawSymbolToken>;
}

impl<T> IntoAnnotations for T
where
    T: Into<RawSymbolToken>,
{
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        vec![self.into()]
    }
}

fn annotations_from_iter<T, I>(collection: I) -> Vec<RawSymbolToken>
where
    T: Into<RawSymbolToken>,
    I: IntoIterator<Item = T>,
{
    collection.into_iter().map(|item| item.into()).collect()
}

impl<T: Into<RawSymbolToken>> IntoAnnotations for Vec<T> {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        annotations_from_iter(self)
    }
}

impl<T: Into<RawSymbolToken>, const N: usize> IntoAnnotations for [T; N] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        annotations_from_iter(self)
    }
}

impl<T: Into<RawSymbolToken> + Clone> IntoAnnotations for &[T] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        annotations_from_iter(self)
    }
}

impl<T: Into<RawSymbolToken> + Clone, const N: usize> IntoAnnotations for &[T; N] {
    fn into_annotations(self) -> Vec<RawSymbolToken> {
        annotations_from_iter(self)
    }
}
