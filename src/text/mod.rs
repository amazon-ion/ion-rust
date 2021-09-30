pub(in crate::text) mod parsers;
pub mod reader;
mod text_buffer;
mod text_data_source;
pub mod writer;

use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::value::owned::OwnedSymbolToken;
use crate::IonType;

/// Represents a single item encountered in a text Ion stream. The enum includes variants for each
/// scalar type as well as variants for the beginning and end of each container type.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TextStreamItem {
    Null(IonType),
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    // TODO: String(&str) will be possible if/when we add reusable buffers to the TextReader.
    String(String),
    Symbol(OwnedSymbolToken),
    // TODO: [BC]lob(&[u8]) will be possible if/when we add reusable buffers to the TextReader.
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    ListStart,
    ListEnd,
    SExpressionStart,
    SExpressionEnd,
    StructStart,
    StructEnd,
    EndOfStream
}

impl TextStreamItem {
    /// Returns the IonType associated with the TextStreamItem in question. If the TextStreamItem
    /// does not represent a scalar value or the beginning of a container, [ion_type] will return
    /// [None].
    pub fn ion_type(&self) -> Option<IonType> {
        let ion_type = match self {
            TextStreamItem::Null(ion_type) => *ion_type,
            TextStreamItem::Boolean(_) => IonType::Boolean,
            TextStreamItem::Integer(_) => IonType::Integer,
            TextStreamItem::Float(_) => IonType::Float,
            TextStreamItem::Decimal(_) => IonType::Decimal,
            TextStreamItem::Timestamp(_) => IonType::Timestamp,
            TextStreamItem::String(_) => IonType::String,
            TextStreamItem::Symbol(_) => IonType::Symbol,
            TextStreamItem::Blob(_) => IonType::Blob,
            TextStreamItem::Clob(_) => IonType::Clob,
            TextStreamItem::ListStart => IonType::List,
            TextStreamItem::SExpressionStart => IonType::SExpression,
            TextStreamItem::StructStart => IonType::Struct,
            _ => return None, // The remaining items are container ends, EndOfStream, etc.
        };
        Some(ion_type)
    }
}
