pub mod reader;
pub mod writer;
pub(crate) mod parsers;

use crate::IonType;
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TextStreamItem {
    Null(IonType),
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(String),
    Symbol(String), // TODO: SymbolToken API
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    ListStart,
    SExpressionStart,
    StructStart,
}

impl TextStreamItem {
    pub fn ion_type(&self) -> IonType {
        match self {
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
        }
    }
}
