use ion_rs::{Decimal, Element, IonType, Sequence};
use super::{Clause, ClauseType, ConformanceErrorKind, InnerResult, parse_text_exp};

use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) enum SymTok {
    Text(String),
    Offset(i64),
    Absent(String, i64),
}

#[derive(Debug, Clone)]
pub(crate) enum ModelValue {
    Null(IonType),
    Bool(bool),
    Int(i64),
    Float(f64),
    Decimal(i64, i64),
    // TODO: Timestamp
    String(String),
    Symbol(SymTok),
    List(Vec<ModelValue>),
    Sexp(Vec<ModelValue>),
    Struct(HashMap<SymTok, ModelValue>),
    Blob(Vec<u8>),
    Clob(Vec<u8>),
}

impl TryFrom<&Sequence> for ModelValue {
    type Error = ConformanceErrorKind;

    fn try_from(other: &Sequence) -> InnerResult<Self> {
        let elems: Vec<Element> = other.iter().cloned().collect();
        let tpe_sym = elems.first().ok_or(ConformanceErrorKind::ExpectedModelValue)?.as_symbol().ok_or(ConformanceErrorKind::ExpectedModelValue)?;
        let tpe = tpe_sym.text().ok_or(ConformanceErrorKind::ExpectedModelValue)?;
        match tpe {
            "Null" => {
                let type_elem = elems.get(1).ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                let type_str = type_elem.as_symbol()
                    .and_then(|s| s.text())
                    .ok_or(ConformanceErrorKind::ExpectedModelValue)?;

                match ion_type_from_str(type_str) {
                    Some(tpe) => Ok(ModelValue::Null(tpe)),
                    None => Err(ConformanceErrorKind::ExpectedModelValue),
                }
            }
            "Bool" => {
                let value = elems.get(1)
                    .and_then(|e| e.as_bool())
                    .ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                Ok(ModelValue::Bool(value))
            }
            "Int" => {
                let value = elems.get(1)
                    .and_then(|e| e.as_i64())
                    .ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                Ok(ModelValue::Int(value))
            }
            "Float" => {
                let value_str = elems.get(1)
                    .and_then(|e| e.as_string())
                    .ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                match value_str.parse::<f64>() {
                    Ok(f) => Ok(ModelValue::Float(f)),
                    Err(_) => Err(ConformanceErrorKind::ExpectedFloatString),
                }
            }
            "Decimal" => todo!(),
            "String" => {
                let string = parse_text_exp(elems.iter().skip(1))?;
                Ok(ModelValue::String(string))
            }
            "Symbol" => {
                let value = elems.get(1).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                match value.ion_type() {
                    IonType::String => Ok(ModelValue::Symbol(SymTok::Text(value.as_string().unwrap().to_owned()))),
                    IonType::Int => Ok(ModelValue::Symbol(SymTok::Offset(value.as_i64().unwrap()))),
                    IonType::SExp => {
                        let clause: Clause = value.as_sequence().unwrap().try_into()?;

                        match clause.tpe {
                            ClauseType::Text => {
                                let text = parse_text_exp(clause.body.iter())?;
                                Ok(ModelValue::Symbol(SymTok::Text(text)))
                            },
                            ClauseType::Absent => {
                                let text = clause.body.get(1).and_then(|v| v.as_string()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                                let offset = clause.body.get(2).and_then(|v| v.as_i64()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                                Ok(ModelValue::Symbol(SymTok::Absent(text.to_string(), offset)))
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => Err(ConformanceErrorKind::ExpectedSymbolType),
                }
            }
            "List" => todo!(),
            "Sexp" => todo!(),
            "Struct" => todo!(),
            "Blob" => todo!(),
            "Clob" => todo!(),
            _ => unreachable!(),
        }
    }
}

impl PartialEq<Element> for ModelValue {
    fn eq(&self, other: &Element) -> bool {
        match self {
            ModelValue::Null(tpe) => other.ion_type() == *tpe && other.is_null(),
            ModelValue::Bool(val) => other.as_bool() == Some(*val),
            ModelValue::Int(val) => other.as_i64() == Some(*val),
            ModelValue::Float(val) => other.as_float() == Some(*val),
            ModelValue::Decimal(coef, exp) => other.as_decimal() == Some(Decimal::new(*coef, *exp)),
            // TODO: Timestamp
            ModelValue::String(val) => other.as_string() == Some(val),
            ModelValue::List(_vals) => todo!(),
            ModelValue::Sexp(_vals) => todo!(),
            ModelValue::Struct(_fields) => todo!(),
            ModelValue::Blob(data) => other.as_blob() == Some(data.as_slice()),
            ModelValue::Clob(data) => other.as_clob() == Some(data.as_slice()),
            ModelValue::Symbol(sym) => {
                if let Some(other_sym) = other.as_symbol() {
                    match sym {
                        SymTok::Text(text) => Some(text.as_ref()) == other_sym.text(),
                        SymTok::Offset(_offset) => todo!(),
                        SymTok::Absent(_text, _offset) => todo!(),
                    }
                } else {
                    false
                }
            }
            _ => todo!(),
        }
    }
}

fn ion_type_from_str(name: &str) -> Option<IonType> {
    match name {
        "null" => Some(IonType::Null),
        "bool" => Some(IonType::Bool),
        "int" => Some(IonType::Int),
        "float" => Some(IonType::Float),
        "decimal" => Some(IonType::Decimal),
        "timestamp" => Some(IonType::Timestamp),
        "string" => Some(IonType::String),
        "symbol" => Some(IonType::Symbol),
        "list" => Some(IonType::List),
        "sexp" => Some(IonType::SExp),
        "struct" => Some(IonType::Struct),
        "blob" => Some(IonType::Blob),
        "clob" => Some(IonType::Clob),
        _ => None,
    }
}
