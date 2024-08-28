use ion_rs::{Decimal, Element, IonType, Sequence};
use ion_rs::decimal::coefficient::Coefficient;
use super::{Clause, ClauseType, ConformanceErrorKind, InnerResult, parse_text_exp, parse_bytes_exp};

use std::collections::HashMap;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub(crate) enum SymTok {
    Text(String),
    Offset(i64),
    Absent(String, i64),
}

impl TryFrom<&Element> for SymTok {
    type Error = ConformanceErrorKind;

    fn try_from(other: &Element) -> InnerResult<Self> {
        match other.ion_type() {
            IonType::String => Ok(SymTok::Text(other.as_string().unwrap().to_owned())),
            IonType::Int => Ok(SymTok::Offset(other.as_i64().unwrap())),
            IonType::SExp => {
                let clause: Clause = other.as_sequence().unwrap().try_into()?;

                match clause.tpe {
                    ClauseType::Text => {
                        let text = parse_text_exp(clause.body.iter())?;
                        Ok(SymTok::Text(text))
                    },
                    ClauseType::Absent => {
                        let text = clause.body.get(1).and_then(|v| v.as_string()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                        let offset = clause.body.get(2).and_then(|v| v.as_i64()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                        Ok(SymTok::Absent(text.to_string(), offset))
                    }
                    _ => unreachable!(),
                }
            }
            _ => Err(ConformanceErrorKind::ExpectedSymbolType),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum ModelValue {
    Null(IonType),
    Bool(bool),
    Int(i64),
    Float(f64),
    Decimal(Decimal),
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
            "Decimal" => {
                let (first, second) = (elems.get(1), elems.get(2));
                match (first.map(|e| e.ion_type()), second.map(|e| e.ion_type())) {
                    (Some(IonType::String), Some(IonType::Int)) => {
                        let (first, second) = (first.unwrap(), second.unwrap()); // SAFETY: We have non-None types.
                        if let Some("negative_0") = first.as_string() {
                            let exp = second.as_i64().ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                            Ok(ModelValue::Decimal(Decimal::new(Coefficient::NEGATIVE_ZERO, exp)))
                        } else {
                            Err(ConformanceErrorKind::ExpectedModelValue)
                        }
                    }
                    (Some(IonType::Int), Some(IonType::Int)) => {
                        let (first, second) = (first.unwrap(), second.unwrap()); // SAFETY: We have non-None types.
                        Ok(ModelValue::Decimal(Decimal::new(
                                first.as_i64().ok_or(ConformanceErrorKind::ExpectedModelValue)?,
                                second.as_i64().ok_or(ConformanceErrorKind::ExpectedModelValue)?,
                        )))
                    }
                    _ => Err(ConformanceErrorKind::ExpectedModelValue),
                }
            }
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
            "List" => {
                let mut list = vec!();
                for elem in elems.iter().skip(1) {
                    if let Some(seq) = elem.as_sequence() {
                        list.push(ModelValue::try_from(seq)?);
                    }
                }
                Ok(ModelValue::List(list))
            }
            "Sexp" => {
                let mut sexp = vec!();
                for elem in elems.iter().skip(1) {
                    if let Some(seq) = elem.as_sequence() {
                        sexp.push(ModelValue::try_from(seq)?);
                    }
                }
                Ok(ModelValue::Sexp(sexp))
            }
            "Struct" => {
                let mut fields = HashMap::new();
                for elem in elems.iter().skip(1) {
                    if let Some(seq) = elem.as_sequence() {
                        // Each elem should be a model symtok followed by a model value.
                        let (first, second) = (seq.get(0), seq.get(1));
                        let field_sym = first.map(SymTok::try_from).ok_or(ConformanceErrorKind::ExpectedSymbolType)?.unwrap();
                        let value = match second.map(|e| e.ion_type()) {
                            Some(IonType::String) => {
                                let string = second.unwrap().as_string().unwrap();
                                ModelValue::String(string.to_string())
                            }
                            Some(IonType::Int) => {
                                let int_val = second.unwrap().as_i64().unwrap();
                                ModelValue::Int(int_val)
                            }
                            Some(IonType::SExp) => {
                                let seq = second.unwrap().as_sequence().unwrap();
                                ModelValue::try_from(seq)?
                            }
                            _ => return Err(ConformanceErrorKind::ExpectedModelValue),
                        };
                        fields.insert(field_sym, value);
                    }
                }
                Ok(ModelValue::Struct(fields))
            }
            "Blob" => Ok(ModelValue::Blob(parse_bytes_exp(elems.iter().skip(1))?)),
            "Clob" => Ok(ModelValue::Clob(parse_bytes_exp(elems.iter().skip(1))?)),
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
            ModelValue::Decimal(dec) => other.as_decimal() == Some(*dec),
            // TODO: Timestamp
            ModelValue::String(val) => other.as_string() == Some(val),
            ModelValue::List(vals) => {
                if other.ion_type() != IonType::List {
                    return false;
                }
                let other_seq = other.as_sequence().unwrap(); // SAFETY: Confirmed it's a list.
                if other_seq.len() != vals.len() {
                    return false;
                }

                for (ours, others) in vals.iter().zip(other_seq) {
                    if ours != others {
                        return false;
                    }
                }
                true
            }
            ModelValue::Sexp(vals) => {
                if other.ion_type() != IonType::SExp {
                    return false;
                }
                let other_seq = other.as_sequence().unwrap(); // SAFETY: Confirmed it's a list.
                if other_seq.len() != vals.len() {
                    return false;
                }

                for (ours, others) in vals.iter().zip(other_seq) {
                    if ours != others {
                        return false;
                    }
                }
                true
            }
            ModelValue::Struct(fields) => {
                if other.ion_type() != IonType::Struct {
                    false
                } else {
                    let struct_val = other.as_struct().unwrap();
                    for (field, val) in struct_val.fields() {
                        let denoted_field = field.text().unwrap(); // TODO: Symbol IDs
                        let denoted_symtok = SymTok::Text(denoted_field.to_string());
                        if let Some(expected_val) = fields.get(&denoted_symtok) {
                            if expected_val != val {
                                return false;
                            }
                        }
                    }
                    true
                }
            }
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
