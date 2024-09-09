use ion_rs::{Decimal, Element, IonType, Sequence, Timestamp, ValueRef};
use ion_rs::{LazyRawValue, LazyRawFieldName, v1_0::RawValueRef};
use ion_rs::decimal::coefficient::Coefficient;
use super::{Clause, ClauseType, ConformanceErrorKind, InnerResult, parse_text_exp, parse_bytes_exp};


/// Represents a symbol in the Data Model representation of ion data.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub(crate) enum SymbolToken {
    Text(String),
    Offset(i64),
    Absent(String, i64),
}

impl std::fmt::Display for SymbolToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SymbolToken::Text(txt) => write!(f, "{}", txt),
            SymbolToken::Offset(id) => write!(f, "#${}", id),
            SymbolToken::Absent(txt, id) => write!(f, "#${}#{}", txt, id),
        }
    }
}


impl TryFrom<&Element> for SymbolToken {
    type Error = ConformanceErrorKind;

    fn try_from(other: &Element) -> InnerResult<Self> {
        match other.ion_type() {
            IonType::String => Ok(SymbolToken::Text(other.as_string().unwrap().to_owned())),
            IonType::Int => Ok(SymbolToken::Offset(other.as_i64().unwrap())),
            IonType::SExp => {
                let clause: Clause = other.as_sequence().unwrap().try_into()?;

                match clause.tpe {
                    ClauseType::Text => {
                        let text = parse_text_exp(clause.body.iter())?;
                        Ok(SymbolToken::Text(text))
                    },
                    ClauseType::Absent => {
                        let symtab = clause.body.first().and_then(|v| v.as_string()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                        let offset = clause.body.get(1).and_then(|v| v.as_i64()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                        Ok(SymbolToken::Absent(symtab.to_string(), offset))
                    }
                    _ => unreachable!(),
                }
            }
            _ => Err(ConformanceErrorKind::ExpectedSymbolType),
        }
    }
}

/// Data Model value representation. Implementation provides parsing of data model clauses and
/// comparison functionality for test evaluation. Each variant represents a single data model value
/// clause.
///
/// [Grammar]: https://github.com/amazon-ion/ion-tests/tree/master/conformance#grammar
#[derive(Debug, Clone)]
pub(crate) enum ModelValue {
    Null(IonType),
    Bool(bool),
    Int(i64),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(String),
    Symbol(SymbolToken),
    List(Vec<ModelValue>),
    Sexp(Vec<ModelValue>),
    Struct(Vec<(SymbolToken, ModelValue)>),
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
            "Decimal" => Ok(ModelValue::Decimal(parse_model_decimal(elems.iter().skip(1))?)),
            "String" => {
                let string = parse_text_exp(elems.iter().skip(1))?;
                Ok(ModelValue::String(string))
            }
            "Symbol" => {
                let value = elems.get(1).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                match value.ion_type() {
                    IonType::String => Ok(ModelValue::Symbol(SymbolToken::Text(value.as_string().unwrap().to_owned()))),
                    IonType::Int => Ok(ModelValue::Symbol(SymbolToken::Offset(value.as_i64().unwrap()))),
                    IonType::SExp => {
                        let clause: Clause = value.as_sequence().unwrap().try_into()?;

                        match clause.tpe {
                            ClauseType::Text => {
                                let text = parse_text_exp(clause.body.iter())?;
                                Ok(ModelValue::Symbol(SymbolToken::Text(text)))
                            },
                            ClauseType::Absent => {
                                let symtab= clause.body.get(1).and_then(|v| v.as_string()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                                let offset = clause.body.get(2).and_then(|v| v.as_i64()).ok_or(ConformanceErrorKind::ExpectedSymbolType)?;
                                Ok(ModelValue::Symbol(SymbolToken::Absent(symtab.to_string(), offset)))
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => Err(ConformanceErrorKind::ExpectedSymbolType),
                }
            }
            "Timestamp" => Ok(ModelValue::Timestamp(parse_timestamp(elems.iter().skip(1))?)),
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
                let mut fields = vec!();
                for elem in elems.iter().skip(1) {
                    if let Some(seq) = elem.as_sequence() {
                        // Each elem should be a model symtok followed by a model value.
                        let (first, second) = (seq.get(0), seq.get(1));
                        let field_sym = first.map(SymbolToken::try_from).ok_or(ConformanceErrorKind::ExpectedSymbolType)?.unwrap();
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

                        fields.push((field_sym, value));
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
            ModelValue::Struct(_) => panic!("should not be using element eq for struct"),
            ModelValue::Blob(data) => other.as_blob() == Some(data.as_slice()),
            ModelValue::Clob(data) => other.as_clob() == Some(data.as_slice()),
            ModelValue::Symbol(sym) => {
                if let Some(other_sym) = other.as_symbol() {
                    match sym {
                        SymbolToken::Text(text) => Some(text.as_ref()) == other_sym.text(),
                        _ => unreachable!(),
                    }
                } else {
                    false
                }
            }
            ModelValue::Timestamp(ts) => other.as_timestamp() == Some(*ts),
        }
    }
}

impl PartialEq<Element> for &ModelValue {
    fn eq(&self, other: &Element) -> bool {
        *self == other
    }
}

impl<T: ion_rs::Decoder> PartialEq<ion_rs::LazyValue<'_, T>> for &ModelValue {
    fn eq(&self, other: &ion_rs::LazyValue<'_, T>) -> bool {
        match self {
            ModelValue::Symbol(symbol_token) if other.ion_type() == IonType::Symbol => {
                let Some(raw_symbol) = other.raw().map(|r| r.read()) else {
                    unreachable!()
                };
                let raw_symbol = raw_symbol.expect("error reading symbol");

                let RawValueRef::Symbol(raw_symbol) = raw_symbol else {
                    return false
                };

                let ValueRef::Symbol(symbol_text) = other.read().expect("error resolving symbol") else {
                    return false;
                };

                let (expected_txt, expected_id) = match symbol_token {
                    SymbolToken::Text(txt) => return symbol_text == txt,
                    SymbolToken::Offset(id) => (&String::from(""), *id as usize),
                    SymbolToken::Absent(txt, id) => (txt, *id as usize),
                };

                raw_symbol.matches_sid_or_text(expected_id, expected_txt)
            }
            ModelValue::Struct(expected_fields) if other.ion_type() == IonType::Struct => {
                let ValueRef::Struct(strukt) = other.read().expect("error reading struct") else {
                    return false;
                };

                let mut is_equal = true;
                let mut strukt_iter = strukt.iter();
                let mut expected_iter = expected_fields.iter();

                while is_equal {
                    let actual = strukt_iter.next();
                    let expected = expected_iter.next();

                    match (actual, expected) {
                        (Some(actual), Some((expected_field, expected_val))) => {
                            let actual = actual.expect("unable to read struct field");
                            let actual_field = actual.raw_name().map(|n| n.read()).expect("unable to get symbolref for field name");
                            let actual_field = actual_field.expect("unable to read symbolref for field name");

                            let (expected_txt, expected_id) = match expected_field {
                                SymbolToken::Text(txt) => (txt, usize::MAX),
                                SymbolToken::Offset(id) => (&String::from(""), *id as usize),
                                SymbolToken::Absent(txt, id) => (txt, *id as usize),
                            };
                            is_equal = is_equal && actual_field.matches_sid_or_text(expected_id, expected_txt);

                            let actual_value = actual.value();

                            is_equal = is_equal && (expected_val == actual_value);
                        }
                        (None, None) => break,
                        _ => is_equal = false,
                    }
                }
                is_equal
            }
            ModelValue::List(expected) if other.ion_type() == IonType::List => {
                let ValueRef::List(list) = other.read().expect("error reading list") else {
                    unreachable!();
                };

                let actual: ion_rs::IonResult<Vec<ion_rs::LazyValue<_>>> = list.iter().collect();
                let actual = actual.expect("Error parsing list");

                actual.iter().zip(expected.iter())
                    .fold(true, |acc, (actual_val, expected_val)| acc && (&expected_val == actual_val))
            }
            ModelValue::Sexp(expected) if other.ion_type() == IonType::SExp => {
                let ValueRef::SExp(sexp) = other.read().expect("error reading sexp") else {
                    unreachable!();
                };

                let actual: ion_rs::IonResult<Vec<ion_rs::LazyValue<_>>> = sexp.iter().collect();
                let actual = actual.expect("Error parsing sexp");
                actual.iter().zip(expected.iter())
                    .fold(true, |acc, (actual_val, expected_val)| acc && (&expected_val == actual_val))
            }
            _ => {
                // Anything that reaches down here isn't a symbol, or can't contain a symbol. So
                // we just have to worry about equality.
                let other_elem: Element = Element::try_from(*other).expect("Unable to convert value into element");
                *self == other_elem
            }
        }
    }
}

/// Parses a Timestamp clause into an ion-rs Timestamp.
fn parse_timestamp<'a, I: IntoIterator<Item=&'a Element>>(elems: I) -> InnerResult<Timestamp> {
    let mut iter = elems.into_iter();
    let first = iter.next().and_then(|e| e.as_symbol()).and_then(|s| s.text());
    match first {
        Some("year") => {
            let year = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            Ok(Timestamp::with_year(year as u32).build()?)
        }
        Some("month") => {
            let year = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let month = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let ts = Timestamp::with_year(year as u32)
                .with_month(month as u32)
                .build()?;
            Ok(ts)
        }
        Some("day") => {
            let year = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let month = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let day = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let ts = Timestamp::with_year(year as u32)
                .with_month(month as u32)
                .with_day(day as u32)
                .build()?;
            Ok(ts)
        }
        Some("minute") => {
            let year = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let month = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let day = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;

            let offset = parse_ts_offset(iter.next().and_then(|e| e.as_sequence()).ok_or(ConformanceErrorKind::ExpectedInteger)?)?;

            let hour = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let minute = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let ts = Timestamp::with_year(year as u32)
                .with_month(month as u32)
                .with_day(day as u32)
                .with_hour_and_minute(hour as u32, minute as u32);
            if let Some(offset) = offset {
                let ts = ts.with_offset(offset as i32);
                Ok(ts.build()?)
            } else {
                Ok(ts.build()?)
            }
        }
        Some("second") => {
            let year = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let month = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let day = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;

            let offset = parse_ts_offset(iter.next().and_then(|e| e.as_sequence()).ok_or(ConformanceErrorKind::ExpectedInteger)?)?;

            let hour = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let minute = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let second = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let ts = Timestamp::with_year(year as u32)
                .with_month(month as u32)
                .with_day(day as u32)
                .with_hour_and_minute(hour as u32, minute as u32)
                .with_second(second as u32);
            if let Some(offset) = offset {
                let ts = ts.with_offset(offset as i32);
                Ok(ts.build()?)
            } else {
                Ok(ts.build()?)
            }
        }
        Some("fraction") => {
            let year = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let month = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let day = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;

            let offset = parse_ts_offset(iter.next().and_then(|e| e.as_sequence()).ok_or(ConformanceErrorKind::ExpectedInteger)?)?;

            let hour = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let minute = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let second = iter.next().and_then(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?;
            let fraction = parse_model_decimal(iter)?;
            let ts = Timestamp::with_year(year as u32)
                .with_month(month as u32)
                .with_day(day as u32)
                .with_hour_and_minute(hour as u32, minute as u32)
                .with_second(second as u32)
                .with_fractional_seconds(fraction);
            if let Some(offset) = offset {
                let ts = ts.with_offset(offset as i32);
                Ok(ts.build()?)
            } else {
                Ok(ts.build()?)
            }
        }
        _ => Err(ConformanceErrorKind::ExpectedTimestampPrecision),
    }
}

/// Parses a data-model value timestamp's 'offset' clause into an i64.
fn parse_ts_offset<'a, I: IntoIterator<Item=&'a Element>>(elems: I) -> InnerResult<Option<i64>> {
    let mut iter = elems.into_iter();
    match iter.next().and_then(|e| e.as_symbol()).and_then(|s| s.text()) {
        Some("offset") => {
            // Either an int or null..
            let offset = iter.next().ok_or(ConformanceErrorKind::ExpectedTimestampOffset)?;
            if offset.is_null() {
                Ok(None)
            } else {
                let offset = offset.as_i64().ok_or(ConformanceErrorKind::ExpectedInteger)?;
                Ok(Some(offset))
            }
        }
        _ => Err(ConformanceErrorKind::ExpectedTimestampOffset),
    }
}

/// Parses a data-model value's Decimal clause into an ion-rs Decimal.
fn parse_model_decimal<'a, I: IntoIterator<Item=&'a Element>>(elems: I) -> InnerResult<Decimal> {
    let mut iter = elems.into_iter();
    let (first, second) = (iter.next(), iter.next());
    match (first.map(|e| e.ion_type()), second.map(|e| e.ion_type())) {
        (Some(IonType::String), Some(IonType::Int)) => {
            let (first, second) = (first.unwrap(), second.unwrap()); // SAFETY: We have non-None types.
            if let Some("negative_0") = first.as_string() {
                let exp = second.as_i64().ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                Ok(Decimal::new(Coefficient::NEGATIVE_ZERO, exp))
            } else {
                Err(ConformanceErrorKind::ExpectedModelValue)
            }
        }
        (Some(IonType::Int), Some(IonType::Int)) => {
            let (first, second) = (first.unwrap(), second.unwrap()); // SAFETY: We have non-None types.
            Ok(Decimal::new(
                    first.as_i64().ok_or(ConformanceErrorKind::ExpectedModelValue)?,
                    second.as_i64().ok_or(ConformanceErrorKind::ExpectedModelValue)?,
            ))
        }
        _ => Err(ConformanceErrorKind::ExpectedModelValue),
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
