use std::str::FromStr;

use ion_rs::{Element, Sequence};

use super::*;

#[allow(non_camel_case_types)]
#[derive(Debug)]
pub(crate) enum ClauseType {
    Ion1_0,
    Ion1_1,
    Ion1_X,
    Text,
    Binary,
    Ivm,
    TopLevel,
    Encoding,
    MacTab,
    Produces,
    Denotes,
    Signals,
    And,
    Not,
    Bytes,
    Then,
    Document,
    Each,
    Absent,
}

impl FromStr for ClauseType {
    type Err = ConformanceErrorKind;

    fn from_str(s: &str) -> InnerResult<Self> {
        use ClauseType::*;

        match s {
            "ion_1_0" => Ok(Ion1_0),
            "ion_1_1" => Ok(Ion1_1),
            "ion_1_x" => Ok(Ion1_X),
            "document" => Ok(Document),
            "toplevel" => Ok(TopLevel),
            "produces" => Ok(Produces),
            "denotes" => Ok(Denotes),
            "text" => Ok(Text),
            "binary" => Ok(Binary),
            "and" => Ok(And),
            "not" => Ok(Not),
            "then" => Ok(Then),
            "each" => Ok(Each),
            "absent" => Ok(Absent),
            "ivm" => Ok(Ivm),
            "signals" => Ok(Signals),
            _ => Err(ConformanceErrorKind::UnknownClause(s.to_owned())),
        }
    }
}

impl ClauseType {
    pub fn is_fragment(&self) -> bool {
        use ClauseType::*;
        matches!(self, Text | Binary | Ivm | TopLevel | Encoding | MacTab)
    }

    pub fn is_expectation(&self) -> bool {
        use ClauseType::*;
        matches!(self, Produces | Denotes | Signals | And | Not)
    }
}

#[derive(Debug)]
pub(crate) struct Clause {
    pub tpe: ClauseType,
    pub body: Vec<Element>,
}

impl TryFrom<&Sequence> for Clause {
    type Error = ConformanceErrorKind;

    fn try_from(other: &Sequence) -> InnerResult<Self> {
        let clause_type = other
            .iter()
            .next()
            .ok_or(ConformanceErrorKind::UnexpectedEndOfDocument)?
            .as_symbol()
            .ok_or(ConformanceErrorKind::ExpectedDocumentClause)?;

        let tpe = ClauseType::from_str(clause_type.text().ok_or(ConformanceErrorKind::ExpectedDocumentClause)?)?;
        let body: Vec<Element> = other.iter().skip(1).cloned().collect();

        Ok(Clause {
            tpe,
            body,
        })
    }
}

impl TryFrom<Sequence> for Clause {
    type Error = ConformanceErrorKind;

    fn try_from(other: Sequence) -> InnerResult<Self> {
        Self::try_from(&other)
    }
}

impl TryFrom<&[Element]> for Clause {
    type Error = ConformanceErrorKind;

    fn try_from(other: &[Element]) -> InnerResult<Self> {
        let clause_type = other
            .iter()
            .next()
            .ok_or(ConformanceErrorKind::UnexpectedEndOfDocument)?
            .as_symbol()
            .ok_or(ConformanceErrorKind::ExpectedDocumentClause)?;

        let tpe = ClauseType::from_str(clause_type.text().ok_or(ConformanceErrorKind::ExpectedDocumentClause)?)?;
        let body: Vec<Element> = other.iter().skip(1).cloned().collect();

        Ok(Clause {
            tpe,
            body,
        })
    }
}
