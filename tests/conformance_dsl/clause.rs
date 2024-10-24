//! A Clause represents the DSL's S-Expression operations for defining tests. Each possible
//! expression should come from a Clause.
//!
//! The grammar defining each of the clauses can be found [here][Grammar].
//!
//! [Grammar]: https://github.com/amazon-ion/ion-tests/blob/master/conformance/README.md#grammar

use std::str::FromStr;

use ion_rs::{Element, Sequence};

use super::*;

/// Represents each type of S-Expression Clause that we can have in the DSL. This currently does
/// not capture the Data Model clauses used in Denotes fragments.
#[allow(non_camel_case_types)]
#[derive(Debug)]
pub(crate) enum ClauseType {
    /// Start an ion 1.0 test document.
    Ion1_0,
    /// Start an ion 1.1 test document.
    Ion1_1,
    /// Start a test document that validates both ion 1.1 and 1.0
    Ion1_X,
    /// Provide a string as text ion, that will be inserted into the test document.
    Text,
    /// Provide a sequence of bytes that is interpreted as binary ion, that will be inserted into
    /// the document.
    Bytes,
    /// Provide a major and minor version that will be emitted into the document as an IVM.
    Ivm,
    /// Specify a ion data to be inserted into the document, using inline ion syntax.
    TopLevel,
    /// Provide ion data defining the contents of an '$ion_encoding' directive.
    Encoding,
    /// Provide ion data defining the contents of a macro table wrapped by a module within an encoding directive.
    MacTab,
    /// Define data that is expected to be produced by the test's document, using inline ion
    /// syntax.
    Produces,
    /// Define data that is expected to be produced by the test's document, using a clause-based
    /// data model.
    Denotes,
    /// Specify that the test should signal (fail).
    Signals,
    /// Evaluate the logical conjunction of the clause's arguments.
    And,
    /// Negate the evaluation of the clause's argument.
    Not,
    /// A continuation that allows for the chaining of fragments and expectations.
    Then,
    /// Specify the start of a test.
    Document,
    /// Combine one or more continuations with a parent document separately.
    Each,
    /// Define a symbol using both text and symbol id for testing in a denotes clause.
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
            "bytes" => Ok(Bytes),
            "and" => Ok(And),
            "not" => Ok(Not),
            "then" => Ok(Then),
            "each" => Ok(Each),
            "absent" => Ok(Absent),
            "ivm" => Ok(Ivm),
            "signals" => Ok(Signals),
            "encoding" => Ok(Encoding),
            "mactab" => Ok(MacTab),
            _ => Err(ConformanceErrorKind::UnknownClause(s.to_owned())),
        }
    }
}

impl ClauseType {
    /// Utility function to test if the Clause is a fragment node.
    pub fn is_fragment(&self) -> bool {
        use ClauseType::*;
        matches!(self, Text | Bytes | Ivm | TopLevel | Encoding | MacTab)
    }

    /// Utility function to test if the Clause is an expectation node.
    pub fn is_expectation(&self) -> bool {
        use ClauseType::*;
        matches!(self, Produces | Denotes | Signals | And | Not)
    }
}

/// Represents a valid clause accepted by the conformance DSL for specifying a test.
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

        let tpe = ClauseType::from_str(
            clause_type
                .text()
                .ok_or(ConformanceErrorKind::ExpectedDocumentClause)?,
        )?;
        let body: Vec<Element> = other.iter().skip(1).cloned().collect();

        Ok(Clause { tpe, body })
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

        let tpe = ClauseType::from_str(
            clause_type
                .text()
                .ok_or(ConformanceErrorKind::ExpectedDocumentClause)?,
        )?;
        let body: Vec<Element> = other.iter().skip(1).cloned().collect();

        Ok(Clause { tpe, body })
    }
}
