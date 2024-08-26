use std::str::FromStr;

use super::*;
use super::context::Context;
use super::continuation::*;

use ion_rs::{Element, Sequence};

pub(crate) fn to_binary<'a, T: IntoIterator<Item=&'a Fragment>>(ctx: &'a Context, fragments: T) -> InnerResult<Vec<u8>> {
    let mut bin_encoded = vec!();
    for frag in fragments {
        let bin = frag.to_binary(ctx)?;
        bin_encoded.extend(bin);
    }
    Ok(bin_encoded)
}

pub(crate) fn to_text<'a, T: IntoIterator<Item=&'a Fragment>>(ctx: &'a Context, fragments: T) -> InnerResult<Vec<u8>> {
    let mut txt_encoded = vec!();
    for frag in fragments {
        let txt = frag.to_text(ctx)?;
        txt_encoded.extend(txt);
        txt_encoded.push(0x20); // Text fragments need to be separated by whitespace.
    }
    Ok(txt_encoded)
}

#[derive(Debug, Default)]
pub(crate) struct Document {
    pub name: Option<String>,
    pub fragments: Vec<Fragment>,
    pub continuation: Continuation,
}

impl Document {
    pub fn run(&self) -> Result<()> {
        let ctx = Context::new(IonVersion::Unspecified, self.encoding(), &self.fragments);
        self.continuation.evaluate(&ctx)?;
        Ok(())
    }

    fn encoding(&self) -> IonEncoding {
        match self.fragments.iter().fold((false,false), |acc, f| {
            (acc.0 || matches!(f, Fragment::Text(_)), acc.1 || matches!(f, Fragment::Binary(_)))
        }) {
            (true, false) => IonEncoding::Text,
            (false, true) => IonEncoding::Binary,
            (false, false) => IonEncoding::Unspecified,
            (true, true) => panic!("Both binary and text fragments specified"), // TODO: Make
                                                                                // error.
        }
    }
}

impl DocumentLike for Document {
    fn set_name(&mut self, name: &str) {
        self.name = Some(name.to_owned());
    }

    fn add_fragment(&mut self, frag: Fragment) {
        self.fragments.push(frag);
    }

    fn set_continuation(&mut self, continuation: Continuation) {
        self.continuation = continuation;
    }
}

impl FromStr for Document {
    type Err = ConformanceError;

    fn from_str(other: &str) -> std::result::Result<Self, Self::Err> {
        let element = Element::read_first(other)?
            .ok_or(ConformanceErrorKind::ExpectedDocumentClause)?;
        let Some(seq) = element.as_sequence() else {
            return Err(ConformanceErrorKind::ExpectedDocumentClause.into());
        };
        Document::try_from(seq.clone()).map_err(|x| x.into())
    }
}

impl TryFrom<Sequence> for Document {
    type Error = ConformanceErrorKind;

    fn try_from(other: Sequence) -> InnerResult<Self> {
        let clause: Clause = Clause::try_from(other)?;

        let mut doc: Document = parse_document_like(&clause)?;
        let continuation = match clause.tpe {
            ClauseType::Ion1_X => {
                Continuation::Extensions(vec!(
                    Continuation::Then(Box::new(Then {
                        test_name: None,
                        fragments: [vec!(Fragment::Ivm(1, 0)), doc.fragments.clone()].concat(),
                        continuation: doc.continuation.clone(),
                    })),
                    Continuation::Then(Box::new(Then {
                        test_name: None,
                        fragments: [vec!(Fragment::Ivm(1, 1)), doc.fragments].concat(),
                        continuation: doc.continuation.clone(),
                    })),
                ))
            }
            ClauseType::Ion1_0 => Continuation::Then(Box::new(Then {
                test_name: None,
                fragments: [vec!(Fragment::Ivm(1, 0)), doc.fragments].concat(),
                continuation: doc.continuation.clone(),
            })),
            ClauseType::Ion1_1 =>  Continuation::Then(Box::new(Then {
                test_name: None,
                fragments: [vec!(Fragment::Ivm(1, 1)), doc.fragments].concat(),
                continuation: doc.continuation.clone(),
            })),
            ClauseType::Document => return Ok(doc),
            _ => return Err(ConformanceErrorKind::ExpectedDocumentClause),
        };
        doc.continuation = continuation;
        doc.fragments = vec!();
        Ok(doc)
    }
}
