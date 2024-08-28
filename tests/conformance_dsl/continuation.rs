use super::*;
use super::context::Context;
use super::model::ModelValue;

use ion_rs::{Element, Sequence};

#[derive(Clone, Debug)]
pub(crate) enum Continuation {
    // expectations
    Produces(Vec<Element>),
    Denotes(Vec<ModelValue>),
    Signals(String),
    // extensions
    Extensions(Vec<Continuation>),
    Then(Box<Then>),
    Each(Vec<EachBranch>, Box<Continuation>),
    And(Vec<Continuation>),
    Not(Box<Continuation>),
}

impl Continuation {
    pub fn evaluate(&self, ctx: &Context) -> InnerResult<()> {
        match self {
            // Produces is terminal, so we can evaluate.
            Continuation::Produces(expected_elems) => {
                let elems = ctx.read_all(ctx.encoding())?;
                if expected_elems.len() != elems.len() {
                    Err(ConformanceErrorKind::MismatchedProduce)
                } else {
                    let zip = expected_elems.iter().zip(elems.iter());
                    match zip.fold(true, |acc, (x, y)| acc && (*x == *y)) {
                        true => Ok(()),
                        false => Err(ConformanceErrorKind::MismatchedProduce),
                    }
                }
            }
            Continuation::Not(inner) => match inner.evaluate(ctx) {
                Err(_) => Ok(()),
                Ok(_) => Err(ConformanceErrorKind::UnknownError),
            },
            Continuation::And(inners) => {
                for c in inners {
                    c.evaluate(ctx)?;
                }
                Ok(())
            }
            Continuation::Then(then) => then.evaluate(ctx),
            Continuation::Denotes(expected_vals) => {
                let elems = ctx.read_all(ctx.encoding())?;
                if expected_vals.len() != elems.len() {
                    Err(ConformanceErrorKind::MismatchedDenotes)
                } else {
                    let zip = expected_vals.iter().zip(elems.iter());
                    match zip.fold(true, |acc, (x, y)| acc && (*x == *y)) {
                        true => Ok(()),
                        false => Err(ConformanceErrorKind::MismatchedDenotes),
                    }
                }
            }
            Continuation::Extensions(exts) => {
                for ext in exts {
                    ext.evaluate(ctx)?;
                }
                Ok(())
            }
            Continuation::Each(branches, continuation) => {
                for branch in branches {
                    let frags = vec!(branch.fragment.clone());
                    let mut new_context = Context::extend(ctx, &frags);
                    new_context.set_encoding(branch.fragment.required_encoding());
                    continuation.evaluate(&new_context)?;
                }
                Ok(())
            }
            Continuation::Signals(msg) => {
                match ctx.read_all(ctx.encoding()) {
                    Err(_e) => Ok(()),
                    Ok(_) => Err(ConformanceErrorKind::ExpectedSignal(msg.to_owned()))?,
                }
            }
        }
    }
}

impl Default for Continuation {
    fn default() -> Self {
        Continuation::Produces(vec!())
    }
}

pub fn parse_continuation(clause: Clause) -> InnerResult<Continuation> {
    let continuation = match clause.tpe {
        ClauseType::Produces => {
            Continuation::Produces(clause.body.clone())
        }
        ClauseType::And => {
            if !clause.body.is_empty() {
                let mut args = vec!();
                for elem in clause.body {
                    if let Some(seq) = elem.as_sequence() {
                        let clause = Clause::try_from(seq)?;
                        if clause.tpe.is_expectation() {
                            let continuation = parse_continuation(clause)?;
                            args.push(continuation);
                        } else {
                            return Err(ConformanceErrorKind::ExpectedExpectation);
                        }
                    } else {
                        return Err(ConformanceErrorKind::ExpectedExpectation);
                    }
                }
                Continuation::And(args)
            } else {
                return Err(ConformanceErrorKind::ExpectedExpectation)
            }
        }
        ClauseType::Not => {
            if clause.body.len() == 1 {
                let inner_elem = clause.body.first().unwrap(); // SAFETY: Just tested len().
                if let Some(inner_seq) = inner_elem.as_sequence() {
                    let inner_clause = Clause::try_from(inner_seq)?;
                    if inner_clause.tpe.is_expectation() {
                        let continuation = parse_continuation(inner_clause)?;
                        return Ok(Continuation::Not(Box::new(continuation)));
                    }
                }
            }
            return Err(ConformanceErrorKind::ExpectedExpectation);
        }
        ClauseType::Then => {
            let then: Then = parse_document_like(&clause)?;
            Continuation::Then(Box::new(then))
        }
        ClauseType::Denotes => {
            let mut values: Vec<ModelValue> = vec!();
            for elem in clause.body {
                if let Some(seq) = elem.as_sequence() {
                    let model_value = ModelValue::try_from(seq)?;
                    values.push(model_value);
                } else {
                    return Err(ConformanceErrorKind::ExpectedModelValue);
                }
            }
            Continuation::Denotes(values)
        }
        ClauseType::Each => {
            let mut parsing_branches = true;
            let mut sequence_idx = 0;
            let mut branches: Vec<EachBranch> = vec!();
            loop {
                if sequence_idx >= clause.body.len() {
                    return Err(ConformanceErrorKind::ExpectedClause);
                }
                if parsing_branches {
                    let mut name: Option<String> = None;
                    // Branch: name-string? fragment
                    // Check for name-string..
                    if let Some(elem) = clause.body.get(sequence_idx).filter(|e| e.ion_type() == IonType::String) {
                        name = elem.as_string().map(|s| s.to_string());
                        sequence_idx += 1;
                    }

                    let seq = clause.body.get(sequence_idx)
                        .and_then(|e| e.as_sequence())
                        .ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                    let seq_iter = seq.iter().peekable();

                    let fragment = match Fragment::try_from(Sequence::new(seq_iter)) {
                        Ok(frag) => frag,
                        Err(ConformanceErrorKind::ExpectedFragment) => {
                            parsing_branches = false;
                            continue;
                        }
                        Err(x) => return Err(x),
                    };
                    branches.push(EachBranch {
                        name,
                        fragment,
                    });
                } else {
                    let seq = clause.body.get(sequence_idx)
                        .and_then(|e| e.as_sequence())
                        .ok_or(ConformanceErrorKind::ExpectedModelValue)?;
                    let clause = Clause::try_from(seq.clone())?;
                    match continuation::parse_continuation(clause) {
                        Ok(c) => return Ok(Continuation::Each(branches, Box::new(c))),
                        Err(e) => return Err(e),
                    }
                }
                sequence_idx += 1;
            }
        }
        ClauseType::Signals => {
            let msg = clause.body.first()
                .and_then(|e| e.as_string())
                .ok_or(ConformanceErrorKind::ExpectedString)?
                .to_string();
            Continuation::Signals(msg)
        }
        _ => unreachable!(),
    };


    Ok(continuation)
}

#[derive(Clone, Debug)]
pub(crate) struct EachBranch {
    name: Option<String>,
    fragment: Fragment,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Then {
    pub test_name: Option<String>,
    pub fragments: Vec<Fragment>,
    pub continuation: Continuation,
}

impl Then {
    pub fn evaluate(&self, ctx: &Context) -> InnerResult<()> {
        // We need to create a new context for the Then scope.
        let mut then_ctx = Context::extend(ctx, &self.fragments);
        then_ctx.set_encoding(self.fragment_encoding());
        then_ctx.set_version(self.fragment_version());

        self.continuation.evaluate(&then_ctx)
    }

    fn fragment_encoding(&self) -> IonEncoding {
        let enc = self.fragments.iter().find(|f| matches!(f, Fragment::Text(_) | Fragment::Binary(_)));
        match enc {
            Some(Fragment::Text(_)) => IonEncoding::Text,
            Some(Fragment::Binary(_)) => IonEncoding::Binary,
            _ => IonEncoding::Unspecified,
        }
    }

    fn fragment_version(&self) -> IonVersion {
        match self.fragments.first() {
            Some(Fragment::Ivm(1, 0)) => IonVersion::V1_0,
            Some(Fragment::Ivm(1, 1)) => IonVersion::V1_1,
            _ => IonVersion::Unspecified,
        }
    }
}

impl DocumentLike for Then {
    fn set_name(&mut self, name: &str) {
        self.test_name = Some(name.to_owned());
    }

    fn add_fragment(&mut self, frag: Fragment) {
        self.fragments.push(frag);
    }

    fn set_continuation(&mut self, continuation: Continuation) {
        self.continuation = continuation;
    }
}
