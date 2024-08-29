#![allow(dead_code)]

mod context;
mod document;
mod continuation;
mod model;
mod fragment;
mod clause;

use std::io::Read;
use std::path::{Path, PathBuf};

use ion_rs::{Element, IonError, IonStream, IonType};

use clause::*;
use document::*;
use fragment::*;

#[allow(unused)]
pub(crate) mod prelude {
    pub(crate) use super::document::Document;
    pub(crate) use super::TestCollection;
    pub(crate) use super::IonVersion;
}

#[derive(Clone, Default, Debug)]
pub(crate) enum ConformanceErrorKind {
    #[default]
    UnknownError,
    IoError(std::io::ErrorKind),
    IonError(IonError),
    UnexpectedEndOfDocument,
    UnknownClause(String),
    ExpectedDocumentClause,
    ExpectedClause,
    ExpectedFragment,
    ExpectedExpectation,
    ExpectedModelValue,
    ExpectedFloatString,
    ExpectedAsciiCodepoint,
    ExpectedSymbolType,
    ExpectedInteger,
    ExpectedSignal(String),
    ExpectedString,
    ExpectedTimestampPrecision,
    ExpectedTimestampOffset,
    InvalidByte,
    InvalidHexString,
    MismatchedProduce,
    MismatchedDenotes,
    UnexpectedValue,
    UnknownVersion,
}

impl From<std::io::Error> for ConformanceErrorKind {
    fn from(other: std::io::Error) -> Self {
        ConformanceErrorKind::IoError(other.kind())
    }
}

impl From<IonError> for ConformanceErrorKind {
    fn from(other: IonError) -> Self {
        ConformanceErrorKind::IonError(other)
    }
}

#[derive(Clone, Default, Debug)]
struct ConformanceErrorImpl {
    file: PathBuf,
    test_name: String,
    kind: ConformanceErrorKind,
}

#[derive(Clone, Default, Debug)]
pub struct ConformanceError(Box<ConformanceErrorImpl>);

impl From<ConformanceErrorImpl> for ConformanceError {
    fn from(inner: ConformanceErrorImpl) -> Self {
        ConformanceError(Box::new(inner))
    }
}

impl From<std::io::Error> for ConformanceError {
    fn from(other: std::io::Error) -> Self {
        ConformanceErrorImpl {
            kind: ConformanceErrorKind::IoError(other.kind()),
            ..Default::default()
        }.into()
    }
}

impl From<IonError> for ConformanceError {
    fn from(other: IonError) -> Self {
        ConformanceErrorImpl {
            kind: ConformanceErrorKind::IonError(other),
            ..Default::default()
        }.into()
    }
}

impl From<ConformanceErrorKind> for ConformanceError {
    fn from(other: ConformanceErrorKind) -> Self {
        ConformanceErrorImpl {
            kind: other,
            ..Default::default()
        }.into()
    }
}

// Used for internal error handling.
type InnerResult<T> = std::result::Result<T, ConformanceErrorKind>;

// Used for public conformance API error handling.
pub(crate) type Result<T> = std::result::Result<T, ConformanceError>;

// Encoding captures whether an encoding is forced by including a text, or binary clause.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum IonEncoding {
    Text,        // Text clause used.
    Binary,      // Binary clause used.
    Unspecified, // No encoding specific clauses.
}


#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Default, Debug, PartialEq)]
pub(crate) enum IonVersion {
    #[default]
    Unspecified,
    V1_0,
    V1_1,
    V1_X,
}

/// A document-like is anything that matches the grammar of a document. Currently this includes
/// both Document, and Then clauses.
pub(crate) trait DocumentLike: Default {
    fn set_name(&mut self, name: &str);
    fn add_fragment(&mut self, frag: Fragment);
    fn set_continuation(&mut self, continuation: continuation::Continuation);
}

pub(crate) fn parse_document_like<T: DocumentLike>(clause: &Clause) -> InnerResult<T> {
    // let clause: Clause = Clause::try_from(seq)?;
    let mut doc_like = T::default();
    let mut sequence_idx = 0;

    // We have an optional name as the second argument..
    if let Some(elem) = clause.body.first().filter(|e| e.ion_type() == IonType::String) {
        if let Some(s) = elem.as_string() {
            doc_like.set_name(s);
        }
        sequence_idx += 1;
    }

    let mut handle_fragments = true;
    loop {
        if sequence_idx >= clause.body.len() {
            return Err(ConformanceErrorKind::ExpectedClause);
        }
        let element = clause.body.get(sequence_idx).expect("unwrapping element");
        if handle_fragments {
            let Some(seq) = element.as_sequence() else {
                return Err(ConformanceErrorKind::ExpectedClause)
            };
            let fragment = match Fragment::try_from(seq.clone()) {
                Ok(frag) => frag,
                Err(ConformanceErrorKind::ExpectedFragment) => {
                    handle_fragments = false;
                    continue;
                }
                Err(x) => return Err(x),
            };
            doc_like.add_fragment(fragment);
            sequence_idx += 1
        } else {
            let Some(seq) = element.as_sequence() else {
                return Err(ConformanceErrorKind::ExpectedClause)
            };
            let clause: Clause = seq.clone().try_into().expect("unable to convert to clause");
            match continuation::parse_continuation(clause) {
                Ok(c) => doc_like.set_continuation(c),
                Err(e) => return Err(e),
            }
            break;
        }
    }
    Ok(doc_like)
}



/// A collection of Tests, usually stored together in a file.
#[derive(Debug)]
pub(crate) struct TestCollection {
    documents: Vec<Document>,
}

impl TestCollection {
    /// Loads a TestCollection from a file at the provided path.
    pub fn load<P: AsRef<Path>>(path: P) -> Result<TestCollection> {
        let test_file = std::fs::File::open(&path)?;
        match Self::load_from(test_file) {
            Err(e) => Err(ConformanceErrorImpl {
               file: path.as_ref().to_owned(),
               ..*e.0
            }.into()),
            Ok(t) => Ok(t),
        }
    }

    pub fn load_from<R: Read>(reader: R) -> Result<TestCollection> {
        let iter = Element::iter(IonStream::new(reader))?;
        let mut docs: Vec<Document> = vec!();

        for element in iter {
            let element = element?;
            match element.ion_type() {
                IonType::SExp => {
                    let seq = element.as_sexp().unwrap();
                    let doc = match Document::try_from(seq.clone()) {
                        Err(kind) => return Err(ConformanceErrorImpl {
                            kind,
                            ..Default::default()
                        }.into()),
                        Ok(doc) => doc,
                    };
                    docs.push(doc);
                }
                _ => todo!(),
            }
        }

        let collection = TestCollection{
            documents: docs,
        };

        Ok(collection)
    }

    pub fn run(&self) -> Result<()> {
        for test in self.documents.iter() {
            test.run()?;
        }
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.documents.len()
    }

    pub fn iter(&self) -> impl Iterator<Item=&Document> {
        self.documents.iter()
    }

}

pub(crate) fn parse_bytes_exp<'a, I: IntoIterator<Item=&'a Element>>(elems: I) -> InnerResult<Vec<u8>> {
    // Bytes can be of the form int (0..255), and a string containing hexadecimal digits.
    use std::result::Result;
    let mut bytes: Vec<u8> = vec!();
    for elem in elems.into_iter() {
        match elem.ion_type() {
            IonType::Int => match elem.as_i64() {
                Some(i) if (0..=255).contains(&i) => bytes.push(i as u8),
                _ => return Err(ConformanceErrorKind::InvalidByte),
            }
            IonType::String => {
                let hex = elem.as_string().ok_or(ConformanceErrorKind::ExpectedString)?.replace(" ", "");
                let hex_bytes = (0..hex.len()).step_by(2).map(|i| u8::from_str_radix(&hex[i..i+2], 16)).collect::<Result<Vec<u8>, _>>();
                match hex_bytes {
                    Err(_) => return Err(ConformanceErrorKind::InvalidHexString),
                    Ok(v) => bytes.extend_from_slice(v.as_slice()),
                }
            }
            _ => return Err(ConformanceErrorKind::InvalidByte),
        }
    }
    Ok(bytes)
}

pub(crate) fn parse_text_exp<'a, I: IntoIterator<Item=&'a Element>>(elems: I) -> InnerResult<String> {
    let bytes: Vec<Vec<u8>> = elems.into_iter().map(|v| match v.ion_type() {
        IonType::String => v.as_string().map(|s| Ok(s.as_bytes().to_vec())).unwrap(),
        IonType::Int => {
            match v.as_i64() {
                Some(i) if i < 256 => Ok(vec!(i as u8)),
                _ => Err(ConformanceErrorKind::ExpectedAsciiCodepoint),
            }
        }
        _ => Err(ConformanceErrorKind::ExpectedModelValue),
    }).collect::<InnerResult<Vec<Vec<u8>>>>()?;

    let val_string = bytes.iter().map(|v| unsafe { String::from_utf8_unchecked(v.to_vec()) }).collect();
    Ok(val_string)

}
