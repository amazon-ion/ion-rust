use std::io;
use thiserror::Error;

#[derive(Debug, Error)]
#[error("{source:?}")]
pub struct IoError {
    #[from]
    source: io::Error,
}

impl IoError {
    pub fn source(&self) -> &io::Error {
        &self.source
    }
}
