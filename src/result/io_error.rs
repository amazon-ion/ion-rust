use std::io;
use std::io::Error;
use thiserror::Error;

/// Indicates that a read or write operation failed due to an I/O error.
#[derive(Debug, Error)]
#[error("{source:?}")]
pub struct IoError {
    source: io::Error,
}

impl From<io::Error> for IoError {
    #[cold]
    #[inline(never)]
    fn from(value: Error) -> Self {
        IoError { source: value }
    }
}

impl IoError {
    pub fn source(&self) -> &io::Error {
        &self.source
    }
}

impl Clone for IoError {
    fn clone(&self) -> Self {
        io::Error::from(self.source.kind()).into()
    }
}

impl PartialEq for IoError {
    fn eq(&self, other: &Self) -> bool {
        self.source().kind() == other.source().kind()
    }
}
