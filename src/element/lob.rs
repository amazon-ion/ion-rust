use crate::element::Bytes;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Blob(pub Bytes);

impl Blob {
    pub fn as_slice(&self) -> &[u8] {
        self.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clob(pub Bytes);

impl Clob {
    pub fn as_slice(&self) -> &[u8] {
        self.as_ref()
    }
}

impl AsRef<[u8]> for Blob {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl AsRef<[u8]> for Clob {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl From<Blob> for Bytes {
    fn from(blob: Blob) -> Self {
        blob.0
    }
}

impl From<Clob> for Bytes {
    fn from(clob: Clob) -> Self {
        clob.0
    }
}

impl From<Vec<u8>> for Blob {
    fn from(data: Vec<u8>) -> Self {
        let bytes: Bytes = data.into();
        Blob(bytes)
    }
}

impl From<Vec<u8>> for Clob {
    fn from(data: Vec<u8>) -> Self {
        let bytes: Bytes = data.into();
        Clob(bytes)
    }
}

impl From<&[u8]> for Blob {
    fn from(data: &[u8]) -> Self {
        Blob::from(data.to_vec())
    }
}

impl From<&[u8]> for Clob {
    fn from(data: &[u8]) -> Self {
        Clob::from(data.to_vec())
    }
}

impl From<&str> for Blob {
    fn from(text: &str) -> Self {
        text.as_bytes().into()
    }
}

impl From<&str> for Clob {
    fn from(text: &str) -> Self {
        text.as_bytes().into()
    }
}
