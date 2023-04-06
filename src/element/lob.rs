use crate::element::Bytes;

/// An in-memory representation of an Ion blob.
///
/// ```rust
/// use ion_rs::element::Blob;
/// let ivm: &[u8] = &[0xEA_u8, 0x01, 0x00, 0xE0]; // Ion 1.0 version marker
/// let blob: Blob = ivm.into();
/// assert_eq!(&blob, ivm);
/// assert_eq!(blob.as_slice().len(), 4);
/// ```
/// ```rust
/// use ion_rs::element::Blob;
/// let blob: Blob = "hello".into();
/// assert_eq!(&blob, "hello".as_bytes());
/// assert_eq!(blob.as_slice().len(), 5);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Blob(pub Bytes);

impl Blob {
    pub fn as_slice(&self) -> &[u8] {
        self.as_ref()
    }
}

/// An in-memory representation of an Ion clob.
///
/// ```rust
/// use ion_rs::element::Clob;
/// let clob: Clob = "hello".into();
/// assert_eq!(&clob, "hello".as_bytes());
/// assert_eq!(clob.as_slice().len(), 5);
/// ```
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

impl PartialEq<[u8]> for Blob {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_ref().eq(other)
    }
}

impl PartialEq<[u8]> for Clob {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_ref().eq(other)
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
