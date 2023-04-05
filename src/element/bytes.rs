/// An owned, immutable byte array.
/// ```rust
/// use ion_rs::element::Bytes;
/// let ivm: &[u8] = &[0xEA_u8, 0x01, 0x00, 0xE0]; // Ion 1.0 version marker
/// let bytes: Bytes = ivm.into();
/// assert_eq!(&bytes, ivm);
/// ```
/// ```rust
/// use ion_rs::element::Bytes;
/// let bytes: Bytes = "hello".into();
/// assert_eq!(&bytes, "hello".as_bytes());
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytes {
    data: Vec<u8>,
}

impl PartialEq<[u8]> for Bytes {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_ref().eq(other)
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(data: Vec<u8>) -> Self {
        Bytes { data }
    }
}

impl From<&[u8]> for Bytes {
    fn from(data: &[u8]) -> Self {
        Bytes {
            data: data.to_vec(),
        }
    }
}

impl From<&str> for Bytes {
    fn from(text: &str) -> Self {
        Bytes {
            data: text.as_bytes().into(),
        }
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        &self.data
    }
}
