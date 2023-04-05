#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytes {
    data: Vec<u8>,
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
