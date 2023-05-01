use crate::ion_data::{IonEq, IonOrd};
use std::cmp::Ordering;

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
/// ```rust
/// use ion_rs::element::Bytes;
/// let bytes: Bytes = b"world".into();
/// assert_eq!(&bytes, b"world".as_slice());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Bytes {
    data: Vec<u8>,
}

impl IonEq for Bytes {
    fn ion_eq(&self, other: &Self) -> bool {
        self == other
    }
}

impl IonOrd for Bytes {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
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

impl<const N: usize> From<&[u8; N]> for Bytes {
    fn from(data: &[u8; N]) -> Self {
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
