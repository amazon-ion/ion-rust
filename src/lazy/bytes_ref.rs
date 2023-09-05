use crate::text::text_formatter::IonValueFormatter;
use crate::Bytes;
use std::borrow::Cow;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;

pub struct BytesRef<'data> {
    data: Cow<'data, [u8]>,
}

impl<'data> Deref for BytesRef<'data> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.data.as_ref()
    }
}

impl<'data> BytesRef<'data> {
    pub fn to_owned(&self) -> Bytes {
        Bytes::from(self.as_ref())
    }

    pub fn into_owned(self) -> Bytes {
        Bytes::from(self)
    }

    pub fn data(&self) -> &[u8] {
        self.as_ref()
    }
}

impl<'data> From<BytesRef<'data>> for Bytes {
    fn from(value: BytesRef<'data>) -> Self {
        match value.data {
            Cow::Borrowed(bytes) => Bytes::from(bytes),
            Cow::Owned(bytes) => Bytes::from(bytes),
        }
    }
}

impl<'data, const N: usize> From<&'data [u8; N]> for BytesRef<'data> {
    fn from(bytes: &'data [u8; N]) -> Self {
        BytesRef {
            data: Cow::from(bytes.as_ref()),
        }
    }
}

impl<'data> From<&'data [u8]> for BytesRef<'data> {
    fn from(bytes: &'data [u8]) -> Self {
        BytesRef {
            data: Cow::from(bytes),
        }
    }
}

impl<'data> From<Vec<u8>> for BytesRef<'data> {
    fn from(bytes: Vec<u8>) -> Self {
        BytesRef {
            data: Cow::from(bytes),
        }
    }
}

impl<'data> From<&'data str> for BytesRef<'data> {
    fn from(text: &'data str) -> Self {
        BytesRef {
            data: Cow::from(text.as_bytes()),
        }
    }
}

impl<'data> PartialEq<[u8]> for BytesRef<'data> {
    fn eq(&self, other: &[u8]) -> bool {
        self.data() == other
    }
}

impl<'data> PartialEq<&[u8]> for BytesRef<'data> {
    fn eq(&self, other: &&[u8]) -> bool {
        self.data() == *other
    }
}

impl<'data> PartialEq<BytesRef<'data>> for [u8] {
    fn eq(&self, other: &BytesRef<'data>) -> bool {
        self == other.data()
    }
}

impl<'a, 'b> PartialEq<BytesRef<'a>> for BytesRef<'b> {
    fn eq(&self, other: &BytesRef<'a>) -> bool {
        self == other.data()
    }
}

impl<'data> Display for BytesRef<'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut formatter = IonValueFormatter { output: f };
        formatter
            .format_blob(self.data())
            .map_err(|_| std::fmt::Error)
    }
}

impl<'data> Debug for BytesRef<'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        const NUM_BYTES_TO_SHOW: usize = 32;
        let data = self.data.as_ref();
        // Shows up to the first 32 bytes in hex
        write!(f, "BytesRef: [")?;
        for byte in data.iter().copied().take(NUM_BYTES_TO_SHOW) {
            write!(f, "{:x} ", byte)?;
        }
        if data.len() > NUM_BYTES_TO_SHOW {
            write!(f, "...{} more", (data.len() - NUM_BYTES_TO_SHOW))?;
        }
        write!(f, "]")?;

        Ok(())
    }
}
