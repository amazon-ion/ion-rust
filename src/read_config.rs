use crate::catalog::EmptyCatalog;
use crate::lazy::any_encoding::AnyEncoding;
use crate::lazy::encoding::{
    BinaryEncoding_1_0, BinaryEncoding_1_1, TextEncoding_1_0, TextEncoding_1_1,
};
use crate::{Catalog, Decoder};

/// Provides configuration details for reader construction.
pub struct ReadConfig<D: Decoder> {
    pub(crate) catalog: Box<dyn Catalog>,
    encoding: D,
}

impl<D: Decoder> ReadConfig<D> {
    fn new(encoding: D) -> Self {
        ReadConfig::new_with_catalog(encoding, EmptyCatalog)
    }

    pub(crate) fn new_with_catalog(encoding: D, catalog: impl Catalog + 'static) -> Self {
        ReadConfig {
            catalog: Box::new(catalog),
            encoding,
        }
    }

    pub fn encoding(&self) -> D {
        self.encoding
    }
}

impl From<TextEncoding_1_0> for ReadConfig<TextEncoding_1_0> {
    fn from(encoding: TextEncoding_1_0) -> Self {
        ReadConfig::new(encoding)
    }
}

impl From<TextEncoding_1_1> for ReadConfig<TextEncoding_1_1> {
    fn from(encoding: TextEncoding_1_1) -> Self {
        ReadConfig::new(encoding)
    }
}

impl From<BinaryEncoding_1_0> for ReadConfig<BinaryEncoding_1_0> {
    fn from(encoding: BinaryEncoding_1_0) -> Self {
        ReadConfig::new(encoding)
    }
}

impl From<BinaryEncoding_1_1> for ReadConfig<BinaryEncoding_1_1> {
    fn from(encoding: BinaryEncoding_1_1) -> Self {
        ReadConfig::new(encoding)
    }
}

impl From<AnyEncoding> for ReadConfig<AnyEncoding> {
    fn from(encoding: AnyEncoding) -> Self {
        ReadConfig::new(encoding)
    }
}
