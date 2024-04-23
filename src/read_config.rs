use crate::lazy::encoding::Encoding;
use crate::write_config::WriteConfigKind;
use std::marker::PhantomData;

/// Writer configuration to provide format and Ion version details to writer through encoding
/// This will be used to create a writer without specifying which writer methods to use
#[cfg(feature = "experimental-lazy-reader")]
#[derive(Clone, Debug)]
pub struct ReadConfig<E: Encoding> {
    pub(crate) kind: WriteConfigKind,
    phantom_data: PhantomData<E>,
}
