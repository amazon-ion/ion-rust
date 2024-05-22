use crate::lazy::encoding::Encoding;
use crate::Catalog;
use std::marker::PhantomData;

/// Provides configuration details for reader construction.
pub struct ReadConfig<E: Encoding> {
    pub(crate) catalog: Box<dyn Catalog>,
    phantom_data: PhantomData<E>,
}
