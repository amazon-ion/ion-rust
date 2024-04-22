use crate::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
use crate::lazy::encoder::{LazyEncoder, SymbolCreationPolicy};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::WriteConfig;
use std::io::Write;

mod container_writers;
pub mod value_writer;
pub mod writer;

impl LazyEncoder for BinaryEncoding_1_0 {
    const SUPPORTS_TEXT_TOKENS: bool = false;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy =
        SymbolCreationPolicy::RequireSymbolId;

    type Writer<W: Write> = LazyRawBinaryWriter_1_0<W>;

    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }
}
