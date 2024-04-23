use std::io::Write;

use crate::lazy::encoder::{LazyEncoder, SymbolCreationPolicy};
use crate::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
use crate::lazy::encoding::BinaryEncoding_1_1;

pub mod container_writers;
pub mod fixed_int;
pub mod fixed_uint;
pub mod flex_int;
pub mod flex_sym;
pub mod flex_uint;
pub mod value_writer;
pub mod writer;

impl LazyEncoder for BinaryEncoding_1_1 {
    const SUPPORTS_TEXT_TOKENS: bool = true;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy =
        SymbolCreationPolicy::RequireSymbolId;

    type Writer<W: Write> = LazyRawBinaryWriter_1_1<W>;
}
