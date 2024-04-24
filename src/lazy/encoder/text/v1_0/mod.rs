use std::io::Write;

use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::{LazyEncoder, SymbolCreationPolicy};
use crate::lazy::encoding::TextEncoding_1_0;

pub mod value_writer;
pub mod writer;

impl LazyEncoder for TextEncoding_1_0 {
    const SUPPORTS_TEXT_TOKENS: bool = true;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy =
        SymbolCreationPolicy::WriteProvidedToken;

    type Writer<W: Write> = LazyRawTextWriter_1_0<W>;
}
