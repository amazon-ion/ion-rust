pub(crate) mod value_writer;
pub(crate) mod writer;

use crate::lazy::encoder::text::v1_1::writer::LazyRawTextWriter_1_1;
use crate::lazy::encoder::{Encoder, SymbolCreationPolicy};
use crate::lazy::encoding::TextEncoding_1_1;
use std::io::Write;

impl Encoder for TextEncoding_1_1 {
    const SUPPORTS_TEXT_TOKENS: bool = true;
    const DEFAULT_SYMBOL_CREATION_POLICY: SymbolCreationPolicy =
        SymbolCreationPolicy::WriteProvidedToken;
    type Writer<W: Write> = LazyRawTextWriter_1_1<W>;
}
