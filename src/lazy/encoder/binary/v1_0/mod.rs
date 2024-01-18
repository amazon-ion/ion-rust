use crate::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
use crate::lazy::encoder::LazyEncoder;
use crate::lazy::encoding::BinaryEncoding_1_0;
use std::io::Write;

mod container_writers;
pub mod value_writer;
pub mod writer;

impl LazyEncoder for BinaryEncoding_1_0 {
    type Writer<W: Write> = LazyRawBinaryWriter_1_0<W>;
}
