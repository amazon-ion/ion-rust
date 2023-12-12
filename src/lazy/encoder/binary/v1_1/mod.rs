use crate::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
use crate::lazy::encoder::LazyEncoder;
use crate::lazy::encoding::BinaryEncoding_1_1;
use std::io::Write;

pub mod container_writers;
pub mod value_writer;
pub mod writer;

impl LazyEncoder for BinaryEncoding_1_1 {
    // TODO: Create 1.1 writer
    type Writer<W: Write> = LazyRawBinaryWriter_1_0<W>;
}
