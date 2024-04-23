use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::Encoding;
use crate::lazy::never::Never;
use crate::{IonResult, WriteConfig};
use std::io::Write;

// TODO: this is a placeholder impl
pub struct LazyRawTextWriter_1_1<W> {
    output: W,
}

impl<W: Write> SequenceWriter for LazyRawTextWriter_1_1<W> {
    type Resources = W;

    fn close(self) -> IonResult<Self::Resources> {
        todo!()
    }
}

impl<W: Write> MakeValueWriter for LazyRawTextWriter_1_1<W> {
    type ValueWriter<'a> = Never
    where
        Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        todo!()
    }
}

impl<W: Write> LazyRawWriter<W> for LazyRawTextWriter_1_1<W> {
    fn new(_output: W) -> IonResult<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn build<E: Encoding>(_config: WriteConfig<E>, _output: W) -> IonResult<Self>
    where
        Self: Sized,
    {
        todo!()
    }

    fn flush(&mut self) -> IonResult<()> {
        todo!()
    }

    fn output(&self) -> &W {
        todo!()
    }

    fn output_mut(&mut self) -> &mut W {
        todo!()
    }
}
