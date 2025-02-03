use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::{
    Decoder, EncodingContext, ExpandedValueSource, HasSpan, LazyExpandedValue, LazyRawValue,
    LazyValue, Span,
};
use std::marker::PhantomData;

pub(crate) enum LazyElementSource<Encoding: Decoder> {
    ValueLiteral(IoBuffer, Encoding::Value<'static>),
}

pub struct LazyElement<Encoding: Decoder> {
    context: EncodingContext,
    source: LazyElementSource<Encoding>,
    spooky: PhantomData<Encoding>,
}

unsafe fn erase_lifetime<Encoding: Decoder>(
    raw_value: Encoding::Value<'_>,
) -> Encoding::Value<'static> {
    unsafe { std::mem::transmute(raw_value) }
}

unsafe fn set_lifetime<'x, Encoding: Decoder>(
    raw_value: Encoding::Value<'static>,
) -> Encoding::Value<'x> {
    unsafe { std::mem::transmute(raw_value) }
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    pub(crate) fn from_literal(
        context: EncodingContext,
        io_buffer: IoBuffer,
        value: Encoding::Value<'_>,
    ) -> Self {
        Self {
            context,
            source: LazyElementSource::ValueLiteral(io_buffer, unsafe {
                erase_lifetime::<Encoding>(value)
            }),
            spooky: PhantomData,
        }
    }

    pub(crate) fn new(context: EncodingContext, source: LazyElementSource<Encoding>) -> Self {
        Self {
            context,
            source,
            spooky: PhantomData,
        }
    }

    pub(crate) fn as_lazy_value<'top>(&'top self) -> LazyValue<'top, Encoding> {
        let expanded: LazyExpandedValue<'top, Encoding> = match &self.source {
            LazyElementSource::ValueLiteral(io_buffer, value) => {
                let backing_span = Span::from(io_buffer);
                let raw_value: Encoding::Value<'top> =
                    unsafe { set_lifetime::<'top, Encoding>(*value) };
                let raw_value = raw_value.with_backing_data(backing_span);
                LazyExpandedValue::from_literal(self.context.get_ref(), raw_value)
            }
        };
        LazyValue::new(expanded)
    }
}

impl<'top, Encoding: Decoder> From<LazyValue<'top, Encoding>> for LazyElement<Encoding> {
    fn from(value: LazyValue<'top, Encoding>) -> Self {
        match value.expanded().source() {
            ExpandedValueSource::ValueLiteral(raw_value) => {
                let span = raw_value.span();
                let span_bytes = span.bytes();
                let io_buffer = IoBuffer::at_offset(span.offset(), span_bytes);
                // TODO: Add the data source reference to the context!
                LazyElement::from_literal(
                    (*value.expanded().context.context).clone(),
                    io_buffer,
                    raw_value,
                )
            }
            ExpandedValueSource::SingletonEExp(_) => todo!(),
            ExpandedValueSource::Template(_, _) => todo!(),
            ExpandedValueSource::Constructed(_, _) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AnyEncoding, IonResult, Reader};

    #[test]
    fn try_it() -> IonResult<()> {
        let mut reader = Reader::new(AnyEncoding, "foo bar baz")?;
        let mut lazy_elements = vec![];
        while let Some(lazy_value) = reader.next()? {
            let owned: LazyElement<_> = LazyElement::from(lazy_value);
            lazy_elements.push(owned);
        }
        drop(reader);

        println!("# values: {}", lazy_elements.len());

        for element in &lazy_elements {
            let lazy_value = element.as_lazy_value();
            let value = lazy_value.read().unwrap();
            println!("{:?}", value);
        }

        Ok(())
    }
}
