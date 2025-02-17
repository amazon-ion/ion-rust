use crate::lazy::expanded::IoBufferSource;
use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::{
    Decoder, EncodingContext, ExpandedValueSource, HasSpan, LazyExpandedValue, LazyRawValue,
    LazyValue, Span,
};
use std::marker::PhantomData;

pub(crate) enum LazyElementSource<Encoding: Decoder> {
    ValueLiteral(Encoding::Value<'static>),
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
    pub(crate) fn from_literal(context: EncodingContext, value: Encoding::Value<'_>) -> Self {
        Self {
            context,
            source: LazyElementSource::ValueLiteral(unsafe { erase_lifetime::<Encoding>(value) }),
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
            LazyElementSource::ValueLiteral(raw_value) => {
                let IoBufferSource::IoBuffer(ref io_buffer) =
                    (unsafe { &*self.context.io_buffer_source.get() })
                else {
                    unreachable!(
                        "tried to access cloned EncodingContext IoBuffer but it didn't exist"
                    );
                };
                let value_span = raw_value.span();
                let value_offset = value_span.offset();
                let value_length = value_span.len();
                // The value begins at stream position `value_offset`.
                // The buffer begins at `io_buffer.stream_offset()`.
                // To find the serialized value within the buffer,
                // subtract the buffer's offset from the value's.
                let local_offset = value_offset - io_buffer.stream_offset();
                let value_bytes = &io_buffer.all_bytes()[local_offset..local_offset + value_length];
                // Construct a new span that is backed by the IoBuffer.
                let backing_span = Span::with_offset(value_offset, value_bytes);
                // SAFETY: Because the IoBuffer's data is reference counted, is guaranteed to live as `self`.
                //         This means we can hand out data that depends on it with a shorter lifetime.
                let raw_value: Encoding::Value<'top> =
                    unsafe { set_lifetime::<'top, Encoding>(*raw_value) };
                let raw_value = raw_value.with_backing_data(backing_span);
                LazyExpandedValue::from_literal(self.context.get_ref(), raw_value)
            }
        };
        LazyValue::new(expanded)
    }
}

impl<'top, Encoding: Decoder> From<LazyValue<'top, Encoding>> for LazyElement<Encoding> {
    fn from(value: LazyValue<'top, Encoding>) -> Self {
        value.to_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AnyEncoding, IonResult, Reader};

    #[test]
    fn try_it() -> IonResult<()> {
        let mut reader = Reader::new(AnyEncoding, "foo bar baz")?;
        let mut lazy_elements: Vec<LazyElement<AnyEncoding>> = vec![];
        while let Some(lazy_value) = reader.next()? {
            let owned: LazyElement<_> = lazy_value.to_owned();
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
