use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::{Decoder, EncodingContext};
use std::marker::PhantomData;

pub(crate) enum LazyElementSource<Encoding: Decoder> {
    ValueLiteral(IoBuffer, Encoding::Value<'static>),
}

pub struct LazyElement<Encoding: Decoder> {
    context: EncodingContext,
    source: LazyElementSource<Encoding>,
    spooky: PhantomData<Encoding>,
}

fn erase_lifetime<Encoding: Decoder>(raw_value: Encoding::Value<'_>) -> Encoding::Value<'static> {
    unsafe { std::mem::transmute(raw_value) }
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    pub(crate) fn new(context: EncodingContext, source: LazyElementSource<Encoding>) -> Self {
        Self {
            context,
            source,
            spooky: PhantomData,
        }
    }

    // pub(crate) fn value(&self) -> Encoding::Value<'_> {
    //     match &self.source {
    //         LazyElementSource::ValueLiteral(_, value) => value,
    //     }
    // }
}

//
// pub enum SavedValueSource<Encoding> {}
//
// impl<Encoding> SavedValue<Encoding> {}
