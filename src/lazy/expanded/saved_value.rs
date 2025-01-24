use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::EncodingContext;
use std::marker::PhantomData;

pub enum SavedValueSource<Encoding> {
    SingletonEExp(PhantomData<Encoding>),
}

pub struct SavedValue<Encoding> {
    buffer: IoBuffer,
    context: EncodingContext,
    source: SavedValueSource<Encoding>,
    spooky: PhantomData<Encoding>,
}
//
// pub enum SavedValueSource<Encoding> {}
//
// impl<Encoding> SavedValue<Encoding> {}
