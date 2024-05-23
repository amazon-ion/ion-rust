//! Provides an ergonomic, lazy view of an Ion stream that permits random access within each
//! top level value.

pub(crate) mod any_encoding;
pub(crate) mod binary;
pub(crate) mod bytes_ref;
pub(crate) mod decoder;
pub(crate) mod encoder;
pub(crate) mod encoding;
pub(crate) mod expanded;
pub(crate) mod lazy_value_cache;
mod never;
pub(crate) mod raw_stream_item;
pub(crate) mod raw_value_ref;
pub(crate) mod reader;
pub(crate) mod sequence;
pub(crate) mod span;
pub(crate) mod str_ref;
pub(crate) mod streaming_raw_reader;
pub(crate) mod r#struct;
pub(crate) mod system_reader;
pub(crate) mod system_stream_item;
pub(crate) mod text;
pub(crate) mod value;
pub(crate) mod value_ref;
