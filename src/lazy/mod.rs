//! Provides an ergonomic, lazy view of an Ion stream that permits random access within each
//! top level value.

pub mod binary;
pub mod decoder;
pub(crate) mod encoding;
pub mod raw_stream_item;
pub mod raw_value_ref;
pub mod reader;
pub mod sequence;
pub mod r#struct;
pub mod system_reader;
pub mod system_stream_item;
pub mod text;
pub mod value;
pub mod value_ref;
