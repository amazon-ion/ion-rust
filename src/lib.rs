#![allow(dead_code)]

/// A [`try`]-like macro to workaround the [`Option`]/[`Result`] nested APIs.
/// These API require checking the type and then calling the appropriate getter function
/// (which returns a None if you got it wrong). This macro turns the `None` into
/// an `IonError` which cannot be currently done with `?`.
macro_rules! try_to {
    ($getter:expr) => {
        match $getter {
            Some(value) => value,
            None => illegal_operation(format!("Missing a value: {}", stringify!($getter)))?,
        }
    };
}

pub mod result;

pub mod binary;
pub mod data_source;
pub mod raw_reader;
pub mod text;
pub mod types;
pub mod value;

pub mod constants;
mod raw_symbol_token;
mod raw_symbol_token_ref;
mod reader;
mod stream_reader;
mod symbol_table;
mod system_reader;
mod writer;

pub use binary::raw_binary_reader::RawBinaryReader;
pub use data_source::IonDataSource;
pub use raw_reader::RawStreamItem;
pub use reader::Reader;
pub use reader::StreamItem;
pub use stream_reader::StreamReader;
pub use symbol_table::SymbolTable;
pub use system_reader::{SystemReader, SystemStreamItem};
pub use types::IonType;

/// Re-exports of third party dependencies that are part of our public API.
///
/// See also: https://github.com/amzn/ion-rust/issues/302.
pub mod external {
    pub use bigdecimal;
}
