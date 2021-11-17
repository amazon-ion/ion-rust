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
mod reader;
mod symbol_table;
mod system_event_handler;

pub use binary::raw_binary_reader::RawBinaryReader;
pub use data_source::IonDataSource;
pub use raw_reader::RawReader;
pub use reader::Reader;
pub use symbol_table::SymbolTable;
pub use system_event_handler::SystemEventHandler;
pub use types::IonType;

/// Re-exports of third party dependencies that are part of our public API.
///
/// See also: https://github.com/amzn/ion-rust/issues/302.
pub mod external {
    pub use bigdecimal;
}
