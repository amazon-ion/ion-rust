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
pub mod system_reader;
pub mod data_source;
pub mod text;
pub mod types;
pub mod value;

pub mod constants;
mod reader;
mod symbol_table;
mod system_event_handler;

pub use binary::cursor::BinaryIonCursor;
pub use system_reader::SystemReader;
pub use data_source::IonDataSource;
pub use reader::Reader;
pub use symbol_table::SymbolTable;
pub use system_event_handler::SystemEventHandler;
pub use types::IonType;
