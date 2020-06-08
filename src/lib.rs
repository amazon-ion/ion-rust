#![allow(dead_code)]

#[macro_use]
extern crate failure_derive;

pub mod result;

pub mod binary;
pub mod cursor;
pub mod data_source;
pub mod types;

pub use binary::cursor::BinaryIonCursor;
pub use cursor::Cursor;
pub use data_source::IonDataSource;
pub use types::IonType;
