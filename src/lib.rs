#![allow(dead_code)]

#[macro_use]
extern crate failure_derive;

pub mod result;

mod binary;
mod cursor;
mod data_source;
mod types;
