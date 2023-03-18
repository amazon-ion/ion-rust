// Copyright Amazon.com, Inc. or its affiliates.

use crate::ion_eq::IonEq;
use crate::text::text_formatter::IonValueFormatter;
use crate::types::decimal::Decimal;
use crate::types::integer::Int;
use crate::types::timestamp::Timestamp;
use crate::{IonResult, IonType, ReaderBuilder, Symbol};
use num_bigint::BigInt;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::iter::FromIterator;

use crate::element::builders::{ListBuilder, SExpBuilder, StructBuilder};
use crate::element::iterators::{
    ElementsIterator, FieldIterator, FieldValuesIterator, IndexVec, SymbolsIterator,
};
use crate::element::reader::ElementReader;
use crate::symbol_ref::AsSymbolRef;
