//! This module provides an implementation of the data types described by the
//! [Ion Data Model](http://amzn.github.io/ion-docs/docs/spec.html#the-ion-data-model)
//! section of the Ion 1.0 spec.

pub type SymbolId = usize;

pub mod coefficient;
pub mod decimal;
pub mod integer;
pub mod magnitude;
pub mod timestamp;

use crate::result::{illegal_operation, IonError};
use ion_c_sys::ION_TYPE;
use std::{convert::TryFrom, fmt};

/// Represents the Ion data type of a given value. To learn more about each data type,
/// read [the Ion Data Model](http://amzn.github.io/ion-docs/docs/spec.html#the-ion-data-model)
/// section of the spec.
#[derive(Debug, PartialEq, Eq, PartialOrd, Copy, Clone)]
pub enum IonType {
    Null,
    Boolean,
    Integer,
    Float,
    Decimal,
    Timestamp,
    Symbol,
    String,
    Clob,
    Blob,
    List,
    SExpression,
    Struct,
}

impl fmt::Display for IonType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                IonType::Null => "null",
                IonType::Boolean => "boolean",
                IonType::Integer => "integer",
                IonType::Float => "float",
                IonType::Decimal => "decimal",
                IonType::Timestamp => "timestamp",
                IonType::Symbol => "symbol",
                IonType::String => "string",
                IonType::Clob => "clob",
                IonType::Blob => "blob",
                IonType::List => "list",
                IonType::SExpression => "sexp",
                IonType::Struct => "struct",
            }
        )
    }
}

impl IonType {
    pub fn is_container(&self) -> bool {
        use IonType::*;
        matches!(self, List | SExpression | Struct)
    }
}

/// Returns the number of base-10 digits needed to represent `value`.
fn num_decimal_digits_in_u64(value: u64) -> u64 {
    if value == 0 {
        return 1;
    }
    let log_base_ten = (value as f64).log10();
    let count = log_base_ten.ceil();
    if log_base_ten == count {
        // If ceil() didn't change the count, then `value` is an exact power of ten.
        // We need to add one to get the correct count.
        // Examples:
        //    (1).log10() ==   (1).log10().ceil() == 0
        //   (10).log10() ==  (10).log10().ceil() == 1
        //  (100).log10() == (100).log10().ceil() == 2
        count as u64 + 1
    } else {
        count as u64
    }
}

impl TryFrom<ION_TYPE> for IonType {
    type Error = IonError;

    fn try_from(value: ION_TYPE) -> Result<Self, Self::Error> {
        use IonType::*;
        match value {
            ion_c_sys::ION_TYPE_NULL => Ok(Null),
            ion_c_sys::ION_TYPE_BOOL => Ok(Boolean),
            ion_c_sys::ION_TYPE_INT => Ok(Integer),
            ion_c_sys::ION_TYPE_FLOAT => Ok(Float),
            ion_c_sys::ION_TYPE_DECIMAL => Ok(Decimal),
            ion_c_sys::ION_TYPE_TIMESTAMP => Ok(Timestamp),
            ion_c_sys::ION_TYPE_SYMBOL => Ok(Symbol),
            ion_c_sys::ION_TYPE_STRING => Ok(String),
            ion_c_sys::ION_TYPE_CLOB => Ok(Clob),
            ion_c_sys::ION_TYPE_BLOB => Ok(Blob),
            ion_c_sys::ION_TYPE_LIST => Ok(List),
            ion_c_sys::ION_TYPE_SEXP => Ok(SExpression),
            ion_c_sys::ION_TYPE_STRUCT => Ok(Struct),
            _ => illegal_operation(format!("Could not convert Ion C ION_TYPE: ${:?}", value)),
        }
    }
}

impl From<IonType> for ION_TYPE {
    fn from(ion_type: IonType) -> ION_TYPE {
        use IonType::*;
        match ion_type {
            Null => ion_c_sys::ION_TYPE_NULL,
            Boolean => ion_c_sys::ION_TYPE_BOOL,
            Integer => ion_c_sys::ION_TYPE_INT,
            Float => ion_c_sys::ION_TYPE_FLOAT,
            Decimal => ion_c_sys::ION_TYPE_DECIMAL,
            Timestamp => ion_c_sys::ION_TYPE_TIMESTAMP,
            Symbol => ion_c_sys::ION_TYPE_SYMBOL,
            String => ion_c_sys::ION_TYPE_STRING,
            Clob => ion_c_sys::ION_TYPE_CLOB,
            Blob => ion_c_sys::ION_TYPE_BLOB,
            List => ion_c_sys::ION_TYPE_LIST,
            SExpression => ion_c_sys::ION_TYPE_SEXP,
            Struct => ion_c_sys::ION_TYPE_STRUCT,
        }
    }
}

#[cfg(test)]
mod type_test {
    use super::*;
    use crate::result::IonResult;
    use ion_c_sys::reader::*;
    use rstest::*;
    use std::convert::TryInto;
    use IonType::*;

    // XXX these tests are a little more complex than we'd normally like, but it at least
    //     tests the real cases from the underlying parser for the mapping, rather that just
    //     testing the opaque pointers.
    #[rstest]
    #[case::null("null", Null)]
    #[case::bool("true", Boolean)]
    #[case::int("-5", Integer)]
    #[case::float("100e0", Float)]
    #[case::decimal("1.1", Decimal)]
    #[case::timestamp("2014-10-16T", Timestamp)]
    #[case::symbol("foobar", Symbol)]
    #[case::string("'''foosball'''", String)]
    #[case::clob("{{'''moon'''}}", Clob)]
    #[case::blob("{{Z29vZGJ5ZQ==}}", Blob)]
    #[case::list("[1, 2, 3]", List)]
    #[case::sexp("(a b c)", SExpression)]
    #[case::structure("{a:1, b:2}", Struct)]
    fn ionc_type_conversion(
        #[case] data: &str,
        #[case] expected_ion_type: IonType,
    ) -> IonResult<()> {
        let mut reader: IonCReaderHandle = data.try_into()?;
        let ion_type: IonType = reader.next()?.try_into()?;
        assert_eq!(expected_ion_type, ion_type);

        let eof_result: IonResult<IonType> = reader.next()?.try_into();
        match eof_result {
            Err(IonError::IllegalOperation { operation: _ }) => {}
            otherwise => panic!("Unexpected conversion of EOF: {:?}", otherwise),
        };

        Ok(())
    }
}
