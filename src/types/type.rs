use crate::result::{illegal_operation, IonError};
use ion_c_sys::ION_TYPE;
use std::convert::TryFrom;

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

impl IonType {
    pub fn is_container(&self) -> bool {
        use IonType::*;
        match self {
            List | SExpression | Struct => true,
            _ => false,
        }
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
