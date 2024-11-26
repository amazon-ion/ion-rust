use crate::{Bytes, Decimal, Int, IonType, Sequence, Str, Struct, Symbol, Timestamp};
use thiserror::Error;

pub type ConversionResult<T> = Result<T, ConversionError>;

/// A mismatch between the expected type and the actual value's type.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("Type conversion error; expected a(n) {output_type}, found a(n) {input_type}")]
pub struct ConversionError {
    input_type: String,
    output_type: String,
}

/// Represents the output of a conversion operation, returning either the successfully
/// converted value or the original value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Conversion<FromType, ToType> {
    /// Conversion success.
    Success(ToType),
    /// Conversion failure; returning original.
    Fail(FromType),
}

impl<FromType, ToType> Conversion<FromType, ToType> {
    pub fn is_success(&self) -> bool {
        matches!(self, Conversion::Success(_))
    }

    pub fn is_failure(&self) -> bool {
        matches!(self, Conversion::Fail(_))
    }
}

impl<FromType, ToType> Conversion<FromType, ToType>
where
    ToType: TypeExpectation,
    FromType: ValueTypeExpectation,
{
    pub fn unwrap(self) -> ToType {
        let result: ConversionResult<ToType> = self.into();
        result.unwrap()
    }
}

pub trait IonTypeExpectation {
    fn ion_type(&self) -> IonType;
}

pub trait ValueTypeExpectation {
    fn expected_type_name(&self) -> String;
}

pub trait TypeExpectation {
    fn expected_type_name() -> String;
}

macro_rules! impl_type_expectation {
    ($ty:ty, $e:expr) => {
        impl TypeExpectation for $ty {
            fn expected_type_name() -> String {
                $e.to_string()
            }
        }
    };
}

macro_rules! impl_type_and_ref_expectation {
    ($ty:ty, $e:expr) => {
        impl_type_expectation!($ty, $e);
        impl_type_expectation!(&$ty, $e);
    };
}

impl_type_and_ref_expectation!(Int, IonType::Int);
impl_type_expectation!(i64, "i64 value");
impl_type_expectation!(f64, IonType::Float);
impl_type_and_ref_expectation!(Decimal, IonType::Decimal);
impl_type_and_ref_expectation!(Timestamp, IonType::Timestamp);
impl_type_and_ref_expectation!(String, "text value");
impl_type_expectation!(&str, "text value");
impl_type_and_ref_expectation!(Str, IonType::String);
impl_type_and_ref_expectation!(Symbol, IonType::Symbol);
impl_type_expectation!(bool, IonType::Bool);
impl_type_and_ref_expectation!(Bytes, "lob value");
impl_type_expectation!(&[u8], "lob value");
impl_type_and_ref_expectation!(Sequence, "sequence value");
impl_type_and_ref_expectation!(Struct, IonType::Struct);

impl<T> ValueTypeExpectation for T
where
    T: IonTypeExpectation,
{
    fn expected_type_name(&self) -> String {
        self.ion_type().to_string()
    }
}

impl<FromType, ToType> From<Conversion<FromType, ToType>> for Option<ToType>
where
    ToType: TypeExpectation,
    FromType: ValueTypeExpectation,
{
    fn from(conversion: Conversion<FromType, ToType>) -> Self {
        match conversion {
            Conversion::Success(to) => Some(to),
            Conversion::Fail(_) => None,
        }
    }
}

impl<FromType, ToType> From<Conversion<FromType, ToType>> for ConversionResult<ToType>
where
    ToType: TypeExpectation,
    FromType: ValueTypeExpectation,
{
    fn from(conversion: Conversion<FromType, ToType>) -> Self {
        match conversion {
            Conversion::Success(to) => Ok(to),
            Conversion::Fail(from) => Err(ConversionError {
                input_type: ToType::expected_type_name(),
                output_type: from.expected_type_name(),
            }),
        }
    }
}

pub trait ConversionExpectation<ToType> {
    fn expect_convert(self, input_type: &impl ValueTypeExpectation) -> ConversionResult<ToType>;
}

impl<ToType> ConversionExpectation<ToType> for Option<ToType>
where
    ToType: TypeExpectation,
{
    fn expect_convert(self, input_type: &impl ValueTypeExpectation) -> ConversionResult<ToType> {
        match self {
            Some(value) => Ok(value),
            None => Err(ConversionError {
                input_type: input_type.expected_type_name(),
                output_type: ToType::expected_type_name(),
            }),
        }
    }
}
