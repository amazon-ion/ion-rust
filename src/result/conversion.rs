use crate::{Bytes, Decimal, Int, IonType, Sequence, Str, Struct, Symbol, Timestamp};

use std::marker::PhantomData;
use thiserror::Error;

pub type ConversionOperationResult<FromType, ToType> =
    Result<ToType, ConversionOperationError<FromType, ToType>>;
pub type ConversionResult<ToType> = Result<ToType, ConversionError>;

/// Represents a mismatch during conversion between the expected type and the actual value's type.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("Type conversion error; expected a(n) {output_type}, found a(n) {input_type}")]
pub struct ConversionError {
    input_type: String,
    output_type: String,
}

impl<FromType, ToType> From<ConversionOperationError<FromType, ToType>> for ConversionError
where
    FromType: ValueTypeExpectation,
    ToType: TypeExpectation,
{
    fn from(err: ConversionOperationError<FromType, ToType>) -> Self {
        ConversionError {
            input_type: err.input_value.expected_type_name(),
            output_type: ToType::expected_type_name(),
        }
    }
}

/// Represents a mismatch during conversion between the expected type and the actual value's type;
/// Holds the original value that was not able to be converted.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("Type conversion error; expected a(n) {}, found a(n) {}",
            ToType::expected_type_name(), .input_value.expected_type_name())]
pub struct ConversionOperationError<FromType, ToType>
where
    FromType: ValueTypeExpectation,
    ToType: TypeExpectation,
{
    input_value: FromType,
    output_type: PhantomData<ToType>,
}

impl<FromType, ToType> ConversionOperationError<FromType, ToType>
where
    FromType: ValueTypeExpectation,
    ToType: TypeExpectation,
{
    pub fn new(input_value: FromType) -> Self {
        Self {
            input_value,
            output_type: PhantomData::default(),
        }
    }
}

impl<FromType, ToType> From<FromType> for ConversionOperationError<FromType, ToType>
where
    FromType: ValueTypeExpectation,
    ToType: TypeExpectation,
{
    fn from(input_value: FromType) -> Self {
        Self::new(input_value)
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
