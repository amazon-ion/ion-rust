use crate::result::{decoding_error_result, IonResult};
use crate::types::IonType;

/// Represents the type information found in the header byte of each binary Ion value.
/// While this value can be readily mapped to a user-level [`IonType`], it is a distinct concept.
/// The IonTypeCode enum captures system-level information that is not exposed to end users of the
/// library, including:
/// * Whether the cursor is positioned over whitespace that needs to be skipped.
/// * Whether the integer value being read is positive or negative.
/// * Whether the next type code is reserved.
///
/// See the
/// [Typed Value Formats](http://amzn.github.io/ion-docs/docs/binary.html#typed-value-formats)
/// section of the spec for more information.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub(crate) enum IonTypeCode {
    NullOrWhitespace, // 0
    Boolean,          // 1
    PositiveInteger,  // 2
    NegativeInteger,  // 3
    Float,            // 4
    Decimal,          // 5
    Timestamp,        // 6
    Symbol,           // 7
    String,           // 8
    Clob,             // 9
    Blob,             // 10
    List,             // 11
    SExpression,      // 12
    Struct,           // 13
    Annotation,       // 14
    Reserved,         // 15
}

impl IonTypeCode {
    /// Attempts to convert the system-level IonTypeCode into the corresponding user-level IonType.
    pub fn into_ion_type(self) -> IonResult<IonType> {
        use self::IonTypeCode::*;
        let ion_type = match self {
            NullOrWhitespace => IonType::Null,
            Boolean => IonType::Boolean,
            PositiveInteger | NegativeInteger => IonType::Integer,
            Float => IonType::Float,
            Decimal => IonType::Decimal,
            Timestamp => IonType::Timestamp,
            Symbol => IonType::Symbol,
            String => IonType::String,
            Clob => IonType::Clob,
            Blob => IonType::Blob,
            List => IonType::List,
            SExpression => IonType::SExpression,
            Struct => IonType::Struct,
            _ => {
                return decoding_error_result(format!(
                    "Attempted to make an IonType from an invalid type code: {:?}",
                    self
                ));
            }
        };
        Ok(ion_type)
    }

    /// Attempts to convert the provided byte into an IonTypeCode. Any value greater than 15
    /// will result in an Error.
    pub fn from(type_code: u8) -> IonResult<IonTypeCode> {
        use self::IonTypeCode::*;
        let ion_type_code = match type_code {
            0 => NullOrWhitespace,
            1 => Boolean,
            2 => PositiveInteger,
            3 => NegativeInteger,
            4 => Float,
            5 => Decimal,
            6 => Timestamp,
            7 => Symbol,
            8 => String,
            9 => Clob,
            10 => Blob,
            11 => List,
            12 => SExpression,
            13 => Struct,
            14 => Annotation,
            15 => Reserved,
            _ => {
                return decoding_error_result(format!("{:?} is not a valid header type code.", type_code));
            }
        };
        Ok(ion_type_code)
    }
}
