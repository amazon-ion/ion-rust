use crate::binary::constants::v1_0::length_codes;
use crate::binary::nibbles::nibbles_from_byte;
use crate::binary::IonTypeCode;
use crate::types::IonType;

/// Contains all of the information that can be extracted from the one-octet type descriptor
/// found at the beginning of each value, annotations wrapper, IVM, or NOP in a binary Ion stream.
/// For more information, consult the
/// [Typed Value Formats](https://amazon-ion.github.io/ion-docs/docs/binary.html#typed-value-formats)
/// section of the binary Ion spec.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct TypeDescriptor {
    pub ion_type_code: IonTypeCode,
    pub ion_type: Option<IonType>,
    pub length_code: u8,
}

/// A statically defined array of TypeDescriptor that allows a binary reader to map a given
/// byte (`u8`) to a `TypeDescriptor` without having to perform any masking or bitshift operations.
pub(crate) const ION_1_0_TYPE_DESCRIPTORS: &[TypeDescriptor; 256] = &init_type_descriptor_cache();

const DEFAULT_HEADER: TypeDescriptor = TypeDescriptor {
    ion_type_code: IonTypeCode::NullOrNop,
    ion_type: None,
    length_code: 0,
};

pub(crate) const fn init_type_descriptor_cache() -> [TypeDescriptor; 256] {
    let mut jump_table = [DEFAULT_HEADER; 256];
    let mut index: usize = 0;
    while index < 256 {
        let byte = index as u8;
        jump_table[index] = TypeDescriptor::from_byte(byte);
        index += 1;
    }
    jump_table
}

impl TypeDescriptor {
    /// Attempts to parse the provided byte. If the type code is unrecognized or the
    /// type code + length code combination is illegal, an error will be returned.
    pub const fn from_byte(byte: u8) -> TypeDescriptor {
        let (type_code, length_code) = nibbles_from_byte(byte);
        use IonTypeCode::*;
        let ion_type_code = match type_code {
            0 => NullOrNop,
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
            14 => AnnotationOrIvm,
            15 => Reserved,
            _ => panic!("type code was larger than a nibble"),
        };
        let ion_type = match ion_type_code {
            NullOrNop if length_code == length_codes::NULL => Some(IonType::Null),
            NullOrNop => None,
            Boolean => Some(IonType::Bool),
            PositiveInteger => Some(IonType::Int),
            NegativeInteger => Some(IonType::Int),
            Float => Some(IonType::Float),
            Decimal => Some(IonType::Decimal),
            Timestamp => Some(IonType::Timestamp),
            Symbol => Some(IonType::Symbol),
            String => Some(IonType::String),
            Clob => Some(IonType::Clob),
            Blob => Some(IonType::Blob),
            List => Some(IonType::List),
            SExpression => Some(IonType::SExp),
            Struct => Some(IonType::Struct),
            AnnotationOrIvm => None,
            Reserved => None,
        };
        TypeDescriptor {
            ion_type,
            ion_type_code,
            length_code,
        }
    }

    pub fn is_null(&self) -> bool {
        self.ion_type.is_some() && self.length_code == length_codes::NULL
    }

    pub fn is_nop(&self) -> bool {
        self.ion_type_code == IonTypeCode::NullOrNop && self.length_code != length_codes::NULL
    }

    pub fn is_ivm_start(&self) -> bool {
        self.ion_type_code == IonTypeCode::AnnotationOrIvm && self.length_code == 0
    }

    pub fn is_annotation_wrapper(&self) -> bool {
        self.ion_type_code == IonTypeCode::AnnotationOrIvm && self.length_code > 0
    }

    #[inline]
    pub fn to_header(self) -> Option<Header> {
        let ion_type = self.ion_type?;
        let header = Header {
            ion_type,
            ion_type_code: self.ion_type_code,
            length_code: self.length_code,
        };
        Some(header)
    }
}

/// Represents a `TypeDescriptor` that appears before an Ion value (and not a NOP, IVM,
/// or annotations wrapper).
///
/// Notably, it stores an `IonType` instead of an `Option<IonType>`, allowing functions that expect
/// a value header to avoid matching/unwrapping.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub ion_type: IonType,
    // The only time the `ion_type_code` is required is to distinguish between positive
    // and negative integers.
    pub ion_type_code: IonTypeCode,
    pub length_code: u8,
}

impl Header {
    pub fn is_null(&self) -> bool {
        self.length_code == length_codes::NULL
    }
}
