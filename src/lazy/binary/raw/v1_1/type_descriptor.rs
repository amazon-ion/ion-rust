use crate::binary::constants::v1_1::length_codes;
use crate::lazy::binary::encoded_value::EncodedHeader;
use crate::lazy::binary::raw::v1_1::IonTypeCode;
use crate::IonType;

/// Contains all of the information that can be extracted from the one-octet type descriptor
/// found at the beginning of each value, annotations wrapper, IVM, or NOP in a binary Ion stream.
/// For more information, consult the
/// [Typed Value Formats](https://amazon-ion.github.io/ion-docs/docs/binary.html#typed-value-formats)
/// section of the binary Ion spec.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct TypeDescriptor {
    pub ion_type_code: IonTypeCode,
    pub ion_type: Option<IonType>,
    pub length_code: u8,
}

/// A statically defined array of TypeDescriptor that allows a binary reader to map a given
/// byte (`u8`) to a `TypeDescriptor` without having to perform any masking or bitshift operations.
pub(crate) static ION_1_1_TYPE_DESCRIPTORS: &[TypeDescriptor; 256] = &init_type_descriptor_cache();

const DEFAULT_HEADER: TypeDescriptor = TypeDescriptor {
    ion_type_code: IonTypeCode::Nop,
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
        let (high_nibble, low_nibble) = (byte >> 4, byte & 0x0F);
        use IonTypeCode::*;

        let ion_type_code = match (high_nibble, low_nibble) {
            (0xE, 0x0) => IonVersionMarker,
            (0xE, 0xA) => NullNull,
            (0xE, 0xC..=0xD) => Nop,
            _ => Boolean, // Temporary, until everything is implemented to satisfy the LUT.
        };
        let ion_type = match ion_type_code {
            NullNull => Some(IonType::Null),
            Nop => None,
            IonVersionMarker => None,
            Boolean => Some(IonType::Bool),
            _ => panic!("the provided ion type code is either not implemented, or invalid"),
        };
        TypeDescriptor {
            ion_type,
            ion_type_code,
            length_code: low_nibble,
        }
    }

    pub fn is_null(&self) -> bool {
        self.ion_type.is_some() && self.length_code == length_codes::NULL
    }

    pub fn is_nop(&self) -> bool {
        self.ion_type_code == IonTypeCode::Nop
    }

    pub fn is_ivm_start(&self) -> bool {
        self.ion_type_code == IonTypeCode::IonVersionMarker
        // self.ion_type_code == IonTypeCode::AnnotationOrIvm && self.length_code == 0
    }

    pub fn is_annotation_wrapper(&self) -> bool {
        false
        // self.ion_type_code == IonTypeCode::AnnotationOrIvm && self.length_code > 0
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

pub enum LengthType {
    InHeader(usize),
    FlexUIntFollows,
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
    pub fn length_type(&self) -> LengthType {
        use LengthType::*;
        match (self.ion_type_code, self.length_code) {
            (IonTypeCode::Nop, 0xC) => InHeader(0),
            (IonTypeCode::NullNull, 0xA) => InHeader(0),
            _ => FlexUIntFollows,
        }
    }
}

impl EncodedHeader for Header {
    type TypeCode = IonTypeCode;

    fn ion_type(&self) -> IonType {
        self.ion_type
    }

    fn type_code(&self) -> Self::TypeCode {
        self.ion_type_code
    }

    fn length_code(&self) -> u8 {
        self.length_code
    }

    fn is_null(&self) -> bool {
        self.ion_type_code == IonTypeCode::NullNull || self.ion_type_code == IonTypeCode::TypedNull
    }
}
