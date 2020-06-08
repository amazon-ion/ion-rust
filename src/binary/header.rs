use crate::{
    binary::{nibbles::nibbles_from_byte, IonTypeCode},
    result::IonResult,
    types::IonType,
};

/// Contains all of the information that can be extracted from the one-octet type descriptor
/// found at the beginning of each value in a binary Ion stream.
/// For more information, consult the
/// [Typed Value Formats](http://amzn.github.io/ion-docs/docs/binary.html#typed-value-formats)
/// section of the binary Ion spec.
#[derive(Copy, Clone, Debug)]
pub(crate) struct Header {
    pub ion_type_code: IonTypeCode,
    pub ion_type: Option<IonType>,
    pub length_code: u8,
}

impl Header {
    /// Attempts to parse the provided byte. If the type code is unrecognized or the
    /// type code + length code combination is illegal, an error will be returned.
    pub fn from_byte(byte: u8) -> IonResult<Header> {
        let (type_code, length_code) = nibbles_from_byte(byte);
        let ion_type_code = IonTypeCode::from(type_code)?;
        let ion_type = ion_type_code.into_ion_type().ok();
        Ok(Header {
            ion_type,
            ion_type_code,
            length_code,
        })
    }
}

/// Parses all possible values of a single byte and stores them in a newly allocated Vec.
/// This Vec may be used as a jump table to avoid re-calculating the meaning of the same byte
/// value repeatedly.
/// It is expected that the jump table will be referenced when a reader attempts to begin reading
/// the next value from its input data. This calling code must handle the end-of-file case,
/// IO errors, and decoding errors. Each value in the table is stored as an
/// IonResult<Option<IonValueHeader>> so that in the even that another value is available and
/// no IO errors occur, the value from the jump table can be returned as-is with no transformations
/// required.
/// All values stored in the table are either an `Err(IonError::DecodingError)` or an
/// `Ok(Some(IonValueHeader))`.
// TODO: Define the jump table as a static constant at compile time to avoid recalculating it.
// https://github.com/amzn/ion-rust/issues/4
pub(crate) fn create_header_byte_jump_table() -> Vec<IonResult<Option<Header>>> {
    let mut header_jump_table = Vec::with_capacity(256);
    for byte_value in 0..=255 {
        let entry = match Header::from_byte(byte_value) {
            Ok(header) => Ok(Some(header)),
            Err(error) => Err(error),
        };
        header_jump_table.push(entry);
    }
    header_jump_table
}
