use crate::constants::MAX_READ_WRITE_DEPTH;
use crate::element::Element;
use crate::lazy::encoder::writer::Writer;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::write_config::WriteConfig;
use crate::{IonResult, IonType};

/// Transcribes text Ion to binary Ion
pub fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
    elements_to_binary_ion(&Element::read_all(text_ion)?)
}

/// Encodes `elements` as binary Ion.
pub fn elements_to_binary_ion<'a>(
    elements: impl IntoIterator<Item = &'a Element>,
) -> IonResult<Vec<u8>> {
    let buffer = Vec::new();
    let config = WriteConfig::<BinaryEncoding_1_0>::new();
    let mut writer = Writer::new(config, buffer)?;
    for element in elements {
        writer.write(element)?;
    }
    writer.close()
}

/// The Ion 1.0 binary type descriptor of an empty container of type `kind`.
pub(crate) fn binary_type_descriptor(kind: IonType) -> u8 {
    match kind {
        IonType::List => 0xB0,
        IonType::SExp => 0xC0,
        IonType::Struct => 0xD0,
        _ => unreachable!("not a container type: {kind}"),
    }
}

/// Encodes an Ion 1.0 binary value whose type descriptor is `type_code`, followed by `contents`.
/// The low four bits of `type_code` must be 0. The length of `contents` is stored in those bits if
/// it is less than 14, and as a VarUInt after the type descriptor otherwise. A struct whose
/// `contents` is one byte long also uses the VarUInt, because `0xD1` starts a sorted struct.
pub(crate) fn binary_value(type_code: u8, contents: Vec<u8>) -> Vec<u8> {
    let mut value = binary_header(type_code, contents.len());
    value.extend(contents);
    value
}

/// Encodes the type descriptor and length of a value that `binary_value` would encode with
/// `length` bytes of contents.
fn binary_header(type_code: u8, mut length: usize) -> Vec<u8> {
    let mut value = vec![type_code];
    if length < 14 && !(type_code == 0xD0 && length == 1) {
        value[0] |= length as u8;
    } else {
        value[0] |= 0x0E;
        let mut var_uint = vec![(length & 0x7F) as u8 | 0x80];
        length >>= 7;
        while length > 0 {
            var_uint.insert(0, (length & 0x7F) as u8);
            length >>= 7;
        }
        value.extend(var_uint);
    }
    value
}

/// Encodes `innermost`, an encoded binary value, in `levels` containers of type `kind` as an
/// Ion 1.0 binary stream. Each struct has one field, named `name` (`$4`).
pub(crate) fn binary_nested(kind: IonType, levels: usize, innermost: Vec<u8>) -> Vec<u8> {
    let field_name: &[u8] = if kind == IonType::Struct {
        &[0x84]
    } else {
        &[]
    };
    // A container's header depends on the length of its contents, so the headers are computed
    // from the innermost container outward and then written in the opposite order. This keeps the
    // time linear in `levels`, which tests that nest values 100,000 levels deep rely on.
    let mut headers = Vec::with_capacity(levels);
    let mut length = innermost.len();
    for _ in 0..levels {
        let header = binary_header(binary_type_descriptor(kind), field_name.len() + length);
        length += header.len() + field_name.len();
        headers.push(header);
    }
    let mut stream = vec![0xE0, 0x01, 0x00, 0xEA];
    for header in headers.iter().rev() {
        stream.extend(header);
        stream.extend(field_name);
    }
    stream.extend(innermost);
    stream
}

/// Whether lazy binary navigation checks [`MAX_READ_WRITE_DEPTH`] at every depth. Binary values
/// store their depth in a `u8` that saturates at 255, so with a greater limit it never fails.
pub(crate) const LAZY_BINARY_DEPTH_IS_CHECKED: bool = MAX_READ_WRITE_DEPTH <= u8::MAX as u16;
