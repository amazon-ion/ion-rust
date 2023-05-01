use crate::element::Element;
use crate::{BinaryWriterBuilder, IonResult, IonWriter};

/// Transcribes text Ion to binary Ion
pub fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
    let mut buffer = Vec::new();
    let mut writer = BinaryWriterBuilder::default().build(&mut buffer)?;
    let elements = Element::read_all(text_ion)?;
    for element in &elements {
        element.write_to(&mut writer)?;
    }
    writer.flush()?;
    drop(writer);
    Ok(buffer)
}
