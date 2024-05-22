use crate::element::Element;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::writer::IonWriter;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::write_config::WriteConfig;
use crate::IonResult;

/// Transcribes text Ion to binary Ion
pub fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
    let buffer = Vec::new();
    let config = WriteConfig::<BinaryEncoding_1_0>::new();
    let mut writer = IonWriter::with_config(config, buffer)?;
    let elements = Element::read_all(text_ion)?;
    for element in &elements {
        element.write_element_to(&mut writer)?;
    }
    writer.close()
}
