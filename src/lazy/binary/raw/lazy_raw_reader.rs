use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::result::{decoding_error, incomplete_data_error};
use crate::{IonResult, RawSymbolTokenRef};
use std::fmt::{self, Debug, Formatter};

pub(crate) struct DataSource<'data> {
    buffer: ImmutableBuffer<'data>,
    bytes_to_skip: usize, // initially 0; try to advance on 'next'
}

impl<'data> DataSource<'data> {
    pub(crate) fn new(buffer: ImmutableBuffer<'data>) -> DataSource<'data> {
        DataSource {
            buffer,
            bytes_to_skip: 0,
        }
    }

    pub(crate) fn buffer(&self) -> ImmutableBuffer<'data> {
        self.buffer
    }

    fn advance_to_next_item(&mut self) -> IonResult<ImmutableBuffer<'data>> {
        if self.buffer.len() < self.bytes_to_skip {
            return incomplete_data_error(
                "cannot advance to next item, insufficient data in buffer",
                self.buffer.offset(),
            );
        }

        if self.bytes_to_skip > 0 {
            Ok(self.buffer.consume(self.bytes_to_skip))
        } else {
            Ok(self.buffer)
        }
    }

    pub(crate) fn try_parse_next<
        F: Fn(ImmutableBuffer<'data>) -> IonResult<Option<LazyRawValue<'data>>>,
    >(
        &mut self,
        parser: F,
    ) -> IonResult<Option<LazyRawValue<'data>>> {
        let buffer = self.advance_to_next_item()?;

        let lazy_value = match parser(buffer) {
            Ok(Some(output)) => output,
            Ok(None) => return Ok(None),
            Err(e) => return Err(e),
        };

        self.buffer = buffer;
        self.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(Some(lazy_value))
    }
}

pub struct LazyRawBinaryReader<'data> {
    data: DataSource<'data>,
}

pub struct LazyRawField<'data> {
    pub(crate) value: LazyRawValue<'data>,
}

impl<'data> LazyRawBinaryReader<'data> {
    pub fn new(data: &'data [u8]) -> LazyRawBinaryReader<'data> {
        Self::new_with_offset(data, 0)
    }

    fn new_with_offset(data: &'data [u8], offset: usize) -> LazyRawBinaryReader<'data> {
        let data = DataSource::new(ImmutableBuffer::new_with_offset(data, offset));
        LazyRawBinaryReader { data }
    }

    fn read_ivm(&mut self, buffer: ImmutableBuffer<'data>) -> IonResult<RawStreamItem<'data>> {
        let ((major, minor), _buffer_after_ivm) = buffer.read_ivm()?;
        if (major, minor) != (1, 0) {
            return decoding_error(format!(
                "unsupported version of Ion: v{}.{}; only 1.0 is supported",
                major, minor,
            ));
        }
        self.data.buffer = buffer;
        self.data.bytes_to_skip = 4; // IVM length
        return Ok(RawStreamItem::VersionMarker(1, 0));
    }

    fn read_value(&mut self, buffer: ImmutableBuffer<'data>) -> IonResult<RawStreamItem<'data>> {
        let lazy_value = match ImmutableBuffer::peek_value_without_field_id(buffer)? {
            Some(lazy_value) => lazy_value,
            None => return Ok(RawStreamItem::Nothing),
        };
        self.data.buffer = buffer;
        self.data.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(RawStreamItem::Value(lazy_value))
    }

    // Elided 'top lifetime
    pub fn next<'top>(&'top mut self) -> IonResult<RawStreamItem<'data>>
    where
        'data: 'top,
    {
        let mut buffer = self.data.advance_to_next_item()?;
        if buffer.is_empty() {
            return Ok(RawStreamItem::Nothing);
        }
        let type_descriptor = buffer.peek_type_descriptor()?;
        if type_descriptor.is_nop() {
            (_, buffer) = buffer.consume_nop_padding(type_descriptor)?;
        } else if type_descriptor.is_ivm_start() {
            return self.read_ivm(buffer);
        }

        self.read_value(buffer)
    }
}

impl<'data> LazyRawField<'data> {
    pub(crate) fn new(value: LazyRawValue<'data>) -> Self {
        LazyRawField { value }
    }

    pub fn name(&self) -> RawSymbolTokenRef<'data> {
        // We're in a struct field, the field ID must be populated.
        let field_id = self.value.encoded_value.field_id.unwrap();
        RawSymbolTokenRef::SymbolId(field_id)
    }

    pub fn value(&self) -> &LazyRawValue<'data> {
        &self.value
    }

    pub(crate) fn into_value(self) -> LazyRawValue<'data> {
        self.value
    }
}

impl<'a> Debug for LazyRawField<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "${}: {:?}",
            self.value.encoded_value.field_id.unwrap(),
            self.value()
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::lazy_raw_reader::LazyRawBinaryReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::raw_stream_item::RawStreamItem;
    use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
    use crate::{IonResult, IonType, RawSymbolTokenRef};

    #[test]
    fn test_struct() -> IonResult<()> {
        // This test only uses symbols in the system symbol table to avoid LST processing
        let data = &to_binary_ion(
            r#"
            {name:"hi", name: "hello"}
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(data);
        let _ivm = reader.next()?.expect_ivm()?;
        let value = reader.next()?.expect_value()?;
        let lazy_struct = value.read()?.expect_struct()?;
        let mut fields = lazy_struct.iter();
        let field1 = fields.next().expect("field 1")?;
        assert_eq!(field1.name(), 4.as_raw_symbol_token_ref()); // 'name'
        Ok(())
    }

    #[test]
    fn test_top_level() -> IonResult<()> {
        let data = &to_binary_ion(
            r#"
            "yo"
            77
            true
            {name:"hi", name: "hello"}
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(data);
        loop {
            match reader.next()? {
                RawStreamItem::VersionMarker(major, minor) => println!("IVM: v{}.{}", major, minor),
                RawStreamItem::Value(value) => println!("{:?}", value.read()?),
                RawStreamItem::Nothing => break,
            }
        }
        Ok(())
    }

    #[test]
    fn annotations() -> IonResult<()> {
        let data = &to_binary_ion(
            r#"
            $ion_symbol_table::{symbols: ["foo", "bar", "baz"]}
            foo::bar::baz::7             
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(data);
        let _ivm = reader.next()?.expect_ivm()?;

        // Read annotations from $ion_symbol_table::{...}
        let symbol_table = reader.next()?.expect_value()?;
        assert_eq!(symbol_table.ion_type(), IonType::Struct);
        let annotations = symbol_table
            .annotations()
            .collect::<IonResult<Vec<RawSymbolTokenRef<'_>>>>()?;
        assert_eq!(annotations.len(), 1);
        assert_eq!(annotations[0], 3.as_raw_symbol_token_ref());

        // Read annotations from foo::bar::baz::7
        let int = reader.next()?.expect_value()?;
        assert_eq!(int.ion_type(), IonType::Int);
        let annotations = int
            .annotations()
            .collect::<IonResult<Vec<RawSymbolTokenRef<'_>>>>()?;
        assert_eq!(annotations.len(), 3);
        assert_eq!(annotations[0], 10.as_raw_symbol_token_ref());
        assert_eq!(annotations[1], 11.as_raw_symbol_token_ref());
        assert_eq!(annotations[2], 12.as_raw_symbol_token_ref());
        Ok(())
    }

    #[test]
    fn nop() -> IonResult<()> {
        let data: Vec<u8> = vec![
            0xe0, 0x01, 0x00, 0xea, // IVM
            0x00, // 1-byte NOP
            0x01, 0xff, // 2-byte NOP
            0x02, 0xff, 0xff, // 3-byte NOP
            0x0f, // null
        ];

        let mut reader = LazyRawBinaryReader::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_null()?,
            IonType::Null
        );

        Ok(())
    }
}
