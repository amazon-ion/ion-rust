use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::result::IonFailure;
use crate::IonResult;

/// A binary Ion 1.0 reader that yields [`LazyRawValue`]s representing the top level values found
/// in the provided input stream.
pub struct LazyRawReader<'data> {
    data: DataSource<'data>,
}

impl<'data> LazyRawReader<'data> {
    /// Constructs a `LazyRawReader` positioned at the beginning of the provided input stream.
    pub fn new(data: &'data [u8]) -> LazyRawReader<'data> {
        Self::new_with_offset(data, 0)
    }

    /// Constructs a `LazyRawReader` positioned at the beginning of the provided input stream.
    /// The provided input stream is itself a slice starting `offset` bytes from the beginning
    /// of a larger data stream. This offset is used for reporting the absolute (stream-level)
    /// position of values encountered in `data`.
    fn new_with_offset(data: &'data [u8], offset: usize) -> LazyRawReader<'data> {
        let data = DataSource::new(ImmutableBuffer::new_with_offset(data, offset));
        LazyRawReader { data }
    }

    /// Helper method called by [`Self::next`]. Reads the current stream item as an Ion version
    /// marker. If the version is not 1.0, returns an [`crate::IonError::Decoding`].
    fn read_ivm(&mut self, buffer: ImmutableBuffer<'data>) -> IonResult<RawStreamItem<'data>> {
        let ((major, minor), _buffer_after_ivm) = buffer.read_ivm()?;
        if (major, minor) != (1, 0) {
            return IonResult::decoding_error(format!(
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
            None => return Ok(RawStreamItem::EndOfStream),
        };
        self.data.buffer = buffer;
        self.data.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(RawStreamItem::Value(lazy_value))
    }

    pub fn next<'top>(&'top mut self) -> IonResult<RawStreamItem<'data>>
    where
        'data: 'top,
    {
        let mut buffer = self.data.advance_to_next_item()?;
        if buffer.is_empty() {
            return Ok(RawStreamItem::EndOfStream);
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

/// Wraps an [`ImmutableBuffer`], allowing the reader to advance each time an item is successfully
/// parsed from it.
pub(crate) struct DataSource<'data> {
    // The buffer we're reading from
    buffer: ImmutableBuffer<'data>,
    // Each time something is parsed from the buffer successfully, the caller will mark the number
    // of bytes that may be skipped the next time `advance_to_next_item` is called.
    bytes_to_skip: usize,
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
            return IonResult::incomplete(
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

    /// Runs the provided parsing function on this DataSource's buffer.
    /// If it succeeds, marks the `DataSource` as ready to advance by the 'n' bytes
    /// that were consumed.
    /// If it does not succeed, the `DataSource` remains unchanged.
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

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::lazy_raw_reader::LazyRawReader;
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
        let mut reader = LazyRawReader::new(data);
        let _ivm = reader.next()?.expect_ivm()?;
        let value = reader.next()?.expect_value()?;
        let lazy_struct = value.read()?.expect_struct()?;
        let mut fields = lazy_struct.iter();
        let field1 = fields.next().expect("field 1")?;
        assert_eq!(field1.name(), 4.as_raw_symbol_token_ref()); // 'name'
        Ok(())
    }

    #[test]
    fn test_sequence() -> IonResult<()> {
        // This test only uses symbols in the system symbol table to avoid LST processing
        let data = &to_binary_ion(
            r#"
            [1, true, foo]
        "#,
        )?;
        let mut reader = LazyRawReader::new(data);
        let _ivm = reader.next()?.expect_ivm()?;
        let _symbol_table = reader.next()?.expect_value()?;
        let lazy_list = reader.next()?.expect_value()?.read()?.expect_list()?;
        // Exercise the `Debug` impl
        println!("Lazy Raw Sequence: {:?}", lazy_list);
        let mut list_values = lazy_list.iter();
        assert_eq!(list_values.next().expect("first")?.ion_type(), IonType::Int);
        assert_eq!(
            list_values.next().expect("second")?.ion_type(),
            IonType::Bool
        );
        assert_eq!(
            list_values.next().expect("third")?.ion_type(),
            IonType::Symbol
        );
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
        let mut reader = LazyRawReader::new(data);
        loop {
            match reader.next()? {
                RawStreamItem::VersionMarker(major, minor) => println!("IVM: v{}.{}", major, minor),
                RawStreamItem::Value(value) => println!("{:?}", value.read()?),
                RawStreamItem::EndOfStream => break,
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
        let mut reader = LazyRawReader::new(data);
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

        let mut reader = LazyRawReader::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_null()?,
            IonType::Null
        );

        Ok(())
    }
}
