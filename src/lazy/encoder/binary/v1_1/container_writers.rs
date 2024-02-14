use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;
use ice_code::ice as cold_path;

use crate::lazy::encoder::binary::v1_1::value_writer::BinaryAnnotatableValueWriter_1_1;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{MacroArgsWriter, SequenceWriter, StructWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{FlexInt, FlexUInt, IonResult, RawSymbolTokenRef, SymbolId};

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_1`],
/// [`BinarySExpWriter_1_1`], and [`BinaryStructWriter_1_1`].
///
/// The [`BinaryContainerWriter_1_1`] does not know which type of container it is writing or whether that container
/// is length-prefixed or delimited. It only encodes provided values to its buffer. The owner of the
/// [`BinaryContainerWriter_1_1`] is responsible for:
///   * writing the correct opcode.
///   * copying the encoded data to the parent buffer (in the case of a length-prefixed container).
///   * writing field names to the [`BinaryContainerWriter_1_1`]'s buffer before each value (in the case of a struct).
pub(crate) struct BinaryContainerWriter_1_1<'value, 'top> {
    // An allocator reference that can be shared with nested container writers
    allocator: &'top BumpAllocator,
    // The buffer to which child values will be encoded. In the case of:
    //   1. a length-prefixed container, this will be a new buffer bump-allocated specifically for this
    //      container.
    //   2. a delimited container, this will be the parent's own encoding buffer, to which the delimited
    //      container start opcode has already been written.
    buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryContainerWriter_1_1<'value, 'top> {
    pub fn new(allocator: &'top BumpAllocator, buffer: &'value mut BumpVec<'top, u8>) -> Self {
        Self { allocator, buffer }
    }

    /// Constructs a new [`BinaryAnnotatableValueWriter_1_1`] using this [`BinaryContainerWriter_1_1`]'s
    /// allocator and targeting its buffer.
    fn value_writer<'a>(&'a mut self) -> BinaryAnnotatableValueWriter_1_1<'a, 'top> {
        BinaryAnnotatableValueWriter_1_1::new(self.allocator, self.buffer())
    }

    /// Encodes the provided `value` to the [`BinaryContainerWriter_1_1`]'s buffer.
    #[inline]
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let annotated_value_writer = self.value_writer();
        value.write_as_ion(annotated_value_writer)?;
        Ok(self)
    }
    pub fn allocator(&self) -> &'top BumpAllocator {
        self.allocator
    }
    pub fn buffer(&mut self) -> &'_ mut BumpVec<'top, u8> {
        self.buffer
    }
}

pub struct BinaryListWriter_1_1<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_1<'value, 'top> {
    pub(crate) fn new(container_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self { container_writer }
    }
}

impl<'value, 'top> MakeValueWriter for BinaryListWriter_1_1<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<'value, 'top> SequenceWriter for BinaryListWriter_1_1<'value, 'top> {
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write(value)?;
        Ok(self)
    }
}

pub struct BinarySExpWriter_1_1<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinarySExpWriter_1_1<'value, 'top> {
    pub(crate) fn new(sequence_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self {
            container_writer: sequence_writer,
        }
    }
}

impl<'value, 'top> MakeValueWriter for BinarySExpWriter_1_1<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_1::new(
            self.container_writer.allocator(),
            self.container_writer.buffer(),
        )
    }
}

impl<'value, 'top> SequenceWriter for BinarySExpWriter_1_1<'value, 'top> {
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write(value)?;
        Ok(self)
    }
}

pub struct BinaryStructWriter_1_1<'value, 'top> {
    // When true, struct field names are encoded as `FlexUInt`s.
    // When false, struct field names are encoded as `FlexSym`s.
    //
    // Always starts as `true`; remains `true` as long as field names being written
    // are symbol IDs. Once a field name with inline text needs to be encoded, switches to `false`.
    flex_uint_encoding: bool,
    container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinaryStructWriter_1_1<'value, 'top> {
    pub(crate) fn new_length_prefixed(
        container_writer: BinaryContainerWriter_1_1<'value, 'top>,
    ) -> Self {
        Self {
            flex_uint_encoding: true,
            container_writer,
        }
    }

    pub(crate) fn new_delimited(container_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self {
            // Delimited structs always use FlexSym encoding.
            flex_uint_encoding: false,
            container_writer,
        }
    }

    pub(crate) fn buffer(&mut self) -> &'_ mut BumpVec<'top, u8> {
        self.container_writer.buffer
    }

    #[inline]
    pub fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: V,
    ) -> IonResult<&mut Self> {
        use RawSymbolTokenRef::*;

        match (self.flex_uint_encoding, name.as_raw_symbol_token_ref()) {
            // We're already in FlexSym encoding mode
            (false, _) => self.write_flex_sym_field(name, value),
            // We're still in FlexUInt encoding mode, but this value requires FlexSym encoding
            (_, Text(_)) | (_, SymbolId(0)) =>
            // This can only happen up to once inside a length-prefixed struct
            {
                self.enable_flex_sym_and_write_field(name, value)
            }
            // We're in FlexUInt encoding mode and can write this field without switching modes
            (_, SymbolId(sid)) => self.write_flex_uint_field(sid, value),
        }
    }

    #[inline]
    fn write_flex_uint_field<V: WriteAsIon>(
        &mut self,
        name: SymbolId,
        value: V,
    ) -> IonResult<&mut Self> {
        FlexUInt::encode_u64(self.buffer(), name as u64);
        self.container_writer.write(value)?;
        Ok(self)
    }

    #[inline(never)]
    fn enable_flex_sym_and_write_field<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: V,
    ) -> IonResult<&mut Self> {
        if self.flex_uint_encoding {
            // This is the first time we're writing a FlexSym field. Emit a FlexUInt 0 to tell
            // readers that we're switching from FlexUInt to FlexSym.
            self.buffer().push(0x01);
            self.flex_uint_encoding = false;
        }
        self.write_flex_sym_field(name, value)
    }

    pub fn write_flex_sym_field<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: V,
    ) -> IonResult<&mut Self> {
        use RawSymbolTokenRef::*;

        // Write the field name
        match name.as_raw_symbol_token_ref() {
            SymbolId(0) => {
                // Encoding `$0` requires a zero byte to indicate an opcode follows,
                // and then opcode 0x90, which indicates symbol ID 0.
                cold_path! {
                    write_symbol_id_zero => self.buffer().extend_from_slice_copy(&[0, 0x90])
                }
            }
            SymbolId(sid) => {
                FlexInt::encode_i64(self.buffer(), sid as i64);
            }
            Text(text_token) => {
                let text = text_token.as_ref();
                let num_bytes = text.len();
                if num_bytes == 0 {
                    // Encoding the empty string requires a zero byte to indicate an opcode follows,
                    // and then opcode 0x80, which indicates a string of length 0.
                    cold_path! {
                        write_empty_string => self.buffer().extend_from_slice_copy(&[0, 0x80])
                    }
                } else {
                    let negated_num_bytes = -(text.len() as i64);
                    FlexInt::encode_i64(self.buffer(), negated_num_bytes);
                    self.buffer().extend_from_slice_copy(text.as_bytes());
                }
            }
        };

        self.container_writer.write(value)?;
        Ok(self)
    }
}

impl<'value, 'top> StructWriter for BinaryStructWriter_1_1<'value, 'top> {
    delegate! {
        to self {
            fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
                &mut self,
                name: A,
                value: V,
            ) -> IonResult<&mut Self>;
        }
    }
}

pub struct BinaryMacroArgsWriter_1_1<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> MakeValueWriter for BinaryMacroArgsWriter_1_1<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<'value, 'top> SequenceWriter for BinaryMacroArgsWriter_1_1<'value, 'top> {}

impl<'value, 'top> MacroArgsWriter for BinaryMacroArgsWriter_1_1<'value, 'top> {}
