use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;

use crate::lazy::encoder::binary::v1_1::container_writers::{
    BinaryContainerWriter_1_1, BinaryListValuesWriter_1_1, BinaryListWriter_1_1,
    BinarySExpValuesWriter_1_1, BinarySExpWriter_1_1, BinaryStructFieldsWriter_1_1,
    BinaryStructWriter_1_1,
};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::{AnnotatableValueWriter, ValueWriter};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Decimal, Int, IonResult, IonType, SymbolId, Timestamp};

pub struct BinaryValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    encoding_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryValueWriter_1_1<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryValueWriter_1_1<'value, 'top> {
        BinaryValueWriter_1_1 {
            allocator,
            encoding_buffer,
        }
    }

    #[inline]
    fn push_byte(&mut self, byte: u8) {
        self.encoding_buffer.push(byte);
    }

    #[inline]
    fn push_bytes(&mut self, bytes: &[u8]) {
        self.encoding_buffer.extend_from_slice(bytes)
    }

    pub(crate) fn buffer(&self) -> &[u8] {
        self.encoding_buffer.as_slice()
    }

    pub fn write_symbol_id(self, _symbol_id: SymbolId) -> IonResult<()> {
        todo!()
    }

    pub fn write_lob(self, _value: &[u8], _type_code: u8) -> IonResult<()> {
        todo!()
    }

    pub fn write_null(self, _ion_type: IonType) -> IonResult<()> {
        todo!()
    }

    pub fn write_bool(self, _value: bool) -> IonResult<()> {
        todo!()
    }

    pub fn write_i64(self, _value: i64) -> IonResult<()> {
        todo!()
    }

    pub fn write_int(self, _value: &Int) -> IonResult<()> {
        todo!()
    }

    pub fn write_f32(self, _value: f32) -> IonResult<()> {
        todo!()
    }

    pub fn write_f64(self, _value: f64) -> IonResult<()> {
        todo!()
    }

    pub fn write_decimal(self, _value: &Decimal) -> IonResult<()> {
        todo!()
    }

    pub fn write_timestamp(self, _value: &Timestamp) -> IonResult<()> {
        todo!()
    }

    pub fn write_string<A: AsRef<str>>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    pub fn write_symbol<A: AsRawSymbolTokenRef>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    pub fn write_clob<A: AsRef<[u8]>>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    pub fn write_blob<A: AsRef<[u8]>>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    fn list_writer(&mut self) -> BinaryListWriter_1_1<'_, 'top> {
        todo!()
    }

    fn sexp_writer(&mut self) -> IonResult<BinarySExpWriter_1_1<'_, 'top>> {
        todo!()
    }

    fn struct_writer(&mut self) -> IonResult<BinaryStructWriter_1_1<'_, 'top>> {
        const STRUCT_TYPE_CODE: u8 = 0xD0;
        Ok(BinaryStructWriter_1_1::new(BinaryContainerWriter_1_1::new(
            STRUCT_TYPE_CODE,
            self.allocator,
            self.encoding_buffer,
        )))
    }

    fn write_list<
        F: for<'a> FnOnce(&mut <Self as ValueWriter>::ListWriter<'a>) -> IonResult<()>,
    >(
        mut self,
        list_fn: F,
    ) -> IonResult<()> {
        self.list_writer().write_values(list_fn)
    }
    fn write_sexp<
        F: for<'a> FnOnce(&mut <Self as ValueWriter>::SExpWriter<'a>) -> IonResult<()>,
    >(
        mut self,
        sexp_fn: F,
    ) -> IonResult<()> {
        self.sexp_writer()?.write_values(sexp_fn)
    }
    fn write_struct<
        F: for<'a> FnOnce(&mut <Self as ValueWriter>::StructWriter<'a>) -> IonResult<()>,
    >(
        mut self,
        struct_fn: F,
    ) -> IonResult<()> {
        self.struct_writer()?.write_fields(struct_fn)
    }
}

impl<'value, 'top> Sealed for BinaryValueWriter_1_1<'value, 'top> {}

impl<'value, 'top> ValueWriter for BinaryValueWriter_1_1<'value, 'top> {
    type ListWriter<'a> = BinaryListValuesWriter_1_1<'a>;
    type SExpWriter<'a> = BinarySExpValuesWriter_1_1<'a>;
    type StructWriter<'a> = BinaryStructFieldsWriter_1_1<'a>;

    delegate! {
        to self {
            fn write_null(self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(self, value: bool) -> IonResult<()>;
            fn write_i64(self, value: i64) -> IonResult<()>;
            fn write_int(self, value: &Int) -> IonResult<()>;
            fn write_f32(self, value: f32) -> IonResult<()>;
            fn write_f64(self, value: f64) -> IonResult<()>;
            fn write_decimal(self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
            fn write_string(self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_symbol(self, value: impl AsRawSymbolTokenRef) -> IonResult<()>;
            fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
                self,
                list_fn: F,
            ) -> IonResult<()>;
            fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
                self,
                sexp_fn: F,
            ) -> IonResult<()>;
            fn write_struct<
                F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>,
            >(
                self,
                struct_fn: F,
            ) -> IonResult<()>;
        }
    }
}

pub struct BinaryAnnotatableValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    encoding_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryAnnotatableValueWriter_1_1<'value, 'top> {
    pub fn new(
        allocator: &'top BumpAllocator,
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryAnnotatableValueWriter_1_1<'value, 'top> {
        BinaryAnnotatableValueWriter_1_1 {
            allocator,
            encoding_buffer,
        }
    }
}

impl<'value, 'top: 'value> AnnotatableValueWriter
    for BinaryAnnotatableValueWriter_1_1<'value, 'top>
{
    type ValueWriter = BinaryValueWriter_1_1<'value, 'top>;
    type AnnotatedValueWriter<'a, SymbolType: AsRawSymbolTokenRef + 'a> =
    BinaryAnnotationsWrapperWriter_1_1<'a, 'top, SymbolType> where Self: 'a;
    fn with_annotations<'a, SymbolType: AsRawSymbolTokenRef>(
        self,
        annotations: &'a [SymbolType],
    ) -> Self::AnnotatedValueWriter<'a, SymbolType>
    where
        Self: 'a,
    {
        BinaryAnnotationsWrapperWriter_1_1::new(self.allocator, annotations, self.encoding_buffer)
    }

    #[inline(always)]
    fn without_annotations(self) -> BinaryValueWriter_1_1<'value, 'top> {
        BinaryValueWriter_1_1::new(self.allocator, self.encoding_buffer)
    }
}

pub struct BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType: AsRawSymbolTokenRef> {
    annotations: &'value [SymbolType],
    allocator: &'top BumpAllocator,
    output_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef>
    BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    pub fn new(
        allocator: &'top BumpAllocator,
        annotations: &'value [SymbolType],
        encoding_buffer: &'value mut BumpVec<'top, u8>,
    ) -> BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType> {
        BinaryAnnotationsWrapperWriter_1_1 {
            annotations,
            allocator,
            output_buffer: encoding_buffer,
        }
    }
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef>
    BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    fn encode_annotated<F>(self, _encode_value_fn: F) -> IonResult<()>
    where
        F: for<'a> FnOnce(BinaryAnnotatedValueWriter_1_1<'a, 'top>) -> IonResult<()>,
    {
        todo!()
    }

    fn annotate_encoded_value(self, _encoded_value: &[u8]) -> IonResult<()> {
        todo!()
    }

    fn encode_annotations_sequence(&self, _buffer: &'_ mut BumpVec<'_, u8>) -> IonResult<()> {
        todo!()
    }

    fn todo_value_writer_impl(self) -> Self {
        todo!()
    }
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef> Sealed
    for BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    // No methods, precludes implementations outside the crate.
}

impl<'value, 'top, SymbolType: AsRawSymbolTokenRef> ValueWriter
    for BinaryAnnotationsWrapperWriter_1_1<'value, 'top, SymbolType>
{
    type ListWriter<'a> = BinaryListValuesWriter_1_1<'a>;
    type SExpWriter<'a> = BinarySExpValuesWriter_1_1<'a>;
    type StructWriter<'a> = BinaryStructFieldsWriter_1_1<'a>;

    fn write_null(self, _ion_type: IonType) -> IonResult<()> {
        todo!()
    }

    fn write_bool(self, _value: bool) -> IonResult<()> {
        todo!()
    }

    fn write_i64(self, _value: i64) -> IonResult<()> {
        todo!()
    }

    fn write_int(self, _value: &Int) -> IonResult<()> {
        todo!()
    }

    fn write_f32(self, _value: f32) -> IonResult<()> {
        todo!()
    }

    fn write_f64(self, _value: f64) -> IonResult<()> {
        todo!()
    }

    fn write_decimal(self, _value: &Decimal) -> IonResult<()> {
        todo!()
    }

    fn write_timestamp(self, _value: &Timestamp) -> IonResult<()> {
        todo!()
    }

    fn write_string(self, _value: impl AsRef<str>) -> IonResult<()> {
        todo!()
    }

    fn write_symbol(self, _value: impl AsRawSymbolTokenRef) -> IonResult<()> {
        todo!()
    }

    fn write_clob(self, _value: impl AsRef<[u8]>) -> IonResult<()> {
        todo!()
    }

    fn write_blob(self, _value: impl AsRef<[u8]>) -> IonResult<()> {
        todo!()
    }

    fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
        self,
        _list_fn: F,
    ) -> IonResult<()> {
        todo!()
    }

    fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
        self,
        _sexp_fn: F,
    ) -> IonResult<()> {
        todo!()
    }

    fn write_struct<F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>>(
        self,
        _struct_fn: F,
    ) -> IonResult<()> {
        todo!()
    }
}

pub struct BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    allocator: &'top BumpAllocator,
    buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    pub fn new(allocator: &'top BumpAllocator, buffer: &'value mut BumpVec<'top, u8>) -> Self {
        Self { allocator, buffer }
    }
    pub(crate) fn value_writer(&mut self) -> BinaryValueWriter_1_1<'_, 'top> {
        BinaryValueWriter_1_1::new(self.allocator, self.buffer)
    }

    pub(crate) fn buffer(&self) -> &[u8] {
        self.buffer.as_slice()
    }
}

impl<'value, 'top> Sealed for BinaryAnnotatedValueWriter_1_1<'value, 'top> {}

impl<'value, 'top: 'value> ValueWriter for BinaryAnnotatedValueWriter_1_1<'value, 'top> {
    type ListWriter<'a> = BinaryListValuesWriter_1_1<'a>;
    type SExpWriter<'a> = BinarySExpValuesWriter_1_1<'a>;
    type StructWriter<'a> = BinaryStructFieldsWriter_1_1<'a>;
    delegate! {
        to self.value_writer() {
            fn write_null(mut self, ion_type: IonType) -> IonResult<()>;
            fn write_bool(mut self, value: bool) -> IonResult<()>;
            fn write_i64(mut self, value: i64) -> IonResult<()>;
            fn write_int(mut self, value: &Int) -> IonResult<()>;
            fn write_f32(mut self, value: f32) -> IonResult<()>;
            fn write_f64(mut self, value: f64) -> IonResult<()>;
            fn write_decimal(mut self, value: &Decimal) -> IonResult<()>;
            fn write_timestamp(mut self, value: &Timestamp) -> IonResult<()>;
            fn write_string(mut self, value: impl AsRef<str>) -> IonResult<()>;
            fn write_symbol(mut self, value: impl AsRawSymbolTokenRef) -> IonResult<()>;
            fn write_clob(mut self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_blob(mut self, value: impl AsRef<[u8]>) -> IonResult<()>;
            fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
                mut self,
                list_fn: F,
            ) -> IonResult<()>;
            fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
                mut self,
                sexp_fn: F,
            ) -> IonResult<()>;
            fn write_struct<
                F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>,
            >(
                mut self,
                struct_fn: F,
            ) -> IonResult<()>;
        }
    }
}
