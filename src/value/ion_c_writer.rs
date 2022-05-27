use crate::result::illegal_operation;
use crate::value::writer::{Binary, Compact, ElementWriter, Format, Pretty, Text};
use crate::value::{Element, Sequence, Struct, SymbolToken};
use crate::{Integer, IonError, IonResult, IonType};
use ion_c_sys::writer::{IonCValueWriter, IonCWriter, IonCWriterHandle};
use ion_c_sys::ION_WRITER_OPTIONS;

pub type SliceElementWriter<'a> = IonCSliceElementWriter<'a>;

impl<'a> IonCSliceElementWriter<'a> {
    pub(crate) fn new(buf: &'a mut [u8], format: Format) -> IonResult<Self> {
        let data = buf.as_ptr();
        let mut options: ION_WRITER_OPTIONS = Default::default();
        match format {
            Text(kind) => {
                options.output_as_binary = 0;
                match kind {
                    Compact => options.pretty_print = 0,
                    Pretty => options.pretty_print = 1,
                };
            }
            Binary => {
                options.output_as_binary = 1;
            }
        };
        let writer = IonCWriterHandle::new_buf(buf, &mut options)?;
        Ok(Self {
            data,
            writer,
            error: None,
        })
    }

    /// Writes an element with an optional field name context (if being written recursively).
    /// This cannot be made generic due to the lack of GAT making it impossible for IonC's
    /// writer to push down the context--it could be written in terms of
    /// `IonCAnnotationsFieldWriterContext` but that would just complicate the code to work around
    /// the lack of GAT.
    pub(crate) fn write_element<E: Element>(
        &mut self,
        field_name_opt: Option<&str>,
        element: &E,
    ) -> IonResult<()> {
        let annotations_opt: Option<Vec<_>> = element.annotations().map(|tok| tok.text()).collect();
        if let Some(annotations) = annotations_opt {
            // get a writing context with the annotations (which could be empty)
            let mut af_writer = self.writer.annotations(&annotations);
            if let Some(field_name) = field_name_opt {
                // decorate the annotation context with the field name when we have one
                af_writer.field(field_name);
            }

            let ion_type = element.ion_type();
            if element.is_null() {
                af_writer.write_null(ion_type.into())?;
            } else {
                // non-null element values
                match ion_type {
                    IonType::Null => {
                        // handled in the null-arm
                    }
                    IonType::Boolean => {
                        af_writer.write_bool(try_to!(element.as_bool()))?;
                    }
                    IonType::Integer => {
                        let any_int = try_to!(element.as_integer());
                        match any_int {
                            Integer::I64(i64_val) => {
                                af_writer.write_i64(*i64_val)?;
                            }
                            Integer::BigInt(big_val) => {
                                af_writer.write_bigint(big_val)?;
                            }
                        }
                    }
                    IonType::Float => {
                        af_writer.write_f64(try_to!(element.as_f64()))?;
                    }
                    IonType::Decimal => {
                        // TODO reconsider Decimal/BigDecimal internal factoring to avoid the clone
                        let decimal = try_to!(element.as_decimal());
                        let big_decimal = decimal.clone().try_into()?;
                        af_writer.write_bigdecimal(&big_decimal)?;
                    }
                    IonType::Timestamp => {
                        // TODO reconsider Timestamp/IonDateTime factoring to avoid the clone
                        let timestamp = try_to!(element.as_timestamp());
                        let ion_dt = timestamp.clone().try_into()?;
                        af_writer.write_datetime(&ion_dt)?;
                    }
                    IonType::Symbol => {
                        af_writer.write_symbol(try_to!(element.as_str()))?;
                    }
                    IonType::String => {
                        af_writer.write_string(try_to!(element.as_str()))?;
                    }
                    IonType::Clob => {
                        af_writer.write_clob(try_to!(element.as_bytes()))?;
                    }
                    IonType::Blob => {
                        af_writer.write_blob(try_to!(element.as_bytes()))?;
                    }
                    IonType::List | IonType::SExpression => {
                        af_writer.start_container(ion_type.into())?;
                        {
                            let seq = try_to!(element.as_sequence());
                            for child in seq.iter() {
                                self.write(child)?;
                            }
                        }
                        self.writer.finish_container()?;
                    }
                    IonType::Struct => {
                        af_writer.start_container(ion_type.into())?;
                        {
                            let structure = try_to!(element.as_struct());
                            for (field_name_token, child) in structure.iter() {
                                let field_name = try_to!(field_name_token.text());
                                self.write_element(Some(field_name), child)?;
                            }
                        }
                        self.writer.finish_container()?;
                    }
                }
            }
            Ok(())
        } else {
            illegal_operation(format!(
                "Could not serialize annotation(s) with no text: {:?}",
                element
            ))
        }
    }
}

impl<'a> ElementWriter for IonCSliceElementWriter<'a> {
    type Output = &'a [u8];

    #[inline]
    fn write<E: Element>(&mut self, element: &E) -> IonResult<()> {
        self.write_element(None, element)
    }

    fn finish(self) -> IonResult<Self::Output> {
        if let Some(error) = self.error {
            return Err(error);
        }

        // close out the writer and get the written length
        let data = self.data;
        let len = {
            // consume the writer so that we drop it at the end
            let mut writer = self.writer;
            writer.finish()?
        };

        // at this point we can make a slice reference bound to the lifetime parameter
        // because the writer is no longer borrowing it implicitly (and has been dropped)
        let output = unsafe { std::slice::from_raw_parts(data, len) };
        Ok(output)
    }
}

/// Implementation of a [`ElementWriter`] to a slice.
///
/// Note that users should not take a dependency on this type name--it is exposed
/// because an opaque type makes using this with the associated lifetimes of the
/// output difficult.  A type alias [`SliceElementWriter`] is a better reference for this
/// would be opaque type.
pub struct IonCSliceElementWriter<'a> {
    /// Raw pointer to the slice we write to--this is borrowed by the Ion C writer
    /// opaquely, so we retain it such that we can return the written data as a
    /// slice reference in `finish`.
    data: *const u8,
    writer: IonCWriterHandle<'a>,
    error: Option<IonError>,
}
