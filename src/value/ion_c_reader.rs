use crate::result::IonResult;
use crate::value::owned::{text_token, OwnedElement, OwnedSequence, OwnedStruct};
use crate::value::reader::ElementReader;
use crate::IonType;
use ion_c_sys::reader::{IonCReader, IonCReaderHandle};
use ion_c_sys::ION_TYPE;

struct IonCReaderIterator<'a> {
    reader: IonCReaderHandle<'a>,
    done: bool,
}

impl<'a> IonCReaderIterator<'a> {
    /// Moves the reader forward converting to `IonResult`.
    #[inline]
    fn read_next(&mut self) -> IonResult<ION_TYPE> {
        Ok(self.reader.next()?)
    }

    /// Materializes a value with an [`IonType`]
    fn materialize(&mut self, ion_type: IonType) -> IonResult<OwnedElement> {
        use crate::types::integer::Integer;
        use crate::value::owned::OwnedValue::*;
        use crate::value::owned::{OwnedSymbolToken, OwnedValue};
        // TODO when doing BorrowedElement, we can compare against the input buffer if
        //      there is one and be smart about when to materialize strings...

        // TODO deal with local SIDs/sources, this requires deeper integration with Ion C
        //      than we're willing to do right now...

        let annotations: Vec<OwnedSymbolToken> = self
            .reader
            .get_annotations()?
            .iter()
            .map(|s| (*s).into())
            .collect();

        let value: OwnedValue = if self.reader.is_null()? {
            Null(ion_type)
        } else {
            match ion_type {
                // technically unreachable...
                IonType::Null => Null(ion_type),
                IonType::Boolean => Boolean(self.reader.read_bool()?),
                // TODO deal with the big integer case
                IonType::Integer => Integer(if let Ok(ival) = self.reader.read_i64() {
                    Integer::I64(ival)
                } else {
                    Integer::BigInt(self.reader.read_bigint()?)
                }),
                IonType::Float => Float(self.reader.read_f64()?),
                IonType::Decimal => Decimal(self.reader.read_bigdecimal()?.into()),
                IonType::Timestamp => Timestamp(self.reader.read_datetime()?.into()),
                // TODO get the `ION_SYMBOL` value and extract the complete symbolic information.
                IonType::Symbol => Symbol(self.reader.read_string()?.as_str().into()),
                IonType::String => String(self.reader.read_string()?.as_str().into()),
                IonType::Clob => Clob(self.reader.read_bytes()?),
                IonType::Blob => Blob(self.reader.read_bytes()?),
                IonType::List => List(self.materialize_sequence()?),
                IonType::SExpression => SExpression(self.materialize_sequence()?),
                IonType::Struct => Struct(self.materialize_struct()?),
            }
        };

        Ok(OwnedElement::new(annotations, value))
    }

    /// Materializes a top-level value with a known Ion C type.
    #[inline]
    fn materialize_top_level(&mut self, ionc_type: ION_TYPE) -> IonResult<OwnedElement> {
        self.materialize(ionc_type.try_into()?)
    }

    fn materialize_sequence(&mut self) -> IonResult<OwnedSequence> {
        let mut children = Vec::new();
        self.reader.step_in()?;
        loop {
            let ionc_type = self.read_next()?;
            if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                break;
            }

            children.push(self.materialize_top_level(ionc_type)?);
        }
        self.reader.step_out()?;
        Ok(children.into_iter().collect())
    }

    fn materialize_struct(&mut self) -> IonResult<OwnedStruct> {
        let mut fields = vec![];
        self.reader.step_in()?;
        loop {
            let ionc_type = self.read_next()?;
            if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                break;
            }

            // TODO get the `ION_SYMBOL` value and extract the complete symbolic information.
            let token = text_token(self.reader.get_field_name()?.as_str());
            let elem = self.materialize_top_level(ionc_type)?;
            fields.push((token, elem));
        }
        self.reader.step_out()?;
        Ok(fields.into_iter().collect())
    }
}

impl<'a> Iterator for IonCReaderIterator<'a> {
    type Item = IonResult<OwnedElement>;

    fn next(&mut self) -> Option<Self::Item> {
        // if we previously returned an error, we're done
        if self.done {
            return None;
        }
        // perform scaffolding over the Some/None part of the API
        match self.read_next() {
            Ok(ionc_type) => {
                if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                    // reader says nothing, we're done!
                    self.done = true;
                    None
                } else {
                    // we've got something
                    let result = self.materialize_top_level(ionc_type);
                    if result.is_err() {
                        // a failure means the iterator is done
                        self.done = true;
                    }
                    Some(result)
                }
            }
            // next failed...
            Err(e) => Some(Err(e)),
        }
    }
}

pub struct IonCElementReader;

impl ElementReader for IonCElementReader {
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<OwnedElement>> + 'b>> {
        let reader = IonCReaderHandle::try_from(data)?;

        Ok(Box::new(IonCReaderIterator {
            reader,
            done: false,
        }))
    }
}

#[cfg(test)]
mod ion_c_reader_tests {
    use super::*;
    use crate::value::reader::ion_c_element_reader;
    use ion_c_sys::result::{IonCError, Position};
    use ion_c_sys::{
        ion_error_code_IERR_INVALID_BINARY, ion_error_code_IERR_INVALID_STATE,
        ion_error_code_IERR_NULL_VALUE,
    };
    use rstest::*;

    #[rstest]
    #[case::unknown_local_symbol(
    br#"
            $ion_1_0
            $ion_symbol_table::{
                symbols:[null]
            }
            $10
        "#,
    vec![
    Err(IonCError::from(ion_error_code_IERR_NULL_VALUE)
    .with_position(Position::text(124, 4, 8))
    .into())
    ]
    )]
    #[case::unknown_shared_symbol_field_name(
    br#"
            $ion_1_0
            $ion_symbol_table::{
                imports:[{name: "my_table", version: 1, max_id: 100}]
            }
            {$10:5}
        "#,
    vec![
    Err(IonCError::from(ion_error_code_IERR_NULL_VALUE)
    .with_position(Position::text(157, 1, 5))
    .into())
    ]
    )]
    #[case::illegal_negative_zero_int(
    &[0xE0, 0x01, 0x00, 0xEA, 0x30],
    vec![
    Err(IonCError::from(ion_error_code_IERR_INVALID_BINARY)
    .with_position(Position::binary(5))
    .into())
    ]
    )]
    #[case::illegal_fcode(
    &[0xE0, 0x01, 0x00, 0xEA, 0xF0],
    vec![
    Err(IonCError::from(ion_error_code_IERR_INVALID_STATE)
    .with_position(Position::binary(5))
    .into())
    ]
    )]
    /// Like read_and_compare, but against results (which makes it easier to test for errors).
    fn read_and_expect(
        #[case] input: &[u8],
        #[case] expected: Vec<IonResult<OwnedElement>>,
    ) -> IonResult<()> {
        let actual: Vec<_> = ion_c_element_reader().iterate_over(input)?.collect();
        assert_eq!(expected, actual);
        Ok(())
    }
}
