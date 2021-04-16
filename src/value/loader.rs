// Copyright Amazon.com, Inc. or its affiliates.

use crate::result::IonResult;
use crate::value::owned::{OwnedElement, OwnedStruct, OwnedSymbolToken, OwnedValue};
use crate::value::AnyInt;
use crate::IonType;
use ion_c_sys::reader::{IonCReader, IonCReaderHandle};
use ion_c_sys::ION_TYPE;
use std::convert::{TryFrom, TryInto};
use std::iter::FromIterator;

use super::owned::text_token;

/// TODO add/refactor trait/implementation for borrowing over some context
///      we could make it generic with generic associated types or just have a lifetime
///      scoped implementation

/// Loads Ion data into [`Element`] instances.
///
/// Users of this trait should not assume any particular implementation of `Element`.
/// In the future, [generic associated types (GAT)][gat] and [existential types in traits][et]
/// should make it easier to model this more abstractly.
///
/// [gat]: https://rust-lang.github.io/rfcs/1598-generic_associated_types.html
/// [et]:https://rust-lang.github.io/rfcs/2071-impl-trait-existential-types.html
pub trait Loader {
    /// Parses Ion over a given slice of data and yields each top-level value as
    /// an [`Element`] instance.
    ///
    /// The [`Iterator`] will generally return `Ok([Element])` but on a failure of
    /// parsing it will return an `Err([IonError])` and then a `None` to signal no more
    /// elements.
    ///
    /// This will return an [`IonError`] if the parser could not be initialized over the given
    /// slice.
    fn iterate_over<'a>(
        &'a self,
        data: &'a [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<OwnedElement>> + 'a>>;
}

struct IonCReaderIterator<'a> {
    reader: IonCReaderHandle<'a>,
}

impl<'a> IonCReaderIterator<'a> {
    /// Moves the reader forward converting to `IonResult`.
    #[inline]
    fn read_next(&mut self) -> IonResult<ION_TYPE> {
        Ok(self.reader.next()?)
    }

    /// Materializes a value with an [`IonType`]
    fn materialize(&mut self, ion_type: IonType) -> IonResult<OwnedElement> {
        use OwnedValue::*;
        // TODO when doing BorrowedElement, we can compare against the input buffer if
        //      there is one and be smart about when to materialize strings...

        // TODO deal with local SIDs/sources, this requires deeper integration with Ion C
        //      than we're willing to do right now...

        let annotations: Vec<OwnedSymbolToken> = self
            .reader
            .get_annotations()?
            .into_iter()
            .map(|s| (*s).into())
            .collect();

        let value: OwnedValue = if self.reader.is_null()? {
            Null(ion_type)
        } else {
            match ion_type {
                // technically unreachable...
                IonType::Null => Null(ion_type),
                IonType::Boolean => Boolean(self.reader.read_bool()?),
                IonType::Integer => {
                    Integer(AnyInt::I64(self.reader.read_i64()?));
                    todo!("BigInt")
                }
                IonType::Float => Float(self.reader.read_f64()?),
                IonType::Decimal => Decimal(self.reader.read_bigdecimal()?.into()),
                IonType::Timestamp => Timestamp(self.reader.read_datetime()?.into()),
                IonType::Symbol => todo!(),
                IonType::String => String(self.reader.read_string()?.as_str().into()),
                IonType::Clob => todo!(),
                IonType::Blob => Blob(self.reader.read_bytes()?),
                IonType::List => todo!(),
                IonType::SExpression => todo!(),
                IonType::Struct => Struct(OwnedStruct::from_iter(self.materialize_struct()?)),
            }
        };

        Ok(OwnedElement::new(annotations, value))
    }

    /// Materializes a top-level value with a known Ion C type.
    #[inline]
    fn materialize_top_level(&mut self, ionc_type: ION_TYPE) -> IonResult<OwnedElement> {
        self.materialize(ionc_type.try_into()?)
    }

    fn materialize_struct(&mut self) -> IonResult<Vec<(OwnedSymbolToken, OwnedElement)>> {
        let mut vec = vec![];
        self.reader.step_in()?;
        loop {
            let ionc_type = self.read_next()?;
            if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                break;
            }

            let token = text_token(self.reader.get_field_name()?.as_ref());
            let elem = self.materialize_top_level(ionc_type)?;
            vec.push((token, elem));
        }
        self.reader.step_out()?;
        Ok(vec)
    }
}

impl<'a> Iterator for IonCReaderIterator<'a> {
    type Item = IonResult<OwnedElement>;

    fn next(&mut self) -> Option<Self::Item> {
        // perform scaffolding over the Some/None part of the API
        match self.read_next() {
            Ok(ionc_type) => {
                if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                    // reader says nothing, we're done!
                    None
                } else {
                    // we've got something
                    Some(self.materialize_top_level(ionc_type))
                }
            }
            // next failed...
            Err(e) => Some(Err(e)),
        }
    }
}

struct IonCLoader {}

impl Loader for IonCLoader {
    fn iterate_over<'a>(
        &'a self,
        data: &'a [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<OwnedElement>> + 'a>> {
        let reader = IonCReaderHandle::try_from(data)?;

        Ok(Box::new(IonCReaderIterator { reader }))
    }
}

/// Returns an implementation defined [`Loader`] instance.
pub fn loader() -> impl Loader {
    IonCLoader {}
}

#[cfg(test)]
mod loader_tests {
    use super::*;
    use crate::value::{Element, Struct};

    #[test]
    fn load_em_up() -> IonResult<()> {
        let data = b"{bool_field: true,string_field: \"string\"}";
        let mut all: Vec<_> = loader().iterate_over(data)?.collect();
        assert_eq!(1, all.len());
        let elem = all.pop().unwrap()?;
        let strukt = elem.as_struct().unwrap();
        assert_eq!(true, strukt.get("bool_field").unwrap().as_bool().unwrap());
        assert_eq!(
            "string",
            strukt.get("string_field").unwrap().as_str().unwrap()
        );

        Ok(())
    }
}
