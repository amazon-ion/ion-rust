// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`](super::Element) into common targets
//! such as byte buffers or files.

use super::Element;
use crate::result::IonResult;

#[cfg(feature = "ion_c")]
use crate::value::ion_c_writer::{IonCSliceElementWriter, SliceElementWriter};

pub use Format::*;
pub use TextKind::*;

/// Serializes [`Element`] instances into some kind of output sink.
pub trait ElementWriter {
    /// The output of the writer when finishing, it could be a managed buffer,
    /// some concept of a stream, metadata about a file, or something appropriate
    /// for the destination.
    type Output;

    /// Serializes a single [`Element`] as a top-level value.
    fn write<E: Element>(&mut self, element: &E) -> IonResult<()>;

    /// Serializes a collection of [`Element`] as a series of top-level values.
    ///
    /// This will return [`Err`] if writing any element causes a failure.
    fn write_all<'a, E: Element + 'a, I: IntoIterator<Item = &'a E>>(
        &'a mut self,
        elements: I,
    ) -> IonResult<()> {
        for element in elements.into_iter() {
            self.write(element)?;
        }
        Ok(())
    }

    /// Consumes this [`ElementWriter`] flushing/finishing/closing it and returns
    /// the underlying output sink.
    ///
    /// If a previous write operation returned [`Err`], this method should also return [`Err`].
    fn finish(self) -> IonResult<Self::Output>;
}

/// Whether or not the text is pretty printed or serialized in a more compact representation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TextKind {
    Compact,
    Pretty,
}

/// Basic configuration options for [`ElementWriter`] instances.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Format {
    Text(TextKind),
    Binary,
    // TODO a mode for Json(TextKind)
}

impl Format {
    // TODO some APIs to make the building more "fluent"

    // TODO eliminate limitation around reading only from slices

    /// Creates a [`ElementWriter`] for the format over a slice.
    ///
    /// Returns [`Err`] if the [`ElementWriter`] cannot be constructed.
    #[cfg(feature = "ion_c")]
    pub fn element_writer_for_slice(self, slice: &mut [u8]) -> IonResult<SliceElementWriter> {
        IonCSliceElementWriter::new(slice, self)
    }

    // TODO into files, cursors, or other such things
}

#[cfg(all(test, feature = "ion_c"))]
mod writer_tests {
    use super::*;
    use crate::result::IonResult;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::value::borrowed::BorrowedElement;
    use crate::value::owned::OwnedElement;
    use crate::value::Builder;
    use crate::value::SymbolToken;
    use crate::IonType;
    use rstest::*;
    use std::str::from_utf8;

    #[inline]
    fn to_utf8(slice: &[u8]) -> &str {
        from_utf8(slice).unwrap_or("<INVALID UTF-8>")
    }

    #[inline]
    fn ion_binary(data: &[u8]) -> Vec<u8> {
        let mut buf = vec![0xE0, 0x01, 0x00, 0xEA];
        buf.extend_from_slice(data);
        buf
    }

    // fixed buffer length to serialize to
    const TEST_BUF_LEN: usize = 4 * 1024 * 1024;

    // these are reasonably basic unit tests to verify the basics of direct encoding (byte-for-byte)
    // we're going to lean a lot more on the test vector round-tripping to get more coverage
    // but those won't expect particular encodings and this can make sure some basic sanity
    // of element writer is doing what is intended (e.g. text mode outputting binary, or pretty not
    // generating pretty output)

    struct TestCase<E: Element> {
        // element to write
        element: E,
        // binary to expect
        binary: Vec<u8>,
        // text to expect
        text: &'static [u8],
        // pretty text to expect
        pretty: &'static [u8],
    }

    fn null_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_null(IonType::Integer),
            binary: ion_binary(&[0x2F]),
            text: b"null.int",
            pretty: b"null.int",
        }
    }

    fn bool_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_bool(true),
            binary: ion_binary(&[0x11]),
            text: b"true",
            pretty: b"true",
        }
    }

    fn int_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_i64(5),
            binary: ion_binary(&[0x21, 0x05]),
            text: b"5",
            pretty: b"5",
        }
    }

    fn float_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_f64(-1.0),
            binary: ion_binary(&[0x48, 0xBF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
            text: b"-1e+0",
            pretty: b"-1e+0",
        }
    }

    fn decimal_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_decimal(Decimal::new(16, -1)),
            binary: ion_binary(&[0x52, 0xC1, 0x10]),
            text: b"1.6",
            pretty: b"1.6",
        }
    }

    fn timestamp_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_timestamp(Timestamp::with_year(2007).build().unwrap()),
            binary: ion_binary(&[0x63, 0xC0, 0x0F, 0xD7]),
            text: b"2007T",
            pretty: b"2007T",
        }
    }

    fn symbol_case<E: Element>() -> TestCase<E> {
        TestCase {
            // note that 'name' is in the system symbol table so should not emit LST
            element: E::Builder::new_symbol(E::SymbolToken::text_token("name")),
            binary: ion_binary(&[0x71, 0x04]),
            text: b"name",
            pretty: b"name",
        }
    }

    fn string_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_string("hello"),
            binary: ion_binary(b"\x85hello"),
            text: br#""hello""#,
            pretty: br#""hello""#,
        }
    }

    fn clob_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_clob(b"moon"),
            binary: ion_binary(b"\x94moon"),
            text: br#"{{"moon"}}"#,
            pretty: br#"{{"moon"}}"#,
        }
    }

    fn blob_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_blob(b"earth"),
            binary: ion_binary(b"\xA5earth"),
            text: b"{{ZWFydGg=}}",
            pretty: b"{{ZWFydGg=}}",
        }
    }

    fn list_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_list(vec![E::Builder::new_list(
                vec![1, 2, 3].into_iter().map(E::Builder::new_i64),
            )]),
            binary: ion_binary(&[0xB7, 0xB6, 0x21, 0x01, 0x21, 0x02, 0x21, 0x03]),
            text: b"[[1,2,3]]",
            pretty: b"\
[
  [
    1,
    2,
    3
  ]
]",
        }
    }

    fn sexp_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_sexp(vec![
                E::Builder::new_symbol(E::SymbolToken::text_token("name")),
                E::Builder::new_sexp(vec!["a", "b", "c"].into_iter().map(E::Builder::new_string)),
            ]),
            binary: ion_binary(&[0xC9, 0x71, 0x04, 0xC6, 0x81, 0x61, 0x81, 0x62, 0x81, 0x63]),
            text: br#"(name ("a" "b" "c"))"#,
            pretty: b"\
(
  name
  (
    \"a\"
    \"b\"
    \"c\"
  )
)",
        }
    }

    fn struct_case<E: Element>() -> TestCase<E> {
        TestCase {
            element: E::Builder::new_struct(
                vec![("name", 1)]
                    .into_iter()
                    .map(|(k, v)| (E::SymbolToken::text_token(k), E::Builder::new_i64(v))),
            ),
            binary: ion_binary(&[0xD3, 0x84, 0x21, 0x01]),
            text: b"{name:1}",
            pretty: b"\
{
  name: 1
}",
        }
    }

    #[rstest]
    #[case::borrowed_null(null_case::<BorrowedElement>())]
    #[case::owned_null(null_case::<OwnedElement>())]
    #[case::borrowed_bool(bool_case::<BorrowedElement>())]
    #[case::owned_bool(bool_case::<OwnedElement>())]
    #[case::borrowed_int(int_case::<BorrowedElement>())]
    #[case::owned_int(int_case::<OwnedElement>())]
    #[case::borrowed_float(float_case::<BorrowedElement>())]
    #[case::owned_float(float_case::<OwnedElement>())]
    #[case::borrowed_decimal(decimal_case::<BorrowedElement>())]
    #[case::owned_decimal(decimal_case::<OwnedElement>())]
    #[case::borrowed_timestamp(timestamp_case::<BorrowedElement>())]
    #[case::owned_timestamp(timestamp_case::<OwnedElement>())]
    #[case::borrowed_symbol(symbol_case::<BorrowedElement>())]
    #[case::owned_symbol(symbol_case::<OwnedElement>())]
    #[case::borrowed_string(string_case::<BorrowedElement>())]
    #[case::owned_string(string_case::<OwnedElement>())]
    #[case::borrowed_clob(clob_case::<BorrowedElement>())]
    #[case::owned_clob(clob_case::<OwnedElement>())]
    #[case::borrowed_blob(blob_case::<BorrowedElement>())]
    #[case::owned_blob(blob_case::<OwnedElement>())]
    #[case::borrowed_list(list_case::<BorrowedElement>())]
    #[case::owned_list(list_case::<OwnedElement>())]
    #[case::borrowed_sexp(sexp_case::<BorrowedElement>())]
    #[case::owned_sexp(sexp_case::<OwnedElement>())]
    #[case::borrowed_struct(struct_case::<BorrowedElement>())]
    #[case::owned_struct(struct_case::<OwnedElement>())]
    fn simple<E: Element>(#[case] test_case: TestCase<E>) -> IonResult<()> {
        assert_write(&test_case.binary[..], &test_case.element, |buf| {
            Binary.element_writer_for_slice(buf)
        })?;

        assert_write(test_case.text, &test_case.element, |buf| {
            Text(Compact).element_writer_for_slice(buf)
        })?;

        assert_write(test_case.pretty, &test_case.element, |buf| {
            Text(Pretty).element_writer_for_slice(buf)
        })?;
        Ok(())
    }

    fn assert_write<E, F>(expected: &[u8], element: &E, make_writer: F) -> IonResult<()>
    where
        E: Element,
        // XXX note that this generic trait bounds requires something like GAT to make it
        //     work on `ElementWriter<Output = &'? [u8]` correctly and is the reason this is exposed
        F: FnOnce(&mut [u8]) -> IonResult<SliceElementWriter>,
    {
        let mut buf = vec![0u8; TEST_BUF_LEN];
        let mut writer = make_writer(&mut buf)?;
        writer.write(element)?;
        let output = writer.finish()?;
        assert_eq!(
            expected,
            output,
            "{} != {}",
            to_utf8(expected),
            to_utf8(output),
        );
        Ok(())
    }
}
