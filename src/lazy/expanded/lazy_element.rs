use crate::{
    AnyEncoding, Decoder, Element, EncodingContext, ExpandedValueSource, IonError,
    LazyExpandedValue, LazyValue,
};
use std::mem;

pub struct LazyElement<Encoding: Decoder = AnyEncoding> {
    context: EncodingContext,
    // A normal `ExpandedValueSource` but with its lifetime erased.
    // All references in the ExpandedValueSource point to heap data owned by the
    // `EncodingContext` above, and so will be valid as long as this `LazyElement` is alive.
    source: ExpandedValueSource<'static, Encoding>,
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    pub(crate) fn new(context: EncodingContext, source: ExpandedValueSource<'_, Encoding>) -> Self {
        // Erase the lifetime.
        let static_source: ExpandedValueSource<'static, Encoding> =
            unsafe { std::mem::transmute(source) };
        Self {
            context,
            source: static_source,
        }
    }

    pub(crate) fn as_lazy_value<'top>(&'top self) -> LazyValue<'top, Encoding> {
        // SAFETY: Because the EncodingContext's data is reference counted, is guaranteed to live as `self`.
        //         This means we can hand out data that depends on it with a shorter lifetime.
        let expanded: LazyExpandedValue<'top, Encoding> = LazyExpandedValue {
            context: self.context.get_ref(),
            source: unsafe { mem::transmute(self.source) },
            variable: None,
        };
        LazyValue::new(expanded)
    }
}

impl<'top, Encoding: Decoder> From<LazyValue<'top, Encoding>> for LazyElement<Encoding> {
    fn from(value: LazyValue<'top, Encoding>) -> Self {
        value.to_owned()
    }
}

impl<'top, Encoding: Decoder> TryFrom<LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value().try_into()
    }
}

impl<'top, Encoding: Decoder> TryFrom<&LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: &LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value().try_into()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::{AnyEncoding, Element, IonResult, Reader, Sequence};
    use std::sync::LazyLock;

    const NUM_STRUCTS: usize = 1_000_000;
    static TEST_DATA: LazyLock<String> = LazyLock::new(|| test_data());

    fn test_data() -> String {
        let test_data = r#"
            $ion_1_1

            // === Values backed by `ExpandedValueSource::ValueLiteral` ===
            foo
            true
            baz::5
            [(), {}, ()]
            2025T
            "Hello"

            // === Macro output backed by `ExpandedValueSource::ValueLiteral` ===
            (:values 1 2 3)

             (:add_macros
                (macro foo () 'singleton value')
                (macro greet (name) (.make_string "Hello, " (%name))))

             // === Produces a value backed by an `ExpandedValueSource::SingletonEExp` ===
             (:foo)

             // === Produces a value backed by an `ExpandedValueSource::Constructed` ===
             (:greet "Alice")
         "#;
        test_data.to_owned()
    }

    fn lazy_element_test<TestFn>(test: TestFn) -> IonResult<()>
    where
        TestFn: FnOnce(Sequence, &mut dyn Iterator<Item = IonResult<LazyElement>>) -> IonResult<()>,
    {
        let test_data = test_data();
        let expected = Element::read_all(&test_data)?;
        let mut reader = Reader::new(AnyEncoding, &test_data)?;
        test(expected, &mut reader)
    }

    #[test]
    fn equivalent_to_lazy_value_when_reading_forward() -> IonResult<()> {
        lazy_element_test(|expected, lazy_elements| {
            // Fully read each LazyElement as it's encountered and compare it to the corresponding
            // expected element. Only one LazyElement exists at a time.
            let actual = lazy_elements
                .map(|result| result.and_then(Element::try_from))
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.iter().eq(&actual));
            Ok(())
        })
    }

    #[test]
    fn equivalent_to_lazy_value_when_read_backward() -> IonResult<()> {
        lazy_element_test(|expected, lazy_elements| {
            // Store the LazyElements in a Vec without reading them.
            let mut lazy_elements_vec = lazy_elements.collect::<IonResult<Vec<LazyElement>>>()?;
            // Read the collected LazyElements in reverse order and store them in another Vec,
            // demonstrating that it's safe/correct to read them in an order that differs from their
            // order in the input stream.
            let actual = lazy_elements_vec
                .iter()
                .rev()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.into_iter().rev().eq(actual));
            Ok(())
        })
    }

    #[test]
    fn values_survive_after_reader_drops() -> IonResult<()> {
        let mut reader = Reader::new(AnyEncoding, "foo")?;
        let lazy_element = reader.expect_next()?.to_owned();
        drop(reader);
        assert_eq!(Element::symbol("foo"), Element::try_from(lazy_element)?);
        Ok(())
    }
}
