use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::value::AnnotationsIterator;
use crate::{
    AnyEncoding, Decoder, Element, EncodingContext, ExpandedValueSource, IonError, IonResult,
    IonType, LazyExpandedValue, LazyValue, ValueRef,
};
use delegate::delegate;
use std::mem;
use std::ops::Deref;

/// A (`LazyValue`, `Resource`) pair, in which the `Resource` is a value that depends on
/// the `LazyValue`.
///
/// `LazyElement` implements many of its methods by first converting itself to a `LazyValue`
/// with a fixed lifetime and then delegating the method call to the `LazyValue`. However,
/// this means that the result of that method call may be borrowed from the `LazyValue`.
///
/// In order to offer an ergonomic API that does not require callers to manually convert the
/// `LazyElement` to a `LazyValue`, `LazyElement` methods return a `LazyResource`.
///
/// `LazyResource` implements `Deref`, allowing the inner `Resource`'s methods to be invoked
/// directly.
///
/// See [`LazyElement::read`] for an example.
pub struct LazyResource<'a, Encoding: Decoder, Resource> {
    value: LazyValue<'a, Encoding>,
    resource: Resource,
}

impl<Encoding: Decoder, Resource> Deref for LazyResource<'_, Encoding, Resource> {
    type Target = Resource;

    fn deref(&self) -> &Self::Target {
        &self.resource
    }
}

/// A (potentially annotated) value in an Ion data stream.
///
/// Unlike an [`Element`], a `LazyElement` does not eagerly read the value's contents or materialize
/// its data, making it comparatively lightweight.
///
/// Unlike a [`LazyValue`], a `LazyElement` shares ownership of its backing resources with the `Reader`.
/// This requires a small amount of bookkeeping overhead, but eliminates the need for lifetimes.
/// `LazyElement` instances can be stored indefinitely and read any number of times.
/// Note, however, that storing `LazyElement`s will also prevent their backing resources from being freed.
pub struct LazyElement<Encoding: Decoder = AnyEncoding> {
    // Reference-counted resources for (eventually) reading the value.
    context: EncodingContext,
    // A normal `ExpandedValueSource` but with its lifetime erased.
    // All references in the ExpandedValueSource point to heap data owned by the
    // `EncodingContext` above, and so will be valid as long as this `LazyElement` is alive.
    source: ExpandedValueSource<'static, Encoding>,
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    /// SAFETY: The caller MUST guarantee that `source` only holds references to heap data owned
    ///         by `context`.
    pub(crate) unsafe fn new(
        context: EncodingContext,
        source: ExpandedValueSource<'_, Encoding>,
    ) -> Self {
        // SAFETY:
        //
        // Because
        //   1. the caller has confirmed that `source` only refers to heap data owned by `context`
        //     AND
        //   2. we save `context` alongside `source`
        // we can safely erase source's lifetime.
        //
        // Anything external to this `LazyElement` to acquires a reference to its contents will
        // go through one of the accessor methods that cause the compiler to recognize that `LazyElement`
        // is borrowed and cannot safely be dropped.
        let static_source: ExpandedValueSource<'static, Encoding> =
            unsafe { mem::transmute(source) };
        Self {
            context,
            source: static_source,
        }
    }

    pub(crate) fn as_lazy_value<'top>(&'top self) -> LazyValue<'top, Encoding> {
        let expanded: LazyExpandedValue<'top, Encoding> = LazyExpandedValue {
            context: self.context.get_ref(),
            // SAFETY: Here we're shortening the `source`'s `'static` lifetime to this method's.
            //         `LazyValue`s are immutable, so handing out a shorter lifetime is not a problem.
            source: unsafe {
                mem::transmute::<
                    ExpandedValueSource<'static, Encoding>,
                    ExpandedValueSource<'top, Encoding>,
                >(self.source)
            },
            // TODO: Preserve variable provenance.
            variable: None,
        };
        LazyValue::new(expanded)
    }
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    // These methods do not return a value with a lifetime and so can use simple delegation.
    delegate! {
        to self.as_lazy_value() {
            pub fn ion_type(&self) -> IonType;
            pub fn is_null(&self) -> bool;
            pub fn is_container(&self) -> bool;
            pub fn is_scalar(&self) -> bool;
            pub fn has_annotations(&self) -> bool;
        }
    }

    // The methods below return values with a lifetime. As such, we need to wrap the
    // return value in a `LazyResource`. This allows the (otherwise temporary) `LazyValue` that
    // the return value depends on to continue living for the same duration as the return value itself.

    /// Reads the value portion of this `LazyElement`.
    pub fn read(&self) -> IonResult<LazyResource<'_, Encoding, ValueRef<'_, Encoding>>> {
        let value = self.as_lazy_value();
        let resource = value.read()?;

        Ok(LazyResource { value, resource })
    }

    /// Returns an iterator over the annotations on this `LazyElement`.
    pub fn annotations(
        &self,
    ) -> IonResult<LazyResource<'_, Encoding, AnnotationsIterator<'_, Encoding>>> {
        let value = self.as_lazy_value();
        let resource = value.annotations();

        Ok(LazyResource { value, resource })
    }

    /// Returns the encoding context that this `LazyElement` uses to read its data.
    pub(crate) fn context(&self) -> LazyResource<'_, Encoding, EncodingContextRef<'_>> {
        let value = self.as_lazy_value();
        let resource = value.context();

        LazyResource { value, resource }
    }
}

impl<'top, Encoding: Decoder> From<LazyValue<'top, Encoding>> for LazyElement<Encoding> {
    fn from(value: LazyValue<'top, Encoding>) -> Self {
        value.to_owned()
    }
}

impl<Encoding: Decoder> TryFrom<LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value().try_into()
    }
}

impl<Encoding: Decoder> TryFrom<&LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: &LazyElement<Encoding>) -> Result<Self, Self::Error> {
        lazy_element.as_lazy_value().try_into()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::lazy::reader::IonResultIterExt;
    use crate::{AnyEncoding, Element, IonResult, IonType, Reader, Sequence};
    use std::sync::LazyLock;

    const NUM_STRUCTS: usize = 1_000_000;
    static TEST_DATA: LazyLock<String> = LazyLock::new(test_data);

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

    /// Reads the output of `test_data()` twice, once using the `Element` API and again using
    /// the `LazyElement` API. The output is passed to `TestFn` to make assertions.
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
        lazy_element_test(|expected, reader| {
            // Fully read each LazyElement as it's encountered and compare it to the corresponding
            // expected element. Only one LazyElement exists at a time.
            let actual = reader
                .map(|result| result.and_then(Element::try_from))
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.iter().eq(&actual));
            Ok(())
        })
    }

    #[test]
    fn equivalent_to_lazy_value_when_read_backward() -> IonResult<()> {
        lazy_element_test(|expected, reader| {
            // Store the LazyElements in a Vec without reading them.
            let lazy_elements_vec = reader.collect::<IonResult<Vec<LazyElement>>>()?;
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
        // Even though we have a `LazyElement`, we can safely drop the `Reader`.
        drop(reader);
        // The `LazyElement` is still valid/usable.
        assert_eq!(Element::symbol("foo"), Element::try_from(lazy_element)?);
        Ok(())
    }

    #[test]
    fn demonstrate_try_filter_and_try_map() -> IonResult<()> {
        let mut reader = Reader::new(AnyEncoding, r#"1 2 3 4 5 6 7 8 9 10"#)?;
        let evens: IonResult<Vec<i64>> = reader
            .try_filter(|element| Ok(element.ion_type() == IonType::Int))
            .try_map(|element| element.read()?.expect_i64())
            .try_filter(|i| Ok(i % 2 == 0))
            .collect();
        drop(reader);
        assert_eq!(vec![2, 4, 6, 8, 10], evens?);
        Ok(())
    }

    #[test]
    fn demonstrate_try_filter_map() -> IonResult<()> {
        let log = r#"
            $ion_1_1
            (:add_macros
                (macro request (requestId server elapsedMs page status)
                    {
                        requestId: (%requestId),
                        server: (%server),
                        elapsedMs: (%elapsedMs),
                        page: (%page),
                        status: (%status),
                    }))
            (:request abc100 'server1.example.com' 40 "index.html" 200)
            (:request def84 'server2.example.com' 3500 "productFoo.html" 200)
            (:request abc101 'server1.example.com' 31 "index.html" 200)
            (:request abc102 'server1.example.com' 4000 "productFoo.html" 200)
            (:request def85 'server2.example.com' 10 "productBar.html" 404)
        "#;

        let mut reader = Reader::new(AnyEncoding, log)?;
        let problem_requests = reader
            .try_filter_map(|element| {
                let event = element.read()?.expect_struct()?;
                let status = event.get_expected("status")?.expect_i64()?;
                let elapsed = event.get_expected("elapsedMs")?.expect_i64()?;
                if status != 200 || elapsed > 1000 {
                    Ok(Some(
                        event.get_expected("requestId")?.expect_text()?.to_owned(),
                    ))
                } else {
                    Ok(None)
                }
            })
            .collect::<IonResult<Vec<String>>>();
        drop(reader);
        assert_eq!(problem_requests?, vec!["def84", "abc102", "def85"]);
        Ok(())
    }
}
