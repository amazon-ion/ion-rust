use crate::result::{decoding_error, illegal_operation, illegal_operation_raw};
use crate::text::parent_container::ParentContainer;

use crate::element::iterators::SymbolsIterator;
use crate::element::{Blob, Clob, Element};
use crate::{
    Decimal, Int, IonError, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp,
};
use std::fmt::Display;
use std::mem;

const INITIAL_PARENTS_CAPACITY: usize = 16;

// TODO: Add an IonElementReader trait implementation
// TODO: once ElementReader trait is removed this can  use the name `ElementReader`
pub struct ElementStreamReader {
    // Represents the element that will be read using this reader
    element: Option<Element>,
    // If the reader is not positioned on a struct the iterator item will store (None, _element_)
    // Otherwise it will store (Some(_field_name_), _element_)
    current_iter: Box<dyn Iterator<Item = (Option<Symbol>, Element)>>,
    iter_stack: Vec<Box<dyn Iterator<Item = (Option<Symbol>, Element)>>>,
    // If the reader is not positioned over a value inside a struct, this is None.
    current_field_name: Option<Symbol>,
    // If the reader has not yet begun reading at the current level or is positioned over an IVM,
    // this is None.
    current_value: Option<Element>,
    is_eof: bool,
    parents: Vec<ParentContainer>,
}

impl ElementStreamReader {
    pub fn new(input: Element) -> ElementStreamReader {
        ElementStreamReader {
            element: Some(input),
            current_iter: Box::new(std::iter::empty()),
            iter_stack: vec![],
            current_field_name: None,
            current_value: None,
            is_eof: false,
            parents: Vec::with_capacity(INITIAL_PARENTS_CAPACITY),
        }
    }

    fn load_next_value(&mut self) -> IonResult<()> {
        // If the reader's current value is the beginning of a container and the user calls `next()`,
        // we need to skip the entire container. We can do this by stepping into and then out of
        // that container; `step_out()` has logic that will exhaust the remaining values.
        let need_to_skip_container = !self.is_null()
            && self
                .current_value
                .as_ref()
                .map(|v| v.ion_type().is_container())
                .unwrap_or(false);

        if need_to_skip_container {
            self.step_in()?;
            self.step_out()?;
        }

        // Unset variables holding onto information about the previous position.
        self.current_value = None;
        self.current_field_name = None;

        if self.parents.is_empty() {
            // If the reader has already found EOF (the end of the top level), there's no need to
            // try to read more data. Return Ok(None).
            if self.is_eof {
                self.current_value = None;
                return Ok(());
            }

            self.current_value = self.element.take();
            // As we already loaded the single element provided to the reader, we have reached eof
            self.is_eof = true;
            return Ok(());
        }

        // If the parent is not empty that means we are inside a container
        // Get the next value of the container using the iterator
        let next_item = self.current_iter.next();
        if next_item.is_none() {
            // If there are no next values left within the iterator
            // then early return
            self.current_value = None;
            return Ok(());
        }
        // Otherwise if there is a next value available then set current value accordingly
        let (field_name, value) = next_item.unwrap();
        self.current_value = Some(value);
        // Field name will either be `None` for container types SExpression, List
        // But for struct it will contain the field name `Symbol`
        self.current_field_name = field_name;

        Ok(())
    }

    /// Constructs an [IonError::IllegalOperation] which explains that the reader was asked to
    /// perform an action that is only allowed when it is positioned over the item type described
    /// by the parameter `expected`.
    fn expected<I: Display>(&self, expected: I) -> IonError {
        illegal_operation_raw(format!(
            "type mismatch: expected a(n) {} but positioned over a(n) {}",
            expected,
            self.current()
        ))
    }

    fn container_values(value: Element) -> Box<dyn Iterator<Item = (Option<Symbol>, Element)>> {
        match value.ion_type() {
            IonType::List | IonType::SExp => Box::new(
                value
                    .as_sequence()
                    .unwrap()
                    .elements()
                    .map(|e| (None, e.to_owned()))
                    .collect::<Vec<(Option<Symbol>, Element)>>()
                    .into_iter(),
            ),
            IonType::Struct => Box::new(
                value
                    .as_struct()
                    .unwrap()
                    .iter()
                    .map(|(s, e)| (Some(s.to_owned()), e.to_owned()))
                    .collect::<Vec<(Option<Symbol>, Element)>>()
                    .into_iter(),
            ),
            _ => unreachable!("Can not step into a scalar type"),
        }
    }

    fn current_value_as<T, F>(&self, expect_message: &'static str, map_fn: F) -> IonResult<T>
    where
        F: Fn(&Element) -> Option<T>,
    {
        self.current_value
            .as_ref()
            .and_then(map_fn)
            .ok_or_else(|| self.expected(expect_message))
    }
}

impl IonReader for ElementStreamReader {
    type Item = StreamItem;
    type Symbol = Symbol;

    fn next(&mut self) -> IonResult<StreamItem> {
        // Parse the next value from the stream, storing it in `self.current_value`.
        self.load_next_value()?;

        // If we're positioned on a value, return its IonType and whether it's null.
        Ok(self.current())
    }

    fn current(&self) -> StreamItem {
        if let Some(ref value) = self.current_value {
            StreamItem::nullable_value(value.ion_type(), value.is_null())
        } else {
            StreamItem::Nothing
        }
    }

    fn ion_type(&self) -> Option<IonType> {
        self.current_value.as_ref().map(|v| v.ion_type())
    }

    fn is_null(&self) -> bool {
        if let Some(ref value) = self.current_value {
            return value.is_null();
        }
        false
    }

    // Clippy reports a redundant closure, but fixing it causes the code to break.
    // See: https://github.com/amazon-ion/ion-rust/issues/472
    #[allow(clippy::redundant_closure)]
    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        let iterator = self
            .current_value
            .as_ref()
            .map(|value| value.annotations().iter())
            .unwrap_or_else(|| SymbolsIterator::empty())
            .cloned()
            // The annotations are already in memory and are already resolved to text, so
            // this step cannot fail. Map each token to Ok(token).
            .map(Ok);
        Box::new(iterator)
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match self.current_field_name.as_ref() {
            Some(name) => Ok(name.clone()),
            None => illegal_operation(
                "field_name() can only be called when the reader is positioned inside a struct",
            ),
        }
    }

    // TODO: See if the match statements for read_*() below could be simplified

    fn read_null(&mut self) -> IonResult<IonType> {
        match self.current_value.as_ref() {
            Some(element) if element.is_null() => Ok(element.ion_type()),
            _ => Err(self.expected("null value")),
        }
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        self.current_value_as("bool value", |v| v.as_bool())
    }

    fn read_int(&mut self) -> IonResult<Int> {
        self.current_value_as("int value", |v| v.as_int().map(|i| i.to_owned()))
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        match self.current_value.as_ref() {
            Some(element) if element.as_int().is_some() => match element.as_int().unwrap() {
                Int::I64(value) => Ok(*value),
                Int::BigInt(value) => {
                    decoding_error(format!("Integer {value} is too large to fit in an i64."))
                }
            },
            _ => Err(self.expected("int value")),
        }
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        self.current_value_as("float value", |v| v.as_float().map(|f| f as f32))
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        self.current_value_as("float value", |v| v.as_float())
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        self.current_value_as("decimal value", |v| v.as_decimal().map(|i| i.to_owned()))
    }

    fn read_string(&mut self) -> IonResult<Str> {
        match self.current_value.as_ref() {
            Some(element) if element.as_text().is_some() => Ok(element.as_text().unwrap().into()),
            _ => Err(self.expected("string value")),
        }
    }

    fn read_str(&mut self) -> IonResult<&str> {
        match self.current_value.as_ref() {
            Some(element) if element.as_text().is_some() => Ok(element.as_text().unwrap()),
            _ => Err(self.expected("string value")),
        }
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        self.current_value_as("symbol value", |v| v.as_symbol().map(|i| i.to_owned()))
    }

    fn read_blob(&mut self) -> IonResult<Blob> {
        match self.current_value.as_ref() {
            Some(element) if element.as_blob().is_some() => {
                Ok(Blob::from(element.as_blob().unwrap()))
            }
            _ => Err(self.expected("blog value")),
        }
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        match self.current_value.as_ref() {
            Some(element) if element.as_clob().is_some() => {
                Ok(Clob::from(element.as_clob().unwrap()))
            }
            _ => Err(self.expected("clob value")),
        }
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        self.current_value_as("timestamp value", |v| {
            v.as_timestamp().map(|i| i.to_owned())
        })
    }

    fn step_in(&mut self) -> IonResult<()> {
        match &self.current_value {
            Some(value) if value.ion_type().is_container() => {
                self.parents.push(ParentContainer::new(value.ion_type()));
                // Create a new iterator for values of the container that we are stepping into
                let mut iter = ElementStreamReader::container_values(value.to_owned());
                // Set `current_iter` to point to the new one, storing the old one in `iter`.
                mem::swap(&mut iter, &mut self.current_iter);
                // Put the old iterator on the stack
                self.iter_stack.push(iter);
                self.current_value = None;
                Ok(())
            }
            Some(value) => {
                illegal_operation(format!("Cannot step_in() to a {:?}", value.ion_type()))
            }
            None => illegal_operation(format!(
                "{} {}",
                "Cannot `step_in`: the reader is not positioned on a value.",
                "Try calling `next()` to advance first."
            )),
        }
    }

    fn step_out(&mut self) -> IonResult<()> {
        if self.parents.is_empty() {
            return illegal_operation(
                "Cannot call `step_out()` when the reader is at the top level.",
            );
        }

        // The container we're stepping out of.
        let parent = self.parents.last().unwrap();

        // If we're not at the end of the current container, advance the cursor until we are.
        if !parent.is_exhausted() {
            while let StreamItem::Value(_) | StreamItem::Null(_) = self.next()? {}
        }

        // Remove the parent container from the stack and clear the current value.
        let _ = self.parents.pop();

        // Remove the iterator related to the parent container from stack and set it as current iterator
        match self.iter_stack.pop() {
            None => {}
            Some(iter) => {
                self.current_iter = iter;
            }
        }
        self.current_value = None;

        if self.parents.is_empty() {
            // We're at the top level; nothing left to do.
            return Ok(());
        }

        Ok(())
    }

    fn parent_type(&self) -> Option<IonType> {
        self.parents.last().map(|parent| parent.ion_type())
    }

    fn depth(&self) -> usize {
        self.parents.len()
    }

    fn ion_version(&self) -> (u8, u8) {
        // An `Element` doesn't have an Ion version associated with it
        // Since `Element`s are an in-memory representation fo Ion data, all versions of 1.x share the same Ion version.
        (1, 0)
    }
}

#[cfg(test)]
mod reader_tests {
    use rstest::*;

    use super::*;
    use crate::result::IonResult;
    use crate::stream_reader::IonReader;
    use crate::types::Decimal;
    use crate::types::Timestamp;

    use crate::IonType;

    fn load_element(text: &str) -> Element {
        Element::read_one(text.as_bytes()).expect("parsing failed unexpectedly")
    }

    fn next_type(reader: &mut ElementStreamReader, ion_type: IonType, is_null: bool) {
        assert_eq!(
            reader.next().unwrap(),
            StreamItem::nullable_value(ion_type, is_null)
        );
    }

    #[test]
    fn test_skipping_containers() -> IonResult<()> {
        let ion_data = load_element(
            r#"
            [1, 2, 3]
        "#,
        );
        let reader = &mut ElementStreamReader::new(ion_data);

        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 1);
        reader.step_out()?;
        // This should skip 2, 3 and reach end of the element
        // Asking for next here should result in `Nothing`
        assert_eq!(reader.next()?, StreamItem::Nothing);
        Ok(())
    }

    #[test]
    fn test_read_nested_containers() -> IonResult<()> {
        let ion_data = load_element(
            r#"
            {
                foo: [
                    1,
                    [2, 3],
                    4
                ],
                bar: {
                    a: 5,
                    b: (true true true)
                }
            }
        "#,
        );
        let reader = &mut ElementStreamReader::new(ion_data);
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        // The reader is now at the '2' nested inside of 'foo'
        reader.step_out()?;
        reader.step_out()?;
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        next_type(reader, IonType::SExp, false);
        reader.step_in()?;
        next_type(reader, IonType::Bool, false);
        next_type(reader, IonType::Bool, false);
        // The reader is now at the second 'true' in the s-expression nested in 'bar'/'b'
        reader.step_out()?;
        reader.step_out()?;
        reader.step_out()?;
        Ok(())
    }

    #[test]
    fn test_read_container_with_mixed_scalars_and_containers() -> IonResult<()> {
        let ion_data = load_element(
            r#"
            {
                foo: 4,
                bar: {
                    a: 5,
                    b: (true true true)
                }
            }
        "#,
        );

        let reader = &mut ElementStreamReader::new(ion_data);
        next_type(reader, IonType::Struct, false);
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.field_name()?, Symbol::owned("foo"));
        next_type(reader, IonType::Struct, false);
        assert_eq!(reader.field_name()?, Symbol::owned("bar"));
        reader.step_in()?;
        next_type(reader, IonType::Int, false);
        assert_eq!(reader.read_i64()?, 5);
        reader.step_out()?;
        assert_eq!(reader.next()?, StreamItem::Nothing);
        reader.step_out()?;
        Ok(())
    }

    #[test]
    fn test_read_container_with_mixed_scalars() -> IonResult<()> {
        let ion_data = load_element(
            r#"
            [ {{ZW5jb2RlZA==}}, {{"hello"}}, 4.5e0, 4.5, 2007-07-12T, foo, "hi!" ]
        "#,
        );

        let reader = &mut ElementStreamReader::new(ion_data);
        next_type(reader, IonType::List, false);
        reader.step_in()?;
        next_type(reader, IonType::Blob, false);
        assert_eq!(reader.read_blob()?, Blob::from("encoded"));
        next_type(reader, IonType::Clob, false);
        assert_eq!(reader.read_clob()?, Clob::from("hello"));
        next_type(reader, IonType::Float, false);
        assert_eq!(reader.read_f64()?, 4.5);
        next_type(reader, IonType::Decimal, false);
        assert_eq!(reader.read_decimal()?, Decimal::new(45, -1));
        next_type(reader, IonType::Timestamp, false);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2007, 7, 12).build().unwrap()
        );
        next_type(reader, IonType::Symbol, false);
        assert_eq!(reader.read_symbol()?, Symbol::owned("foo"));
        next_type(reader, IonType::String, false);
        assert_eq!(reader.read_string()?, "hi!".to_string());
        reader.step_out()?;
        Ok(())
    }

    #[rstest]
    #[case(" null ", Element::from(IonType::Null))]
    #[case(" null.string ", Element::from(IonType::String))]
    #[case(" true ", true)]
    #[case(" false ", false)]
    #[case(" 738 ", 738)]
    #[case(" 2.5e0 ", 2.5)]
    #[case(" 2.5 ", Decimal::new(25, -1))]
    #[case(" 2007-07-12T ", Timestamp::with_ymd(2007, 7, 12).build().unwrap())]
    #[case(" foo ", Symbol::owned("foo"))]
    #[case(" \"hi!\" ", "hi!".to_owned())]
    #[case(" {{ZW5jb2RlZA==}} ", Blob::from("encoded"))]
    #[case(" {{\"hello\"}} ", Clob::from("hello"))]
    fn test_read_single_top_level_values<E: Into<Element>>(
        #[case] text: &str,
        #[case] expected_value: E,
    ) {
        let reader = &mut ElementStreamReader::new(load_element(text));
        let expected_element = expected_value.into();
        next_type(
            reader,
            expected_element.ion_type(),
            expected_element.is_null(),
        );
        // TODO: Redo (or remove?) this test. There's not an API that exposes the
        //       AnnotatedTextValue any more. We're directly accessing `current_value` as a hack.
        let actual_element = reader.current_value.clone();
        assert_eq!(actual_element.unwrap(), expected_element);
    }

    #[rstest]
    #[case(" foo::bar::null ", Element::from(IonType::Null).with_annotations(["foo", "bar"]))]
    #[case(" foo::true ", Element::from(true).with_annotations(["foo"]))]
    #[case(" 'foo'::5 ", Element::from(5).with_annotations(["foo"]))]
    fn test_top_level_values_with_annotations<E: Into<Element>>(
        #[case] text: &str,
        #[case] expected_value: E,
    ) {
        let reader = &mut ElementStreamReader::new(load_element(text));
        let expected_element = expected_value.into();
        next_type(
            reader,
            expected_element.ion_type(),
            expected_element.is_null(),
        );
        let actual_element = reader.current_value.clone();
        // check if both the elements are equal, this also considers annotations equality
        assert_eq!(actual_element.unwrap(), expected_element);

        // verify if the annotations are read without error
        let reader_annotations: IonResult<Vec<Symbol>> = reader.annotations().collect();
        assert!(reader_annotations.is_ok());
    }

    #[test]
    fn structs_trailing_comma() -> IonResult<()> {
        let pretty_ion = load_element(
            r#"
            // Structs with last field with/without trailing comma
            (
                {a:1, b:2,}     // with trailing comma
                {a:1, b:2 }     // without trailing comma
            )
        "#,
        );
        let mut reader = ElementStreamReader::new(pretty_ion);
        assert_eq!(reader.next()?, StreamItem::Value(IonType::SExp));
        reader.step_in()?;
        assert_eq!(reader.next()?, StreamItem::Value(IonType::Struct));

        reader.step_in()?;
        assert_eq!(reader.next()?, StreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?, Symbol::owned("a".to_string()));
        assert_eq!(reader.read_i64()?, 1);
        assert_eq!(reader.next()?, StreamItem::Value(IonType::Int));
        assert_eq!(reader.field_name()?, Symbol::owned("b".to_string()));
        assert_eq!(reader.read_i64()?, 2);
        reader.step_out()?;

        assert_eq!(reader.next()?, StreamItem::Value(IonType::Struct));
        reader.step_out()?;
        Ok(())
    }
}
