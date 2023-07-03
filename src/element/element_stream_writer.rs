use crate::element::builders::StructBuilder;
use crate::element::{Annotations, Element, IntoAnnotatedElement, Value};
use crate::ion_writer::IonWriter;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::types::Bytes;
use crate::{
    Decimal, Int, IonResult, IonType, RawSymbolTokenRef, Str, Symbol, SymbolTable, Timestamp,
};

// Represents a level into which the writer has stepped.
// A writer that has not yet called step_in() is at the top level.
#[derive(Debug, PartialEq)]
struct ContainerContext {
    annotations: Annotations,
    field_name: Option<Symbol>,
    container: Container,
}

// A container for values that the writer will write into.
// A writer that has not yet called step_in() is at the top level.
#[derive(Debug, PartialEq)]
enum Container {
    TopLevel,
    SExpression(Vec<Element>),
    List(Vec<Element>),
    Struct(Vec<(Symbol, Element)>),
}

/// An application-level Element writer. This writer creates [`Element`]s, [`Extend::extend`]ing
/// its output with each top-level value.
pub struct ElementStreamWriter<'e, E>
where
    E: Extend<Element>,
{
    output: &'e mut E,
    containers: Vec<ContainerContext>,
    annotations: Annotations,
    field_name: Option<Symbol>,
    symbol_table: SymbolTable,
}

impl<'e, E> ElementStreamWriter<'e, E>
where
    E: Extend<Element>,
{
    pub fn new(output: &'e mut E) -> ElementStreamWriter<'e, E> {
        ElementStreamWriter {
            output,
            containers: vec![ContainerContext {
                annotations: Annotations::empty(),
                field_name: None,
                container: Container::TopLevel,
            }],
            annotations: Annotations::empty(),
            field_name: None,
            symbol_table: SymbolTable::default(),
        }
    }

    fn current_container(&self) -> &ContainerContext {
        // `self.containers` is never empty; it always has at least the top level.
        self.containers.last().unwrap()
    }

    fn current_container_mut(&mut self) -> &mut ContainerContext {
        // `self.containers` is never empty; it always has at least the top level.
        self.containers.last_mut().unwrap()
    }

    fn take_current_annotations(&mut self) -> Annotations {
        std::mem::replace(&mut self.annotations, Annotations::empty())
    }

    fn push_container(&mut self, container: Container) -> IonResult<()> {
        let annotations = self.take_current_annotations();
        let field_name = self.field_name.take();
        self.containers.push(ContainerContext {
            annotations,
            field_name,
            container,
        });
        Ok(())
    }

    fn pop_container(&mut self) -> IonResult<ContainerContext> {
        if self.containers.len() <= 1 {
            return IonResult::illegal_operation("cannot step out of the top level");
        }
        // `self.containers` is never empty; it always has at least the top level.
        Ok(self.containers.pop().unwrap())
    }

    fn set_current_annotations(&mut self, annotations: Annotations) {
        self.annotations = annotations;
    }

    fn write_scalar(&mut self, value: Value) -> IonResult<()> {
        let annotations = self.take_current_annotations();
        let element = value.with_annotations(annotations);
        self.write_element(element)
    }

    fn write_element(&mut self, element: Element) -> IonResult<()> {
        let field_name = self.field_name.take();
        match &mut self.current_container_mut().container {
            Container::TopLevel => self.output_mut().extend(std::iter::once(element)),
            Container::SExpression(seq) => seq.push(element),
            Container::List(seq) => seq.push(element),
            Container::Struct(fields) => {
                if let Some(field_name) = field_name {
                    fields.push((field_name, element));
                } else {
                    return IonResult::illegal_operation(
                        "Values inside a struct must have a field name.",
                    );
                }
            }
        };
        Ok(())
    }

    fn to_symbol<A>(&self, sym_ref: A) -> IonResult<Symbol>
    where
        A: AsRawSymbolTokenRef,
    {
        match sym_ref.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(symbol_id) => {
                if self.symbol_table.sid_is_valid(symbol_id) {
                    Ok(self
                        .symbol_table
                        .symbol_for(symbol_id)
                        .cloned()
                        .unwrap_or(Symbol::unknown_text()))
                } else {
                    IonResult::illegal_operation(format!("Symbol ID ${symbol_id} is undefined."))
                }
            }
            RawSymbolTokenRef::Text(txt) => Ok(Symbol::owned(txt)),
        }
    }
}

impl<'e, E> IonWriter for ElementStreamWriter<'e, E>
where
    E: Extend<Element>,
{
    type Output = &'e mut E;

    fn ion_version(&self) -> (u8, u8) {
        (1, 0)
    }

    fn write_ion_version_marker(&mut self, _major: u8, _minor: u8) -> IonResult<()> {
        // Nothing to do here
        Ok(())
    }

    fn supports_text_symbol_tokens(&self) -> bool {
        true
    }

    fn set_annotations<I, A>(&mut self, annotations: I)
    where
        A: AsRawSymbolTokenRef,
        I: IntoIterator<Item = A>,
    {
        let annotations: IonResult<_> =
            annotations.into_iter().map(|s| self.to_symbol(s)).collect();
        match annotations {
            Ok(annotations) => {
                self.set_current_annotations(Annotations::new(annotations));
            }
            Err(e) => {
                // TODO: This panic should be fixed as part of https://github.com/amazon-ion/ion-rust/issues/564
                panic!("Cannot set as annotation due to {e}");
            }
        }
    }

    fn write_null(&mut self, ion_type: IonType) -> IonResult<()> {
        self.write_scalar(Value::Null(ion_type))
    }

    fn write_bool(&mut self, value: bool) -> IonResult<()> {
        self.write_scalar(Value::Bool(value))
    }

    fn write_i64(&mut self, value: i64) -> IonResult<()> {
        self.write_scalar(Value::Int(value.into()))
    }

    fn write_int(&mut self, value: &Int) -> IonResult<()> {
        self.write_scalar(Value::Int(value.clone()))
    }

    fn write_f32(&mut self, value: f32) -> IonResult<()> {
        self.write_scalar(Value::Float(value as f64))
    }

    fn write_f64(&mut self, value: f64) -> IonResult<()> {
        self.write_scalar(Value::Float(value))
    }

    fn write_decimal(&mut self, value: &Decimal) -> IonResult<()> {
        self.write_scalar(Value::Decimal(value.clone()))
    }

    fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
        self.write_scalar(Value::Timestamp(value.clone()))
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(&mut self, value: A) -> IonResult<()> {
        let symbol = self.to_symbol(value)?;
        self.write_scalar(Value::Symbol(symbol))
    }

    fn write_string<A: AsRef<str>>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(Value::String(Str::from(value.as_ref())))
    }

    fn write_clob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(Value::Clob(Bytes::from(value.as_ref())))
    }

    fn write_blob<A: AsRef<[u8]>>(&mut self, value: A) -> IonResult<()> {
        self.write_scalar(Value::Blob(Bytes::from(value.as_ref())))
    }

    fn step_in(&mut self, ion_type: IonType) -> IonResult<()> {
        let container = match ion_type {
            IonType::Struct => Container::Struct(vec![]),
            IonType::List => Container::List(vec![]),
            IonType::SExp => Container::SExpression(vec![]),
            _ => {
                return IonResult::illegal_operation(format!("Cannot step into a(n) {ion_type:?}"))
            }
        };
        self.push_container(container)
    }

    fn set_field_name<A: AsRawSymbolTokenRef>(&mut self, name: A) {
        match self.to_symbol(name) {
            Ok(s) => self.field_name = Some(s),
            Err(e) => {
                // TODO: This panic should be fixed as part of https://github.com/amazon-ion/ion-rust/issues/564
                panic!("Cannot set field name due to {e}");
            }
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        match self.current_container().container {
            Container::TopLevel => None,
            Container::SExpression(_) => Some(IonType::SExp),
            Container::List(_) => Some(IonType::List),
            Container::Struct(_) => Some(IonType::Struct),
        }
    }

    fn depth(&self) -> usize {
        self.containers.len() - 1
    }

    fn step_out(&mut self) -> IonResult<()> {
        let ContainerContext {
            annotations,
            field_name,
            container,
        } = self.pop_container()?;
        let value = match container {
            Container::TopLevel => {
                return IonResult::illegal_operation("cannot step out of the top level")
            }
            Container::SExpression(seq) => Value::SExp(seq.into()),
            Container::List(seq) => Value::List(seq.into()),
            Container::Struct(fields) => {
                Value::Struct(StructBuilder::new().with_fields(fields).build())
            }
        };
        self.field_name = field_name;
        let element = value.with_annotations(annotations);
        self.write_element(element)
    }

    fn flush(&mut self) -> IonResult<()> {
        Ok(())
    }

    fn output(&self) -> &Self::Output {
        &self.output
    }

    fn output_mut(&mut self) -> &mut Self::Output {
        &mut self.output
    }
}

#[cfg(test)]
mod tests {

    use crate::element::element_stream_writer::ElementStreamWriter;
    use crate::element::{Element, IntoAnnotatedElement, Value};

    use crate::element::builders::{SequenceBuilder, StructBuilder};
    use crate::result::IonResult;

    use crate::ion_writer::IonWriter;
    use crate::types::{Bytes, Timestamp};
    use crate::{Decimal, IonType, Symbol};

    #[track_caller]
    fn writer_test_with_assertion<F, E, A>(mut commands: F, expected: Vec<E>, mut assertion: A)
    where
        E: Into<Element>,
        F: FnMut(&mut ElementStreamWriter<Vec<Element>>) -> IonResult<()>,
        A: FnMut(Vec<Element>, Vec<Element>),
    {
        let mut output = Vec::new();
        let mut writer = ElementStreamWriter::new(&mut output);
        commands(&mut writer).expect("Invalid ElementStreamWriter test commands.");
        writer.flush().expect("Call to flush() failed.");
        let expected: Vec<Element> = expected.into_iter().map(|e| e.into()).collect();

        assertion(output, expected);
    }

    #[track_caller]
    fn writer_test<F, E>(commands: F, expected: Vec<E>)
    where
        E: Into<Element>,
        F: FnMut(&mut ElementStreamWriter<Vec<Element>>) -> IonResult<()>,
    {
        writer_test_with_assertion(commands, expected, |actual, expected| {
            assert_eq!(actual, expected);
        })
    }

    #[track_caller]
    fn writer_scalar_test_with_assertion<F, E, A>(commands: F, expected: E, mut assertion: A)
    where
        E: Into<Element>,
        F: FnMut(&mut ElementStreamWriter<Vec<Element>>) -> IonResult<()>,
        A: FnMut(Element, Element),
    {
        writer_test_with_assertion(
            commands,
            vec![expected.into()],
            |mut actual, mut expected| {
                assert_eq!(actual.len(), 1);
                assert_eq!(expected.len(), 1);
                assertion(actual.pop().unwrap(), expected.pop().unwrap());
            },
        );
    }

    #[track_caller]
    fn writer_scalar_test<F, E>(commands: F, expected: E)
    where
        E: Into<Element>,
        F: FnMut(&mut ElementStreamWriter<Vec<Element>>) -> IonResult<()>,
    {
        writer_scalar_test_with_assertion(commands, expected, |actual, expected| {
            assert_eq!(actual, expected);
        })
    }

    #[test]
    fn write_null_null() {
        writer_scalar_test(|w| w.write_null(IonType::Null), Value::Null(IonType::Null));
    }

    #[test]
    fn write_null_string() {
        writer_scalar_test(
            |w| w.write_null(IonType::String),
            Value::Null(IonType::String),
        );
    }

    #[test]
    fn write_bool_true() {
        writer_scalar_test(|w| w.write_bool(true), Value::Bool(true));
    }

    #[test]
    fn write_bool_false() {
        writer_scalar_test(|w| w.write_bool(false), Value::Bool(false));
    }

    #[test]
    fn write_i64() {
        writer_scalar_test(|w| w.write_i64(7), Value::Int(7i64.into()));
    }

    #[test]
    fn write_f32() {
        writer_scalar_test(|w| w.write_f32(700f32), Value::Float(700.));
    }

    #[test]
    fn write_f64() {
        writer_scalar_test(|w| w.write_f64(700f64), Value::Float(700.));
    }

    #[test]
    fn write_annotated_i64() {
        writer_scalar_test(
            |w| {
                w.set_annotations(["foo", "bar", "baz quux"]);
                w.write_i64(7)
            },
            Value::Int(7i64.into()).with_annotations(["foo", "bar", "baz quux"]),
        );
    }

    #[test]
    fn write_decimal() {
        let decimal: Decimal = 731221.9948f64.try_into().expect("float to decimal");
        writer_scalar_test_with_assertion(
            |w| w.write_decimal(&decimal),
            Value::Decimal(Decimal::new(7312219948u64, -4)),
            |actual, expected| {
                assert_eq!(actual.ion_type(), IonType::Decimal);
                assert_eq!(expected.ion_type(), IonType::Decimal);
                let actual = actual.as_decimal().unwrap().clone();
                let expected = expected.as_decimal().unwrap().clone();
                let (diff_int, diff_fract) = Decimal::difference_by_parts_lossy(&actual, &expected);
                assert_eq!(diff_int, 0.into(), "integer component expected equal");
                assert!(diff_fract < 100_000.into()); // 100,000 arbitrarily chosen as 1/3 of the 15 decimal digits of precision
            },
        );
    }

    #[test]
    fn write_timestamp_with_year() {
        let timestamp = Timestamp::with_year(2000)
            .build()
            .expect("building timestamp failed");
        writer_scalar_test(
            |w| w.write_timestamp(&timestamp),
            Value::Timestamp(
                Timestamp::with_year(2000)
                    .build()
                    .expect("timestamp expected value"),
            ),
        );
    }

    #[test]
    fn write_timestamp_with_month() {
        let timestamp = Timestamp::with_year(2000)
            .with_month(8)
            .build()
            .expect("building timestamp failed");
        writer_scalar_test(
            |w| w.write_timestamp(&timestamp),
            Value::Timestamp(
                Timestamp::with_year(2000)
                    .with_month(8)
                    .build()
                    .expect("timestamp expected value"),
            ),
        );
    }

    #[test]
    fn write_timestamp_with_ymd() {
        let timestamp = Timestamp::with_ymd(2000, 8, 22)
            .build()
            .expect("building timestamp failed");
        writer_scalar_test(
            |w| w.write_timestamp(&timestamp),
            Value::Timestamp(
                Timestamp::with_year(2000)
                    .with_month(8)
                    .with_day(22)
                    .build()
                    .expect("timestamp expected value"),
            ),
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms() {
        let timestamp = Timestamp::with_ymd(2000, 8, 22)
            .with_hms(15, 45, 11)
            .build_at_offset(2 * 60)
            .expect("building timestamp failed");
        writer_scalar_test(
            |w| w.write_timestamp(&timestamp),
            Value::Timestamp(
                Timestamp::with_year(2000)
                    .with_month(8)
                    .with_day(22)
                    .with_hms(15, 45, 11)
                    .build_at_offset(120)
                    .expect("timestamp expected value"),
            ),
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms_millis() {
        let timestamp = Timestamp::with_ymd_hms_millis(2000, 8, 22, 15, 45, 11, 931)
            .build_at_offset(-5 * 60)
            .expect("building timestamp failed");
        writer_scalar_test(
            |w| w.write_timestamp(&timestamp),
            Value::Timestamp(
                Timestamp::with_year(2000)
                    .with_month(8)
                    .with_day(22)
                    .with_hms(15, 45, 11)
                    .with_milliseconds(931)
                    .build_at_offset(-300)
                    .expect("timestamp expected value"),
            ),
        );
    }

    #[test]
    fn write_timestamp_with_ymd_hms_millis_unknown_offset() {
        let timestamp = Timestamp::with_ymd_hms_millis(2000, 8, 22, 15, 45, 11, 931)
            .build_at_unknown_offset()
            .expect("building timestamp failed");
        writer_scalar_test(
            |w| w.write_timestamp(&timestamp),
            Value::Timestamp(
                Timestamp::with_year(2000)
                    .with_month(8)
                    .with_day(22)
                    .with_hms(15, 45, 11)
                    .with_milliseconds(931)
                    .build_at_unknown_offset()
                    .expect("timestamp expected value"),
            ),
        );
    }

    #[test]
    fn write_blob() {
        writer_scalar_test(
            |w| w.write_blob("hello".as_bytes()),
            Value::Blob(Bytes::from(&[104, 101, 108, 108, 111])),
        );
    }

    #[test]
    fn write_clob() {
        writer_scalar_test(
            |w| w.write_clob("a\"\'\n".as_bytes()),
            Value::Clob(Bytes::from(&[97, 34, 39, 10])),
        );
        writer_scalar_test(
            |w| w.write_clob("❤️".as_bytes()),
            Value::Clob(Bytes::from("❤️")),
        );
        writer_scalar_test(
            |w| w.write_clob("hello world".as_bytes()),
            Value::Clob(Bytes::from(&[
                104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100,
            ])),
        );
    }

    #[test]
    fn top_level_values() {
        writer_test(
            |w| {
                w.write_bool(true)?;
                w.write_bool(false)
            },
            vec![Value::Bool(true), Value::Bool(false)],
        );
    }

    #[test]
    fn top_level_values_with_nesting() {
        writer_test(
            |w| {
                w.write_bool(true)?;
                w.step_in(IonType::List)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.write_symbol("bar")?;
                w.step_out()
            },
            vec![
                Value::Bool(true),
                Value::List(
                    SequenceBuilder::new()
                        .push("foo")
                        .push(21)
                        .push(Value::Symbol(Symbol::from("bar")))
                        .build(),
                ),
            ],
        );
    }

    #[test]
    fn write_list() {
        writer_scalar_test(
            |w| {
                w.step_in(IonType::List)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.write_symbol("bar")?;
                w.step_out()
            },
            Value::List(
                SequenceBuilder::new()
                    .push("foo")
                    .push(21)
                    .push(Value::Symbol(Symbol::from("bar")))
                    .build(),
            ),
        );
    }

    #[test]
    fn write_nested_list() {
        writer_scalar_test(
            |w| {
                w.step_in(IonType::List)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.step_in(IonType::List)?;
                w.write_symbol("bar")?;
                w.step_out()?;
                w.step_out()
            },
            Value::List(
                SequenceBuilder::new()
                    .push("foo")
                    .push(21)
                    .push(Value::List(
                        SequenceBuilder::new()
                            .push(Value::Symbol(Symbol::from("bar")))
                            .build(),
                    ))
                    .build(),
            ),
        );
    }

    #[test]
    fn write_s_expression() {
        writer_scalar_test(
            |w| {
                w.step_in(IonType::SExp)?;
                w.write_string("foo")?;
                w.write_i64(21)?;
                w.write_symbol("bar")?;
                w.step_out()
            },
            Value::SExp(
                SequenceBuilder::new()
                    .push("foo")
                    .push(21)
                    .push(Value::Symbol(Symbol::from("bar")))
                    .build(),
            ),
        );
    }

    #[test]
    fn write_struct() {
        writer_scalar_test(
            |w| {
                w.step_in(IonType::Struct)?;
                w.set_field_name("a");
                w.write_string("foo")?;
                w.set_field_name("b");
                w.write_i64(21)?;
                w.set_field_name("c");
                w.set_annotations(["quux"]);
                w.write_symbol("bar")?;
                w.step_out()
            },
            Value::Struct(
                StructBuilder::new()
                    .with_field("a", "foo")
                    .with_field("b", 21)
                    .with_field(
                        "c",
                        Value::Symbol(Symbol::from("bar")).with_annotations(["quux"]),
                    )
                    .build(),
            ),
        );
    }
}
