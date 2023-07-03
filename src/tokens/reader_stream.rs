// Copyright Amazon.com, Inc. or its affiliates.

use super::{
    AnnotationsThunk, ContainerType, Content, FieldNameThunk, Instruction, ScalarThunk, ScalarType,
    ScalarValue, Token, TokenStream,
};
use crate::result::IonFailure;
use crate::thunk::Thunk;
use crate::{IonReader, IonResult, IonType, StreamItem, Symbol};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

const INVALID_TOKEN_ERR_TEXT: &str = "TokenStream is past this token";
const INVALID_TOKEN_PANIC_TEXT: &str = "Invalid underlying reader state";

// TODO make this more generic with respect to other readers--the problem is Item/Symbol
// TODO this has to abstract over potentially system reader to implement macros

/// Internal tracking state of the returned token.  This is necessary because the lifetime of the
/// token returned from the stream is bound to the stream itself.
///
/// This is essentially strongly typed [`Option`] with convenience to operate within the
/// context of a [`ReaderTokenStream`]
enum UnderlyingReader<R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol>,
{
    Active(R),
    Inactive,
}

impl<R> UnderlyingReader<R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol>,
{
    fn try_mut_ref(&mut self) -> IonResult<&mut R> {
        use UnderlyingReader::*;
        match self {
            Active(reader) => Ok(reader),
            Inactive => IonResult::illegal_operation(INVALID_TOKEN_ERR_TEXT),
        }
    }

    fn try_ref(&self) -> IonResult<&R> {
        use UnderlyingReader::*;
        match self {
            Active(reader) => Ok(reader),
            Inactive => IonResult::illegal_operation(INVALID_TOKEN_ERR_TEXT),
        }
    }

    fn as_mut_ref(&mut self) -> &mut R {
        self.try_mut_ref().expect(INVALID_TOKEN_PANIC_TEXT)
    }

    fn as_ref(&self) -> &R {
        self.try_ref().expect(INVALID_TOKEN_PANIC_TEXT)
    }

    /// Invalidates this reader returning its original underlying reader.
    fn invalidate(&mut self) -> Self {
        std::mem::replace(self, UnderlyingReader::Inactive)
    }
}

/// Indicates the state of the last token returned.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum PendingToken {
    Materialized,
    Deferred,
    None,
}

impl PendingToken {
    fn is_deferred(&self) -> bool {
        matches!(self, PendingToken::Deferred)
    }
}

/// Condensed version of the item of the [`IonReader`].
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum ReaderPosition {
    /// We are positioned on nothing.
    Nothing,
    /// We are positioned on some value, which could be a null-container or scalar.
    NonContainer,
    /// We are positioned on the start of some container.
    Container(ContainerType),
}

/// Adapter for a [`TokenStream`] over an arbitrary [`IonReader`]
pub struct ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    // XXX this is so we can have multiple closures to lazily evaluate tokens
    reader_cell: Rc<RefCell<UnderlyingReader<R>>>,
    pending_token: PendingToken,
    position: ReaderPosition,
    // XXX this allows us to explicitly capture a lifetime for the reader we operate on
    phantom: PhantomData<&'a R>,
}

/// These generate the methods that produce lazy content for our stream against the underlying
/// reader.  There is a lot of boilerplate and variants so this avoids copy/paste errors.
macro_rules! scalar_content_method {
    ($name:ident, $scalar_variant:ident, $reader:ident, $read_expr:expr) => {
        #[inline]
        fn $name(&mut self) -> Content<'a> {
            let reader_cell = Rc::clone(&self.reader_cell);
            ScalarThunk(
                ScalarType::$scalar_variant,
                Thunk::defer(move || {
                    let mut underlying = reader_cell.borrow_mut();
                    let $reader = underlying.try_mut_ref()?;
                    Ok(ScalarValue::$scalar_variant($read_expr))
                }),
            )
            .into()
        }
    };
}

impl<'a, R> ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    #[inline]
    fn annotations_thunk(&self) -> AnnotationsThunk<'a> {
        let reader_cell = Rc::clone(&self.reader_cell);
        Thunk::defer(move || reader_cell.borrow().try_ref()?.annotations().collect())
    }

    #[inline]
    fn field_name_thunk(&self) -> FieldNameThunk<'a> {
        match self.parent_type() {
            Some(IonType::Struct) => {
                let reader_cell = Rc::clone(&self.reader_cell);
                // XXX note that we expect a field name, so we do want that to surface as error
                //     and not None
                Thunk::defer(move || Ok(Some(reader_cell.borrow().try_ref()?.field_name()?)))
            }
            _ => Thunk::wrap(None),
        }
    }

    scalar_content_method!(bool_token, Bool, reader, reader.read_bool()?);
    scalar_content_method!(int_token, Int, reader, reader.read_int()?);
    scalar_content_method!(float_token, Float, reader, reader.read_f64()?);
    scalar_content_method!(decimal_token, Decimal, reader, reader.read_decimal()?);
    scalar_content_method!(timestamp_token, Timestamp, reader, reader.read_timestamp()?);
    scalar_content_method!(string_token, String, reader, reader.read_string()?);
    scalar_content_method!(symbol_token, Symbol, reader, reader.read_symbol()?);
    scalar_content_method!(blob_token, Blob, reader, reader.read_blob()?.into());
    scalar_content_method!(clob_token, Clob, reader, reader.read_clob()?.into());

    #[inline]
    fn invalidate_token(&mut self) {
        // only invalidate if we have something deferred
        if self.pending_token.is_deferred() {
            let underlying = {
                let mut original = self.reader_cell.borrow_mut();
                original.invalidate()
            };
            self.reader_cell = Rc::new(RefCell::new(underlying));
        }
    }

    #[inline]
    fn next(&mut self) -> IonResult<StreamItem> {
        let mut underlying = self.reader_cell.borrow_mut();
        let reader = underlying.as_mut_ref();
        self.position = ReaderPosition::Nothing;
        let item = reader.next()?;
        self.position = match item {
            StreamItem::Value(ion_type) => match ion_type {
                IonType::List => ReaderPosition::Container(ContainerType::List),
                IonType::SExp => ReaderPosition::Container(ContainerType::SExp),
                IonType::Struct => ReaderPosition::Container(ContainerType::Struct),
                _ => ReaderPosition::NonContainer,
            },
            StreamItem::Null(_) => ReaderPosition::NonContainer,
            StreamItem::Nothing => ReaderPosition::Nothing,
        };
        Ok(item)
    }

    #[inline]
    fn step_in(&mut self) -> IonResult<()> {
        let mut underlying = self.reader_cell.borrow_mut();
        let reader = underlying.as_mut_ref();
        self.position = ReaderPosition::Nothing;
        reader.step_in()
    }

    #[inline]
    fn step_out(&mut self) -> IonResult<()> {
        let mut underlying = self.reader_cell.borrow_mut();
        let reader = underlying.as_mut_ref();
        self.position = ReaderPosition::Nothing;
        reader.step_out()
    }

    #[inline]
    fn is_null(&self) -> bool {
        let underlying = self.reader_cell.borrow();
        let reader = underlying.as_ref();
        reader.is_null()
    }

    #[inline]
    fn ion_type(&self) -> Option<IonType> {
        let underlying = self.reader_cell.borrow();
        let reader = underlying.as_ref();
        reader.ion_type()
    }

    #[inline]
    fn parent_type(&self) -> Option<IonType> {
        let underlying = self.reader_cell.borrow();
        let reader = underlying.as_ref();
        reader.parent_type()
    }
}

impl<'a, R> TokenStream<'a> for ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    fn next_token(&mut self, instruction: Instruction) -> IonResult<Token<'a>> {
        use self::Instruction::*;

        // once we enter this method--we must invalidate any outstanding token references.
        // this has to do with the lifetime of the returned token which cannot be statically modeled
        self.invalidate_token();

        // assume materialized
        self.pending_token = PendingToken::Materialized;
        Ok(match instruction {
            Next => {
                // if we're on a container, we need to step in
                if matches!(self.position, ReaderPosition::Container(_)) {
                    self.step_in()?;
                }

                let item = self.next()?;
                match item {
                    StreamItem::Value(ion_type) | StreamItem::Null(ion_type) => {
                        // basically any value has a deferred operation
                        self.pending_token = PendingToken::Deferred;
                        let annotations_thunk = self.annotations_thunk();
                        let field_name_thunk = self.field_name_thunk();
                        let token = if self.is_null() {
                            Content::Null(ion_type)
                        } else {
                            match self.ion_type() {
                                None => {
                                    IonResult::illegal_operation("No type for value from reader")?
                                }
                                Some(IonType::Null) => {
                                    IonResult::illegal_operation("Null type for value from reader")?
                                }
                                Some(IonType::Bool) => self.bool_token(),
                                Some(IonType::Int) => self.int_token(),
                                Some(IonType::Float) => self.float_token(),
                                Some(IonType::Decimal) => self.decimal_token(),
                                Some(IonType::Timestamp) => self.timestamp_token(),
                                Some(IonType::Symbol) => self.symbol_token(),
                                Some(IonType::String) => self.string_token(),
                                Some(IonType::Clob) => self.clob_token(),
                                Some(IonType::Blob) => self.blob_token(),
                                Some(IonType::List) => Content::StartContainer(ContainerType::List),
                                Some(IonType::SExp) => Content::StartContainer(ContainerType::SExp),
                                Some(IonType::Struct) => {
                                    Content::StartContainer(ContainerType::Struct)
                                }
                            }
                        };
                        Token::new(annotations_thunk, field_name_thunk, token)
                    }
                    StreamItem::Nothing => match self.parent_type() {
                        None => Content::EndStream.into(),
                        Some(IonType::SExp) => {
                            self.step_out()?;
                            Content::EndContainer(ContainerType::SExp).into()
                        }
                        Some(IonType::List) => {
                            self.step_out()?;
                            Content::EndContainer(ContainerType::List).into()
                        }
                        Some(IonType::Struct) => {
                            self.step_out()?;
                            Content::EndContainer(ContainerType::Struct).into()
                        }
                        Some(ion_type) => IonResult::illegal_operation(format!(
                            "Unexpected non-container type: {}",
                            ion_type
                        ))?,
                    },
                }
            }
            NextEnd => match self.position {
                ReaderPosition::Container(container_type) => {
                    // we're on the start of a container so we don't have to move the reader
                    // but we have to emulate moving the reader
                    self.position = ReaderPosition::Nothing;
                    Content::EndContainer(container_type)
                }
                _ => match self.parent_type() {
                    None => IonResult::illegal_operation("Cannot skip to next end at top-level")?,
                    Some(ion_type) => {
                        self.step_out()?;

                        match ion_type {
                            IonType::List => Content::EndContainer(ContainerType::List),
                            IonType::SExp => Content::EndContainer(ContainerType::SExp),
                            IonType::Struct => Content::EndContainer(ContainerType::Struct),
                            _ => IonResult::illegal_operation(format!(
                                "Unexpected container type: {}",
                                ion_type
                            ))?,
                        }
                    }
                },
            }
            .into(),
        })
    }
}

impl<'a, R> From<R> for ReaderTokenStream<'a, R>
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + 'a,
{
    fn from(value: R) -> Self {
        ReaderTokenStream {
            reader_cell: Rc::new(RefCell::new(UnderlyingReader::Active(value))),
            pending_token: PendingToken::None,
            position: ReaderPosition::Nothing,
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Instruction::*;
    use super::*;
    use crate::data_source::IonDataSource;
    use crate::element::{Blob as ElemBlob, Clob as ElemClob};
    use crate::tokens::{ContainerType, ScalarValue, Value};
    use crate::{Decimal, IonError, IonResult, ReaderBuilder, Symbol};
    use rstest::rstest;

    /// An arbitrary timestamp as a filler for testing purposes.
    fn sample_timestamp() -> crate::Timestamp {
        crate::Timestamp::with_year(1999).build().unwrap()
    }

    type Src = (Instruction, Token<'static>);
    type Srcs = Vec<Src>;

    fn single_src<T>(value: T) -> IonResult<Srcs>
    where
        T: Into<Value>,
    {
        let value = value.into();
        let scalar_value: ScalarValue = value.try_into()?;

        Ok(vec![(Next, scalar_value.into())])
    }

    fn container_src(container_type: ContainerType, contents: IonResult<Srcs>) -> IonResult<Srcs> {
        let mut srcs = vec![];
        srcs.push((Next, Content::StartContainer(container_type).into()));
        srcs.append(&mut contents?);
        srcs.push((Next, Content::EndContainer(container_type).into()));
        Ok(srcs)
    }

    fn container_skip_src(
        container_type: ContainerType,
        contents: IonResult<Srcs>,
    ) -> IonResult<Srcs> {
        last_next_end(container_src(container_type, contents))
    }

    fn last_next_end(contents: IonResult<Srcs>) -> IonResult<Srcs> {
        let mut srcs = contents?;
        let (_, token) = srcs.pop().ok_or(IonError::illegal_operation(
            "No last element in stream to change",
        ))?;
        srcs.push((NextEnd, token));
        Ok(srcs)
    }

    fn field_named_srcs<C, I, S>(names: C, srcs: IonResult<Srcs>) -> IonResult<Srcs>
    where
        C: IntoIterator<Item = S, IntoIter = I>,
        I: Iterator<Item = S>,
        S: AsRef<str>,
    {
        names
            .into_iter()
            .zip(srcs?.into_iter())
            .map(|(name, (insn, a_tok))| {
                Ok((
                    insn,
                    a_tok.with_field_name(Thunk::wrap(Some(name.as_ref().into()))),
                ))
            })
            .collect()
    }

    fn annotate_first_srcs<C, I, S>(annotations: C, srcs_res: IonResult<Srcs>) -> IonResult<Srcs>
    where
        C: IntoIterator<Item = S, IntoIter = I>,
        I: Iterator<Item = S>,
        S: AsRef<str>,
    {
        let mut srcs = srcs_res?;
        if srcs.is_empty() {
            return IonResult::illegal_operation("Cannot annotate nothing");
        }

        // not exactly efficient, but that's fine here
        let (instruction, mut token) = srcs.remove(0);
        let annotations: Vec<Symbol> = annotations.into_iter().map(|s| s.as_ref().into()).collect();
        token = token.with_annotations(Thunk::wrap(annotations.into()));
        srcs.insert(0, (instruction, token));

        Ok(srcs)
    }

    fn singleton_struct_src() -> IonResult<Srcs> {
        container_src(
            ContainerType::Struct,
            field_named_srcs(["a"], single_src(5)),
        )
    }

    #[rstest]
    #[case::bool(single_src(false), "false")]
    #[case::int(single_src(5), "5")]
    #[case::float(single_src(5.0), "5e0")]
    #[case::decimal(single_src(Decimal::from(50)), "50.")]
    #[case::timestamp(single_src(sample_timestamp()), "1999T")]
    #[case::string(single_src("hello"), "'''hello'''")]
    #[case::symbol(single_src(Symbol::from("world")), "world")]
    #[case::blob(single_src(ElemBlob::from("foo".as_bytes())), "{{ Zm9v }}")]
    #[case::clob(single_src(ElemClob::from("bar".as_bytes())), "{{'''bar'''}}")]
    #[case::singleton_list(container_src(ContainerType::List, single_src(false)), "[false]")]
    #[case::singleton_sexp(container_src(ContainerType::SExp, single_src(1.0)), "(1e0)")]
    #[case::singleton_struct(singleton_struct_src(), "{a:5}")]
    #[case::empty_list(container_src(ContainerType::List, Ok(vec![])), "[]")]
    #[case::empty_sexp(container_src(ContainerType::SExp, Ok(vec![])), "()")]
    #[case::empty_struct(container_src(ContainerType::Struct, Ok(vec![])), "{}")]
    #[case::ann_empty_list(annotate_first_srcs(["a"], container_src(ContainerType::List, Ok(vec![]))), "a::[]")]
    #[case::ann_empty_sexp(annotate_first_srcs(["b"], container_src(ContainerType::SExp, Ok(vec![]))), "b::()")]
    #[case::ann_empty_struct(annotate_first_srcs(["c"], container_src(ContainerType::Struct, Ok(vec![]))), "c::{}")]
    #[case::list_skip_start(container_skip_src(ContainerType::List, Ok(vec![])), "[1, 2, 3, 4, 5]")]
    #[case::sexp_skip_start(container_skip_src(ContainerType::SExp, Ok(vec![])), "(a b c d e f)")]
    #[case::struct_skip_start(container_skip_src(ContainerType::Struct, Ok(vec![])), "{a:1, b:2}")]
    #[case::list_skip_second(
        container_skip_src(ContainerType::List, single_src(1)),
        "[1, 2, 3, 4, 5]"
    )]
    #[case::sexp_skip_second(
        container_skip_src(ContainerType::SExp, single_src(Symbol::from("a"))),
        "(a b c d e f)"
    )]
    #[case::struct_skip_second(last_next_end(singleton_struct_src()), "{a:5, b:6, c:7}")]
    #[case::ann(annotate_first_srcs(["a", "b", "c"], single_src(false)), "a::b::c::false")]
    fn stream_test<S>(#[case] expected: IonResult<Srcs>, #[case] data: S) -> IonResult<()>
    where
        S: IonDataSource,
    {
        use Content::*;
        let mut expected_src = expected?;
        // add the terminator
        expected_src.push((Next, EndStream.into()));
        let expected_count = expected_src.len();

        let reader = ReaderBuilder::new().build(data)?;
        let mut tokens: ReaderTokenStream<_> = reader.into();
        let mut actual_count: usize = 0;
        for (instruction, expected_token) in expected_src {
            actual_count += 1;
            let token = tokens.next_token(instruction)?;

            let (exp_ann_thunk, exp_field_name_thunk, exp_content) = expected_token.into_inner();
            let (ann_thunk, field_name_thunk, content) = token.into_inner();

            let exp_anns = exp_ann_thunk.evaluate()?;
            let actual_anns = ann_thunk.evaluate()?;
            assert_eq!(exp_anns, actual_anns);

            let exp_field_name = exp_field_name_thunk.evaluate()?;
            let field_name = field_name_thunk.evaluate()?;
            assert_eq!(exp_field_name, field_name);

            match (exp_content, content) {
                (Null(exp_ion_type), Null(actual_ion_type)) => {
                    assert_eq!(exp_ion_type, actual_ion_type);
                }
                (Scalar(exp_scalar_thunk), Scalar(actual_scalar_thunk)) => {
                    let exp_scalar = exp_scalar_thunk.evaluate()?;
                    let actual_scalar = actual_scalar_thunk.evaluate()?;
                    assert_eq!(exp_scalar, actual_scalar);
                }
                (StartContainer(exp_c_type), StartContainer(actual_c_type)) => {
                    assert_eq!(exp_c_type, actual_c_type);
                }
                (EndContainer(exp_c_type), EndContainer(actual_c_type)) => {
                    assert_eq!(exp_c_type, actual_c_type);
                }
                (EndStream, EndStream) => {
                    // nothing to assert!
                }
                (exp_token, actual_token) => {
                    panic!(
                        "Tokens {:?} and {:?} are not the same",
                        exp_token, actual_token
                    );
                }
            }
        }
        assert_eq!(expected_count, actual_count);
        Ok(())
    }

    #[test]
    fn test_lifetime() -> IonResult<()> {
        let reader = ReaderBuilder::new().build("[1, 2, 3]")?;
        let mut tokens: ReaderTokenStream<_> = reader.into();
        {
            let invalid_token = tokens.next_token(Next)?;
            let mut valid_token = tokens.next_token(Next)?;

            // make sure the token is invalid (annotations/field name on start container)
            match invalid_token.materialize() {
                Err(IonError::IllegalOperation(e)) => {
                    assert_eq!(INVALID_TOKEN_ERR_TEXT, e.operation())
                }
                Err(e) => panic!("Unexpected Error: {}", e),
                _ => panic!("Should not be able to materialize"),
            };

            valid_token.memoize()?;
            let _next_token = tokens.next_token(Next)?;

            let (mut annotations, mut field_name, mut content) = valid_token.into_inner();
            assert!(field_name.memoize()?.is_none());
            assert_eq!(0, annotations.memoize()?.len());
            let scalar_opt = content.memoize_scalar()?;
            assert_eq!(Some(&ScalarValue::Int(1.into())), scalar_opt);
        }
        Ok(())
    }
}
