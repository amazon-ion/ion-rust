// Copyright Amazon.com, Inc. or its affiliates.

use super::{ContainerType, Content, Instruction, Token, TokenStream};
use crate::element::{Annotations, Blob, Clob};
use crate::result::{illegal_operation, illegal_operation_raw};
use crate::tokens::ScalarValue;
use crate::types::integer::IntAccess;
use crate::{Decimal, Int, IonReader, IonResult, IonType, Str, StreamItem, Symbol, Timestamp};
use std::cell::RefCell;

/// Adapts any [`TokenStream`] into an [`IonReader`].
///
/// It is important to note that adapting a stream in the middle of a container stream
/// will treat it as top-level and only surface what it can see at that level.  It will not
/// step out of the container.
pub struct TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    stream: T,
    /// Models what containers we are in
    container_stack: Vec<ContainerType>,

    // XXX this is a RefCell<AnnotationToken> because we need interior mutability for memoization
    /// the current token
    curr_token_cell: Option<RefCell<Token<'a>>>,

    /// remember the current read item
    curr_item: StreamItem,

    /// memory set aside to support `read_str` since we cannot safely return a reference into the
    /// `RefCell` that holds the token without wrapping it in a `Ref`.
    str_buf: Str,
}

impl<'a, T> TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    /// Advances the stream, setting the current token and item.
    fn next_token(&mut self, instruction: Instruction) -> IonResult<StreamItem> {
        let token = self.stream.next_token(instruction)?;
        let item = match &token.content {
            Content::Null(ion_type) => StreamItem::Null(*ion_type),
            Content::Scalar(thunk) => StreamItem::Value(thunk.scalar_type().into()),
            Content::StartContainer(container_type) => StreamItem::Value((*container_type).into()),
            Content::EndContainer(_) => StreamItem::Nothing,
            Content::EndStream => StreamItem::Nothing,
        };
        self.curr_item = item;
        self.curr_token_cell = Some(RefCell::new(token));
        Ok(item)
    }

    /// Resets the state to just before something at the current level of the stream
    fn reset_curr_state(&mut self) -> IonResult<()> {
        self.curr_item = StreamItem::Nothing;
        self.curr_token_cell = None;
        Ok(())
    }
}

impl<'a, T> From<T> for TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    fn from(stream: T) -> Self {
        TokenStreamReader {
            stream,
            container_stack: vec![],
            curr_token_cell: None,
            curr_item: StreamItem::Nothing,
            str_buf: Str::from(""),
        }
    }
}

const STEP_IN_ERROR_TEXT: &str = "Cannot step in, not at start of container";
const STEP_OUT_ERROR_TEXT: &str = "Cannot step out, not in a container";
const NO_FIELD_NAME_ERROR_TEXT: &str = "No field name";
const NOT_POSITIONED_ON_ANYTHING_ERROR_TEXT: &str = "Not positioned on anything";
const CANNOT_READ_NON_SCALAR_ERROR_TEXT: &str = "Cannot read from non-scalar";

/// Generates the read methods against the underlying token/item state.
/// This eliminates the boilerplate around each definition avoiding a lot of copy/paste.
///
/// * `me` - the identifier for `self` to make it visible to `scalar_exp`.
/// * `method` - the name of the method.
/// * `scalar_type` - the return type for the method.
/// * `variant` - the unqualified variant of [`ScalarValue`] to match over the current token.
/// * `scalar` - the matched identifier of the contents of [`ScalarValue`].
/// * `scalar_exp` - the expression to generate the return value.
macro_rules! read_method_self {
    ($me:ident, $method:ident, $scalar_type:ty, $variant:ident, $scalar:ident, $scalar_exp:expr) => {
        fn $method(&mut $me) -> IonResult<$scalar_type> {
            match &$me.curr_token_cell {
                None => illegal_operation(NOT_POSITIONED_ON_ANYTHING_ERROR_TEXT),
                Some(token_cell) => {
                    let mut token = token_cell.borrow_mut();
                    match token.content_mut().no_memoize_scalar() {
                        Ok(Some(ScalarValue::$variant($scalar))) => Ok($scalar_exp),
                        Ok(Some(scalar_value)) => illegal_operation(format!(
                            concat!("Cannot read ", stringify!($scalar_type), " from {}"),
                            scalar_value.scalar_type()
                        )),
                        Ok(None) => illegal_operation(CANNOT_READ_NON_SCALAR_ERROR_TEXT),
                        Err(e) => Err(e),
                    }
                }
            }
        }
    };
}

/// Shorthand for `read_method_self` where we do not need to capture `self` in the expression.
macro_rules! read_method {
    ($method:ident, $scalar_type:ty, $variant:ident, $scalar:ident, $scalar_exp:expr) => {
        read_method_self!(self, $method, $scalar_type, $variant, $scalar, $scalar_exp);
    };
}

impl<'a, T> IonReader for TokenStreamReader<'a, T>
where
    T: TokenStream<'a>,
{
    type Item = StreamItem;
    type Symbol = Symbol;

    fn ion_version(&self) -> (u8, u8) {
        // XXX A `TokenStream` doesn't know its underlying Ion version, we just say 1.0
        //     because all Ion 1.x versions have the same data model.
        (1, 0)
    }

    fn next(&mut self) -> IonResult<Self::Item> {
        match &self.curr_token_cell {
            None => self.next_token(Instruction::Next),
            Some(token_cell) => {
                let token = token_cell.borrow();
                let insn_opt: Option<_> = match token.content() {
                    // normal values are just a next
                    Content::Null(_) | Content::Scalar(_) => Some(Instruction::Next),
                    Content::StartContainer(_) => {
                        match self.curr_item {
                            // container values are not stepped into
                            StreamItem::Value(_) => Some(Instruction::NextEnd),
                            StreamItem::Null(_) => {
                                unreachable!("Cannot be null and on a start container")
                            }
                            // if our current item is nothing, we've stepped in
                            StreamItem::Nothing => Some(Instruction::Next),
                        }
                    }
                    // end positions are terminal unless step_out if applicable
                    Content::EndContainer(_) | Content::EndStream => None,
                };
                drop(token);
                // we need to drop the cell borrow before we can advance
                match insn_opt {
                    Some(instruction) => self.next_token(instruction),
                    None => Ok(StreamItem::Nothing),
                }
            }
        }
    }

    fn current(&self) -> Self::Item {
        self.curr_item
    }

    fn ion_type(&self) -> Option<IonType> {
        match (self.curr_item, &self.curr_token_cell) {
            (StreamItem::Nothing, _) => None,
            (_, None) => None,
            (_, Some(token_cell)) => {
                let token = token_cell.borrow();
                match token.content() {
                    Content::Null(ion_type) => Some(*ion_type),
                    Content::Scalar(thunk) => Some(thunk.scalar_type().into()),
                    Content::StartContainer(container_type) => Some((*container_type).into()),
                    Content::EndContainer(_) => {
                        // the end of a container is considered not positioned
                        None
                    }
                    Content::EndStream => None,
                }
            }
        }
    }

    fn annotations<'b>(&'b self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'b> {
        let iter = match &self.curr_token_cell {
            None => Annotations::empty().into_iter(),
            Some(token_cell) => {
                let mut token = token_cell.borrow_mut();
                let annotations_result = token.annotations.no_memoize();
                match annotations_result {
                    Ok(annotations) => annotations.into_iter(),
                    Err(e) => {
                        // if this happens we return a singleton error
                        return Box::new([Err(e)].into_iter());
                    }
                }
            }
        };
        Box::new(iter.map(Ok))
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        match &self.curr_token_cell {
            None => illegal_operation(NO_FIELD_NAME_ERROR_TEXT),
            Some(token_cell) => {
                let mut token = token_cell.borrow_mut();
                match token.share_field_name() {
                    Ok(Some(symbol)) => Ok(symbol),
                    Ok(None) => illegal_operation(NO_FIELD_NAME_ERROR_TEXT),
                    Err(e) => Err(e),
                }
            }
        }
    }

    fn is_null(&self) -> bool {
        matches!(self.curr_item, StreamItem::Null(_))
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        match &self.curr_item {
            StreamItem::Null(ion_type) => Ok(*ion_type),
            StreamItem::Value(ion_type) => {
                illegal_operation(format!("Cannot read null for {} value", ion_type))
            }
            StreamItem::Nothing => illegal_operation("Cannot read null on nothing"),
        }
    }

    read_method!(read_bool, bool, Bool, boolean, boolean);
    read_method!(
        read_i64,
        i64,
        Int,
        integer,
        integer
            .as_i64()
            .ok_or_else(|| illegal_operation_raw("Integer too large for i64"))?
    );
    read_method!(read_int, Int, Int, integer, integer);
    read_method!(read_f32, f32, Float, float, float as f32);
    read_method!(read_f64, f64, Float, float, float);
    read_method!(read_decimal, Decimal, Decimal, decimal, decimal);
    read_method!(read_string, Str, String, string, string);
    read_method_self!(self, read_str, &str, String, string, {
        // XXX we need to keep the computed value in our own memory
        self.str_buf = string;
        self.str_buf.text()
    });
    read_method!(read_symbol, Symbol, Symbol, symbol, symbol);
    read_method!(read_blob, Blob, Blob, blob, Blob(blob));
    read_method!(read_clob, Clob, Clob, clob, Clob(clob));
    read_method!(read_timestamp, Timestamp, Timestamp, timestamp, timestamp);

    fn step_in(&mut self) -> IonResult<()> {
        match &self.curr_token_cell {
            None => illegal_operation(STEP_IN_ERROR_TEXT),
            Some(token_cell) => {
                let token = token_cell.borrow();
                match token.content() {
                    Content::StartContainer(container_type) => {
                        // position the item over nothing
                        self.curr_item = StreamItem::Nothing;
                        // push container context
                        self.container_stack.push(*container_type);
                        Ok(())
                    }
                    _ => illegal_operation(STEP_IN_ERROR_TEXT),
                }
            }
        }
    }

    fn step_out(&mut self) -> IonResult<()> {
        // pop container context
        match self.container_stack.pop() {
            Some(stack_container_type) => {
                // advance stream to the end of the container--unless we're already there
                let next_end = match &self.curr_token_cell {
                    None => unreachable!("No token within a container"),
                    Some(token_cell) => {
                        let token = token_cell.borrow();
                        match token.content() {
                            Content::EndContainer(end_container_type) => {
                                assert_eq!(stack_container_type, *end_container_type);
                                // no advancement necessary, we're at the end of the container
                                false
                            }
                            Content::EndStream => {
                                illegal_operation("End of stream in the middle of container")?
                            }
                            _ => {
                                // we are not at the end of the current container
                                true
                            }
                        }
                    }
                };
                // we have to do this after the above because of the cell borrow
                if next_end {
                    self.next_token(Instruction::NextEnd)?;
                }
                // at this point we need to reset the current token to basically indicate that
                // we've consumed it and can continue on our way
                self.reset_curr_state()?;
                Ok(())
            }
            None => illegal_operation(STEP_OUT_ERROR_TEXT),
        }
    }

    fn parent_type(&self) -> Option<IonType> {
        self.container_stack
            .last()
            .map(|container_type| (*container_type).into())
    }

    fn depth(&self) -> usize {
        self.container_stack.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::element::reader::ElementReader;
    use crate::element::Element;
    use crate::ion_data::ion_eq_f64;
    use crate::tokens::reader_stream::ReaderTokenStream;
    use crate::{IonData, ReaderBuilder};
    use rstest::rstest;
    use rstest_reuse::{self, *};
    use std::iter::zip;

    #[template]
    #[rstest]
    #[case::null("null")]
    #[case::null_int("null.int")]
    #[case::ann_null_float("a::b::null.float")]
    #[case::bool("true")]
    #[case::ann_bool("foo::false")]
    #[case::int("127")]
    #[case::ann_int("i8::-127")]
    #[case::float("1e0")]
    #[case::ann_inf("too::much::+inf")]
    #[case::ann_nan("not::a::number::nan")]
    #[case::dec("127.0000000000")]
    #[case::ann_dec("woah::such::precision::-127.0000000e100")]
    #[case::timestamp("2023-05-01T12:37:43Z")]
    #[case::ann_timestamp("back::to::the::future::2099T")]
    #[case::symbol("'moon'")]
    #[case::ann_symbol("hello::world")]
    #[case::string("'''hello brown cow'''")]
    #[case::ann_string("poo::emoji::\"\\U0001F4A9\"")]
    #[case::clob("{{ '''<html></html>''' }}")]
    #[case::ann_clob("sgml::{{ '''<html></html>''' }}")]
    #[case::clob("{{ Blob }}")]
    #[case::ann_clob("this::is::real::{{ BLOB }}")]
    #[case::empty_sexp("()")]
    #[case::empty_list("[]")]
    #[case::empty_struct("{}")]
    #[case::ann_empty_sexp("a::()")]
    #[case::ann_empty_list("b::[]")]
    #[case::ann_empty_struct("c::{}")]
    #[case::struct_nested("{a:1, b:2, c:{d:3, e:{f:4, g:5, h:6}, j:7, k:8, l:{m:9}}}")]
    #[case::deeply_nested("([([([((a b c) d e), 1, 2] f g), 3, 4])])")]
    fn test_cases<S: AsRef<str>>(#[case] text: S) {}

    /// Very basic equivalence testing
    #[apply(test_cases)]
    fn test_element_equiv<S: AsRef<str>>(text: S) -> IonResult<()> {
        // read normally
        let expected = Element::read_all(text.as_ref())?;

        // read "through" a stream
        let stream: ReaderTokenStream<_> = ReaderBuilder::default().build(text.as_ref())?.into();
        let mut reader: TokenStreamReader<_> = stream.into();
        let actual = reader.read_all_elements()?;

        assert_eq!(expected.len(), actual.len());
        for (exp_elem, act_elem) in zip(expected.iter(), actual.iter()) {
            assert!(
                IonData::eq(exp_elem, act_elem),
                "{} != {}",
                exp_elem,
                act_elem
            );
        }
        Ok(())
    }

    const ION_TYPES: &[IonType] = &[
        IonType::Null,
        IonType::Bool,
        IonType::Int,
        IonType::Float,
        IonType::Decimal,
        IonType::Timestamp,
        IonType::Symbol,
        IonType::String,
        IonType::Clob,
        IonType::Blob,
        IonType::List,
        IonType::SExp,
        IonType::Struct,
    ];

    /// Just look at the top-level
    #[apply(test_cases)]
    fn test_top_level<S: AsRef<str>>(text: S) -> IonResult<()> {
        // read normally
        let expected = Element::read_all(text.as_ref())?;

        // read "through" a stream
        let stream: ReaderTokenStream<_> = ReaderBuilder::default().build(text.as_ref())?.into();
        let mut reader: TokenStreamReader<_> = stream.into();

        assert_eq!(None, reader.ion_type());
        assert_eq!(None, reader.parent_type());
        assert_eq!((1, 0), reader.ion_version());

        let mut count = 0;
        for top_level in &expected {
            count += 1;
            assert_eq!(0, reader.depth());
            assert!(reader.parent_type().is_none());
            match reader.next()? {
                StreamItem::Value(ion_type) => {
                    assert_eq!(top_level.ion_type(), ion_type);
                    assert_eq!(Some(ion_type), reader.ion_type());
                    assert!(!reader.is_null());
                    assert!(reader.read_null().is_err());
                    // let us permute the the Ion types to make sure the read surface
                    // works as expected
                    for other_type in ION_TYPES {
                        match (ion_type, *other_type) {
                            (my_type, test_type) if my_type == test_type => match my_type {
                                IonType::Null => {
                                    unreachable!("handled by null case");
                                }
                                IonType::Bool => {
                                    assert_eq!(top_level.as_bool().unwrap(), reader.read_bool()?)
                                }
                                IonType::Int => {
                                    assert_eq!(top_level.as_int().unwrap(), &reader.read_int()?)
                                }
                                IonType::Float => {
                                    let left = top_level.as_float().unwrap();
                                    let right = reader.read_f64()?;
                                    // TODO deal with f32
                                    assert!(ion_eq_f64(&left, &right));
                                }
                                IonType::Decimal => assert_eq!(
                                    *top_level.as_decimal().unwrap(),
                                    reader.read_decimal()?
                                ),
                                IonType::Timestamp => assert_eq!(
                                    *top_level.as_timestamp().unwrap(),
                                    reader.read_timestamp()?
                                ),
                                IonType::Symbol => assert_eq!(
                                    *top_level.as_symbol().unwrap(),
                                    reader.read_symbol()?
                                ),
                                IonType::String => assert_eq!(
                                    top_level.as_string().unwrap(),
                                    reader.read_string()?
                                ),
                                IonType::Clob => {
                                    assert_eq!(
                                        top_level.as_clob().unwrap(),
                                        reader.read_clob()?.as_slice()
                                    )
                                }
                                IonType::Blob => {
                                    assert_eq!(
                                        top_level.as_blob().unwrap(),
                                        reader.read_blob()?.as_slice()
                                    )
                                }
                                IonType::List | IonType::SExp | IonType::Struct => {
                                    reader.step_in()?;
                                    assert_eq!(1, reader.depth());
                                    assert_eq!(None, reader.ion_type());
                                    assert_eq!(Some(my_type), reader.parent_type());
                                    reader.step_out()?;
                                }
                            },
                            (_my_type, test_type) => match test_type {
                                IonType::Bool => assert!(reader.read_bool().is_err()),
                                IonType::Int => assert!(reader.read_int().is_err()),
                                IonType::Float => {
                                    assert!(reader.read_f32().is_err());
                                    assert!(reader.read_f64().is_err());
                                }
                                IonType::Decimal => assert!(reader.read_decimal().is_err()),
                                IonType::Timestamp => assert!(reader.read_timestamp().is_err()),
                                IonType::Symbol => assert!(reader.read_symbol().is_err()),
                                IonType::String => assert!(reader.read_string().is_err()),
                                IonType::Clob => assert!(reader.read_clob().is_err()),
                                IonType::Blob => assert!(reader.read_blob().is_err()),
                                IonType::Null | IonType::List | IonType::SExp | IonType::Struct => {
                                    // no checks
                                }
                            },
                        }
                    }
                }
                StreamItem::Null(ion_type) => {
                    assert_eq!(Some(ion_type), reader.ion_type());
                    assert!(reader.is_null());
                    assert_eq!(ion_type, reader.read_null()?);
                    assert!(reader.read_bool().is_err());
                    assert!(reader.read_int().is_err());
                    assert!(reader.read_f32().is_err());
                    assert!(reader.read_f64().is_err());
                    assert!(reader.read_decimal().is_err());
                    assert!(reader.read_timestamp().is_err());
                    assert!(reader.read_symbol().is_err());
                    assert!(reader.read_string().is_err());
                    assert!(reader.read_clob().is_err());
                    assert!(reader.read_blob().is_err());
                }
                StreamItem::Nothing => {
                    unreachable!("Should not see nothing!");
                }
            };
        }
        assert_eq!(expected.len(), count);
        Ok(())
    }
}
