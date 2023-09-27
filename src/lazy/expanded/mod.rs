//! A view of the Ion data with all e-expressions lazily expanded.
//!
//! The types defined in this module each wrap their corresponding type from the "raw" view of the
//! data, replacing the word `Raw` with the word `Expanded` in the type name.
//!
//! The expanded types expose largely the same API, with some key differences:
//!   1. Most method invocations require an [`EncodingContext`] to be specified, giving the
//!      evaluator access to the necessary macro definitions and the symbol table.
//!   2. All macro invocations encountered in the raw layer are fully expanded, meaning that
//!      values surfaced by calls to `next()` on readers/iterators may be the result of macro
//!      evaluation. Said differently: not every value returned by `next()` has a corresponding
//!      literal in the input stream.
//!
//! Note that symbol tokens MAY be resolved in the process of evaluating a macro, but where possible
//! they will remain unresolved. For example, this e-expression:
//! ```ion_1_1
//!     (:repeat 3 $4)
//! ```
//! would expand to this stream of raw values:
//! ```ion_1_1
//!     $4 $4 $4
//! ```
//! while this e-expression:
//! ```ion_1_1
//!     `(:make_string "What's your " $4 "?")`
//! ```
//! would resolve the `$4` in the process of evaluating `make_string`, expanding to:
//! ```ion_1_1
//!     `"What's your name?"`
//! ```
//!
//! Leaving symbol tokens unresolved is an optimization; annotations, field names, and symbol values
//! that are ignored by the reader do not incur the cost of symbol table resolution.

use std::fmt::{Debug, Formatter};
use std::iter::empty;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;

use sequence::{LazyExpandedList, LazyExpandedSExp};

use crate::element::iterators::SymbolsIterator;
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{LazyDecoder, LazyRawReader, LazyRawValue};
use crate::lazy::encoding::RawValueLiteral;
use crate::lazy::expanded::macro_evaluator::EExpEvaluator;
use crate::lazy::expanded::macro_table::MacroTable;
use crate::lazy::expanded::r#struct::LazyExpandedStruct;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::str_ref::StrRef;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::{
    Decimal, Element, Int, IonResult, IonType, RawSymbolTokenRef, SymbolTable, Timestamp, Value,
};

// All of these modules (and most of their types) are currently `pub` as the lazy reader is gated
// behind an experimental feature flag. We may constrain access to them in the future as the code
// stabilizes.
pub mod e_expression;
pub mod macro_evaluator;
pub mod macro_table;
pub mod sequence;
pub mod stack;
pub mod r#struct;
pub mod tdl_macro;
pub mod template;

/// A collection of resources that can be used to encode or decode Ion values.
/// The `'top` lifetime associated with the [`EncodingContext`] reflects the fact that it can only
/// be used as long as the reader is positioned on the same top level value (i.e. the symbol and
/// macro tables are guaranteed not to change).
//  It should be possible to loosen this definition of `'top` to include several top level values
//  as long as the macro and symbol tables do not change between them, though this would require
//  carefully designing the API to emphasize that the sequence of values is either the set that
//  happens to be available in the buffer OR the set that leads up to the next encoding directive.
//  The value proposition of being able to lazily explore multiple top level values concurrently
//  would need to be proved out first.
#[derive(Copy, Clone, Debug)]
pub struct EncodingContext<'top> {
    pub(crate) macro_table: &'top MacroTable,
    pub(crate) symbol_table: &'top SymbolTable,
    pub(crate) allocator: &'top BumpAllocator,
}

impl<'top> EncodingContext<'top> {
    pub fn new(
        macro_table: &'top MacroTable,
        symbol_table: &'top SymbolTable,
        allocator: &'top BumpAllocator,
    ) -> Self {
        Self {
            macro_table,
            symbol_table,
            allocator,
        }
    }
}

#[derive(Debug)]
/// Stream components emitted by a LazyExpandingReader. These items may be encoded directly in the
/// stream, or may have been produced by the evaluation of an encoding expression (e-expression).
pub enum ExpandedStreamItem<'top, 'data, D: LazyDecoder<'data>> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawBinaryValue`](crate::lazy::binary::raw::value::LazyRawBinaryValue).
    Value(LazyExpandedValue<'top, 'data, D>),
    /// The end of the stream
    EndOfStream,
}

impl<'top, 'data, D: LazyDecoder<'data>> ExpandedStreamItem<'top, 'data, D> {
    /// Returns an error if this stream item is a version marker or the end of the stream.
    /// Otherwise, returns the lazy value it contains.
    fn expect_value(&self) -> IonResult<&LazyExpandedValue<'top, 'data, D>> {
        match self {
            ExpandedStreamItem::Value(value) => Ok(value),
            _ => IonResult::decoding_error(format!("Expected a value, but found a {:?}", self)),
        }
    }
}

/// A reader that evaluates macro invocations in the data stream and surfaces the resulting
/// raw values to the caller.
pub struct LazyExpandingReader<'data, D: LazyDecoder<'data>> {
    raw_reader: D::Reader,
    evaluator: EExpEvaluator<'data, D>,
}

impl<'data, D: LazyDecoder<'data>> LazyExpandingReader<'data, D> {
    pub(crate) fn new(raw_reader: D::Reader) -> Self {
        Self {
            raw_reader,
            evaluator: EExpEvaluator::new(),
        }
    }

    /// Returns the next [`ExpandedStreamItem`] either by continuing to evaluate a macro invocation
    /// in progress or by pulling a value from the input stream.
    pub fn next<'top>(
        &mut self,
        context: EncodingContext<'top>,
    ) -> IonResult<ExpandedStreamItem<'top, 'data, D>>
    where
        'data: 'top,
    {
        loop {
            if self.evaluator.stack_depth() > 0 {
                // If the evaluator still has macro expansions in its stack, we need to give it the
                // opportunity to produce the next value.
                match self.evaluator.next(context, 0) {
                    Ok(Some(value)) => return Ok(ExpandedStreamItem::Value(value)),
                    Ok(None) => {
                        // While the evaluator had macros in its stack, they did not produce any more
                        // values. The stack is now empty.
                    }
                    Err(e) => return Err(e),
                };
            }

            // If we reach this point, the evaluator's macro stack is empty. We'll pull another
            // expression from the input stream.
            use RawStreamItem::*;
            let expanded_item = match self.raw_reader.next()? {
                VersionMarker(major, minor) => ExpandedStreamItem::VersionMarker(major, minor),
                // We got our value; return it.
                Value(raw_value) => ExpandedStreamItem::Value(LazyExpandedValue {
                    source: ExpandedValueSource::ValueLiteral(raw_value),
                    context,
                }),
                // It's another macro invocation, we'll start evaluating it.
                EExpression(e_exp) => {
                    // Push the invocation onto the evaluation stack.
                    self.evaluator.push(context, e_exp)?;
                    // Return to the top of the loop to pull the next value (if any) from the evaluator.
                    continue;
                }
                EndOfStream => ExpandedStreamItem::EndOfStream,
            };
            return Ok(expanded_item);
        }
    }
}

/// The source of data backing a [`LazyExpandedValue`].
#[derive(Debug, Clone)]
pub enum ExpandedValueSource<'top, 'data, D: LazyDecoder<'data>> {
    /// This value was a literal in the input stream.
    ValueLiteral(D::Value),
    /// This value was part of a template definition.
    Template(&'top Element),
    /// This value was the computed result of a macro invocation like `(:make_string ...)`.
    Constructed(
        // TODO: Make this an associated type on the LazyDecoder trait so 1.0 types can set
        //       it to `Never` and the compiler can eliminate this code path where applicable.
        (
            // A collection of bump-allocated annotation strings
            BumpVec<'top, &'top str>,
            ExpandedValueRef<'top, 'data, D>,
        ),
    ),
}

// Converts the raw value literal types associated with each format decoder (e.g. LazyRawTextValue_1_1)
// into an ExpandedValueSource.
impl<'top, 'data, V: RawValueLiteral, D: LazyDecoder<'data, Value = V>> From<V>
    for ExpandedValueSource<'top, 'data, D>
{
    fn from(value: V) -> Self {
        ExpandedValueSource::ValueLiteral(value)
    }
}

// Converts an Element from the body of a template into an ExpandedValueSource.
impl<'top, 'data, D: LazyDecoder<'data>> From<&'top Element>
    for ExpandedValueSource<'top, 'data, D>
{
    fn from(element: &'top Element) -> Self {
        ExpandedValueSource::Template(element)
    }
}

/// A value produced by expanding the 'raw' view of the input data.
#[derive(Clone)]
pub struct LazyExpandedValue<'top, 'data, D: LazyDecoder<'data>> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) source: ExpandedValueSource<'top, 'data, D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> Debug for LazyExpandedValue<'top, 'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.source)
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> LazyExpandedValue<'top, 'data, D> {
    pub(crate) fn from_value(context: EncodingContext<'top>, value: D::Value) -> Self {
        Self {
            context,
            source: ExpandedValueSource::ValueLiteral(value),
        }
    }

    pub(crate) fn from_template(context: EncodingContext<'top>, element: &'top Element) -> Self {
        Self {
            context,
            source: ExpandedValueSource::Template(element),
        }
    }

    pub fn ion_type(&self) -> IonType {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.ion_type(),
            Template(element) => element.ion_type(),
            Constructed((_annotations, value)) => value.ion_type(),
        }
    }

    pub fn is_null(&self) -> bool {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.is_null(),
            Template(element) => element.is_null(),
            Constructed((_annotations, value)) => {
                matches!(value, ExpandedValueRef::Null(_))
            }
        }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, 'data, D> {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => ExpandedAnnotationsIterator::new(
                ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            ),
            Template(element) => ExpandedAnnotationsIterator::new(
                ExpandedAnnotationsSource::Template(element.annotations().iter()),
            ),
            Constructed((_annotations, _value)) => {
                // TODO: iterate over constructed annotations
                // For now we return an empty iterator
                ExpandedAnnotationsIterator::new(ExpandedAnnotationsSource::Constructed(Box::new(
                    empty(),
                )))
            }
        }
    }

    pub fn read(&self) -> IonResult<ExpandedValueRef<'top, 'data, D>> {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => Ok(ExpandedValueRef::from_raw(self.context, value.read()?)),
            Template(element) => Ok(ExpandedValueRef::from_template(element, self.context)),
            Constructed((_annotations, value)) => Ok((*value).clone()),
        }
    }

    pub fn context(&self) -> EncodingContext<'top> {
        self.context
    }
}

pub enum ExpandedAnnotationsSource<'top, 'data, D: LazyDecoder<'data>> {
    ValueLiteral(D::AnnotationsIterator),
    Template(SymbolsIterator<'top>),
    // TODO: This is a placeholder impl and always returns an empty iterator
    Constructed(Box<dyn Iterator<Item = IonResult<RawSymbolTokenRef<'top>>> + 'top>),
}

pub struct ExpandedAnnotationsIterator<'top, 'data, D: LazyDecoder<'data>> {
    source: ExpandedAnnotationsSource<'top, 'data, D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> ExpandedAnnotationsIterator<'top, 'data, D> {
    pub fn new(source: ExpandedAnnotationsSource<'top, 'data, D>) -> Self {
        Self { source }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> Iterator
    for ExpandedAnnotationsIterator<'top, 'data, D>
{
    type Item = IonResult<RawSymbolTokenRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        use ExpandedAnnotationsSource::*;
        match &mut self.source {
            ValueLiteral(value_annotations_iter) => value_annotations_iter.next(),
            Template(element_annotations_iter) => element_annotations_iter
                .next()
                .map(|symbol| Ok(symbol.as_raw_symbol_token_ref())),
            Constructed(iter) => iter.next(),
        }
    }
}

// TODO: This type does not implement `Copy` because some of its variants can own heap resources.
//       (Specifically: Int, Decimal, String, Symbol, Blob, Clob.) If plumb the bump allocator all
//       the way down to the raw readers, then the situations that require allocation can
//       hold a 'top reference to a bump allocation instead of a static reference to a heap allocation.
//       This will enable us to remove several calls to `clone()`, which can be much slower than copies.
#[derive(Clone)]
pub enum ExpandedValueRef<'top, 'data, D: LazyDecoder<'data>> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(StrRef<'top>),
    Symbol(RawSymbolTokenRef<'top>),
    Blob(BytesRef<'top>),
    Clob(BytesRef<'top>),
    SExp(LazyExpandedSExp<'top, 'data, D>),
    List(LazyExpandedList<'top, 'data, D>),
    Struct(LazyExpandedStruct<'top, 'data, D>),
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> PartialEq for ExpandedValueRef<'top, 'data, D> {
    fn eq(&self, other: &Self) -> bool {
        use ExpandedValueRef::*;
        match (self, other) {
            (Null(i1), Null(i2)) => i1 == i2,
            (Bool(b1), Bool(b2)) => b1 == b2,
            (Int(i1), Int(i2)) => i1 == i2,
            (Float(i1), Float(i2)) => i1 == i2,
            (Decimal(i1), Decimal(i2)) => i1 == i2,
            (Timestamp(i1), Timestamp(i2)) => i1 == i2,
            (String(i1), String(i2)) => i1 == i2,
            (Symbol(i1), Symbol(i2)) => i1 == i2,
            (Blob(i1), Blob(i2)) => i1 == i2,
            (Clob(i1), Clob(i2)) => i1 == i2,
            _ => false,
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> ExpandedValueRef<'top, 'data, D> {
    fn expected<T>(self, expected_name: &str) -> IonResult<T> {
        IonResult::decoding_error(format!(
            "expected a(n) {} but found a {:?}",
            expected_name, self
        ))
    }

    pub fn expect_null(self) -> IonResult<IonType> {
        if let ExpandedValueRef::Null(ion_type) = self {
            Ok(ion_type)
        } else {
            self.expected("null")
        }
    }

    pub fn expect_bool(self) -> IonResult<bool> {
        if let ExpandedValueRef::Bool(b) = self {
            Ok(b)
        } else {
            self.expected("bool")
        }
    }

    pub fn expect_int(self) -> IonResult<Int> {
        if let ExpandedValueRef::Int(i) = self {
            Ok(i)
        } else {
            self.expected("int")
        }
    }

    pub fn expect_i64(self) -> IonResult<i64> {
        if let ExpandedValueRef::Int(i) = self {
            i.expect_i64()
        } else {
            self.expected("i64 (int)")
        }
    }

    pub fn expect_float(self) -> IonResult<f64> {
        if let ExpandedValueRef::Float(f) = self {
            Ok(f)
        } else {
            self.expected("float")
        }
    }

    pub fn expect_decimal(self) -> IonResult<Decimal> {
        if let ExpandedValueRef::Decimal(d) = self {
            Ok(d)
        } else {
            self.expected("decimal")
        }
    }

    pub fn expect_timestamp(self) -> IonResult<Timestamp> {
        if let ExpandedValueRef::Timestamp(t) = self {
            Ok(t)
        } else {
            self.expected("timestamp")
        }
    }

    pub fn expect_string(self) -> IonResult<StrRef<'top>> {
        if let ExpandedValueRef::String(s) = self {
            Ok(s)
        } else {
            self.expected("string")
        }
    }

    pub fn expect_symbol(self) -> IonResult<RawSymbolTokenRef<'top>> {
        if let ExpandedValueRef::Symbol(s) = self {
            Ok(s.clone())
        } else {
            self.expected("symbol")
        }
    }

    pub fn expect_blob(self) -> IonResult<BytesRef<'top>> {
        if let ExpandedValueRef::Blob(b) = self {
            Ok(b)
        } else {
            self.expected("blob")
        }
    }

    pub fn expect_clob(self) -> IonResult<BytesRef<'top>> {
        if let ExpandedValueRef::Clob(c) = self {
            Ok(c)
        } else {
            self.expected("clob")
        }
    }

    pub fn expect_list(self) -> IonResult<LazyExpandedList<'top, 'data, D>> {
        if let ExpandedValueRef::List(s) = self {
            Ok(s)
        } else {
            self.expected("list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazyExpandedSExp<'top, 'data, D>> {
        if let ExpandedValueRef::SExp(s) = self {
            Ok(s)
        } else {
            self.expected("sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyExpandedStruct<'top, 'data, D>> {
        if let ExpandedValueRef::Struct(s) = self {
            Ok(s)
        } else {
            self.expected("struct")
        }
    }

    fn from_raw(context: EncodingContext<'top>, value: RawValueRef<'data, D>) -> Self {
        use RawValueRef::*;
        match value {
            Null(ion_type) => ExpandedValueRef::Null(ion_type),
            Bool(b) => ExpandedValueRef::Bool(b),
            Int(i) => ExpandedValueRef::Int(i),
            Float(f) => ExpandedValueRef::Float(f),
            Decimal(d) => ExpandedValueRef::Decimal(d),
            Timestamp(t) => ExpandedValueRef::Timestamp(t),
            String(s) => ExpandedValueRef::String(s),
            Symbol(s) => ExpandedValueRef::Symbol(s),
            Blob(b) => ExpandedValueRef::Blob(b),
            Clob(c) => ExpandedValueRef::Clob(c),
            SExp(s) => ExpandedValueRef::SExp(LazyExpandedSExp::from_literal(context, s)),
            List(l) => ExpandedValueRef::List(LazyExpandedList::from_literal(context, l)),
            Struct(s) => ExpandedValueRef::Struct(LazyExpandedStruct::from_literal(context, s)),
        }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> Debug for ExpandedValueRef<'top, 'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ExpandedValueRef::*;
        match self {
            Null(ion_type) => write!(f, "null.{}", ion_type),
            Bool(b) => write!(f, "{}", b),
            Int(i) => write!(f, "{}", i),
            Float(float) => write!(f, "{}", float),
            Decimal(d) => write!(f, "{}", d),
            Timestamp(t) => write!(f, "{}", t),
            String(s) => write!(f, "{}", s),
            Symbol(s) => write!(f, "{:?}", s),
            Blob(b) => write!(f, "blob ({} bytes)", b.len()),
            Clob(c) => write!(f, "clob ({} bytes)", c.len()),
            // TODO: Debug impls for LazyExpandedRaw[ContainerType]
            SExp(_s) => write!(f, "<sexp>"),
            List(_l) => write!(f, "<list>"),
            Struct(_s) => write!(f, "<struct>"),
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> ExpandedValueRef<'top, 'data, D> {
    fn from_template(element: &'top Element, context: EncodingContext<'top>) -> Self {
        use Value::*;
        match element.value() {
            Null(ion_type) => ExpandedValueRef::Null(*ion_type),
            Bool(b) => ExpandedValueRef::Bool(*b),
            Int(i) => ExpandedValueRef::Int(i.clone()),
            Float(f) => ExpandedValueRef::Float(*f),
            Decimal(d) => ExpandedValueRef::Decimal(d.clone()),
            Timestamp(t) => ExpandedValueRef::Timestamp(t.clone()),
            String(s) => ExpandedValueRef::String(StrRef::from(s.text())),
            Symbol(s) => ExpandedValueRef::Symbol(s.as_raw_symbol_token_ref()),
            Blob(b) => ExpandedValueRef::Blob(BytesRef::from(b.as_ref())),
            Clob(c) => ExpandedValueRef::Clob(BytesRef::from(c.as_ref())),
            List(s) => ExpandedValueRef::List(LazyExpandedList::from_template(
                context,
                element.annotations(),
                s,
            )),
            SExp(s) => ExpandedValueRef::SExp(LazyExpandedSExp::from_template(
                context,
                element.annotations(),
                s,
            )),
            Struct(s) => ExpandedValueRef::Struct(LazyExpandedStruct::from_template(
                context,
                element.annotations(),
                s,
            )),
        }
    }

    fn ion_type(&self) -> IonType {
        use ExpandedValueRef::*;
        match self {
            Null(ion_type) => *ion_type,
            Bool(_) => IonType::Bool,
            Int(_) => IonType::Int,
            Float(_) => IonType::Float,
            Decimal(_) => IonType::Decimal,
            Timestamp(_) => IonType::Timestamp,
            String(_) => IonType::String,
            Symbol(_) => IonType::Symbol,
            Blob(_) => IonType::Blob,
            Clob(_) => IonType::Clob,
            SExp(_) => IonType::SExp,
            List(_) => IonType::List,
            Struct(_) => IonType::Struct,
        }
    }
}
