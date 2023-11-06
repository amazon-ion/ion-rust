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

use std::cell::{Cell, UnsafeCell};
use std::fmt::{Debug, Formatter};
use std::iter::empty;

use bumpalo::Bump as BumpAllocator;

use sequence::{LazyExpandedList, LazyExpandedSExp};

use crate::element::iterators::SymbolsIterator;
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{LazyDecoder, LazyRawReader, LazyRawValue};
use crate::lazy::encoding::RawValueLiteral;
use crate::lazy::expanded::compiler::TemplateCompiler;
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, RawEExpression};
use crate::lazy::expanded::macro_table::MacroTable;
use crate::lazy::expanded::r#struct::LazyExpandedStruct;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{TemplateElement, TemplateMacro, TemplateValue};
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::str_ref::StrRef;
use crate::lazy::system_reader::{LazySystemReader, PendingLst};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
use crate::lazy::value::LazyValue;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, IonType, RawSymbolTokenRef, SymbolTable, Timestamp};

// All of these modules (and most of their types) are currently `pub` as the lazy reader is gated
// behind an experimental feature flag. We may constrain access to them in the future as the code
// stabilizes.
pub mod compiler;
pub mod e_expression;
pub mod macro_evaluator;
pub mod macro_table;
pub mod sequence;
pub mod r#struct;
pub mod template;

/// A collection of resources that can be used to encode or decode Ion values.
/// The `'top` lifetime associated with the [`EncodingContext`] reflects the fact that it can only
/// be used as long as the reader is positioned on the same top level expression (i.e. the symbol and
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
pub enum ExpandedStreamItem<'top, D: LazyDecoder> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawBinaryValue`](crate::lazy::binary::raw::value::LazyRawBinaryValue).
    Value(LazyExpandedValue<'top, D>),
    /// The end of the stream
    EndOfStream,
}

impl<'top, D: LazyDecoder> ExpandedStreamItem<'top, D> {
    /// Returns an error if this stream item is a version marker or the end of the stream.
    /// Otherwise, returns the lazy value it contains.
    fn expect_value(&self) -> IonResult<&LazyExpandedValue<'top, D>> {
        match self {
            ExpandedStreamItem::Value(value) => Ok(value),
            _ => IonResult::decoding_error(format!("Expected a value, but found a {:?}", self)),
        }
    }
}

/// A reader that evaluates macro invocations in the data stream and surfaces the resulting
/// raw values to the caller.
pub struct LazyExpandingReader<'data, D: LazyDecoder> {
    raw_reader: UnsafeCell<D::Reader<'data>>,
    // The expanding raw reader needs to be able to return multiple values from a single expression.
    // For example, if the raw reader encounters this e-expression:
    //
    //     (:values foo bar baz)
    //
    // then the expanding reader will need to yield a `foo` on the first call to `next()`, a
    // `bar` on the second, and a `baz` on the third.
    //
    // A natural way to model this in Rust would be to surface an `Expr` type to the user and allow
    // them to iterate over the values in its expansion. However, E-expressions are an encoding
    // detail; we do not want them to impact the application-layer APIs for reading an Ion stream.
    // As such, we need to instead store internal state that persists across an indefinite number
    // of calls to `next()`.
    //
    // The `EncodingContext` passed as an argument to each call to `next()` provides a bump allocator
    // whose storage is guaranteed to remain available as long as the reader remains on the same
    // top-level expression. When an e-expression is encountered in the data stream, we can store a
    // MacroEvaluator there until the reader advances to the next top-level expression. However,
    // there is not a lifetime we can use that meets our use case; `'data`--the duration of the
    // &[u8] from which we're reading--is too long, and `'top`--the duration of the current call
    // to `next()`--is too short.
    //
    // Instead, we can hold a pointer to the active MacroEvaluator in the bump allocator when one
    // is in use. Each time that `next()` is called with the `'top` lifetime, we will dereference
    // the pointer and coerce the result into a `&'top mut MacroEvaluator`, allowing the value it
    // yields that can be used until `next()` is called again.
    //
    // Because there is not valid lifetime we can use for the type `*mut MacroEvaluator<'lifetime>`,
    // in the field below, we cast away the pointer's type for the purposes of storage and then cast
    // it back at dereference time when a 'top lifetime is available.
    evaluator_ptr: Cell<Option<*mut ()>>,

    // XXX: The `UnsafeCell` wrappers around the fields below are a workaround for
    //      a limitation in rustc's borrow checker that prevents mutable references from being
    //      conditionally returned in a loop.
    //
    //      See: https://github.com/rust-lang/rust/issues/70255
    //
    //      There is a rustc fix for this limitation on the horizon.
    //
    //      See: https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/
    //
    //      Indeed, using the experimental `-Zpolonius` flag on the nightly compiler allows the
    //      version of this code without `unsafe` types to work. The alternative to the
    //      hack is wrapping each field in something like `RefCell`, which adds a small amount of
    //      overhead to each access. Given that this is the hottest path in the code and that a
    //      fix is inbound, I think this use of `unsafe` is warranted for now.
    //
    // Holds information found in symbol tables and encoding directives (TODO) that can be applied
    // to the encoding context the next time the reader is between top-level expressions.
    pending_lst: UnsafeCell<PendingLst>,
    // A bump allocator that is cleared between top-level expressions.
    allocator: UnsafeCell<BumpAllocator>,
    // TODO: Make the symbol and macro tables traits on `D` such that they can be configured
    //       statically. Then 1.0 types can use `Never` for the macro table.
    symbol_table: UnsafeCell<SymbolTable>,
    macro_table: UnsafeCell<MacroTable>,
}

impl<'data, D: LazyDecoder> LazyExpandingReader<'data, D> {
    pub(crate) fn new(raw_reader: D::Reader<'data>) -> Self {
        Self {
            raw_reader: raw_reader.into(),
            evaluator_ptr: None.into(),
            allocator: BumpAllocator::new().into(),
            pending_lst: PendingLst::new().into(),
            symbol_table: SymbolTable::new().into(),
            macro_table: MacroTable::new().into(),
        }
    }

    // TODO: This method is temporary. It will be removed when the ability to read 1.1 encoding
    //       directives from the input stream is available. Until then, template creation is manual.
    pub fn register_template(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        let template_macro: TemplateMacro =
            { TemplateCompiler::compile_from_text(self.context(), template_definition)? };

        let macro_table = self.macro_table.get_mut();
        macro_table.add_macro(template_macro)
    }

    fn context(&self) -> EncodingContext<'_> {
        // SAFETY: The only time that the macro table, symbol table, and allocator can be modified
        // is in the body of the method `between_top_level_expressions`. As long as nothing holds
        // a reference to the `EncodingContext` we create here when that method is running,
        // this is safe.
        unsafe {
            EncodingContext::new(
                &*self.macro_table.get(),
                &*self.symbol_table.get(),
                &*self.allocator.get(),
            )
        }
    }

    fn ptr_to_mut_ref<'a, T>(ptr: *mut ()) -> &'a mut T {
        let typed_ptr: *mut T = ptr.cast();
        unsafe { &mut *typed_ptr }
    }

    /// Dereferences a raw pointer storing the address of the active MacroEvaluator.
    fn ptr_to_evaluator<'top>(evaluator_ptr: *mut ()) -> &'top mut MacroEvaluator<'top, D> {
        Self::ptr_to_mut_ref(evaluator_ptr)
    }

    fn ref_as_ptr<T>(reference: &mut T) -> *mut () {
        let ptr: *mut T = reference;
        let untyped_ptr: *mut () = ptr.cast();
        untyped_ptr
    }

    /// Converts a mutable reference to the active MacroEvaluator into a raw, untyped pointer.
    fn evaluator_to_ptr(evaluator: &mut MacroEvaluator<'_, D>) -> *mut () {
        Self::ref_as_ptr(evaluator)
    }

    /// Updates the encoding context with the information stored in the `PendingLst`.
    // TODO: This only works on Ion 1.0 symbol tables for now, hence the name `PendingLst`
    fn apply_pending_lst(pending_lst: &mut PendingLst, symbol_table: &mut SymbolTable) {
        // If the symbol table's `imports` field had a value of `$ion_symbol_table`, then we're
        // appending the symbols it defined to the end of our existing local symbol table.
        // Otherwise, we need to clear the existing table before appending the new symbols.
        if !pending_lst.is_lst_append {
            // We're setting the symbols list, not appending to it.
            symbol_table.reset();
        }
        // `drain()` empties the pending symbols list
        for symbol in pending_lst.symbols.drain(..) {
            symbol_table.intern_or_add_placeholder(symbol);
        }
        pending_lst.is_lst_append = false;
        pending_lst.has_changes = false;
    }

    /// Inspects a `LazyExpandedValue` to determine whether it is a symbol table or an
    /// application-level value. Returns it as the appropriate variant of `SystemStreamItem`.
    fn interpret_value<'top>(
        &self,
        value: LazyExpandedValue<'top, D>,
    ) -> IonResult<SystemStreamItem<'top, D>> {
        // If this value is a symbol table...
        if LazySystemReader::is_symbol_table_struct(&value)? {
            // ...traverse it and record any new symbols in our `pending_lst`.
            let pending_lst = unsafe { &mut *self.pending_lst.get() };
            LazySystemReader::process_symbol_table(pending_lst, &value)?;
            pending_lst.has_changes = true;
            let lazy_struct = LazyStruct {
                expanded_struct: value.read()?.expect_struct().unwrap(),
            };
            return Ok(SystemStreamItem::SymbolTable(lazy_struct));
        }
        // Otherwise, it's an application value.
        let lazy_value = LazyValue::new(value);
        return Ok(SystemStreamItem::Value(lazy_value));
    }

    /// This method is invoked just before the reader begins reading the next top-level expression
    /// from the data stream. It is NOT invoked between multiple top level _values_ coming from a
    /// single expression.
    ///
    /// This is the reader's opportunity to make any pending changes to the encoding context.
    fn between_top_level_expressions(&self) {
        // SAFETY: This is the only place where we modify the encoding context. Take care not to
        //         alias the allocator, symbol table, or macro table in this scope.

        // We're going to clear the bump allocator, so drop our reference to the evaluator that
        // lives there.
        self.evaluator_ptr.set(None);

        // Clear the allocator.
        let allocator: &mut BumpAllocator = unsafe { &mut *self.allocator.get() };
        allocator.reset();

        // If the pending LST has changes to apply, do so.
        let pending_lst: &mut PendingLst = unsafe { &mut *self.pending_lst.get() };
        if pending_lst.has_changes {
            let symbol_table: &mut SymbolTable = unsafe { &mut *self.symbol_table.get() };
            Self::apply_pending_lst(pending_lst, symbol_table);
        }
    }

    /// Returns the next application-level value.
    ///
    /// This method will consume and process as many system-level values as possible until it
    /// encounters an application-level value or the end of the stream.
    pub fn next_value(&mut self) -> IonResult<Option<LazyValue<D>>> {
        loop {
            match self.next_item()? {
                SystemStreamItem::VersionMarker(_, _) => {
                    // TODO: Handle version changes 1.0 <-> 1.1
                }
                SystemStreamItem::SymbolTable(_) => {
                    // The symbol table is processed by `next_item` before it is returned. There's
                    // nothing to be done here.
                }
                SystemStreamItem::Value(value) => return Ok(Some(value)),
                SystemStreamItem::EndOfStream => return Ok(None),
            }
        }
    }

    /// Returns the next [`SystemStreamItem`] either by continuing to evaluate a macro invocation
    /// in progress or by pulling another expression from the input stream.
    pub fn next_item<'top>(&'top self) -> IonResult<SystemStreamItem<'top, D>>
    where
        'data: 'top,
    {
        // If there's already an active macro evaluator, that means the reader is still in the process
        // of expanding a macro invocation it previously encountered. See if it has a value to give us.
        if let Some(stream_item) = self.next_from_evaluator()? {
            return Ok(stream_item);
        }

        // Otherwise, we're now between top level expressions. Take this opportunity to apply any
        // pending changes to the encoding context and reset state as needed.
        self.between_top_level_expressions();

        // See if the raw reader can get another expression from the input stream. It's possible
        // to find an expression that yields no values (for example: `(:void)`), so we perform this
        // step in a loop until we get a value or end-of-stream.

        let allocator: &BumpAllocator = unsafe { &*self.allocator.get() };
        loop {
            // Pull another top-level expression from the input stream if one is available.
            use crate::lazy::raw_stream_item::RawStreamItem::*;
            let raw_reader = unsafe { &mut *self.raw_reader.get() };
            match raw_reader.next(allocator)? {
                VersionMarker(major, minor) => {
                    return Ok(SystemStreamItem::VersionMarker(major, minor))
                }
                // We got our value; return it.
                Value(raw_value) => {
                    let value = LazyExpandedValue {
                        source: ExpandedValueSource::ValueLiteral(raw_value),
                        context: self.context(),
                    };
                    return self.interpret_value(value);
                }
                // It's another macro invocation, we'll start evaluating it.
                EExpression(e_exp) => {
                    let context = self.context();
                    let resolved_e_exp = e_exp.resolve(context)?;
                    // Get the current evaluator or make a new one
                    let evaluator = match self.evaluator_ptr.get() {
                        // If there's already an evaluator, dereference the pointer.
                        Some(ptr) => Self::ptr_to_evaluator(ptr),
                        // If there's not, make a new one.
                        None => context
                            .allocator
                            // E-expressions always have an empty environment
                            .alloc_with(move || MacroEvaluator::new(context, Environment::empty())),
                    };
                    // Push the invocation onto the evaluation stack.
                    evaluator.push(context, resolved_e_exp)?;
                    self.evaluator_ptr
                        .set(Some(Self::evaluator_to_ptr(evaluator)));

                    // Try to get a value by starting to evaluate the e-expression.
                    if let Some(value) = self.next_from_evaluator()? {
                        // If we get a value, return it.
                        return Ok(value);
                    } else {
                        // If the expression was equivalent to `(:void)`, return to the top of
                        // the loop and get the next expression.
                        continue;
                    }
                }
                EndOfStream => return Ok(SystemStreamItem::EndOfStream),
            };
        }
    }

    /// If there is not an evaluation in process, returns `Ok(None)`.
    /// If there is an evaluation in process but it does not yield another value, returns `Ok(None)`.
    /// If there is an evaluation in process and it yields another value, returns `Ok(Some(value))`.
    /// Otherwise, returns `Err`.
    fn next_from_evaluator(&self) -> IonResult<Option<SystemStreamItem<D>>> {
        let evaluator_ptr = match self.evaluator_ptr.get() {
            // There's not currently an evaluator.
            None => return Ok(None),
            // There's an evaluator in the process of expanding a macro.
            Some(ptr) => ptr,
        };
        let evaluator = Self::ptr_to_evaluator(evaluator_ptr);

        match evaluator.next(self.context()) {
            Ok(Some(value)) => {
                // See if this value was a symbol table that needs interpretation.
                self.interpret_value(value).map(Some)
            }
            Ok(None) => {
                // While the evaluator had macros in its stack, they did not produce any more
                // values. The stack is now empty.
                Ok(None)
            }
            Err(e) => Err(e),
        }
    }
}

/// The source of data backing a [`LazyExpandedValue`].
#[derive(Copy, Clone)]
pub enum ExpandedValueSource<'top, D: LazyDecoder> {
    /// This value was a literal in the input stream.
    ValueLiteral(D::Value<'top>),
    /// This value was part of a template definition.
    Template(Environment<'top, D>, TemplateElement<'top>),
    /// This value was the computed result of a macro invocation like `(:make_string `...)`.
    Constructed(
        // TODO: Make this an associated type on the LazyDecoder trait so 1.0 types can set
        //       it to `Never` and the compiler can eliminate this code path where applicable.
        // Constructed data stored in the bump allocator. Holding references instead of the data
        // itself allows this type (and those that contain it) to impl `Copy`.
        &'top [&'top str],               // Annotations (if any)
        &'top ExpandedValueRef<'top, D>, // Value
    ),
}

impl<'top, D: LazyDecoder> Debug for ExpandedValueSource<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            ExpandedValueSource::ValueLiteral(v) => write!(f, "{v:?}"),
            ExpandedValueSource::Template(_, template_element) => {
                write!(f, "{:?}", template_element.value())
            }
            ExpandedValueSource::Constructed(_, value) => write!(f, "{value:?}"),
        }
    }
}

// Converts the raw value literal types associated with each format decoder (e.g. LazyRawTextValue_1_1)
// into an ExpandedValueSource.
impl<'top, V: RawValueLiteral, D: LazyDecoder<Value<'top> = V>> From<V>
    for ExpandedValueSource<'top, D>
{
    fn from(value: V) -> Self {
        ExpandedValueSource::ValueLiteral(value)
    }
}

/// A value produced by expanding the 'raw' view of the input data.
#[derive(Copy, Clone)]
pub struct LazyExpandedValue<'top, D: LazyDecoder> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) source: ExpandedValueSource<'top, D>,
}

impl<'top, D: LazyDecoder> Debug for LazyExpandedValue<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.source)
    }
}

impl<'top, D: LazyDecoder> LazyExpandedValue<'top, D> {
    pub(crate) fn from_value(context: EncodingContext<'top>, value: D::Value<'top>) -> Self {
        Self {
            context,
            source: ExpandedValueSource::ValueLiteral(value),
        }
    }

    pub(crate) fn from_template(
        context: EncodingContext<'top>,
        environment: Environment<'top, D>,
        element: TemplateElement<'top>,
    ) -> Self {
        Self {
            context,
            source: ExpandedValueSource::Template(environment, element),
        }
    }

    pub fn ion_type(&self) -> IonType {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.ion_type(),
            Template(_, element) => element.value().ion_type(),
            Constructed(_annotations, value) => value.ion_type(),
        }
    }

    pub fn is_null(&self) -> bool {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.is_null(),
            Template(_, element) => element.value().is_null(),
            Constructed(_, value) => {
                matches!(value, ExpandedValueRef::Null(_))
            }
        }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => ExpandedAnnotationsIterator::new(
                ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            ),
            Template(_, element) => ExpandedAnnotationsIterator::new(
                ExpandedAnnotationsSource::Template(SymbolsIterator::new(element.annotations())),
            ),
            Constructed(_annotations, _value) => {
                // TODO: iterate over constructed annotations
                // For now we return an empty iterator
                ExpandedAnnotationsIterator::new(ExpandedAnnotationsSource::Constructed(Box::new(
                    empty(),
                )))
            }
        }
    }

    pub fn read(&self) -> IonResult<ExpandedValueRef<'top, D>> {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => Ok(ExpandedValueRef::from_raw(self.context, value.read()?)),
            Template(environment, element) => Ok(ExpandedValueRef::from_template(
                self.context,
                *environment,
                element,
            )),
            Constructed(_annotations, value) => Ok((*value).clone()),
        }
    }

    pub fn context(&self) -> EncodingContext<'top> {
        self.context
    }
}

impl<'top, D: LazyDecoder> From<LazyExpandedValue<'top, D>> for LazyValue<'top, D> {
    fn from(expanded_value: LazyExpandedValue<'top, D>) -> Self {
        LazyValue { expanded_value }
    }
}

impl<'top, D: LazyDecoder> From<LazyExpandedStruct<'top, D>> for LazyStruct<'top, D> {
    fn from(expanded_struct: LazyExpandedStruct<'top, D>) -> Self {
        LazyStruct { expanded_struct }
    }
}

impl<'top, D: LazyDecoder> From<LazyExpandedSExp<'top, D>> for LazySExp<'top, D> {
    fn from(expanded_sexp: LazyExpandedSExp<'top, D>) -> Self {
        LazySExp { expanded_sexp }
    }
}

impl<'top, D: LazyDecoder> From<LazyExpandedList<'top, D>> for LazyList<'top, D> {
    fn from(expanded_list: LazyExpandedList<'top, D>) -> Self {
        LazyList { expanded_list }
    }
}

pub enum ExpandedAnnotationsSource<'top, D: LazyDecoder> {
    ValueLiteral(D::AnnotationsIterator<'top>),
    Template(SymbolsIterator<'top>),
    // TODO: This is a placeholder impl and always returns an empty iterator
    Constructed(Box<dyn Iterator<Item = IonResult<RawSymbolTokenRef<'top>>> + 'top>),
}

pub struct ExpandedAnnotationsIterator<'top, D: LazyDecoder> {
    source: ExpandedAnnotationsSource<'top, D>,
}

impl<'top, D: LazyDecoder> ExpandedAnnotationsIterator<'top, D> {
    pub fn new(source: ExpandedAnnotationsSource<'top, D>) -> Self {
        Self { source }
    }
}

impl<'top, D: LazyDecoder> Iterator for ExpandedAnnotationsIterator<'top, D> {
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
pub enum ExpandedValueRef<'top, D: LazyDecoder> {
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
    SExp(LazyExpandedSExp<'top, D>),
    List(LazyExpandedList<'top, D>),
    Struct(LazyExpandedStruct<'top, D>),
}

impl<'top, D: LazyDecoder> PartialEq for ExpandedValueRef<'top, D> {
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
            // The container variants hold lazy references to the containers themselves.
            // We cannot compare their equality without recursively reading those containers,
            // which introduces many opportunities to encounter an error that this method cannot
            // surface. Because this is `PartialEq`, we have the option of returning `false` for
            // values that cannot be compared to one another.
            _ => false,
        }
    }
}

impl<'top, D: LazyDecoder> ExpandedValueRef<'top, D> {
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

    pub fn expect_list(self) -> IonResult<LazyExpandedList<'top, D>> {
        if let ExpandedValueRef::List(s) = self {
            Ok(s)
        } else {
            self.expected("list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazyExpandedSExp<'top, D>> {
        if let ExpandedValueRef::SExp(s) = self {
            Ok(s)
        } else {
            self.expected("sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyExpandedStruct<'top, D>> {
        if let ExpandedValueRef::Struct(s) = self {
            Ok(s)
        } else {
            self.expected("struct")
        }
    }

    fn from_raw(context: EncodingContext<'top>, value: RawValueRef<'top, D>) -> Self {
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

impl<'top, D: LazyDecoder> Debug for ExpandedValueRef<'top, D> {
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

impl<'top, D: LazyDecoder> ExpandedValueRef<'top, D> {
    fn from_template(
        context: EncodingContext<'top>,
        environment: Environment<'top, D>,
        element: &TemplateElement<'top>,
    ) -> Self {
        use TemplateValue::*;
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
                environment,
                element.template(),
                element.annotations_range(),
                *s,
            )),
            SExp(s) => ExpandedValueRef::SExp(LazyExpandedSExp::from_template(
                context,
                environment,
                element.template(),
                element.annotations_range(),
                *s,
            )),
            Struct(s, index) => ExpandedValueRef::Struct(LazyExpandedStruct::from_template(
                context,
                environment,
                element.template(),
                element.annotations_range(),
                *s,
                index,
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
