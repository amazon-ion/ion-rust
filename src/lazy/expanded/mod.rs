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

use bumpalo::Bump as BumpAllocator;

use sequence::{LazyExpandedList, LazyExpandedSExp};

use crate::element::iterators::SymbolsIterator;
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{LazyDecoder, LazyRawReader, LazyRawValue};
use crate::lazy::encoding::RawValueLiteral;
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, RawEExpression};
use crate::lazy::expanded::macro_table::MacroTable;
use crate::lazy::expanded::r#struct::LazyExpandedStruct;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{TemplateElement, TemplateValue};
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::str_ref::StrRef;
use crate::lazy::system_reader::{LazySystemReader, PendingLst};
use crate::lazy::system_stream_item::SystemStreamItem;
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
    evaluator_ptr: Option<*mut ()>,
    // A bump allocator that is cleared between top-level expressions.
    allocator: BumpAllocator,
    // The encoding context can only be changed between top level expressions. This field stores
    // changes that need to be applied at the next opportunity.
    // TODO: Remove this RefCell when the Polonius borrow checker is available.
    //       See: https://github.com/rust-lang/rust/issues/70255
    pending_lst: PendingLst,
    has_pending_lst_changes: bool,
    // TODO: Make the symbol and macro tables traits on `D` such that they can be configured
    //       statically. Then 1.0 types can use `Never` for the macro table.
    symbol_table: SymbolTable,
    macro_table: MacroTable,
}

impl<'data, D: LazyDecoder<'data>> LazyExpandingReader<'data, D> {
    pub(crate) fn new(raw_reader: D::Reader) -> Self {
        Self {
            raw_reader,
            evaluator_ptr: None,
            allocator: BumpAllocator::new(),
            has_pending_lst_changes: false,
            pending_lst: PendingLst {
                is_lst_append: false,
                symbols: Vec::new(),
            },
            symbol_table: SymbolTable::new(),
            macro_table: MacroTable::new(),
        }
    }

    // TODO: Remove this when template definitions can be read in from the input stream and
    //       do not need to be registered with the reader manually.
    pub(crate) fn macro_table_mut(&mut self) -> &mut MacroTable {
        &mut self.macro_table
    }

    pub(crate) fn context(&self) -> EncodingContext<'_> {
        EncodingContext::new(&self.macro_table, &self.symbol_table, &self.allocator)
    }

    /// Dereferences a raw pointer storing the address of the active MacroEvaluator.
    fn ptr_to_evaluator<'top>(evaluator_ptr: *mut ()) -> &'top mut MacroEvaluator<'top, 'data, D> {
        let ptr: *mut MacroEvaluator<'top, 'data, D> = evaluator_ptr.cast();
        // SAFETY: The pointer passed in is expected to refer to a MacroEvaluator living in the bump
        // allocator. In order for 'top to be a valid lifetime, the bump allocator can only be
        // reset between top-level expressions.
        let evaluator: &'top mut MacroEvaluator<'top, 'data, D> = unsafe { &mut *ptr };
        evaluator
    }

    /// Converts a mutable reference to the active MacroEvaluator into a raw, untyped pointer.
    // This allows the pointer to be stored in `self.evaluator_ptr` in anticipation of the following
    // call to `next()`.
    fn evaluator_to_ptr(evaluator: &mut MacroEvaluator<'_, 'data, D>) -> *mut () {
        let ptr: *mut MacroEvaluator<'_, 'data, D> = evaluator;
        let untyped_ptr: *mut () = ptr.cast();
        untyped_ptr
    }

    /// If `maybe_evaluator_ptr` is `Some(pointer)`, this function will return a mutable reference
    /// (`&mut`) to the `MacroEvaluator` to which `pointer` refers.
    /// If `maybe_evaluator_ptr` is `None`, this function will initialize a new `MacroEvaluator`
    /// in the current `EncodingContext` and return a mutable reference to it.
    fn get_or_make_evaluator<'top>(
        maybe_evaluator_ptr: Option<*mut ()>,
        context: EncodingContext<'top>,
    ) -> &'top mut MacroEvaluator<'top, 'data, D> {
        // If there's already an evaluator, dereference the pointer.
        if let Some(evaluator_ptr) = maybe_evaluator_ptr {
            return Self::ptr_to_evaluator::<'top>(evaluator_ptr);
        }
        // If there isn't an evaluator, we create a new one with an empty environment.
        context
            .allocator
            .alloc_with(move || MacroEvaluator::new(context, Environment::empty()))
    }

    /// Given a `LazyExpandedValue` representing a symbol table, update the `PendingList` with the
    /// new encoding context information that will be applied after the current top level expression.
    fn update_pending_lst(
        &self,
        symbol_table_value: &LazyExpandedValue<'_, 'data, D>,
    ) -> IonResult<()> {
        let reader: &mut LazyExpandingReader<'data, D> = Self::unsafe_get_mut(self);
        reader.has_pending_lst_changes = true;
        LazySystemReader::process_symbol_table(&mut reader.pending_lst, symbol_table_value)
    }

    /// Updates the encoding context with the information stored in the `PendingLst`.
    // TODO: This only works on Ion 1.0 symbol tables for now
    fn apply_pending_lst(&mut self) {
        // If the symbol table's `imports` field had a value of `$ion_symbol_table`, then we're
        // appending the symbols it defined to the end of our existing local symbol table.
        // Otherwise, we need to clear the existing table before appending the new symbols.
        if !self.pending_lst.is_lst_append {
            // We're setting the symbols list, not appending to it.
            self.symbol_table.reset();
        }
        // `drain()` empties the pending symbols list
        for symbol in self.pending_lst.symbols.drain(..) {
            self.symbol_table.intern_or_add_placeholder(symbol);
        }
        self.pending_lst.is_lst_append = false;
        self.has_pending_lst_changes = false;
    }

    /// Inspects a `LazyExpandedValue` to determine whether it is a symbol table or an
    /// application-level value. Returns it as the appropriate variant of `SystemStreamItem`.
    fn interpret_expanded_value<'top>(
        &self,
        value: LazyExpandedValue<'top, 'data, D>,
    ) -> IonResult<SystemStreamItem<'top, 'data, D>> {
        if LazySystemReader::is_symbol_table_struct(&value)? {
            self.update_pending_lst(&value)?;
            let lazy_struct = LazyStruct {
                expanded_struct: value.read()?.expect_struct().unwrap(),
            };
            return Ok(SystemStreamItem::SymbolTable(lazy_struct));
        }
        let lazy_value = LazyValue::new(value);
        return Ok(SystemStreamItem::Value(lazy_value));
    }

    fn unsafe_get_mut<T>(value: &T) -> &mut T {
        #![allow(clippy::mut_from_ref)]
        // XXX: This `unsafe` hack is a workaround for a limitation in the borrow checker that
        //      prevents it from understanding that a mutable borrow in the body of the loop does
        //      not necessarily need to prevent all other borrows.
        //      https://github.com/rust-lang/rust/issues/70255
        //
        //      There is a rustc fix for this limitation on the horizon. See:
        //      https://smallcultfollowing.com/babysteps/blog/2023/09/22/polonius-part-1/
        //      https://blog.rust-lang.org/inside-rust/2023/10/06/polonius-update.html
        //
        //      Indeed, using the experimental `-Zpolonius` flag on the nightly compiler allows the
        //      version of this code without this `unsafe` hack to work. The alternative to the
        //      hack is wrapping several components inside the expanding reader in something like
        //      a `RefCell`, which adds a small amount of overhead to each access. Given that this
        //      code is the hot path and a fix is inbound, I think this use of `unsafe` is warranted.
        //
        //      SAFETY: This method should only be used for transient access to fields in a loop.
        //      The reference it produces MUST NOT be persisted across loop iterations or returned.

        // Cast the reference to a const pointer
        let ptr = value as *const T;
        unsafe {
            // Cast the const pointer to a mut pointer
            let mut_ptr = ptr as *mut T;
            // Cast the mut pointer to a mut reference
            &mut *mut_ptr
        }
        // ^--- These operations only "exist" at compile time, and should boil away during rustc's
        //      optimization passes.
    }

    /// This method is invoked just before the reader begins reading the next top-level expression
    /// from the data stream. It is NOT invoked between multiple top level _values_ coming from a
    /// single expression.
    ///
    /// This is the reader's opportunity to make any pending changes to the encoding context.
    fn between_top_level_expressions(&self) {
        // When this is called:
        // * We are between top-level values.
        // * The user is no longer holding references to values yielded by prior calls to `next()`.
        // * `self.evaluator_ptr` is `None`.
        //
        // This means that nothing is holding a reference to the bump allocator's memory.
        let reader = Self::unsafe_get_mut(self);
        reader.evaluator_ptr = None;
        if self.has_pending_lst_changes {
            reader.apply_pending_lst();
        }
        reader.allocator.reset();
    }

    pub(crate) fn unsafe_next_value<'top>(
        &'top self,
    ) -> IonResult<Option<LazyValue<'top, 'data, D>>> {
        loop {
            // We need the unsafe mut access hack because we're calling 'next()' in a loop.
            // However, there's never a time that the reference we get can survive across iterations.
            match Self::unsafe_get_mut(self).next_item()? {
                SystemStreamItem::VersionMarker(_, _) => {
                    // TODO: Handle version changes 1.0 <-> 1.1
                }
                SystemStreamItem::SymbolTable(_) => {}
                SystemStreamItem::Value(value) => return Ok(Some(value)),
                SystemStreamItem::EndOfStream => return Ok(None),
            }
        }
    }

    /// Returns the next [`SystemStreamItem`] either by continuing to evaluate a macro invocation
    /// in progress or by pulling another expression from the input stream.
    pub fn next_item<'top>(&'top mut self) -> IonResult<SystemStreamItem<'top, 'data, D>>
    where
        'data: 'top,
    {
        loop {
            // See if there's already an active macro evaluator.
            if let Some(evaluator_ptr) = self.evaluator_ptr {
                let evaluator = Self::ptr_to_evaluator(evaluator_ptr);
                if evaluator.macro_stack_depth() > 0 {
                    // If the evaluator still has macro expansions in its stack, we need to give it the
                    // opportunity to produce the next value.
                    match evaluator.next(self.context(), 0) {
                        Ok(Some(value)) => {
                            return self.interpret_expanded_value(value);
                        }
                        Ok(None) => {
                            // While the evaluator had macros in its stack, they did not produce any more
                            // values. The stack is now empty.
                        }
                        Err(e) => return Err(e),
                    };
                }
            }

            self.between_top_level_expressions();

            // We'll pull another top-level expression from the input stream if one is available.
            use RawStreamItem::*;
            let expanded_item = match Self::unsafe_get_mut(&self.raw_reader).next()? {
                VersionMarker(major, minor) => SystemStreamItem::VersionMarker(major, minor),
                // We got our value; return it.
                Value(raw_value) => {
                    let value = LazyExpandedValue {
                        source: ExpandedValueSource::ValueLiteral(raw_value),
                        context: self.context(),
                    };
                    return self.interpret_expanded_value(value);
                }
                // It's another macro invocation, we'll start evaluating it.
                EExpression(e_exp) => {
                    let context = EncodingContext::new(
                        &self.macro_table,
                        &self.symbol_table,
                        &self.allocator,
                    );
                    let resolved_e_exp = e_exp.resolve(context)?;
                    let evaluator = Self::get_or_make_evaluator(self.evaluator_ptr, context);
                    // Push the invocation onto the evaluation stack.
                    evaluator.push(context, resolved_e_exp)?;
                    *Self::unsafe_get_mut(&self.evaluator_ptr) =
                        Some(Self::evaluator_to_ptr(evaluator));
                    // Return to the top of the loop to pull the next value (if any) from the evaluator.
                    continue;
                }
                EndOfStream => SystemStreamItem::EndOfStream,
            };

            return Ok(expanded_item);
        }
    }
}

/// The source of data backing a [`LazyExpandedValue`].
#[derive(Copy, Clone)]
pub enum ExpandedValueSource<'top, 'data, D: LazyDecoder<'data>> {
    /// This value was a literal in the input stream.
    ValueLiteral(D::Value),
    /// This value was part of a template definition.
    Template(Environment<'top, 'data, D>, TemplateElement<'top>),
    /// This value was the computed result of a macro invocation like `(:make_string `...)`.
    Constructed(
        // TODO: Make this an associated type on the LazyDecoder trait so 1.0 types can set
        //       it to `Never` and the compiler can eliminate this code path where applicable.
        // Constructed data stored in the bump allocator. Holding references instead of the data
        // itself allows this type (and those that contain it) to impl `Copy`.
        &'top [&'top str],
        &'top ExpandedValueRef<'top, 'data, D>,
    ),
}

impl<'top, 'data, D: LazyDecoder<'data>> Debug for ExpandedValueSource<'top, 'data, D> {
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
impl<'top, 'data, V: RawValueLiteral, D: LazyDecoder<'data, Value = V>> From<V>
    for ExpandedValueSource<'top, 'data, D>
{
    fn from(value: V) -> Self {
        ExpandedValueSource::ValueLiteral(value)
    }
}

/// A value produced by expanding the 'raw' view of the input data.
#[derive(Copy, Clone)]
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

    pub(crate) fn from_template(
        context: EncodingContext<'top>,
        environment: Environment<'top, 'data, D>,
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

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, 'data, D> {
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

    pub fn read(&self) -> IonResult<ExpandedValueRef<'top, 'data, D>> {
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

impl<'top, 'data, D: LazyDecoder<'data>> From<LazyExpandedValue<'top, 'data, D>>
    for LazyValue<'top, 'data, D>
{
    fn from(expanded_value: LazyExpandedValue<'top, 'data, D>) -> Self {
        LazyValue { expanded_value }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> From<LazyExpandedStruct<'top, 'data, D>>
    for LazyStruct<'top, 'data, D>
{
    fn from(expanded_struct: LazyExpandedStruct<'top, 'data, D>) -> Self {
        LazyStruct { expanded_struct }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> From<LazyExpandedSExp<'top, 'data, D>>
    for LazySExp<'top, 'data, D>
{
    fn from(expanded_sexp: LazyExpandedSExp<'top, 'data, D>) -> Self {
        LazySExp { expanded_sexp }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> From<LazyExpandedList<'top, 'data, D>>
    for LazyList<'top, 'data, D>
{
    fn from(expanded_list: LazyExpandedList<'top, 'data, D>) -> Self {
        LazyList { expanded_list }
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
            // The container variants hold lazy references to the containers themselves.
            // We cannot compare their equality without recursively reading those containers,
            // which introduces many opportunities to encounter an error that this method cannot
            // surface. Because this is `PartialEq`, we have the option of returning `false` for
            // values that cannot be compared to one another.
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
    fn from_template(
        context: EncodingContext<'top>,
        environment: Environment<'top, 'data, D>,
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
            Struct(s) => ExpandedValueRef::Struct(LazyExpandedStruct::from_template(
                context,
                environment,
                element.template(),
                element.annotations_range(),
                *s,
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
