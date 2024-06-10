//! A view of the Ion data with all e-expressions lazily expanded.
//!
//! The types defined in this module each wrap their corresponding type from the "raw" view of the
//! data, replacing the word `Raw` with the word `Expanded` in the type name.
//!
//! The expanded types expose largely the same API, with some key differences:
//!   1. Most method invocations require an [`EncodingContextRef`] to be specified, giving the
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
use std::ops::Deref;

use bumpalo::Bump as BumpAllocator;

use sequence::{LazyExpandedList, LazyExpandedSExp};

use crate::element::iterators::SymbolsIterator;
use crate::lazy::any_encoding::IonEncoding;
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{Decoder, LazyRawValue};
use crate::lazy::encoding::RawValueLiteral;
use crate::lazy::expanded::compiler::TemplateCompiler;
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, RawEExpression};
use crate::lazy::expanded::macro_table::MacroTable;
use crate::lazy::expanded::r#struct::LazyExpandedStruct;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    TemplateElement, TemplateMacro, TemplateMacroRef, TemplateValue,
};
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::str_ref::StrRef;
use crate::lazy::streaming_raw_reader::{IonInput, StreamingRawReader};
use crate::lazy::system_reader::{PendingLst, SystemReader};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
use crate::lazy::value::LazyValue;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::{
    AnyEncoding, Catalog, Decimal, Int, IonResult, IonType, RawSymbolRef, SymbolTable, Timestamp,
};

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
/// The `'top` lifetime associated with the [`EncodingContextRef`] reflects the fact that it can only
/// be used as long as the reader is positioned on the same top level expression (i.e. the symbol and
/// macro tables are guaranteed not to change).
//  It should be possible to loosen this definition of `'top` to include several top level values
//  as long as the macro and symbol tables do not change between them, though this would require
//  carefully designing the API to emphasize that the sequence of values is either the set that
//  happens to be available in the buffer OR the set that leads up to the next encoding directive.
//  The value proposition of being able to lazily explore multiple top level values concurrently
//  would need to be proved out first.
#[derive(Debug)]
pub struct EncodingContext {
    pub(crate) macro_table: MacroTable,
    pub(crate) symbol_table: SymbolTable,
    pub(crate) allocator: BumpAllocator,
}

impl EncodingContext {
    pub fn new(
        macro_table: MacroTable,
        symbol_table: SymbolTable,
        allocator: BumpAllocator,
    ) -> Self {
        Self {
            macro_table,
            symbol_table,
            allocator,
        }
    }

    pub fn empty() -> Self {
        Self::new(MacroTable::new(), SymbolTable::new(), BumpAllocator::new())
    }

    pub fn get_ref(&self) -> EncodingContextRef {
        EncodingContextRef { context: self }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EncodingContextRef<'top> {
    context: &'top EncodingContext,
}

impl<'top> EncodingContextRef<'top> {
    pub fn new(context: &'top EncodingContext) -> Self {
        Self { context }
    }

    #[cfg(test)]
    pub fn unit_test_context() -> EncodingContextRef<'static> {
        // For the sake of the unit tests, make a dummy encoding context with no lifetime
        // constraints.
        EncodingContextRef::new(Box::leak(Box::new(EncodingContext::empty())))
    }

    pub fn allocator(&self) -> &'top BumpAllocator {
        &self.context.allocator
    }

    pub fn symbol_table(&self) -> &'top SymbolTable {
        &self.context.symbol_table
    }

    pub fn macro_table(&self) -> &'top MacroTable {
        &self.context.macro_table
    }
}

impl<'top> Deref for EncodingContextRef<'top> {
    type Target = EncodingContext;

    fn deref(&self) -> &Self::Target {
        self.context
    }
}

#[derive(Debug)]
/// Stream components emitted by a LazyExpandingReader. These items may be encoded directly in the
/// stream, or may have been produced by the evaluation of an encoding expression (e-expression).
pub enum ExpandedStreamItem<'top, D: Decoder> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawBinaryValue`](crate::lazy::binary::raw::value::LazyRawBinaryValue_1_0).
    Value(LazyExpandedValue<'top, D>),
    /// The end of the stream
    EndOfStream,
}

impl<'top, D: Decoder> ExpandedStreamItem<'top, D> {
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
pub struct ExpandingReader<Encoding: Decoder, Input: IonInput> {
    raw_reader: UnsafeCell<StreamingRawReader<Encoding, Input>>,
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
    encoding_context: UnsafeCell<EncodingContext>,
    catalog: Box<dyn Catalog>,
}

impl<Encoding: Decoder, Input: IonInput> ExpandingReader<Encoding, Input> {
    pub(crate) fn new(
        raw_reader: StreamingRawReader<Encoding, Input>,
        catalog: Box<dyn Catalog>,
    ) -> Self {
        Self {
            raw_reader: raw_reader.into(),
            evaluator_ptr: None.into(),
            encoding_context: EncodingContext::empty().into(),
            pending_lst: PendingLst::new().into(),
            catalog,
        }
    }

    // TODO: This method is temporary. It will be removed when the ability to read 1.1 encoding
    //       directives from the input stream is available. Until then, template creation is manual.
    pub fn register_template(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        let template_macro: TemplateMacro = self.compile_template(template_definition)?;
        self.add_macro(template_macro)
    }

    fn compile_template(&self, template_definition: &str) -> IonResult<TemplateMacro> {
        TemplateCompiler::compile_from_text(self.context(), template_definition)
    }

    fn add_macro(&mut self, template_macro: TemplateMacro) -> IonResult<MacroAddress> {
        let macro_table = &mut self.context_mut().macro_table;
        macro_table.add_macro(template_macro)
    }

    pub fn context(&self) -> EncodingContextRef<'_> {
        // SAFETY: The only time that the macro table, symbol table, and allocator can be modified
        // is in the body of the method `between_top_level_expressions`. As long as nothing holds
        // a reference to the `EncodingContext` we create here when that method is running,
        // this is safe.
        unsafe { (*self.encoding_context.get()).get_ref() }
    }

    pub fn context_mut(&mut self) -> &mut EncodingContext {
        // SAFETY: If the caller has a `&mut` reference to `self`, it is the only mutable reference
        //         that can modify `self.encoding_context`.
        unsafe { &mut *self.encoding_context.get() }
    }

    // SAFETY: This method takes an immutable reference to `self` and then modifies the
    //         EncodingContext's bump allocator via `UnsafeCell`. This should only be called from
    //         `between_top_level_values`, and the caller must confirm that nothing else holds a
    //         reference to any structures within `EncodingContext`.
    unsafe fn reset_bump_allocator(&self) {
        let context: &mut EncodingContext = &mut *self.encoding_context.get();
        context.allocator.reset();
    }

    pub fn pending_lst(&self) -> &PendingLst {
        // If the user is able to call this method, the PendingLst is not being modified and it's
        // safe to immutably reference.
        unsafe { &*self.pending_lst.get() }
    }

    pub fn pending_lst_mut(&mut self) -> &mut PendingLst {
        // SAFETY: If the caller has a `&mut` reference to `self`, it is the only mutable reference
        //         that can modify `self.pending_lst`.
        unsafe { &mut *self.pending_lst.get() }
    }

    fn ptr_to_mut_ref<'a, T>(ptr: *mut ()) -> &'a mut T {
        let typed_ptr: *mut T = ptr.cast();
        unsafe { &mut *typed_ptr }
    }

    /// Dereferences a raw pointer storing the address of the active MacroEvaluator.
    fn ptr_to_evaluator<'top>(evaluator_ptr: *mut ()) -> &'top mut MacroEvaluator<'top, Encoding> {
        Self::ptr_to_mut_ref(evaluator_ptr)
    }

    fn ref_as_ptr<T>(reference: &mut T) -> *mut () {
        let ptr: *mut T = reference;
        let untyped_ptr: *mut () = ptr.cast();
        untyped_ptr
    }

    /// Converts a mutable reference to the active MacroEvaluator into a raw, untyped pointer.
    fn evaluator_to_ptr(evaluator: &mut MacroEvaluator<'_, Encoding>) -> *mut () {
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
        // `drain()` empties the pending `imported_symbols` and `symbols` lists
        for symbol in pending_lst.imported_symbols.drain(..) {
            symbol_table.add_symbol(symbol);
        }
        for symbol in pending_lst.symbols.drain(..) {
            symbol_table.add_symbol(symbol);
        }
        pending_lst.is_lst_append = false;
        pending_lst.has_changes = false;
    }

    /// Inspects a `LazyExpandedValue` to determine whether it is a symbol table or an
    /// application-level value. Returns it as the appropriate variant of `SystemStreamItem`.
    fn interpret_value<'top>(
        &self,
        value: LazyExpandedValue<'top, Encoding>,
    ) -> IonResult<SystemStreamItem<'top, Encoding>> {
        // If this value is a symbol table...
        if SystemReader::<_, Input>::is_symbol_table_struct(&value)? {
            // ...traverse it and record any new symbols in our `pending_lst`.
            let pending_lst = unsafe { &mut *self.pending_lst.get() };
            SystemReader::<_, Input>::process_symbol_table(pending_lst, &*self.catalog, &value)?;
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
        // We're going to clear the bump allocator, so drop our reference to the evaluator that
        // lives there.
        self.evaluator_ptr.set(None);

        // Clear the bump allocator.
        // SAFETY: This is the only place where we modify the encoding context. Take care not to
        //         alias the allocator, symbol table, or macro table inside this `unsafe` scope.
        unsafe { self.reset_bump_allocator() };

        // If the pending LST has changes to apply, do so.
        // SAFETY: Nothing else holds a reference to the `PendingLst`'s contents, so we can use the
        //         `UnsafeCell` to get a mutable reference to it.
        let pending_lst: &mut PendingLst = unsafe { &mut *self.pending_lst.get() };
        if pending_lst.has_changes {
            // SAFETY: Nothing else holds a reference to the `EncodingContext`'s contents, so we can use the
            //         `UnsafeCell` to get a mutable reference to its symbol table.
            let symbol_table: &mut SymbolTable =
                &mut unsafe { &mut *self.encoding_context.get() }.symbol_table;
            Self::apply_pending_lst(pending_lst, symbol_table);
        }
    }

    /// Returns the next application-level value.
    ///
    /// This method will consume and process as many system-level values as possible until it
    /// encounters an application-level value or the end of the stream.
    pub fn next_value(&mut self) -> IonResult<Option<LazyValue<Encoding>>> {
        loop {
            match self.next_item()? {
                SystemStreamItem::VersionMarker(_marker) => {
                    // TODO: Handle version changes 1.0 <-> 1.1
                }
                SystemStreamItem::SymbolTable(_) => {
                    // The symbol table is processed by `next_item` before it is returned. There's
                    // nothing to be done here.
                }
                SystemStreamItem::Value(value) => return Ok(Some(value)),
                SystemStreamItem::EndOfStream(_) => return Ok(None),
            }
        }
    }

    /// Returns the next [`SystemStreamItem`] either by continuing to evaluate a macro invocation
    /// in progress or by pulling another expression from the input stream.
    pub fn next_item(&self) -> IonResult<SystemStreamItem<'_, Encoding>> {
        // NB: This method takes an immutable reference to `self` but uses `UnsafeCell` to modify
        //     `self` safely. This allows `next_item` to be used in a loop from next_value without
        //     encountering the borrow checker limitations this method skirts. If/when the borrow
        //     checker issue is addressed, we may change this to `&mut self`.

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

        let allocator: &BumpAllocator = self.context().allocator();
        let context_ref = EncodingContextRef::new(allocator.alloc_with(|| self.context()));
        loop {
            // Pull another top-level expression from the input stream if one is available.
            use crate::lazy::raw_stream_item::RawStreamItem::*;
            let raw_reader = unsafe { &mut *self.raw_reader.get() };
            match raw_reader.next(context_ref)? {
                VersionMarker(marker) => return Ok(SystemStreamItem::VersionMarker(marker)),
                // We got our value; return it.
                Value(raw_value) => {
                    let value = LazyExpandedValue::from_literal(context_ref, raw_value);
                    return self.interpret_value(value);
                }
                // It's another macro invocation, we'll start evaluating it.
                EExpression(e_exp) => {
                    let context = self.context();
                    let resolved_e_exp = e_exp.resolve(context_ref)?;
                    // Get the current evaluator or make a new one
                    let evaluator = match self.evaluator_ptr.get() {
                        // If there's already an evaluator, dereference the pointer.
                        Some(ptr) => Self::ptr_to_evaluator(ptr),
                        // If there's not, make a new one.
                        None => context
                            .allocator
                            // E-expressions always have an empty environment
                            .alloc_with(move || {
                                MacroEvaluator::new(context_ref, Environment::empty())
                            }),
                    };
                    // Push the invocation onto the evaluation stack.
                    evaluator.push(resolved_e_exp)?;
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
                EndOfStream(end_position) => {
                    return Ok(SystemStreamItem::EndOfStream(end_position));
                }
            };
        }
    }

    /// If there is not an evaluation in process, returns `Ok(None)`.
    /// If there is an evaluation in process but it does not yield another value, returns `Ok(None)`.
    /// If there is an evaluation in process and it yields another value, returns `Ok(Some(value))`.
    /// Otherwise, returns `Err`.
    fn next_from_evaluator(&self) -> IonResult<Option<SystemStreamItem<Encoding>>> {
        let evaluator_ptr = match self.evaluator_ptr.get() {
            // There's not currently an evaluator.
            None => return Ok(None),
            // There's an evaluator in the process of expanding a macro.
            Some(ptr) => ptr,
        };
        let evaluator = Self::ptr_to_evaluator(evaluator_ptr);

        match evaluator.next() {
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

impl<Input: IonInput> ExpandingReader<AnyEncoding, Input> {
    pub fn detected_encoding(&self) -> IonEncoding {
        let raw_reader = unsafe { &*self.raw_reader.get() };
        raw_reader.encoding()
    }
}

/// The source of data backing a [`LazyExpandedValue`].
#[derive(Copy, Clone)]
pub enum ExpandedValueSource<'top, D: Decoder> {
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

impl<'top, Encoding: Decoder> Debug for ExpandedValueSource<'top, Encoding> {
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
impl<'top, V: RawValueLiteral, Encoding: Decoder<Value<'top> = V>> From<V>
    for ExpandedValueSource<'top, Encoding>
{
    fn from(value: V) -> Self {
        ExpandedValueSource::ValueLiteral(value)
    }
}

/// A variable found in the body of a template macro.
#[derive(Debug, Copy, Clone)]
pub struct TemplateVariableReference<'top> {
    template: TemplateMacroRef<'top>,
    signature_index: u16,
}

impl<'top> TemplateVariableReference<'top> {
    pub fn new(template: TemplateMacroRef<'top>, signature_index: u16) -> Self {
        Self {
            template,
            signature_index,
        }
    }

    fn name(&self) -> &'top str {
        self.template.signature.parameters()[self.signature_index()].name()
    }

    fn host_template(&self) -> TemplateMacroRef<'top> {
        self.template
    }

    fn signature_index(&self) -> usize {
        self.signature_index as usize
    }
}

/// A value produced by expanding the 'raw' view of the input data.
#[derive(Copy, Clone)]
pub struct LazyExpandedValue<'top, Encoding: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) source: ExpandedValueSource<'top, Encoding>,
    // If this value came from a variable reference in a template macro expansion, the
    // template and the name of the variable can be found here.
    pub(crate) variable: Option<TemplateVariableReference<'top>>,
}

impl<'top, Encoding: Decoder> Debug for LazyExpandedValue<'top, Encoding> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.source)
    }
}

impl<'top, Encoding: Decoder> LazyExpandedValue<'top, Encoding> {
    pub(crate) fn from_literal(
        context: EncodingContextRef<'top>,
        value: Encoding::Value<'top>,
    ) -> Self {
        Self {
            context,
            source: ExpandedValueSource::ValueLiteral(value),
            variable: None,
        }
    }

    pub(crate) fn from_template(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, Encoding>,
        element: TemplateElement<'top>,
    ) -> Self {
        Self {
            context,
            source: ExpandedValueSource::Template(environment, element),
            variable: None,
        }
    }

    pub(crate) fn from_constructed(
        context: EncodingContextRef<'top>,
        annotations: &'top [&'top str],
        value: &'top ExpandedValueRef<'top, Encoding>,
    ) -> Self {
        Self {
            context,
            source: ExpandedValueSource::Constructed(annotations, value),
            variable: None,
        }
    }

    pub(crate) fn via_variable(mut self, variable_ref: TemplateVariableReference<'top>) -> Self {
        self.variable = Some(variable_ref);
        self
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

    pub fn has_annotations(&self) -> bool {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.has_annotations(),
            Template(_, element) => !element.annotations().is_empty(),
            Constructed(annotations, _) => !annotations.is_empty(),
        }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, Encoding> {
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

    pub fn read(&self) -> IonResult<ExpandedValueRef<'top, Encoding>> {
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

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    pub fn source(&self) -> ExpandedValueSource<'top, Encoding> {
        self.source
    }
}

impl<'top, Encoding: Decoder> From<LazyExpandedValue<'top, Encoding>>
    for LazyValue<'top, Encoding>
{
    fn from(expanded_value: LazyExpandedValue<'top, Encoding>) -> Self {
        LazyValue { expanded_value }
    }
}

impl<'top, Encoding: Decoder> From<LazyExpandedStruct<'top, Encoding>>
    for LazyStruct<'top, Encoding>
{
    fn from(expanded_struct: LazyExpandedStruct<'top, Encoding>) -> Self {
        LazyStruct { expanded_struct }
    }
}

impl<'top, Encoding: Decoder> From<LazyExpandedSExp<'top, Encoding>> for LazySExp<'top, Encoding> {
    fn from(expanded_sexp: LazyExpandedSExp<'top, Encoding>) -> Self {
        LazySExp { expanded_sexp }
    }
}

impl<'top, Encoding: Decoder> From<LazyExpandedList<'top, Encoding>> for LazyList<'top, Encoding> {
    fn from(expanded_list: LazyExpandedList<'top, Encoding>) -> Self {
        LazyList { expanded_list }
    }
}

pub enum ExpandedAnnotationsSource<'top, Encoding: Decoder> {
    ValueLiteral(Encoding::AnnotationsIterator<'top>),
    Template(SymbolsIterator<'top>),
    // TODO: This is a placeholder impl and always returns an empty iterator
    Constructed(Box<dyn Iterator<Item = IonResult<RawSymbolRef<'top>>> + 'top>),
}

pub struct ExpandedAnnotationsIterator<'top, Encoding: Decoder> {
    source: ExpandedAnnotationsSource<'top, Encoding>,
}

impl<'top, Encoding: Decoder> ExpandedAnnotationsIterator<'top, Encoding> {
    pub fn new(source: ExpandedAnnotationsSource<'top, Encoding>) -> Self {
        Self { source }
    }
}

impl<'top, Encoding: Decoder> Iterator for ExpandedAnnotationsIterator<'top, Encoding> {
    type Item = IonResult<RawSymbolRef<'top>>;

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
//       (Specifically: Int, Decimal, String, Symbol, Blob, Clob.) If we plumb the bump allocator all
//       the way down to the raw readers, then the situations that require allocation can
//       hold a 'top reference to a bump allocation instead of a static reference to a heap allocation.
//       This will enable us to remove several calls to `clone()`, which can be much slower than copies.
#[derive(Clone)]
pub enum ExpandedValueRef<'top, Encoding: Decoder> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(StrRef<'top>),
    Symbol(RawSymbolRef<'top>),
    Blob(BytesRef<'top>),
    Clob(BytesRef<'top>),
    SExp(LazyExpandedSExp<'top, Encoding>),
    List(LazyExpandedList<'top, Encoding>),
    Struct(LazyExpandedStruct<'top, Encoding>),
}

impl<'top, Encoding: Decoder> PartialEq for ExpandedValueRef<'top, Encoding> {
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

impl<'top, Encoding: Decoder> ExpandedValueRef<'top, Encoding> {
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

    pub fn expect_symbol(self) -> IonResult<RawSymbolRef<'top>> {
        if let ExpandedValueRef::Symbol(s) = self {
            Ok(s)
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

    pub fn expect_list(self) -> IonResult<LazyExpandedList<'top, Encoding>> {
        if let ExpandedValueRef::List(s) = self {
            Ok(s)
        } else {
            self.expected("list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazyExpandedSExp<'top, Encoding>> {
        if let ExpandedValueRef::SExp(s) = self {
            Ok(s)
        } else {
            self.expected("sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyExpandedStruct<'top, Encoding>> {
        if let ExpandedValueRef::Struct(s) = self {
            Ok(s)
        } else {
            self.expected("struct")
        }
    }

    fn from_raw(context: EncodingContextRef<'top>, value: RawValueRef<'top, Encoding>) -> Self {
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

impl<'top, D: Decoder> Debug for ExpandedValueRef<'top, D> {
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

impl<'top, Encoding: Decoder> ExpandedValueRef<'top, Encoding> {
    fn from_template(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, Encoding>,
        element: &TemplateElement<'top>,
    ) -> Self {
        use TemplateValue::*;
        match element.value() {
            Null(ion_type) => ExpandedValueRef::Null(*ion_type),
            Bool(b) => ExpandedValueRef::Bool(*b),
            Int(i) => ExpandedValueRef::Int(*i),
            Float(f) => ExpandedValueRef::Float(*f),
            Decimal(d) => ExpandedValueRef::Decimal(*d),
            Timestamp(t) => ExpandedValueRef::Timestamp(*t),
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
