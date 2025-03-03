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

use bumpalo::Bump as BumpAllocator;
use sequence::{LazyExpandedList, LazyExpandedSExp};
use std::cell::{Cell, UnsafeCell};
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, Range};
use std::rc::Rc;
use std::sync::Arc;

use crate::element::iterators::SymbolsIterator;
use crate::lazy::any_encoding::{IonEncoding, IonVersion};
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{Decoder, LazyRawValue};
use crate::lazy::encoding::RawValueLiteral;
use crate::lazy::expanded::compiler::TemplateCompiler;
use crate::lazy::expanded::e_expression::EExpression;
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, MacroExpr, RawEExpression};
use crate::lazy::expanded::macro_table::{Macro, MacroTable, ION_1_1_SYSTEM_MACROS};
use crate::lazy::expanded::r#struct::LazyExpandedStruct;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{TemplateElement, TemplateMacro, TemplateValue};
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::str_ref::StrRef;
use crate::lazy::streaming_raw_reader::{IoBuffer, IoBufferHandle, IonInput, StreamingRawReader};
use crate::lazy::system_reader::{PendingContextChanges, SystemReader};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::text::raw::v1_1::reader::MacroAddress;
use crate::lazy::value::LazyValue;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::IonFailure;
use crate::{
    Catalog, Decimal, HasRange, HasSpan, Int, IonResult, IonType, RawStreamItem, RawSymbolRef,
    RawVersionMarker, Span, SymbolRef, SymbolTable, Timestamp, ValueRef,
};

// All of these modules (and most of their types) are currently `pub` as the lazy reader is gated
// behind an experimental feature flag. We may constrain access to them in the future as the code
// stabilizes.
pub mod compiler;
pub mod e_expression;
pub mod encoding_module;
pub mod lazy_element;
pub mod macro_evaluator;
pub mod macro_table;
pub mod sequence;
pub mod r#struct;
pub mod template;

/// The encoding context holds an `IoBufferSource`.
///
/// During initialization, it is set to `None`, indicating that there is not yet a meaningfully
/// initialized IoBuffer.
///
/// When the reader's `IonInput` has populated its input buffer, the instance is set to `Reader`.
/// The dynamic `IoBufferHandle` reference refers to the `IonInput` implementation. If the input is
/// a stream, then the sliding window over the input stream is an `IoBuffer` instance that can be
/// cheaply cloned. However, if the input is a fixed slice, then there is no need for a heap-allocated
/// `IoBuffer`; the reader's `IonInput` will hold off on allocating one until it is necessary to
/// construct a `LazyElement`. Once created, all `LazyElement`s will share the same IoBuffer instance.
#[derive(Clone)]
pub(crate) enum IoBufferSource {
    // The EncodingContext does not have a meaningfully initialized input buffer yet.
    None,
    // The EncodingContext that owns this IoBufferSource belongs to the reader.
    // It holds a valid reference to the input source and thus can return an IoBuffer representing
    // the buffer's current contents. Doing so may or may not require heap allocation depending
    // on the underlying `IoBufferHandle` implementation.
    Reader(&'static dyn IoBufferHandle),
    // The EncodingContext that owns this IoBufferSource belongs to a `LazyElement`;
    // the EncodingContext was previously cloned from the reader's instance.
    // It holds an already-constructed IoBuffer that can be cheaply cloned.
    IoBuffer(IoBuffer),
}

/// A collection of resources that can be used to encode or decode Ion values.
//  It should be possible to loosen this definition of `'top` to include several top level values
//  as long as the macro and symbol tables do not change between them, though this would require
//  carefully designing the API to emphasize that the sequence of values is either the set that
//  happens to be available in the buffer OR the set that leads up to the next encoding directive.
//  The value proposition of being able to lazily explore multiple top level values concurrently
//  would need to be proved out first.
pub struct EncodingContext {
    // XXX: These fields are their own `Rc<_>` pointers to enable parts of the encoding context to be
    //      re-used across top-level values. For example, if the symbol table changes between values
    //      but the macro table does not, the two values can still point to the same macro table instance.
    pub(crate) macro_table: Rc<MacroTable>,
    pub(crate) symbol_table: Rc<SymbolTable>,
    pub(crate) allocator: Rc<BumpAllocator>,

    pub(crate) io_buffer_source: UnsafeCell<IoBufferSource>,
}

impl Clone for EncodingContext {
    fn clone(&self) -> Self {
        // If this EncodingContext previously held a (now dying) reference to the current input,
        // we need to give it its own IoBuffer to guarantee the bytes are available as long as it is.
        let io_buffer = self.save_io_buffer();
        Self {
            macro_table: self.macro_table.clone(),
            symbol_table: self.symbol_table.clone(),
            allocator: self.allocator.clone(),
            io_buffer_source: IoBufferSource::IoBuffer(io_buffer).into(),
        }
    }
}

impl Debug for EncodingContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let symbol_table = self.symbol_table();
        let num_symbols = symbol_table.len();
        let num_macros = self.macro_table().len();
        let ion_version = symbol_table.ion_version();
        write!(f, "EncodingContext {{ion_version = {ion_version:?}, {num_macros} macros, {num_symbols} symbols}} ")
    }
}

impl EncodingContext {
    pub fn new(
        macro_table: MacroTable,
        symbol_table: SymbolTable,
        allocator: BumpAllocator,
    ) -> Self {
        Self {
            macro_table: Rc::new(macro_table),
            symbol_table: Rc::new(symbol_table),
            allocator: Rc::new(allocator),
            io_buffer_source: IoBufferSource::None.into(),
        }
    }

    pub fn for_ion_version(version: IonVersion) -> Self {
        let macro_table = MacroTable::with_system_macros(version);
        Self::new(macro_table, SymbolTable::new(version), BumpAllocator::new())
    }

    pub fn empty() -> Self {
        Self::new(
            MacroTable::empty(),
            SymbolTable::empty(IonVersion::default()),
            BumpAllocator::new(),
        )
    }

    pub fn get_ref(&self) -> EncodingContextRef<'_> {
        EncodingContextRef { context: self }
    }

    pub fn save_io_buffer(&self) -> IoBuffer {
        match unsafe { &*self.io_buffer_source.get() } {
            IoBufferSource::IoBuffer(ref buffer) => buffer.clone(),
            IoBufferSource::Reader(handle) => handle.save_io_buffer(),
            IoBufferSource::None => {
                panic!("io_buffer() called on EncodingContext before Input reference was set.")
            }
        }
    }

    /// SAFETY: This method should _only_ be called by the StreamingRawReader and then only
    ///         after the current value has been read and no other changes to input can happen.
    pub(crate) unsafe fn set_io_buffer_handle(&self, handle: &dyn IoBufferHandle) {
        // SAFETY: This is always safe to *set*. It can only be read from when there is no chance of
        //         the reader's data source being modified. This can only happen between `'top` lifetimes,
        //         so from the end user's perspective it's always safe provided that we're not misusing it internally.
        //         It should be unset at the beginning of each `'top` lifetime.
        let buffer_handle: &'static dyn IoBufferHandle = unsafe { std::mem::transmute(handle) };
        let io_buffer_source = unsafe { &mut *self.io_buffer_source.get() };
        *io_buffer_source = IoBufferSource::Reader(buffer_handle);
    }

    pub fn macro_table(&self) -> &MacroTable {
        &self.macro_table
    }

    /// If there is only one strong reference to the macro table, returns a mutable reference to it.
    /// Otherwise, clones the macro table, allowing the other referents to continue using the previous copy.
    pub fn macro_table_mut(&mut self) -> &mut MacroTable {
        Rc::make_mut(&mut self.macro_table)
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }

    pub fn allocator(&self) -> &BumpAllocator {
        &self.allocator
    }

    fn make_allocator_mut(allocator: &mut Rc<BumpAllocator>) -> &mut BumpAllocator {
        // This is the same logic as `Rc::make_mut`. We can't use that method here because
        // the bump allocator doesn't implement `Clone`, a required bound.
        if Rc::strong_count(allocator) > 1 {
            *allocator = Rc::new(BumpAllocator::new());
        }

        Rc::get_mut(allocator).expect("allocator should be initialized")
    }

    pub fn allocator_mut(&mut self) -> &mut BumpAllocator {
        Self::make_allocator_mut(&mut self.allocator)
    }

    // TODO: These methods are temporary; they will be removed once shared modules are supported.
    pub fn register_template_src(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        let template_macro: TemplateMacro =
            TemplateCompiler::compile_from_source(self.get_ref(), template_definition)?;
        self.register_template(template_macro)
    }

    pub fn register_template(&mut self, template_macro: TemplateMacro) -> IonResult<MacroAddress> {
        self.macro_table_mut().add_template_macro(template_macro)
    }

    pub(crate) fn tables_mut(&mut self) -> (&mut MacroTable, &mut SymbolTable) {
        let Self {
            macro_table,
            symbol_table,
            ..
        } = self;
        (Rc::make_mut(macro_table), Rc::make_mut(symbol_table))
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EncodingContextRef<'top> {
    pub(crate) context: &'top EncodingContext,
}

impl<'top> EncodingContextRef<'top> {
    pub fn new(context: &'top EncodingContext) -> Self {
        Self { context }
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

    pub(crate) fn none_macro(&self) -> Arc<Macro> {
        ION_1_1_SYSTEM_MACROS
            .clone_macro_with_name("none")
            .expect("`none` macro in system macro table")
    }

    pub(crate) fn values_macro(&self) -> Arc<Macro> {
        ION_1_1_SYSTEM_MACROS
            .clone_macro_with_name("values")
            .expect("`values` macro in system macro table")
    }
}

impl Deref for EncodingContextRef<'_> {
    type Target = EncodingContext;

    fn deref(&self) -> &Self::Target {
        self.context
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
    // Because there is not a valid lifetime we can use for the type `*mut MacroEvaluator<'lifetime>`,
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
    pending_context_changes: UnsafeCell<PendingContextChanges>,
    encoding_context: UnsafeCell<EncodingContext>,
    catalog: Box<dyn Catalog>,
}

impl<Encoding: Decoder, Input: IonInput> ExpandingReader<Encoding, Input> {
    pub(crate) fn new(
        raw_reader: StreamingRawReader<Encoding, Input>,
        catalog: Box<dyn Catalog>,
    ) -> Self {
        let encoding = raw_reader.encoding();
        Self {
            raw_reader: raw_reader.into(),
            evaluator_ptr: None.into(),
            encoding_context: EncodingContext::for_ion_version(encoding.version()).into(),
            pending_context_changes: PendingContextChanges::new().into(),
            catalog,
        }
    }

    // TODO: This method is temporary. It will be removed when the ability to read 1.1 encoding
    //       directives from the input stream is available. Until then, template creation is manual.
    pub fn register_template_src(&mut self, template_definition: &str) -> IonResult<MacroAddress> {
        let template_macro: TemplateMacro = self.compile_template(template_definition)?;
        self.register_template(template_macro)
    }

    pub fn register_template(&mut self, template_macro: TemplateMacro) -> IonResult<MacroAddress> {
        self.add_macro(template_macro)
    }

    fn compile_template(&self, template_definition: &str) -> IonResult<TemplateMacro> {
        TemplateCompiler::compile_from_source(self.context(), template_definition)
    }

    fn add_macro(&mut self, template_macro: TemplateMacro) -> IonResult<MacroAddress> {
        let macro_table = self.context_mut().macro_table_mut();
        macro_table.add_template_macro(template_macro)
    }

    pub fn context(&self) -> EncodingContextRef<'_> {
        // SAFETY: The only time that the macro table, symbol table, and allocator can be modified
        // is in the body of the method `between_top_level_expressions`. As long as nothing holds
        // a reference to the `EncodingContext` we create here when that method is running,
        // this is safe.
        unsafe { (*self.encoding_context.get()).get_ref() }
    }

    pub fn context_mut(&mut self) -> &mut EncodingContext {
        self.encoding_context.get_mut()
    }

    // SAFETY: This method takes an immutable reference to `self` and then modifies the
    //         EncodingContext's bump allocator via `UnsafeCell`. This should only be called from
    //         `between_top_level_values`, and the caller must confirm that nothing else holds a
    //         reference to any structures within `EncodingContext`.
    unsafe fn reset_bump_allocator(&self) {
        let context: &mut EncodingContext = &mut *self.encoding_context.get();
        context.allocator_mut().reset();
    }

    pub fn pending_context_changes(&self) -> &PendingContextChanges {
        // If the user is able to call this method, the PendingLst is not being modified and it's
        // safe to immutably reference.
        unsafe { &*self.pending_context_changes.get() }
    }

    pub fn pending_lst_mut(&mut self) -> &mut PendingContextChanges {
        // SAFETY: If the caller has a `&mut` reference to `self`, it is the only mutable reference
        //         that can modify `self.pending_lst`.
        unsafe { &mut *self.pending_context_changes.get() }
    }

    #[inline]
    fn ptr_to_mut_ref<'a, T>(ptr: *mut ()) -> &'a mut T {
        let typed_ptr: *mut T = ptr.cast();
        unsafe { &mut *typed_ptr }
    }

    /// Dereferences a raw pointer storing the address of the active MacroEvaluator.
    #[inline]
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

    /// Updates the encoding context with the information stored in the `PendingContextChanges`.
    fn apply_pending_context_changes(
        pending_changes: &mut PendingContextChanges,
        symbol_table: &mut SymbolTable,
        macro_table: &mut MacroTable,
    ) {
        if let Some(new_version) = pending_changes.switch_to_version.take() {
            symbol_table.reset_to_version(new_version);
            macro_table.reset_to_system_macros();
            pending_changes.has_changes = false;
            pending_changes.is_lst_append = false;
            // If we're switching to a new version, the last stream item was a version marker
            // and there are no other pending changes. The `take()` above clears the `switch_to_version`.
            return;
        }

        if let Some(mut module) = pending_changes.take_new_active_module() {
            std::mem::swap(symbol_table, module.symbol_table_mut());
            std::mem::swap(macro_table, module.macro_table_mut());
            pending_changes.has_changes = false;
            pending_changes.is_lst_append = false;
            return;
        }

        // If the symbol table's `imports` field had a value of `$ion_symbol_table`, then we're
        // appending the symbols it defined to the end of our existing local symbol table.
        // Otherwise, we need to clear the existing table before appending the new symbols.
        if !pending_changes.is_lst_append {
            // We're setting the symbols list, not appending to it.
            symbol_table.reset_to_prefix_only();
        }
        // `drain()` empties the pending `imported_symbols` and `symbols` lists
        for symbol in pending_changes.imported_symbols.drain(..) {
            symbol_table.add_symbol(symbol);
        }
        for symbol in pending_changes.symbols.drain(..) {
            symbol_table.add_symbol(symbol);
        }
        pending_changes.is_lst_append = false;
        pending_changes.has_changes = false;
    }

    #[inline]
    fn interpret_value<'top>(
        &self,
        value: LazyExpandedValue<'top, Encoding>,
    ) -> IonResult<SystemStreamItem<'top, Encoding>> {
        if value.has_annotations() && matches!(value.ion_type(), IonType::Struct | IonType::SExp) {
            self.fully_interpret_value(value)
        } else {
            Ok(SystemStreamItem::Value(LazyValue::new(value)))
        }
    }

    /// Inspects a `LazyExpandedValue` to determine whether it is a symbol table or an
    /// application-level value. Returns it as the appropriate variant of `SystemStreamItem`.
    fn fully_interpret_value<'top>(
        &self,
        value: LazyExpandedValue<'top, Encoding>,
    ) -> IonResult<SystemStreamItem<'top, Encoding>> {
        // If this value is a symbol table...
        if SystemReader::<_, Input>::is_symbol_table_struct(&value)? {
            // ...traverse it and record any new symbols in our `pending_lst`.
            let pending_changes = unsafe { &mut *self.pending_context_changes.get() };
            SystemReader::<_, Input>::process_symbol_table(
                pending_changes,
                &*self.catalog,
                &value,
            )?;
            pending_changes.has_changes = true;
            let lazy_struct = LazyStruct {
                expanded_struct: value.read()?.expect_struct()?,
            };
            return Ok(SystemStreamItem::SymbolTable(lazy_struct));
        } else if self.detected_encoding().version() == IonVersion::v1_1
            && SystemReader::<_, Input>::is_encoding_directive_sexp(&value)?
        {
            let pending_changes = unsafe { &mut *self.pending_context_changes.get() };
            SystemReader::<_, Input>::process_encoding_directive(pending_changes, value)?;
            pending_changes.has_changes = true;
            let lazy_sexp = LazySExp {
                expanded_sexp: value.read()?.expect_sexp()?,
            };
            return Ok(SystemStreamItem::EncodingDirective(lazy_sexp));
        }
        // Otherwise, it's an application value.
        let lazy_value = LazyValue::new(value);
        Ok(SystemStreamItem::Value(lazy_value))
    }

    fn interpret_ivm<'top>(
        &self,
        marker: <Encoding as Decoder>::VersionMarker<'top>,
    ) -> IonResult<SystemStreamItem<'top, Encoding>> {
        let new_version = marker.stream_version_after_marker()?;
        // If this is the first item in the stream or we're changing versions, we need to ensure
        // the encoding context is set up for this version.
        if marker.range().start == 0 || new_version != marker.stream_version_before_marker() {
            // SAFETY: Version markers do not hold a reference to the symbol table.
            let pending_changes = unsafe { &mut *self.pending_context_changes.get() };
            pending_changes.switch_to_version = Some(new_version);
            pending_changes.has_changes = true;
        }
        Ok(SystemStreamItem::VersionMarker(marker))
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

        // SAFETY: This is the only place where we modify the encoding context. Take care not to
        //         alias the allocator, symbol table, or macro table inside this `unsafe` scope.
        unsafe {
            // If we're holding a reference to the input data source, drop it.
            (*self.encoding_context.get()).io_buffer_source = IoBufferSource::None.into();
            // Clear the bump allocator.
            self.reset_bump_allocator();
        }

        // If the pending LST has changes to apply, do so.
        // SAFETY: Nothing else holds a reference to the `PendingLst`'s contents, so we can use the
        //         `UnsafeCell` to get a mutable reference to it.
        let pending_lst: &mut PendingContextChanges =
            unsafe { &mut *self.pending_context_changes.get() };
        if pending_lst.has_changes {
            // SAFETY: Nothing else holds a reference to the `EncodingContext`'s contents, so we can use the
            //         `UnsafeCell` to get a mutable reference to its symbol table.
            let encoding_context_ref = unsafe { &mut *self.encoding_context.get() };
            let (macro_table, symbol_table) = encoding_context_ref.tables_mut();
            Self::apply_pending_context_changes(pending_lst, symbol_table, macro_table);
        }
    }

    /// Returns the next application-level value.
    ///
    /// This method will consume and process as many system-level values as possible until it
    /// encounters an application-level value or the end of the stream.
    pub fn next_value(&mut self) -> IonResult<Option<LazyValue<'_, Encoding>>> {
        use SystemStreamItem::*;
        loop {
            match self.next_system_item() {
                Ok(Value(value)) => return Ok(Some(value)),
                Ok(EndOfStream(_)) => return Ok(None),
                Ok(_) => {}
                Err(e) => return Err(e),
            };
        }
    }

    pub fn detected_encoding(&self) -> IonEncoding {
        // SAFETY: We have an immutable reference to `self`, so it's legal for us to have an immutable
        //         reference to one of its fields.
        unsafe { &*self.raw_reader.get() }.encoding()
    }

    /// Returns the next IVM, value, or system value as an `ExpandedStreamItem`.
    ///
    /// This path is less optimized than `next_system_item` because it needs to surface additional
    /// items that do not impact the application. However, it's useful for tooling that needs more
    /// visibility into the expansion process.
    pub fn next_item(&mut self) -> IonResult<ExpandedStreamItem<'_, Encoding>> {
        // If there's already an active macro evaluator, that means the reader is still in the process
        // of expanding a macro invocation it previously encountered. See if it has a value to give us.
        if let Some(ptr) = self.evaluator_ptr.get() {
            // If there's already an evaluator, dereference the pointer.
            let evaluator = Self::ptr_to_evaluator(ptr);
            match evaluator.next() {
                Ok(Some(value)) => {
                    if evaluator.is_empty() {
                        // If the evaluator is empty, unset the pointer so we know not to query it
                        // further.
                        self.evaluator_ptr.set(None);
                    }
                    return Ok(self.interpret_value(value)?.as_expanded_stream_item());
                }
                Ok(None) => {}
                Err(e) => return Err(e),
            }
        }

        // Otherwise, we're now between top level expressions. Take this opportunity to apply any
        // pending changes to the encoding context and reset state as needed.
        self.between_top_level_expressions();

        // See if the raw reader can get another expression from the input stream. It's possible
        // to find an expression that yields no values (for example: `(:none)`), so we perform this
        // step in a loop until we get a value or end-of-stream.
        let context_ref = self.context();

        // Pull another top-level expression from the input stream if one is available.
        use crate::lazy::raw_stream_item::RawStreamItem::*;
        let raw_reader = unsafe { &mut *self.raw_reader.get() };
        match raw_reader.next(context_ref)? {
            VersionMarker(marker) => {
                let _system_item = self.interpret_ivm(marker)?;
                Ok(ExpandedStreamItem::VersionMarker(marker))
            }
            // We got our value; return it.
            Value(raw_value) => {
                let value = LazyExpandedValue::from_literal(context_ref, raw_value);
                Ok(self.interpret_value(value)?.as_expanded_stream_item())
            }
            // It's another macro invocation, we'll add it to the evaluator so it will be evaluated
            // on the next call and then we'll return the e-expression itself.
            EExp(e_exp) => {
                let resolved_e_exp = e_exp.resolve(context_ref)?;

                // Get the current evaluator or make a new one
                let evaluator = match self.evaluator_ptr.get() {
                    // If there's already an evaluator in the bump, it's empty. Overwrite it with our new one.
                    Some(ptr) => {
                        let bump_evaluator_ref = Self::ptr_to_evaluator(ptr);
                        bump_evaluator_ref.push(resolved_e_exp.expand()?);
                        bump_evaluator_ref
                    }
                    // If there's not an evaluator in the bump, make a new one.
                    None => {
                        let new_evaluator = MacroEvaluator::for_eexp(resolved_e_exp)?;
                        context_ref.allocator.alloc_with(|| new_evaluator)
                    }
                };

                // Save the pointer to the evaluator
                self.evaluator_ptr
                    .set(Some(Self::evaluator_to_ptr(evaluator)));

                Ok(ExpandedStreamItem::EExp(resolved_e_exp))
            }
            EndOfStream(end_position) => Ok(ExpandedStreamItem::EndOfStream(end_position)),
        }
    }

    /// Returns the next [`SystemStreamItem`] either by continuing to evaluate a macro invocation
    /// in progress or by pulling another expression from the input stream.
    pub fn next_system_item(&self) -> IonResult<SystemStreamItem<'_, Encoding>> {
        // NB: This method takes an immutable reference to `self` but uses `UnsafeCell` to modify
        //     `self` safely. This allows `next_item` to be used in a loop from next_value without
        //     encountering the borrow checker limitations this method skirts. If/when the borrow
        //     checker issue is addressed, we may change this to `&mut self`.

        // If there's already an active macro evaluator, that means the reader is still in the process
        // of expanding a macro invocation it previously encountered. See if it has a value to give us.
        if let Some(ptr) = self.evaluator_ptr.get() {
            // If there's already an evaluator, dereference the pointer.
            let evaluator = Self::ptr_to_evaluator(ptr);
            match evaluator.next() {
                Ok(Some(value)) => {
                    if evaluator.is_empty() {
                        // If the evaluator is empty, unset the pointer so we know not to query it
                        // further.
                        self.evaluator_ptr.set(None);
                    }
                    return self.interpret_value(value);
                }
                Ok(None) => {}
                Err(e) => return Err(e),
            }
        }

        // Otherwise, we're now between top level expressions. Take this opportunity to apply any
        // pending changes to the encoding context and reset state as needed.
        self.between_top_level_expressions();

        // See if the raw reader can get another expression from the input stream. It's possible
        // to find an expression that yields no values (for example: `(:none)`), so we perform this
        // step in a loop until we get a value or end-of-stream.
        let context_ref = self.context();

        loop {
            // Pull another top-level expression from the input stream if one is available.
            use crate::lazy::raw_stream_item::RawStreamItem::*;
            let raw_reader = unsafe { &mut *self.raw_reader.get() };
            match raw_reader.next(context_ref)? {
                VersionMarker(marker) => {
                    return self.interpret_ivm(marker);
                }
                // We got our value; return it.
                Value(raw_value) => {
                    let value = LazyExpandedValue::from_literal(context_ref, raw_value);
                    return self.interpret_value(value);
                }
                // It's another macro invocation, we'll start evaluating it.
                EExp(e_exp) => {
                    let resolved_e_exp = e_exp.resolve(context_ref)?;

                    // If this e-expression invokes a template with a non-system, singleton expansion, we can use the
                    // e-expression to back a LazyExpandedValue. It will only be evaluated if the user calls `read()`.
                    if let Some(value) = LazyExpandedValue::try_from_e_expression(resolved_e_exp) {
                        // Because the expansion is guaranteed not to be a system value, we do not need to interpret it.
                        return Ok(SystemStreamItem::Value(LazyValue::new(value)));
                    }
                    let new_evaluator = MacroEvaluator::for_eexp(resolved_e_exp)?;
                    // Get the current evaluator or make a new one
                    let evaluator = match self.evaluator_ptr.get() {
                        // If there's already an evaluator in the bump, it's empty. Overwrite it with our new one.
                        Some(ptr) => {
                            let bump_evaluator_ref = Self::ptr_to_evaluator(ptr);
                            *bump_evaluator_ref = new_evaluator;
                            bump_evaluator_ref
                        }
                        // If there's not an evaluator in the bump, make a new one.
                        None => context_ref.allocator.alloc_with(|| new_evaluator),
                    };

                    // Try to get a value by starting to evaluate the e-expression.
                    if let Some(value) = evaluator.next()? {
                        // If we get a value and the evaluator isn't empty yet, save its pointer
                        // so we can try to get more out of it when `next_at_or_above_depth` is called again.
                        if !evaluator.is_empty() {
                            self.evaluator_ptr
                                .set(Some(Self::evaluator_to_ptr(evaluator)));
                        }
                        // If we get a value, return it.
                        return self.interpret_value(value);
                    } else {
                        // If the expression was equivalent to `(:none)`, return to the top of
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
}

/// The source of data backing a [`LazyExpandedValue`].
#[derive(Copy, Clone)]
pub enum ExpandedValueSource<'top, D: Decoder> {
    /// This value was a literal in the input stream.
    ValueLiteral(D::Value<'top>),
    /// This value is backed by an e-expression invoking a macro known to produce a single value.
    SingletonEExp(EExpression<'top, D>),
    /// This value was part of a template definition.
    Template(Environment<'top, D>, TemplateElement<'top>),
    /// This value was the computed result of a macro invocation like `(:make_string `...)`.
    Constructed(
        // TODO: Make this an associated type on the LazyDecoder trait so 1.0 types can set
        //       it to `Never` and the compiler can eliminate this code path where applicable.
        // Constructed data stored in the bump allocator. Holding references instead of the data
        // itself allows this type (and those that contain it) to impl `Copy`.
        &'top [SymbolRef<'top>], // Annotations (if any)
        &'top ValueRef<'top, D>, // Value
    ),
}

impl<Encoding: Decoder> Debug for ExpandedValueSource<'_, Encoding> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            ExpandedValueSource::SingletonEExp(eexp) => write!(f, "singleton eexp {eexp:?}"),
            ExpandedValueSource::ValueLiteral(v) => write!(f, "value literal {v:?}"),
            ExpandedValueSource::Template(_, template_element) => {
                write!(f, "template {:?}", template_element.value())
            }
            ExpandedValueSource::Constructed(_, value) => write!(f, "constructed {value:?}"),
        }
    }
}

#[derive(Debug, Copy, Clone)]
/// Expanded stream components that a RawReader may encounter.
/// Like `RawStreamItem`, `ExpandedStreamItem` includes both value literals and e-expressions
/// found in the input.
/// Unlike `RawStreamItem`, `ExpandedStreamItem` _also_ includes ephemeral values that were produced
/// by evaluating the e-expressions. Additionally, system values are identified and surfaced as
/// either `SymbolTable`s or `EncodingDirectives`s.
pub enum ExpandedStreamItem<'top, D: Decoder> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(D::VersionMarker<'top>),
    /// An Ion 1.1+ macro invocation. Ion 1.0 readers will never return a macro invocation.
    EExp(EExpression<'top, D>),
    /// An Ion application value.
    Value(LazyValue<'top, D>),
    /// An annotated Ion struct representing a symbol table.
    SymbolTable(LazyStruct<'top, D>),
    /// An annotated Ion s-expression representing an encoding directive.
    EncodingDirective(LazySExp<'top, D>),
    /// The end of the stream
    EndOfStream(EndPosition),
}

impl<'top, D: Decoder> ExpandedStreamItem<'top, D> {
    /// Returns `true` if this item was produced by evaluating a macro. Otherwise, returns `false`.
    pub fn is_ephemeral(&self) -> bool {
        use ExpandedStreamItem::*;
        match self {
            VersionMarker(_) | EExp(_) | EndOfStream(_) => false,
            Value(value) => value.expanded().is_ephemeral(),
            SymbolTable(symtab) => symtab.as_value().expanded().is_ephemeral(),
            EncodingDirective(directive) => directive.as_value().expanded().is_ephemeral(),
        }
    }

    /// If this stream item is not ephemeral, returns the `LazyRawStreamItem` backing it.
    pub fn raw_item(&self) -> Option<LazyRawStreamItem<'top, D>> {
        use ExpandedStreamItem::*;
        let raw_item = match self {
            VersionMarker(m) => RawStreamItem::VersionMarker(*m),
            EExp(eexp) => RawStreamItem::EExp(eexp.raw_invocation),
            Value(v) => return v.raw().map(RawStreamItem::Value),
            SymbolTable(symbol_table) => {
                return symbol_table.as_value().raw().map(RawStreamItem::Value)
            }
            EncodingDirective(directive) => {
                return directive.as_value().raw().map(RawStreamItem::Value)
            }
            EndOfStream(position) => RawStreamItem::EndOfStream(*position),
        };
        Some(raw_item)
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
    macro_ref: &'top Macro,
    signature_index: u16,
}

impl<'top> TemplateVariableReference<'top> {
    pub fn new(macro_ref: &'top Macro, signature_index: u16) -> Self {
        Self {
            macro_ref,
            signature_index,
        }
    }

    pub fn name(&self) -> &'top str {
        self.macro_ref.signature().parameters()[self.signature_index()].name()
    }

    pub fn host_macro(&self) -> &'top Macro {
        self.macro_ref
    }

    pub fn signature_index(&self) -> usize {
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

impl<Encoding: Decoder> Debug for LazyExpandedValue<'_, Encoding> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.read_resolved()?)
    }
}

impl<'top, Encoding: Decoder> LazyExpandedValue<'top, Encoding> {
    // If the provided e-expression can be resolved to a template macro that is eligible to back
    // a lazy value without first being evaluated, returns `Some(lazy_expanded_value)`.
    // To be eligible, the body of the template macro must be an Ion value literal that is not
    // a system value.
    pub(crate) fn try_from_e_expression(eexp: EExpression<'top, Encoding>) -> Option<Self> {
        let analysis = eexp.expansion_analysis();
        if !analysis.can_be_lazily_evaluated_at_top_level() {
            return None;
        }

        Some(Self {
            context: eexp.context,
            source: ExpandedValueSource::SingletonEExp(eexp),
            variable: None,
        })
    }

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
        annotations: &'top [SymbolRef<'top>],
        value: &'top ValueRef<'top, Encoding>,
    ) -> Self {
        Self {
            context,
            source: ExpandedValueSource::Constructed(annotations, value),
            variable: None,
        }
    }

    pub(crate) fn via_variable(
        mut self,
        variable_ref: Option<TemplateVariableReference<'top>>,
    ) -> Self {
        self.variable = variable_ref;
        self
    }

    pub fn ion_type(&self) -> IonType {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.ion_type(),
            Template(_, element) => element.value().ion_type(),
            Constructed(_annotations, value) => value.ion_type(),
            SingletonEExp(eexp) => eexp.require_expansion_singleton().ion_type(),
        }
    }

    pub fn is_null(&self) -> bool {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.is_null(),
            Template(_, element) => element.value().is_null(),
            Constructed(_, value) => {
                matches!(value, ValueRef::Null(_))
            }
            SingletonEExp(eexp) => eexp.require_expansion_singleton().is_null(),
        }
    }

    pub fn has_annotations(&self) -> bool {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.has_annotations(),
            Template(_, element) => !element.annotations().is_empty(),
            Constructed(annotations, _) => !annotations.is_empty(),
            SingletonEExp(eexp) => eexp.require_expansion_singleton().has_annotations(),
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
            Constructed(annotations, _value) => {
                // For now we return an empty iterator
                ExpandedAnnotationsIterator::new(ExpandedAnnotationsSource::Constructed(
                    annotations.iter(),
                ))
            }
            SingletonEExp(eexp) => ExpandedAnnotationsIterator::new(
                ExpandedAnnotationsSource::Template(eexp.require_singleton_annotations()),
            ),
        }
    }

    #[inline]
    pub fn read(&self) -> IonResult<ExpandedValueRef<'top, Encoding>> {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => Ok(ExpandedValueRef::from_raw(self.context, value.read()?)),
            Template(environment, element) => Ok(ExpandedValueRef::from_template(
                self.context,
                *environment,
                element,
            )),
            Constructed(_annotations, value) => Ok((**value).as_expanded()),
            SingletonEExp(ref eexp) => eexp.expand_to_single_value()?.read(),
        }
    }

    #[inline(always)]
    pub fn read_resolved(&self) -> IonResult<ValueRef<'top, Encoding>> {
        use ExpandedValueSource::*;
        match &self.source {
            ValueLiteral(value) => value.read_resolved(self.context),
            Template(environment, element) => {
                Ok(ValueRef::from_template(self.context, *environment, element))
            }
            Constructed(_annotations, value) => Ok(**value),
            SingletonEExp(ref eexp) => self.read_resolved_singleton_eexp(eexp),
        }
    }

    #[inline(never)]
    fn read_resolved_singleton_eexp(
        &self,
        eexp: &EExpression<'top, Encoding>,
    ) -> IonResult<ValueRef<'top, Encoding>> {
        let new_expansion = MacroExpr::from_eexp(*eexp).expand()?;
        new_expansion.expand_singleton()?.read_resolved()
    }

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    pub fn source(&self) -> ExpandedValueSource<'top, Encoding> {
        self.source
    }

    pub fn expect_value_literal(&self) -> IonResult<Encoding::Value<'top>> {
        if let ExpandedValueSource::ValueLiteral(literal) = self.source {
            return Ok(literal);
        }
        IonResult::decoding_error("expected LazyExpandedValue to be a literal")
    }

    /// Returns `true` if this value was produced by evaluating a macro. Otherwise, returns `false`.
    pub fn is_ephemeral(&self) -> bool {
        !matches!(&self.source, ExpandedValueSource::ValueLiteral(_)) || self.is_parameter()
    }

    /// Returns `true` if this value was an argument passed into a macro.
    pub fn is_parameter(&self) -> bool {
        self.variable.is_some()
    }

    pub fn variable(&self) -> Option<TemplateVariableReference<'top>> {
        self.variable
    }

    pub fn range(&self) -> Option<Range<usize>> {
        if let ExpandedValueSource::ValueLiteral(value) = &self.source {
            return Some(value.range());
        }
        None
    }

    pub fn span(&self) -> Option<Span<'top>> {
        if let ExpandedValueSource::ValueLiteral(value) = &self.source {
            return Some(value.span());
        }
        None
    }

    #[cfg(feature = "source-location")]
    pub fn location(&self) -> Option<(usize, usize)> {
        if let ExpandedValueSource::ValueLiteral(value) = &self.source {
            return Some(value.location());
        }
        None
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
    Constructed(std::slice::Iter<'top, SymbolRef<'top>>),
}

impl<Encoding: Decoder> ExpandedAnnotationsSource<'_, Encoding> {
    pub fn empty() -> Self {
        Self::Constructed(std::slice::Iter::default())
    }
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
                .map(|symbol| Ok(symbol.as_raw_symbol_ref())),
            Constructed(iter) => Some(Ok(iter.next()?.as_raw_symbol_ref())),
        }
    }
}

#[derive(Copy, Clone)]
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

impl<Encoding: Decoder> PartialEq for ExpandedValueRef<'_, Encoding> {
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

impl<D: Decoder> Debug for ExpandedValueRef<'_, D> {
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
            Symbol(s) => ExpandedValueRef::Symbol(s.as_raw_symbol_ref()),
            Blob(b) => ExpandedValueRef::Blob(BytesRef::from(b.as_ref())),
            Clob(c) => ExpandedValueRef::Clob(BytesRef::from(c.as_ref())),
            List => ExpandedValueRef::List(LazyExpandedList::from_template(
                context,
                environment,
                *element,
            )),
            SExp => ExpandedValueRef::SExp(LazyExpandedSExp::from_template(
                context,
                environment,
                *element,
            )),
            Struct(index) => ExpandedValueRef::Struct(LazyExpandedStruct::from_template(
                context,
                environment,
                element,
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
