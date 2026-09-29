//! A view of the Ion data produced by the "raw" readers, with symbol tokens resolvable against the
//! active symbol table.
//!
//! The types defined in this module each wrap their corresponding type from the "raw" view of the
//! data, replacing the word `Raw` with the word `Expanded` in the type name.
//!
//! The expanded types expose largely the same API, with one key difference: most method invocations
//! require an [`EncodingContextRef`] to be specified, giving the reader access to the symbol table.
//!
//! Note that symbol tokens are only resolved where necessary; where possible they will remain
//! unresolved. Leaving symbol tokens unresolved is an optimization; annotations, field names, and
//! symbol values that are ignored by the reader do not incur the cost of symbol table resolution.

use bumpalo::Bump as BumpAllocator;
use sequence::{LazyExpandedList, LazyExpandedSExp};
use std::cell::UnsafeCell;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, Range};
use std::rc::Rc;

use crate::catalog::Catalog;
use crate::lazy::any_encoding::{IonEncoding, IonVersion};
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::{Decoder, LazyRawValue};
use crate::lazy::encoding::RawValueLiteral;
use crate::lazy::expanded::r#struct::LazyExpandedStruct;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem};
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::str_ref::StrRef;
use crate::lazy::streaming_raw_reader::{IoBuffer, IoBufferHandle, IonInput, StreamingRawReader};
use crate::lazy::system_reader::{PendingContextChanges, SystemReader};
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::value::LazyValue;
use crate::location::SourceLocation;
use crate::result::IonFailure;
use crate::{
    Decimal, HasRange, HasSpan, Int, IonResult, IonType, RawStreamItem, RawSymbolRef,
    RawVersionMarker, Span, SymbolTable, Timestamp, ValueRef,
};

// All of these modules (and most of their types) are currently `pub` as the lazy reader is gated
// behind an experimental feature flag. We may constrain access to them in the future as the code
// stabilizes.
pub mod lazy_element;
pub mod sequence;
pub mod r#struct;

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
    //      re-used across top-level values. For example, a `LazyElement` that clones this context
    //      shares the symbol table and the arena with the reader rather than copying them.
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
        let ion_version = symbol_table.ion_version();
        write!(
            f,
            "EncodingContext {{ion_version = {ion_version:?}, {num_symbols} symbols}} "
        )
    }
}

impl EncodingContext {
    pub fn new(symbol_table: SymbolTable, allocator: BumpAllocator) -> Self {
        Self {
            symbol_table: Rc::new(symbol_table),
            allocator: Rc::new(allocator),
            io_buffer_source: IoBufferSource::None.into(),
        }
    }

    pub fn for_ion_version(version: IonVersion) -> Self {
        Self::new(SymbolTable::new(version), BumpAllocator::new())
    }

    pub fn empty() -> Self {
        Self::new(
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

    /// If there is only one strong reference to the symbol table, returns a mutable reference to it.
    /// Otherwise, clones the symbol table, allowing the other referents to continue using the
    /// previous copy.
    pub(crate) fn symbol_table_mut(&mut self) -> &mut SymbolTable {
        Rc::make_mut(&mut self.symbol_table)
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

    pub fn location_for_span(&self, span: Option<Span<'_>>) -> Option<SourceLocation> {
        // SAFETY: `io_buffer_source` is an `UnsafeCell` so that the `StreamingRawReader` can set it
        //         after each top-level value; it is only ever mutated between `'top` lifetimes, so
        //         no mutation can be in flight while this reference is live. The reference does not
        //         escape this function -- the returned `SourceLocation` is owned and borrows nothing
        //         from the `IoBufferSource` -- so callers cannot hold it across a mutation. That is
        //         what allows `impl TryFrom<LazyValue> for Element` to hoist its `location()` call
        //         above `read()`.
        match unsafe { &*self.io_buffer_source.get() } {
            IoBufferSource::IoBuffer(ref buffer) => Some(
                buffer
                    .source_location_state()
                    .calculate_location_for_span(span?),
            ),
            IoBufferSource::Reader(handle) => Some(
                handle
                    .source_location_state()
                    .calculate_location_for_span(span?),
            ),
            IoBufferSource::None => None,
        }
    }
}

impl Deref for EncodingContextRef<'_> {
    type Target = EncodingContext;

    fn deref(&self) -> &Self::Target {
        self.context
    }
}

/// A reader that surfaces the raw values found in the data stream to the caller, resolving symbol
/// tokens against the active symbol table as needed.
#[cfg_attr(feature = "experimental-tooling-apis", visibility::make(pub))]
pub(crate) struct ExpandingReader<Encoding: Decoder, Input: IonInput> {
    raw_reader: UnsafeCell<StreamingRawReader<Encoding, Input>>,

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
    // Holds information found in symbol tables that can be applied to the encoding context the
    // next time the reader is between top-level expressions.
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
            encoding_context: EncodingContext::for_ion_version(encoding.version()).into(),
            pending_context_changes: PendingContextChanges::new().into(),
            catalog,
        }
    }

    pub fn context(&self) -> EncodingContextRef<'_> {
        // SAFETY: The only time that the symbol table and allocator can be modified is in the body
        // of the method `between_top_level_expressions`. As long as nothing holds a reference to the
        // `EncodingContext` we create here when that method is running, this is safe.
        unsafe { (*self.encoding_context.get()).get_ref() }
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

    /// Updates the encoding context with the information stored in the `PendingContextChanges`.
    fn apply_pending_context_changes(
        pending_changes: &mut PendingContextChanges,
        symbol_table: &mut SymbolTable,
    ) {
        if let Some(new_version) = pending_changes.switch_to_version.take() {
            symbol_table.reset_to_version(new_version);
            pending_changes.has_changes = false;
            pending_changes.is_lst_append = false;
            // If we're switching to a new version, the last stream item was a version marker
            // and there are no other pending changes. The `take()` above clears the `switch_to_version`.
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
        // SAFETY: Version markers do not hold a reference to the symbol table.
        let pending_changes = unsafe { &mut *self.pending_context_changes.get() };
        pending_changes.switch_to_version = Some(new_version);
        pending_changes.has_changes = true;
        Ok(SystemStreamItem::VersionMarker(marker))
    }

    /// This method is invoked just before the reader begins reading the next top-level expression
    /// from the data stream. It is NOT invoked between multiple top level _values_ coming from a
    /// single expression.
    ///
    /// This is the reader's opportunity to make any pending changes to the encoding context.
    fn between_top_level_expressions(&self) {
        // SAFETY: This is the only place where we modify the encoding context. Take care not to
        //         alias the allocator or the symbol table inside this `unsafe` scope.
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
            let symbol_table = encoding_context_ref.symbol_table_mut();
            Self::apply_pending_context_changes(pending_lst, symbol_table);
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
    /// visibility into the stream's encoding.
    pub fn next_item(&mut self) -> IonResult<ExpandedStreamItem<'_, Encoding>> {
        // We're now between top level expressions. Take this opportunity to apply any pending
        // changes to the encoding context and reset state as needed.
        self.between_top_level_expressions();

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
            EndOfStream(end_position) => Ok(ExpandedStreamItem::EndOfStream(end_position)),
        }
    }

    /// Returns the next [`SystemStreamItem`] by pulling another expression from the input stream.
    pub fn next_system_item(&self) -> IonResult<SystemStreamItem<'_, Encoding>> {
        // NB: This method takes an immutable reference to `self` but uses `UnsafeCell` to modify
        //     `self` safely. This allows `next_item` to be used in a loop from next_value without
        //     encountering the borrow checker limitations this method skirts. If/when the borrow
        //     checker issue is addressed, we may change this to `&mut self`.

        // We're now between top level expressions. Take this opportunity to apply any pending
        // changes to the encoding context and reset state as needed.
        self.between_top_level_expressions();

        let context_ref = self.context();

        // Pull another top-level expression from the input stream if one is available.
        use crate::lazy::raw_stream_item::RawStreamItem::*;
        let raw_reader = unsafe { &mut *self.raw_reader.get() };
        match raw_reader.next(context_ref)? {
            VersionMarker(marker) => self.interpret_ivm(marker),
            // We got our value; return it.
            Value(raw_value) => {
                let value = LazyExpandedValue::from_literal(context_ref, raw_value);
                self.interpret_value(value)
            }
            EndOfStream(end_position) => Ok(SystemStreamItem::EndOfStream(end_position)),
        }
    }
}

/// The source of data backing a [`LazyExpandedValue`].
//
// This enum used to have variants for macro-produced values (`SingletonEExp`, `Template`, and
// `Constructed`). Ion 1.0 has no macros, so only `ValueLiteral` remains.
#[derive(Copy, Clone)]
pub enum ExpandedValueSource<'top, D: Decoder> {
    /// This value was a literal in the input stream.
    ValueLiteral(D::Value<'top>),
}

impl<Encoding: Decoder> Debug for ExpandedValueSource<'_, Encoding> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            ExpandedValueSource::ValueLiteral(v) => write!(f, "value literal {v:?}"),
        }
    }
}

#[derive(Debug, Copy, Clone)]
/// Stream components that a reader may encounter, with system values identified and surfaced as
/// `SymbolTable`s.
#[cfg_attr(feature = "experimental-tooling-apis", visibility::make(pub))]
pub(crate) enum ExpandedStreamItem<'top, D: Decoder> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(D::VersionMarker<'top>),
    /// An Ion application value.
    Value(LazyValue<'top, D>),
    /// An annotated Ion struct representing a symbol table.
    SymbolTable(LazyStruct<'top, D>),
    /// The end of the stream
    EndOfStream(EndPosition),
}

#[cfg_attr(not(feature = "experimental-tooling-apis"), allow(dead_code))]
impl<'top, D: Decoder> ExpandedStreamItem<'top, D> {
    /// Returns `true` if this item was produced by evaluating a macro. Otherwise, returns `false`.
    pub fn is_ephemeral(&self) -> bool {
        use ExpandedStreamItem::*;
        match self {
            VersionMarker(_) | EndOfStream(_) => false,
            Value(value) => value.expanded().is_ephemeral(),
            SymbolTable(symtab) => symtab.as_value().expanded().is_ephemeral(),
        }
    }

    /// If this stream item is not ephemeral, returns the `LazyRawStreamItem` backing it.
    pub fn raw_item(&self) -> Option<LazyRawStreamItem<'top, D>> {
        use ExpandedStreamItem::*;
        let raw_item = match self {
            VersionMarker(m) => RawStreamItem::VersionMarker(*m),
            Value(v) => return v.raw().map(RawStreamItem::Value),
            SymbolTable(symbol_table) => {
                return symbol_table.as_value().raw().map(RawStreamItem::Value)
            }
            EndOfStream(position) => RawStreamItem::EndOfStream(*position),
        };
        Some(raw_item)
    }
}

// Converts the raw value literal types associated with each format decoder (e.g. LazyRawTextValue_1_0)
// into an ExpandedValueSource.
impl<'top, V: RawValueLiteral, Encoding: Decoder<Value<'top> = V>> From<V>
    for ExpandedValueSource<'top, Encoding>
{
    fn from(value: V) -> Self {
        ExpandedValueSource::ValueLiteral(value)
    }
}

/// A value produced by expanding the 'raw' view of the input data.
#[derive(Copy, Clone)]
pub struct LazyExpandedValue<'top, Encoding: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) source: ExpandedValueSource<'top, Encoding>,
}

impl<Encoding: Decoder> Debug for LazyExpandedValue<'_, Encoding> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.read_resolved()?)
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
        }
    }

    pub fn ion_type(&self) -> IonType {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        value.ion_type()
    }

    pub fn is_null(&self) -> bool {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        value.is_null()
    }

    pub fn has_annotations(&self) -> bool {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        value.has_annotations()
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, Encoding> {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        ExpandedAnnotationsIterator::new(ExpandedAnnotationsSource::ValueLiteral(
            value.annotations(),
        ))
    }

    #[inline]
    pub fn read(&self) -> IonResult<ExpandedValueRef<'top, Encoding>> {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        Ok(ExpandedValueRef::from_raw(self.context, value.read()?))
    }

    #[inline(always)]
    pub fn read_resolved(&self) -> IonResult<ValueRef<'top, Encoding>> {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        value.read_resolved(self.context)
    }

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    pub fn source(&self) -> ExpandedValueSource<'top, Encoding> {
        self.source
    }

    pub fn expect_value_literal(&self) -> IonResult<Encoding::Value<'top>> {
        let ExpandedValueSource::ValueLiteral(literal) = self.source;
        Ok(literal)
    }

    /// Returns `true` if this value was produced by evaluating a macro. Otherwise, returns `false`.
    ///
    /// Ion 1.0 has no macros, so every value is a literal from the input stream and this always
    /// returns `false`.
    pub fn is_ephemeral(&self) -> bool {
        false
    }

    pub fn range(&self) -> Option<Range<usize>> {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        Some(value.range())
    }

    pub fn span(&self) -> Option<Span<'top>> {
        let ExpandedValueSource::ValueLiteral(value) = &self.source;
        Some(value.span())
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

// The `Template` and `Constructed` variants this enum used to have were only reachable from macro
// expansion; Ion 1.0 annotations always come from a value literal in the input stream.
pub enum ExpandedAnnotationsSource<'top, Encoding: Decoder> {
    ValueLiteral(Encoding::AnnotationsIterator<'top>),
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
        let ExpandedAnnotationsSource::ValueLiteral(value_annotations_iter) = &mut self.source;
        value_annotations_iter.next()
    }
}

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
            "expected a(n) {expected_name} but found a {self:?}",
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
            Null(ion_type) => write!(f, "null.{ion_type}"),
            Bool(b) => write!(f, "{b}"),
            Int(i) => write!(f, "{i}"),
            Float(float) => write!(f, "{float}"),
            Decimal(d) => write!(f, "{d}"),
            Timestamp(t) => write!(f, "{t}"),
            String(s) => write!(f, "{s}"),
            Symbol(s) => write!(f, "{s:?}"),
            Blob(b) => write!(f, "blob ({} bytes)", b.len()),
            Clob(c) => write!(f, "clob ({} bytes)", c.len()),
            // TODO: Debug impls for LazyExpandedRaw[ContainerType]
            SExp(_s) => write!(f, "<sexp>"),
            List(_l) => write!(f, "<list>"),
            Struct(_s) => write!(f, "<struct>"),
        }
    }
}
