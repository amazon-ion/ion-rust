use std::mem;

use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::annotation_seq::AnnotationsVec;
use crate::lazy::encoder::binary::v1_0::value_writer::{BinaryValueWriter_1_0, MAX_INLINE_LENGTH};
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::result::cold_error;
use crate::{v1_0, ContextWriter, Encoding, IonResult, RawSymbolRef, ValueWriterConfig};

/// The number of header bytes reserved ahead of a container's body or an annotations wrapper's
/// contents: a type descriptor plus a one-byte VarUInt length, which is exact for 14–127 byte
/// bodies. Shorter bodies shift left by one byte when the header is filled in; longer ones shift
/// right.
pub(crate) const HEADER_RESERVE: usize = 2;

/// The number of header bytes (type descriptor plus any VarUInt length) needed for a value whose
/// body is `length` bytes long.
#[inline]
pub(crate) fn header_length(length: usize) -> usize {
    if length <= MAX_INLINE_LENGTH {
        1
    } else {
        1 + VarUInt::encoded_size_of(length as u64)
    }
}

/// Moves everything from `from` to the end of `buffer` by `shift` bytes.
#[inline(always)]
pub(crate) fn shift_tail(buffer: &mut Vec<u8>, from: usize, shift: isize) {
    // A zero shift is checked inline and only an actual move makes a call. Zero is common for
    // container headers (14–127 byte bodies) and `annot_length` (under 128). Each header that
    // shrinks to one byte (contents of 13 bytes or fewer) shifts what follows it left by one, so a
    // small annotated container's body shifts by -2.
    if shift != 0 {
        move_tail(buffer, from, shift);
    }
}

#[inline(never)]
fn move_tail(buffer: &mut Vec<u8>, from: usize, shift: isize) {
    let end = buffer.len();
    if shift > 0 {
        let shift = shift as usize;
        buffer.resize(end + shift, 0);
        buffer.copy_within(from..end, from + shift);
    } else {
        let shift = shift.unsigned_abs();
        buffer.copy_within(from..end, from - shift);
        buffer.truncate(end - shift);
    }
}

/// Writes `value` as a VarUInt that fills `slot`, which must be `VarUInt::encoded_size_of(value)`
/// bytes long.
#[inline]
pub(crate) fn write_var_uint_into(slot: &mut [u8], mut value: usize) {
    if let [byte] = slot {
        *byte = 0x80 | value as u8;
        return;
    }
    let mut end_flag = 0x80;
    for byte in slot.iter_mut().rev() {
        *byte = (value & 0x7F) as u8 | end_flag;
        end_flag = 0;
        value >>= 7;
    }
}

/// Writes a type descriptor with `type_code` and a length of `length` into `slot`, which must be
/// `header_length(length)` bytes long.
#[inline]
pub(crate) fn write_header(slot: &mut [u8], type_code: u8, length: usize) {
    if length <= MAX_INLINE_LENGTH {
        slot[0] = type_code | length as u8;
    } else {
        slot[0] = type_code | 0x0E;
        write_var_uint_into(&mut slot[1..], length);
    }
}

/// An RAII guard that truncates `buffer` back to its length at construction when dropped, unless
/// [`commit`](Self::commit) is called first. An encoding that fails or panics part way through
/// leaves no bytes behind.
pub(crate) struct TruncateOnDrop<'a> {
    pub(crate) buffer: &'a mut Vec<u8>,
    pub(crate) start: usize,
}

impl<'a> TruncateOnDrop<'a> {
    pub(crate) fn new(buffer: &'a mut Vec<u8>) -> Self {
        let start = buffer.len();
        Self { buffer, start }
    }

    /// Keeps everything written since construction.
    pub(crate) fn commit(self) {
        mem::forget(self);
    }
}

impl Drop for TruncateOnDrop<'_> {
    fn drop(&mut self) {
        self.buffer.truncate(self.start);
    }
}

/// Appends the start of an annotations wrapper to `buffer`: [`HEADER_RESERVE`] bytes reserved for
/// the wrapper header, then `annot_length` and the annotation SIDs. Writes nothing if `annotations`
/// is empty. On error, part of the prefix may be left in `buffer`; callers roll back with their own
/// [`TruncateOnDrop`].
pub(crate) fn write_annotations_prefix(
    buffer: &mut Vec<u8>,
    annotations: &AnnotationsVec<'_>,
) -> IonResult<()> {
    if annotations.is_empty() {
        return Ok(());
    }
    // Reserve the wrapper header and a one-byte `annot_length`.
    let annot_length_position = buffer.len() + HEADER_RESERVE;
    let sids_start = annot_length_position + 1;
    buffer.resize(sids_start, 0);
    for annotation in annotations {
        let sid = match annotation.as_raw_symbol_ref() {
            RawSymbolRef::SymbolId(sid) => sid,
            other_token => {
                return cold_error!(
                    encoding_error,
                    "binary Ion 1.0 only supports symbol ID annotations (received '{other_token:?}')"
                );
            }
        };
        VarUInt::write_u64(buffer, sid as u64)?;
    }
    let sids_length = buffer.len() - sids_start;
    let annot_length_size = VarUInt::encoded_size_of(sids_length as u64);
    shift_tail(buffer, sids_start, annot_length_size as isize - 1);
    write_var_uint_into(
        &mut buffer[annot_length_position..annot_length_position + annot_length_size],
        sids_length,
    );
    Ok(())
}

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_0`],
/// [`BinarySExpWriter_1_0`], and [`BinaryStructWriter_1_0`].
///
/// The container is encoded in place in its parent's buffer: [`HEADER_RESERVE`] bytes are reserved
/// for its header (and for its annotations wrapper's header, if any) and filled in by `end`.
/// Dropping the writer without `end` truncates the buffer back to where the container began, so a
/// container writer must be closed or dropped, not leaked; a leaked writer leaves its partial
/// encoding in the buffer.
pub struct BinaryContainerWriter_1_0<'value> {
    // A byte containing the high nibble of the encoded container's type descriptor.
    type_code: u8,
    // The container's encoding, from where it begins to the end of the buffer.
    encoding: TruncateOnDrop<'value>,
    // Where the container's reserved header begins. If the container is annotated, its reserved
    // annotations wrapper header is at `encoding.start` and its annotations sequence lies between
    // the two.
    header: usize,
}

impl<'value> BinaryContainerWriter_1_0<'value> {
    pub fn new(type_code: u8, buffer: &'value mut Vec<u8>) -> Self {
        let encoding = TruncateOnDrop::new(buffer);
        let header = encoding.start;
        encoding.buffer.resize(header + HEADER_RESERVE, 0);
        Self {
            type_code,
            encoding,
            header,
        }
    }

    /// Like [`new`](Self::new), but wraps the container in `annotations` (if there are any).
    pub fn new_annotated(
        type_code: u8,
        buffer: &'value mut Vec<u8>,
        annotations: &AnnotationsVec<'_>,
    ) -> IonResult<Self> {
        let encoding = TruncateOnDrop::new(buffer);
        write_annotations_prefix(encoding.buffer, annotations)?;
        let header = encoding.buffer.len();
        encoding.buffer.resize(header + HEADER_RESERVE, 0);
        Ok(Self {
            type_code,
            encoding,
            header,
        })
    }

    fn is_annotated(&self) -> bool {
        self.header != self.encoding.start
    }

    /// Fills in the reserved header(s), shifting the encoding where a header turned out shorter or
    /// longer than [`HEADER_RESERVE`].
    pub fn end(mut self) {
        let body_start = self.header + HEADER_RESERVE;
        let body_length = self.encoding.buffer.len() - body_start;
        let header_size = header_length(body_length);
        if self.is_annotated() {
            self.end_annotated(body_length, header_size);
        } else {
            shift_tail(
                self.encoding.buffer,
                body_start,
                header_size as isize - HEADER_RESERVE as isize,
            );
            write_header(
                &mut self.encoding.buffer[self.header..self.header + header_size],
                self.type_code,
                body_length,
            );
        }
        self.encoding.commit();
    }

    /// The annotated part of `end`, kept out of line so that closing an unannotated container
    /// stays small.
    #[inline(never)]
    fn end_annotated(&mut self, body_length: usize, header_size: usize) {
        let body_start = self.header + HEADER_RESERVE;
        let header_shift = header_size as isize - HEADER_RESERVE as isize;
        let start = self.encoding.start;
        let annotations_start = start + HEADER_RESERVE;
        let envelope_length = (self.header - annotations_start) + header_size + body_length;
        let wrapper_size = header_length(envelope_length);
        let wrapper_shift = wrapper_size as isize - HEADER_RESERVE as isize;
        // The body moves first: its destination starts at or after `self.header`, so it never
        // overwrites the annotations sequence, whose own destination then ends `header_size` bytes
        // before the body's new start.
        shift_tail(
            self.encoding.buffer,
            body_start,
            wrapper_shift + header_shift,
        );
        self.shift_annotations(annotations_start, wrapper_shift);
        let header = (self.header as isize + wrapper_shift) as usize;
        write_header(
            &mut self.encoding.buffer[header..header + header_size],
            self.type_code,
            body_length,
        );
        write_header(
            &mut self.encoding.buffer[start..start + wrapper_size],
            0xE0,
            envelope_length,
        );
    }

    /// Moves the annotations sequence (`annotations_start..self.header`) by `shift` bytes.
    fn shift_annotations(&mut self, annotations_start: usize, shift: isize) {
        if shift != 0 {
            let destination = (annotations_start as isize + shift) as usize;
            self.encoding
                .buffer
                .copy_within(annotations_start..self.header, destination);
        }
    }
}

const LIST_TYPE_CODE: u8 = 0xB0;
const SEXP_TYPE_CODE: u8 = 0xC0;
const STRUCT_TYPE_CODE: u8 = 0xD0;

pub struct BinaryListWriter_1_0<'value> {
    pub(crate) container_writer: BinaryContainerWriter_1_0<'value>,
}

impl<'value> BinaryListWriter_1_0<'value> {
    pub(crate) fn with_container_writer(
        container_writer: BinaryContainerWriter_1_0<'value>,
    ) -> Self {
        Self { container_writer }
    }

    pub(crate) fn new(buffer: &'value mut Vec<u8>) -> Self {
        BinaryListWriter_1_0::with_container_writer(BinaryContainerWriter_1_0::new(
            LIST_TYPE_CODE,
            buffer,
        ))
    }

    pub(crate) fn new_annotated(
        buffer: &'value mut Vec<u8>,
        annotations: &AnnotationsVec<'_>,
    ) -> IonResult<Self> {
        let container_writer =
            BinaryContainerWriter_1_0::new_annotated(LIST_TYPE_CODE, buffer, annotations)?;
        Ok(Self::with_container_writer(container_writer))
    }
}

impl ContextWriter for BinaryListWriter_1_0<'_> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a>
    where
        Self: 'a;
}

impl MakeValueWriter for BinaryListWriter_1_0<'_> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        BinaryValueWriter_1_0::new(&mut *self.container_writer.encoding.buffer)
    }
}

impl SequenceWriter for BinaryListWriter_1_0<'_> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.end();
        Ok(())
    }
}

impl ContextWriter for BinarySExpWriter_1_0<'_> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a>
    where
        Self: 'a;
}

impl MakeValueWriter for BinarySExpWriter_1_0<'_> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        BinaryValueWriter_1_0::new(&mut *self.container_writer.encoding.buffer)
    }
}

impl SequenceWriter for BinarySExpWriter_1_0<'_> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.end();
        Ok(())
    }
}

pub struct BinarySExpWriter_1_0<'value> {
    container_writer: BinaryContainerWriter_1_0<'value>,
}

impl<'value> BinarySExpWriter_1_0<'value> {
    pub(crate) fn with_container_writer(
        container_writer: BinaryContainerWriter_1_0<'value>,
    ) -> Self {
        Self { container_writer }
    }

    pub(crate) fn new(buffer: &'value mut Vec<u8>) -> Self {
        let container_writer = BinaryContainerWriter_1_0::new(SEXP_TYPE_CODE, buffer);
        Self::with_container_writer(container_writer)
    }

    pub(crate) fn new_annotated(
        buffer: &'value mut Vec<u8>,
        annotations: &AnnotationsVec<'_>,
    ) -> IonResult<Self> {
        let container_writer =
            BinaryContainerWriter_1_0::new_annotated(SEXP_TYPE_CODE, buffer, annotations)?;
        Ok(Self::with_container_writer(container_writer))
    }
}

pub struct BinaryStructWriter_1_0<'value> {
    container_writer: BinaryContainerWriter_1_0<'value>,
}

impl<'value> BinaryStructWriter_1_0<'value> {
    pub(crate) fn with_container_writer(container: BinaryContainerWriter_1_0<'value>) -> Self {
        Self {
            container_writer: container,
        }
    }

    pub(crate) fn new(buffer: &'value mut Vec<u8>) -> Self {
        Self::with_container_writer(BinaryContainerWriter_1_0::new(STRUCT_TYPE_CODE, buffer))
    }

    pub(crate) fn new_annotated(
        buffer: &'value mut Vec<u8>,
        annotations: &AnnotationsVec<'_>,
    ) -> IonResult<Self> {
        let container_writer =
            BinaryContainerWriter_1_0::new_annotated(STRUCT_TYPE_CODE, buffer, annotations)?;
        Ok(Self::with_container_writer(container_writer))
    }
}

impl FieldEncoder for BinaryStructWriter_1_0<'_> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        // Write the field name
        let sid = match name.as_raw_symbol_ref() {
            RawSymbolRef::SymbolId(sid) => sid,
            other => {
                return cold_error!(
                    encoding_error,
                    "the v1.0 raw binary writer only supports symbol ID struct field names, received {other:?}"
                );
            }
        };
        VarUInt::write_u64(self.container_writer.encoding.buffer, sid as u64)?;
        Ok(())
    }
}

impl ContextWriter for BinaryStructWriter_1_0<'_> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a>
    where
        Self: 'a;
}

impl MakeValueWriter for BinaryStructWriter_1_0<'_> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        BinaryValueWriter_1_0::new(&mut *self.container_writer.encoding.buffer)
    }
}

impl StructWriter for BinaryStructWriter_1_0<'_> {
    fn close(self) -> IonResult<()> {
        self.container_writer.end();
        Ok(())
    }

    fn config(&self) -> ValueWriterConfig {
        v1_0::Binary::default_value_writer_config()
    }
}
