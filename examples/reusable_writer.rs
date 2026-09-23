//! Pattern: a *generic* thread-local reusable writer, built on the shipped `idle`/`attach`/`detach`
//! primitives. This is the kind of opinionated convenience that belongs OUTSIDE the core format
//! library — in an application module or a companion crate.
//!
//! Creating a writer per document allocates a fresh scratch arena (and, for the managed writer, a
//! symbol table and two sub-writers) every time. A service encoding many small documents (one per
//! request/message, often one thread per core) pays that setup on every value. Caching one idle
//! writer per thread and reusing it amortizes the setup.
//!
//! It is generic over the encoding `E`, but only encodings whose raw writer implements `Reusable`
//! can be reused — today that is Ion 1.0, both binary and text. That restriction is a `where` bound
//! on the `impl` block rather than a runtime check, so `ThreadLocalWriter<E>` for a non-reusable `E`
//! (Ion 1.1) simply has no `acquire` method: the mistake is a compile error, not a fallback path.
//!
//! At most ONE idle writer is cached per encoding per thread — this is a reuse cache, not a pool: a
//! second concurrent `acquire` for the same encoding just builds another writer, and whichever
//! guard finishes last leaves its writer in the slot. (It is possible to extend this example to
//! support a pool of multiple writers, if an application's workload regularly demands multiple open
//! writers within a single thread.)
//!
//! [`ThreadLocalWriter::acquire`] hands out a [`WriterGuard`] RAII guard that derefs to the
//! underlying [`Writer`], so callers encode with the writer's normal API. `finish` flushes the
//! document, returns the writer to this thread's slot, and hands back the sink. If the guard is
//! dropped without `finish` (early return, `?`, panic-unwind), the writer is still returned and
//! nothing further is written: `Drop` calls `detach`, which discards — does not flush — whatever has
//! been encoded since the last flush.
//!
//! What that does and does not guarantee: `flush` is a top-level-only operation (the borrow checker
//! withholds it while a container writer is open), so the sink only ever receives COMPLETE top-level
//! values, never a partially encoded one. It does NOT undo earlier flushes — values the caller
//! already flushed stay committed to the sink, as with any streaming writer. Dropping the guard
//! abandons the unflushed remainder; it does not roll the document back.

#[cfg(not(feature = "experimental-reader-writer"))]
fn main() {
    eprintln!("This example requires the 'experimental' feature. Rebuild it with the flag `--features experimental`.");
}

#[cfg(feature = "experimental-reader-writer")]
fn main() -> ion_rs::IonResult<()> {
    imp::run()
}

#[cfg(feature = "experimental-reader-writer")]
mod imp {
    use ion_rs::{
        v1_0, Element, Encoder, Encoding, IonResult, Reusable, TextFormat, WriteConfig, Writer,
    };
    use std::any::{Any, TypeId};
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::io::Write;
    use std::marker::PhantomData;
    use std::ops::{Deref, DerefMut};

    /// This thread's cached idle writer for each encoding — at most one `Writer<E, ()>` per `E`.
    ///
    /// A `thread_local!` holds a single concrete type, but `Writer<E, ()>` is a *different* type for
    /// every `E`. Rather than declare one `thread_local!` per encoding (which would defeat being
    /// generic over `E`), the per-encoding slots are type-erased behind `Box<dyn Any>` and keyed by
    /// `TypeId::of::<E>()`. One thread-local therefore serves every encoding, and `downcast_mut`
    /// recovers the concrete slot. The `TypeId` key makes the downcast infallible.
    type ReusableWriters = HashMap<TypeId, Box<dyn Any>>;

    thread_local! {
        static WRITERS: RefCell<ReusableWriters> = RefCell::new(HashMap::new());
    }

    /// Zero-sized handle to this thread's reusable `E` writer.
    pub struct ThreadLocalWriter<E>(PhantomData<E>);

    impl<E: Encoding> ThreadLocalWriter<E>
    where
        // Only encodings with a reusable raw writer have `idle`/`attach`/`detach` at all.
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        /// Reuses this thread's cached `E` writer (building one when the slot is empty), binds `sink`
        /// to it, and returns a guard that returns the writer to the slot when it is done.
        pub fn acquire<W: Write>(
            config: impl Into<WriteConfig<E>>,
            sink: W,
        ) -> IonResult<WriterGuard<E, W>> {
            let cached = WRITERS.with(|writers| {
                writers
                    .borrow_mut()
                    .get_mut(&TypeId::of::<E>())
                    .and_then(|erased| erased.downcast_mut::<Option<Writer<E, ()>>>())
                    .and_then(Option::take)
            });
            let idle = match cached {
                Some(mut idle) => {
                    // The cached writer was built for whatever config the PREVIOUS caller passed;
                    // `set_config` makes it adopt this one in place, without discarding the warm
                    // state that makes reuse worthwhile. Skipping this would silently hand out a
                    // writer that encodes in the wrong format (e.g. compact instead of pretty text).
                    idle.set_config(config);
                    idle
                }
                None => Writer::<E, ()>::idle(config)?,
            };
            Ok(WriterGuard {
                writer: Some(idle.attach(sink)),
            })
        }
    }

    /// Returns `idle` to this thread's slot for `E`, replacing whatever was cached there.
    fn cache<E: Encoding>(writers: &RefCell<ReusableWriters>, idle: Writer<E, ()>)
    where
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        let mut writers = writers.borrow_mut();
        let erased = writers
            .entry(TypeId::of::<E>())
            .or_insert_with(|| Box::new(Option::<Writer<E, ()>>::None));
        // Infallible: the entry under `TypeId::of::<E>()` is only ever an `Option<Writer<E, ()>>`.
        // At most one writer is kept per encoding; any previously cached one is dropped here.
        if let Some(slot) = erased.downcast_mut::<Option<Writer<E, ()>>>() {
            *slot = Some(idle);
        }
    }

    /// RAII guard over the reused writer. Deref to the writer to encode, then call [`Self::finish`]
    /// to flush and reclaim the sink. Dropping the guard without `finish` still returns the writer to
    /// its slot, but discards whatever has not been flushed.
    // `#[must_use]` catches `let _ = ThreadLocalWriter::acquire(config, sink);` -- a guard whose
    // result is IGNORED, which returns the writer immediately and emits nothing. It does NOT catch a
    // guard that is bound to a variable and then dropped without `finish`; no attribute can require
    // that call, which is why the discard-on-drop behavior is documented instead.
    #[must_use = "a WriterGuard emits nothing on its own: encode through it, then call finish() to flush the document and reclaim the sink"]
    pub struct WriterGuard<E: Encoding, W: Write>
    where
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        // `Some` while active; taken by `finish`/`drop` so the writer is returned exactly once.
        writer: Option<Writer<E, W>>,
    }

    impl<E: Encoding, W: Write> WriterGuard<E, W>
    where
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        /// Flushes the document, returns the writer to this thread's slot, and hands back the sink.
        /// If the flush fails, the writer is returned anyway and the error is propagated (the sink is
        /// not handed back).
        pub fn finish(mut self) -> IonResult<W> {
            // `take` so the `Drop` impl below does nothing: the writer is already accounted for.
            let mut writer = self.take_writer();
            // `detach` writes nothing, so the document has to be flushed here -- and this is the only
            // step that can fail, which is why `finish` and not `Drop` is the way to emit a document.
            // Hold the error rather than returning it: `detach` and caching are infallible, and a
            // guard that dropped the writer on an I/O error would throw away a warm writer per failure.
            let flush_result = writer.flush();
            let (idle, sink) = writer.detach();
            WRITERS.with(|writers| cache(writers, idle));
            flush_result?;
            Ok(sink)
        }

        /// Removes the active writer from the guard.
        ///
        /// The `Option` exists only so `finish` and `Drop` can each move the writer out; it is
        /// `Some` for the guard's entire observable lifetime.
        fn take_writer(&mut self) -> Writer<E, W> {
            match self.writer.take() {
                Some(writer) => writer,
                None => unreachable!("a WriterGuard always holds a writer until finish/drop"),
            }
        }
    }

    impl<E: Encoding, W: Write> Deref for WriterGuard<E, W>
    where
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        type Target = Writer<E, W>;

        fn deref(&self) -> &Self::Target {
            match self.writer.as_ref() {
                Some(writer) => writer,
                None => unreachable!("a WriterGuard always holds a writer until finish/drop"),
            }
        }
    }

    impl<E: Encoding, W: Write> DerefMut for WriterGuard<E, W>
    where
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        fn deref_mut(&mut self) -> &mut Self::Target {
            match self.writer.as_mut() {
                Some(writer) => writer,
                None => unreachable!("a WriterGuard always holds a writer until finish/drop"),
            }
        }
    }

    impl<E: Encoding, W: Write> Drop for WriterGuard<E, W>
    where
        <E as Encoder>::Writer<Vec<u8>>: Reusable,
    {
        fn drop(&mut self) {
            // `finish` was NOT called (early return / `?` / panic). Return the writer and DISCARD
            // everything encoded since the last flush: `detach` writes nothing, so there is no I/O
            // error to swallow here in `Drop`. Values the caller already flushed remain in the sink;
            // only complete top-level values can have been flushed, so what is there is always
            // well-formed Ion.
            if let Some(writer) = self.writer.take() {
                let (idle, _sink) = writer.detach();
                // `try_with`, not `with`: a guard dropped during thread teardown (after the
                // thread-local has been destroyed) would make `with` panic, and panicking in
                // `Drop` while unwinding aborts the process. Losing the cached writer is fine.
                let _ = WRITERS.try_with(|writers| cache(writers, idle));
            }
        }
    }

    pub fn run() -> IonResult<()> {
        let documents = [
            r#"{ status: "ok", items: [1, 2, 3] }"#,
            r#"{ status: "error", message: "not found" }"#,
            r#"[a, b, c]"#,
        ]
        .into_iter()
        .map(Element::read_one)
        .collect::<IonResult<Vec<_>>>()?;

        for (i, element) in documents.iter().enumerate() {
            // The first iteration builds a writer; later ones reuse the writer (and its warm scratch
            // arena) that the previous `finish` returned to the slot.
            let mut writer = ThreadLocalWriter::acquire(v1_0::Binary, Vec::new())?;
            writer.write(element)?; // via `DerefMut` to the underlying `Writer`
            writer.write(element)?; // two top-level values, to show the guard is not one-shot
            let bytes = writer.finish()?;
            println!("binary doc {i}: encoded {} bytes", bytes.len());
        }

        for (i, element) in documents.iter().enumerate() {
            let mut writer =
                ThreadLocalWriter::acquire(v1_0::Text.with_format(TextFormat::Pretty), Vec::new())?;
            writer.write(element)?;
            writer.write(element)?;
            let bytes = writer.finish()?;
            println!("text doc {i}: encoded {} bytes", bytes.len());
        }
        Ok(())
    }
}
