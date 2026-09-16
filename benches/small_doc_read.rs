//! Benchmarks the cost of reading *small* binary Ion 1.0 documents, constructing a fresh
//! reader for each document.
//!
//! The other benchmarks in this suite amortize per-document fixed costs (reader construction,
//! IVM handling, and local symbol table processing) by streaming many values through a single
//! reader. Workloads that read one document per record, message, or database item pay those
//! fixed costs on every read. This benchmark measures them directly:
//!
//! * `element_read_one`: `Element::read_one` on a single document (stable API, no experimental
//!   features required).
//! * `lazy_reader_any` / `lazy_reader_binary`: the lazy `Reader` with `AnyEncoding` and
//!   `v1_0::Binary` respectively, reading all values in a single document (requires the
//!   `experimental-reader-writer` feature, like the other benchmarks in this suite).
//! * `multi_ivm`: many small documents concatenated into one stream (each preceded by an IVM),
//!   read through a *single* reader. This exercises the encoding-context reset and local symbol
//!   table processing that run at every IVM boundary, with reader construction amortized across
//!   the documents in the stream.
//!
//! Documents are structs with a mixed scalar field profile (strings, ints, bools, a timestamp)
//! whose field names require a local symbol table. Three sizes (~200 B, ~2 KB, ~20 KB) show how
//! the fixed costs amortize as documents grow.

use criterion::{criterion_group, criterion_main, Criterion};

mod data {
    use ion_rs::v1_0::Binary;
    use ion_rs::Element;
    use std::fmt::Write;

    /// Returns the text of a struct document containing `num_groups` repetitions of a ten-field
    /// group of mixed scalars. Field names are suffixed with the group index to produce
    /// progressively larger local symbol tables.
    fn small_doc_text(num_groups: usize) -> String {
        let mut text = String::new();
        text.push('{');
        for group in 0..num_groups {
            write!(
                &mut text,
                r#"
                recordId_{group}: "R{group:04}AB{group:04}CD",
                displayName_{group}: "widget display name {group}",
                region_{group}: "north-region-{group}",
                category_{group}: "general-category-{group}",
                count_{group}: {},
                sizeBytes_{group}: {},
                active_{group}: true,
                archived_{group}: false,
                created_{group}: 2024-11-05T12:34:56.789Z,
                score_{group}: {},
                "#,
                42 + group,
                1_048_576 + group,
                98_765 + group,
            )
            .unwrap();
        }
        text.push('}');
        text
    }

    /// Encodes a document with `num_groups` field groups as binary Ion 1.0
    /// (IVM + local symbol table + struct).
    pub fn small_doc_binary(num_groups: usize) -> Vec<u8> {
        Element::read_one(small_doc_text(num_groups))
            .expect("failed to parse benchmark document text")
            .encode_as(Binary)
            .expect("failed to encode benchmark document")
    }

    /// The `num_groups` values that produce documents of roughly 200 B, 2 KB, and 20 KB.
    pub const GROUP_COUNTS: &[usize] = &[1, 12, 120];
}

/// Benchmarks `Element::read_one` — the stable, default-feature entry point.
fn element_benchmark(c: &mut Criterion) {
    use criterion::{black_box, BenchmarkId, Throughput};

    let mut group = c.benchmark_group("small_doc_read/element_read_one");
    for &num_groups in data::GROUP_COUNTS {
        let binary = data::small_doc_binary(num_groups);
        group.throughput(Throughput::Bytes(binary.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{}B", binary.len())),
            &binary,
            |b, binary| {
                b.iter(|| {
                    let element = ion_rs::Element::read_one(black_box(binary.as_slice())).unwrap();
                    black_box(element);
                });
            },
        );
    }
    group.finish();
}

#[cfg(feature = "experimental-reader-writer")]
mod lazy_benchmark {
    use super::data;
    use criterion::{black_box, BenchmarkId, Criterion, Throughput};
    use ion_rs::{
        AnyEncoding, Decoder, IonInput, IonResult, LazyStruct, LazyValue, Reader, ValueRef,
    };

    /// Reads this value and, if it's a container, any nested values. Returns the number of
    /// values read.
    fn count_value_and_children<D: Decoder>(lazy_value: &LazyValue<'_, D>) -> IonResult<usize> {
        use ValueRef::*;
        let child_count = match lazy_value.read()? {
            List(s) => count_sequence_children(s.iter())?,
            SExp(s) => count_sequence_children(s.iter())?,
            Struct(s) => count_struct_children(&s)?,
            scalar => {
                let _ = black_box(scalar);
                0
            }
        };
        Ok(1 + child_count)
    }

    /// Reads the child values of a list or s-expression. Returns the number of values read.
    fn count_sequence_children<'a, D: Decoder>(
        lazy_sequence: impl Iterator<Item = IonResult<LazyValue<'a, D>>>,
    ) -> IonResult<usize> {
        let mut count = 0;
        for value in lazy_sequence {
            count += count_value_and_children(&value?)?;
        }
        Ok(count)
    }

    /// Reads the field values of a struct. Returns the number of values read.
    fn count_struct_children<D: Decoder>(lazy_struct: &LazyStruct<'_, D>) -> IonResult<usize> {
        let mut count = 0;
        for field in lazy_struct {
            count += count_value_and_children(&field?.value())?;
        }
        Ok(count)
    }

    /// Reads every value in the stream, leaving the reader exhausted.
    fn read_all_values<D: Decoder, I: IonInput>(reader: &mut Reader<D, I>) -> IonResult<usize> {
        let mut count = 0;
        while let Some(value) = reader.next()? {
            count += count_value_and_children(&value)?;
        }
        Ok(count)
    }

    /// Benchmarks reading a single small document through a freshly constructed lazy `Reader`,
    /// once with `AnyEncoding` and once with `v1_0::Binary`.
    fn single_document(c: &mut Criterion) {
        for &num_groups in data::GROUP_COUNTS {
            let binary = data::small_doc_binary(num_groups);
            let label = format!("{}B", binary.len());

            let mut group = c.benchmark_group("small_doc_read/lazy_reader_any");
            group.throughput(Throughput::Bytes(binary.len() as u64));
            group.bench_with_input(BenchmarkId::from_parameter(&label), &binary, |b, binary| {
                b.iter(|| {
                    let mut reader =
                        Reader::new(AnyEncoding, black_box(binary.as_slice())).unwrap();
                    black_box(read_all_values(&mut reader).unwrap());
                });
            });
            group.finish();

            let mut group = c.benchmark_group("small_doc_read/lazy_reader_binary");
            group.throughput(Throughput::Bytes(binary.len() as u64));
            group.bench_with_input(BenchmarkId::from_parameter(&label), &binary, |b, binary| {
                b.iter(|| {
                    let mut reader =
                        Reader::new(ion_rs::v1_0::Binary, black_box(binary.as_slice())).unwrap();
                    black_box(read_all_values(&mut reader).unwrap());
                });
            });
            group.finish();
        }
    }

    /// Benchmarks reading many small documents concatenated into a single stream — each document
    /// preceded by its own IVM — through a single reader. The encoding context (symbol table and
    /// macro table) is reset at every IVM boundary. Reader construction happens once per
    /// iteration (amortized across `NUM_DOCS` documents), so the measurement is dominated by the
    /// per-document reset and local symbol table processing.
    fn multi_ivm(c: &mut Criterion) {
        const NUM_DOCS: usize = 100;
        let mut group = c.benchmark_group("small_doc_read/multi_ivm");
        for &num_groups in data::GROUP_COUNTS {
            let one_doc = data::small_doc_binary(num_groups);
            let stream: Vec<u8> = one_doc.repeat(NUM_DOCS);
            group.throughput(Throughput::Bytes(stream.len() as u64));
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{NUM_DOCS}x{}B", one_doc.len())),
                &stream,
                |b, stream| {
                    b.iter(|| {
                        let mut reader =
                            Reader::new(AnyEncoding, black_box(stream.as_slice())).unwrap();
                        black_box(read_all_values(&mut reader).unwrap());
                    });
                },
            );
        }
        group.finish();
    }

    pub fn criterion_benchmark(c: &mut Criterion) {
        single_document(c);
        multi_ivm(c);
    }
}

#[cfg(not(feature = "experimental-reader-writer"))]
mod lazy_benchmark {
    use criterion::Criterion;

    /// The lazy `Reader` cases require the `experimental-reader-writer` feature; without it,
    /// only the `Element::read_one` cases run.
    pub fn criterion_benchmark(_c: &mut Criterion) {
        eprintln!(
            "note: skipping lazy Reader benchmark cases; \
             enable the 'experimental-reader-writer' feature to include them"
        );
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    element_benchmark(c);
    lazy_benchmark::criterion_benchmark(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
