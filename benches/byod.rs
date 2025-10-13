//! Bring Your Own Data Benchmark
//!
//! This benchmark is disabled by default but can be run explicitly.
//!
//! The intention is to provide your own ion data to run benchmarks on, rather than running
//! benchmarks on hardcoded data.
//!
//! The current implementation works like this:
//!
//! - The benchmark looks for an environment variabled named "ION_BENCH", this variable should
//!   contain the path to the ion data that you wish to benchmark.
//! - The `full-read` benchmark is a benchmark that will measure reading all of the data in the
//!   original file as provided by the user.
//! - There are a number of benchmarks prefixed with `convert-`. These benchmarks will convert the
//!   original data into either a 1.0 or 1.1 stream with potentially other options. For instance,
//!   the `convert-prefixed-full-read` benchmark will convert the original data into a 1.1 stream
//!   using prefixed containers for all containers in the stream. One caveat to this however, is
//!   that the current conversion does not handle macro invocations, and instead evaluates the
//!   macros. This will lead to a converted data set that does not execute any macros, but rather
//!   inlines all of the values that the macros generated. The benchmark will need to be updated
//!   in order to facilitate a more accurate conversion.
//! - The write benchmarks, which are prefixed with `full-write` use the same converted data to
//!   test write performance. The same caveat exists with these, the converted data does not invoke
//!   macros, and will inline all of the data produced by the macros.
//!
//! An example use of this benchmark would look something like this:
//! ```bash
//! ION_BENCH=./benchmark_data/simple.10n cargo bench --features experimental --bench byod
//! ```
//!
use criterion::{criterion_group, criterion_main};

#[cfg(not(feature = "experimental"))]
mod benchmark {
    use criterion::Criterion;
    pub fn full_read(_c: &mut Criterion) {
        panic!("This benchmark requires the 'experimental' feature to work; try again with `--features experimental`");
    }
}

#[cfg(feature = "experimental")]
mod benchmark {
    use criterion::{BenchmarkId, Criterion};
    use ion_rs::{v1_1::BinaryWriter, Element, *};
    use std::{env, fs, hint::black_box};

    pub fn bench_byod_full(c: &mut Criterion) {
        let Some(file) = env::var("ION_BENCH").ok() else {
            eprintln!("Provide a data file by specifying its path using either the ION_BENCH_1_0, or ION_BENCH_1_1, envoronment variable");
            return;
        };

        let data = fs::read(&file).expect("unable to read data");

        let mut read_group = c.benchmark_group("read");
        read_group.measurement_time(std::time::Duration::from_secs(30));

        // Read the provided data as-is with an encoding-agnostic reader.
        read_group.bench_with_input(BenchmarkId::new("full-read", &file), &data, |b, data| {
            b.iter(|| {
                let reader = Reader::new(AnyEncoding, data).expect("Unable to create reader");
                full_read(reader);
            })
        });

        // Convert the provided data into an ion 1.0 stream, and then measure the performance of
        // reading the stream-equivalent data using a 1.0 reader.
        let one_oh_data = rewrite_as_1_0(&data);
        read_group.bench_with_input(
            BenchmarkId::new("convert-1.0-full-read", &file),
            &one_oh_data,
            |b, data| {
                // Benchmark Read of known 1.0 data.
                b.iter(|| {
                    let reader = Reader::new(AnyEncoding, data).expect("Unable to create reader");
                    full_read(reader);
                });
            },
        );
        drop(one_oh_data);

        // Convert the provided data into an ion 1.1 stream that uses delimited containers and then
        // measure the performance of reading the stream-equivalent data using a 1.1 reader.
        let delimited_data = rewrite_delimited_containers(&data);
        read_group.bench_with_input(
            BenchmarkId::new("convert-delimited-full-read", &file),
            &delimited_data,
            |b, data| {
                b.iter(|| {
                    let reader = Reader::new(AnyEncoding, data).expect("unable to create reader");
                    full_read(reader);
                });
            },
        );
        drop(delimited_data);

        // Convert the provided data into an ion 1.1 stream that uses prefixed containers and then
        // measure the performance of reading the stream-equivalent data using a 1.1 reader.
        let prefixed_data = rewrite_prefixed_containers(&data);
        read_group.bench_with_input(
            BenchmarkId::new("convert-prefixed-full-read", &file),
            &prefixed_data,
            |b, data| {
                b.iter(|| {
                    let reader = Reader::new(AnyEncoding, data).expect("unable to create reader");
                    full_read(reader);
                });
            },
        );
        drop(prefixed_data);

        // Convert the provided data into an ion 1.1 stream that uses inlined text symbols and then
        // measure the performance of reading the stream-equivalent data using a 1.1 reader.
        let inlined_data = rewrite_inline_symbols(&data);
        read_group.bench_with_input(
            BenchmarkId::new("convert-inlined-symbols-full-read", &file),
            &inlined_data,
            |b, data| {
                b.iter(|| {
                    let reader = Reader::new(AnyEncoding, data).expect("unable to create reader");
                    full_read(reader);
                });
            },
        );
        drop(inlined_data);

        // Convert the provided data into an ion 1.1 stream that uses symbol IDs and then measure
        // the performance of reading the stream-equivalent data using a 1.1 reader.
        let referenced_data = rewrite_referenced_symbols(&data);
        read_group.bench_with_input(
            BenchmarkId::new("convert-referenced-symbols-full-read", &file),
            &referenced_data,
            |b, data| {
                b.iter(|| {
                    let reader = Reader::new(AnyEncoding, data).expect("unable to create reader");
                    full_read(reader);
                });
            },
        );
        drop(referenced_data);

        read_group.finish();

        let mut write_group = c.benchmark_group("write");
        write_group.measurement_time(std::time::Duration::from_secs(30));

        // Read the original data using the Element API, and re-write it to an ion 1.1 stream using
        // a writer configured with default settings.
        write_group.bench_with_input(
            BenchmarkId::new("full-write-binary-1.1-default", &file),
            &data,
            |b, data| {
                let size = data.len();
                let elems = Element::read_all(data).expect("unable to read elements");
                b.iter(|| {
                    let buffer = Vec::<u8>::with_capacity(size);
                    let mut writer =
                        BinaryWriter::new(v1_1::Binary, buffer).expect("unable to create writer");
                    for elem in &elems {
                        writer.write(elem).expect("unable to write value");
                    }
                });
            },
        );

        // Read the original data using the Element API, and re-write it to an ion 1.1 stream using
        // a writer configured to use delimited containers.
        write_group.bench_with_input(
            BenchmarkId::new("full-write-binary-1.1-delimited", &file),
            &data,
            |b, data| {
                let size = data.len();
                let elems = Element::read_all(data).expect("unable to read elements");
                b.iter(|| {
                    let buffer = Vec::<u8>::with_capacity(size);
                    let mut writer =
                        BinaryWriter::new(v1_1::Binary, buffer).expect("unable to create writer");
                    for elem in &elems {
                        writer
                            .value_writer()
                            .with_container_encoding(ContainerEncoding::Delimited)
                            .write(elem)
                            .expect("unable to write value");
                    }
                });
            },
        );

        // Read the original data using the Element API, and re-write it to an ion 1.1 stream using
        // a writer configured to use inline symbols.
        write_group.bench_with_input(
            BenchmarkId::new("full-write-binary-1.1-inline-symbols", &file),
            &data,
            |b, data| {
                let size = data.len();
                let elems = Element::read_all(data).expect("unable to read elements");
                b.iter(|| {
                    let buffer = Vec::<u8>::with_capacity(size);
                    let mut writer =
                        BinaryWriter::new(v1_1::Binary, buffer).expect("unable to create writer");
                    for elem in &elems {
                        writer
                            .value_writer()
                            .with_symbol_value_encoding(SymbolValueEncoding::InlineText)
                            .write(elem)
                            .expect("unable to write value");
                    }
                });
            },
        );

        // Read the original data using the Element API, and re-write it to an ion 1.1 stream using
        // a writer configured to use inline symbols for annotations.
        write_group.bench_with_input(
            BenchmarkId::new("full-write-binary-1.1-inline-annotations", &file),
            &data,
            |b, data| {
                let size = data.len();
                let elems = Element::read_all(data).expect("unable to read elements");
                b.iter(|| {
                    let buffer = Vec::<u8>::with_capacity(size);
                    let mut writer =
                        Writer::new(v1_1::Binary, buffer).expect("unable to create writer");
                    for elem in &elems {
                        writer
                            .value_writer()
                            .with_annotations_encoding(AnnotationsEncoding::InlineText)
                            .write(elem)
                            .expect("unable to write value");
                    }
                });
            },
        );

        // Read the original data using the Element API, and re-write it to an ion 1.0 stream using
        // a writer configured with default settings.
        write_group.bench_with_input(
            BenchmarkId::new("full-write-binary-1.0", &file),
            &data,
            |b, data| {
                let size = data.len();
                let elems = Element::read_all(data).expect("unable to read elements");
                b.iter(|| {
                    let buffer = Vec::<u8>::with_capacity(size);
                    let mut writer =
                        Writer::new(v1_0::Binary, buffer).expect("unable to create writer");
                    for elem in &elems {
                        writer.write(elem).expect("unable to write value");
                    }
                    let _ = writer.close();
                });
            },
        );

        write_group.finish();
    }

    fn rewrite_prefixed_containers(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        let elems = Element::read_all(data).expect("Unable to read elements");
        let buffer = Vec::<u8>::with_capacity(size);
        let mut writer = Writer::new(v1_1::Binary, buffer).expect("unable to create writer");
        for elem in &elems {
            writer
                .value_writer()
                .with_container_encoding(ContainerEncoding::LengthPrefixed)
                .write(elem)
                .expect("unable to write value");
        }
        writer.close().expect("unable to close writer")
    }

    fn rewrite_delimited_containers(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        let elems = Element::read_all(data).expect("Unable to read elements");
        let buffer = Vec::<u8>::with_capacity(size);
        let mut writer = Writer::new(v1_1::Binary, buffer).expect("unable to create writer");
        for elem in &elems {
            writer
                .value_writer()
                .with_container_encoding(ContainerEncoding::Delimited)
                .write(elem)
                .expect("unable to write value");
        }
        writer.close().expect("unable to close writer")
    }

    fn rewrite_inline_symbols(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        let elems = Element::read_all(data).expect("Unable to read elements");
        let buffer = Vec::<u8>::with_capacity(size);
        let mut writer = Writer::new(v1_1::Binary, buffer).expect("unable to create writer");
        for elem in &elems {
            writer
                .value_writer()
                .with_annotations_encoding(AnnotationsEncoding::InlineText)
                .with_symbol_value_encoding(SymbolValueEncoding::InlineText)
                .with_field_name_encoding(FieldNameEncoding::InlineText)
                .write(elem)
                .expect("unable to write value");
        }
        writer.close().expect("unable to close writer")
    }

    fn rewrite_referenced_symbols(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        let elems = Element::read_all(data).expect("Unable to read elements");
        let buffer = Vec::<u8>::with_capacity(size);
        let mut writer = Writer::new(v1_1::Binary, buffer).expect("unable to create writer");
        for elem in &elems {
            writer
                .value_writer()
                .with_annotations_encoding(AnnotationsEncoding::SymbolIds)
                .with_symbol_value_encoding(SymbolValueEncoding::SymbolIds)
                .with_field_name_encoding(FieldNameEncoding::SymbolIds)
                .write(elem)
                .expect("unable to write value");
        }
        writer.close().expect("unable to close writer")
    }

    fn rewrite_inline_annotations(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        let elems = Element::read_all(data).expect("Unable to read elements");
        let buffer = Vec::<u8>::with_capacity(size);
        let mut writer = Writer::new(v1_1::Binary, buffer).expect("unable to create writer");
        for elem in &elems {
            writer
                .value_writer()
                .with_annotations_encoding(AnnotationsEncoding::InlineText)
                .write(elem)
                .expect("unable to write value");
        }
        writer.close().expect("unable to close writer")
    }

    fn rewrite_as_1_0(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        // Read initial data.
        let elems = Element::read_all(data).expect("unable to read elements");
        // Write data as 1.0
        let buffer = Vec::<u8>::with_capacity(size);
        elems
            .encode_to(buffer, v1_0::Binary)
            .expect("unable to re-encode elements")
    }

    fn rewrite_as_1_1(data: &Vec<u8>) -> Vec<u8> {
        let size = data.len();
        // Read initial data.
        let elems = Element::read_all(data).expect("unable to read elements");
        // Write data as 1.1
        let buffer = Vec::<u8>::with_capacity(size);
        elems
            .encode_to(buffer, v1_1::Binary)
            .expect("unable to re-encode elements")
    }

    #[inline]
    fn handle_lazy_value<D: Decoder>(value: LazyValue<'_, D>) {
        match black_box(value.read()).expect("unable to read value") {
            ValueRef::Null(_tpe) => (),
            ValueRef::Bool(_val) => (),
            ValueRef::Int(_val) => (),
            ValueRef::Float(_val) => (),
            ValueRef::Decimal(_val) => (),
            ValueRef::Timestamp(_val) => (),
            ValueRef::String(_val) => (),
            ValueRef::Symbol(_val) => (),
            ValueRef::Blob(_val) => (),
            ValueRef::Clob(_val) => (),
            ValueRef::SExp(sexp) => full_read_sexp(sexp),
            ValueRef::List(list) => full_read_list(list),
            ValueRef::Struct(strukt) => full_read_struct(strukt),
        }
    }

    fn full_read<D: Decoder, I: IonInput>(mut reader: Reader<D, I>) {
        loop {
            let Some(val) = reader.next().unwrap() else {
                break;
            };

            handle_lazy_value(val);
        }
    }

    fn full_read_struct<D: Decoder>(strukt: LazyStruct<'_, D>) {
        for field in &strukt {
            let field = field.expect("unable to read field");
            handle_lazy_value(field.value());
        }
    }

    fn full_read_sexp<D: Decoder>(sexp: LazySExp<'_, D>) {
        for value in &sexp {
            let value = value.expect("unable to read sexp value");
            handle_lazy_value(value);
        }
    }

    fn full_read_list<D: Decoder>(list: LazyList<'_, D>) {
        for value in &list {
            let value = value.expect("unable to read list item");
            handle_lazy_value(value);
        }
    }
}

criterion_group!(benches, benchmark::bench_byod_full);
criterion_main!(benches);
