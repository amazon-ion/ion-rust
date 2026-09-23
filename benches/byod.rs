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
//! - The `convert-1.0-full-read` benchmark converts the original data into a binary Ion 1.0
//!   stream and then measures reading the stream-equivalent data.
//! - The write benchmark, `full-write-binary-1.0`, reads the original data using the `Element` API
//!   and measures re-writing it as binary Ion 1.0.
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
    use ion_rs::{Element, *};
    use std::{env, fs, hint::black_box};

    pub fn bench_byod_full(c: &mut Criterion) {
        let Some(file) = env::var("ION_BENCH").ok() else {
            eprintln!(
                "Provide a data file by specifying its path using the ION_BENCH environment variable"
            );
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

        read_group.finish();

        let mut write_group = c.benchmark_group("write");
        write_group.measurement_time(std::time::Duration::from_secs(30));

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
