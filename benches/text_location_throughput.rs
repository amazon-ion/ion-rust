//! Measures read throughput (bytes/second) for text Ion, exercising the source-location
//! row lookup in `SourceLocationState::calculate_location_for_span`.
//!
//! `Element::read_all` attaches a `SourceLocation` to every value it materializes, so each
//! value costs one offset-to-row resolution against a table of row start offsets.
//!
//! Data:
//! * `ints_5000_multiline` / `ints_5000_oneline` -- the same 5000 integers in the same number of
//!   bytes, differing only in row count (5000 vs 1). Isolates the row lookup from parsing. Both
//!   are generated in-process from one source, so the byte counts match structurally and these
//!   two cases always run.
//!
//! Criterion reports throughput in bytes/second because each case sets `Throughput::Bytes`,
//! which makes the differently-sized inputs directly comparable.

use criterion::{criterion_group, criterion_main};

mod benchmark {
    use criterion::{black_box, Criterion, Throughput};
    use ion_rs::Element;

    /// 5000 integers, joined by `separator`. With `"\n"` this is a 5000-row input; with `" "` it
    /// is a single row of the same integers, so the two differ only in row count.
    fn generated_ints(separator: &str) -> String {
        let mut data = (0..5000u64)
            .map(|i| (1_000_000_000 + i * 7919).to_string())
            .collect::<Vec<_>>()
            .join(separator);
        data.push('\n');
        data
    }

    pub fn criterion_benchmark(c: &mut Criterion) {
        // The generated cases are the controlled comparison, so they go first: they always run,
        // and they are the cheapest.
        let generated_cases = [
            ("ints_5000_multiline", generated_ints("\n")),
            ("ints_5000_oneline", generated_ints(" ")),
        ];

        let mut group = c.benchmark_group("text location throughput");
        for (id, data) in &generated_cases {
            bench_case(&mut group, id, data);
        }

        group.finish();
    }

    fn bench_case(
        group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
        id: &str,
        data: &str,
    ) {
        group.throughput(Throughput::Bytes(data.len() as u64));
        group.bench_function(id, |b| {
            b.iter(|| {
                let elements = Element::read_all(data).unwrap();
                black_box(elements);
            })
        });
    }
}

criterion_group!(benches, benchmark::criterion_benchmark);
criterion_main!(benches);
