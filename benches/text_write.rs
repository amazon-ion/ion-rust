//! Text encoding throughput for `Element`s: `Display` and the text writer in each format.
//!
//! The corpus is a file of Ion data named by the `ION_BENCH` environment variable. Each benchmark
//! reads it with the `Element` API once, then measures re-encoding every top-level value as text.
//! A benchmark run is only comparable to another that ran in its own process, so select one
//! benchmark per invocation with a filter:
//!
//! ```bash
//! ION_BENCH=path/to/data.10n cargo bench --features experimental --bench text_write -- 'writer/compact$'
//! ```
//!
//! Every benchmark reports its throughput as the size of the corpus's Compact text, whatever the
//! format it writes, so that their throughputs are comparable.
use criterion::{criterion_group, criterion_main};

#[cfg(not(feature = "experimental"))]
mod benchmark {
    use criterion::Criterion;
    pub fn criterion_benchmark(_c: &mut Criterion) {
        panic!("This benchmark requires the 'experimental' feature to work; try again with `--features experimental`");
    }
}

#[cfg(feature = "experimental")]
mod benchmark {
    use criterion::{Criterion, Throughput};
    use ion_rs::{v1_0, Element, Sequence, TextFormat, Writer};
    use std::fmt::Write as _;
    use std::hint::black_box;
    use std::{env, fs};

    const FORMATS: [(&str, TextFormat); 3] = [
        ("compact", TextFormat::Compact),
        ("lines", TextFormat::Lines),
        ("pretty", TextFormat::Pretty),
    ];

    fn encode_stream(elements: &Sequence, format: TextFormat, buffer: Vec<u8>) -> Vec<u8> {
        let mut writer =
            Writer::new(v1_0::Text.with_format(format), buffer).expect("unable to create writer");
        for element in elements {
            writer.write(element).expect("unable to write value");
        }
        writer.close().expect("unable to close writer")
    }

    pub fn criterion_benchmark(c: &mut Criterion) {
        let Ok(file) = env::var("ION_BENCH") else {
            eprintln!("Provide a data file by specifying its path using the ION_BENCH environment variable");
            return;
        };
        let data = fs::read(&file).expect("unable to read data");
        let elements = Element::read_all(&data).expect("unable to read elements");
        let compact_len = encode_stream(&elements, TextFormat::Compact, Vec::new()).len();

        let mut group = c.benchmark_group("text_write");
        group.throughput(Throughput::Bytes(compact_len as u64));
        if compact_len > 16 * 1024 * 1024 {
            group.sample_size(10);
        }

        // `to_string` on each top-level value, as a caller formatting values one at a time would.
        group.bench_function("display/to_string", |b| {
            b.iter(|| {
                for element in &elements {
                    black_box(black_box(element).to_string());
                }
            })
        });

        // `Display` into a reused, already-grown `String`.
        group.bench_function("display/reused_string", |b| {
            let mut buffer = String::with_capacity(compact_len * 2);
            b.iter(|| {
                buffer.clear();
                for element in &elements {
                    write!(buffer, "{}", black_box(element)).expect("writing to a String");
                }
                black_box(buffer.len());
            })
        });

        // One writer for the whole stream, with the layout fixed at compile time by a style marker.
        macro_rules! bench_styled_writer {
            ($label:literal, $style:expr) => {
                group.bench_function(concat!("writer_styled/", $label), |b| {
                    let mut buffer = Vec::with_capacity(compact_len * 4);
                    b.iter(|| {
                        buffer.clear();
                        let mut writer = Writer::new($style, std::mem::take(&mut buffer))
                            .expect("unable to create writer");
                        for element in black_box(&elements) {
                            writer.write(element).expect("unable to write value");
                        }
                        buffer = writer.close().expect("unable to close writer");
                        black_box(buffer.len());
                    })
                });
            };
        }
        bench_styled_writer!("compact", v1_0::CompactText);
        bench_styled_writer!("lines", v1_0::LinesText);
        bench_styled_writer!("pretty", v1_0::PrettyText);

        // A fresh writer per top-level value, each producing its own `Vec`, as `encode_as/compact`
        // does but with the layout fixed at compile time by a style marker.
        group.bench_function("writer_per_value/compact", |b| {
            b.iter(|| {
                for element in &elements {
                    let mut writer = Writer::new(v1_0::CompactText, Vec::new())
                        .expect("unable to create writer");
                    writer
                        .write(black_box(element))
                        .expect("unable to write value");
                    black_box(writer.close().expect("unable to close writer"));
                }
            })
        });

        // One reused writer, attached to a new `Vec` for each top-level value.
        group.bench_function("writer_reused/compact", |b| {
            let mut idle = Some(Writer::idle(v1_0::CompactText).expect("unable to create writer"));
            b.iter(|| {
                for element in &elements {
                    let parked = idle
                        .take()
                        .expect("the idle writer is put back after each value");
                    let mut writer = parked.attach(Vec::new());
                    writer
                        .write(black_box(element))
                        .expect("unable to write value");
                    writer.flush().expect("unable to flush writer");
                    let (parked, output) = writer.detach();
                    black_box(output);
                    idle = Some(parked);
                }
            })
        });

        for (label, format) in FORMATS {
            // One writer for the whole stream, with the layout chosen at run time.
            group.bench_function(format!("writer/{label}"), |b| {
                let mut buffer = Vec::with_capacity(compact_len * 4);
                b.iter(|| {
                    buffer.clear();
                    buffer =
                        encode_stream(black_box(&elements), format, std::mem::take(&mut buffer));
                    black_box(buffer.len());
                })
            });

            // A fresh writer per top-level value, as `encode_as` does.
            group.bench_function(format!("encode_as/{label}"), |b| {
                let config = v1_0::Text.with_format(format);
                b.iter(|| {
                    for element in &elements {
                        black_box(
                            black_box(element)
                                .encode_as(config.clone())
                                .expect("unable to encode value"),
                        );
                    }
                })
            });
        }
        group.finish();
    }
}

criterion_group!(benches, benchmark::criterion_benchmark);
criterion_main!(benches);
