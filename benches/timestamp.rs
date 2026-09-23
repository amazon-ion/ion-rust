use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::{v1_0, Element, IonData, IonResult, Timestamp};
use std::collections::hash_map::DefaultHasher;
use std::fmt::Write as FmtWrite;
use std::hash::{Hash, Hasher};

// Repeat for operations that are fast enough that they are running into the precision limit of
// the system clock (i.e. operations that take nanoseconds).
const ITERS: usize = 100;

fn build_timestamps() -> Vec<Timestamp> {
    vec![
        // Year only
        Timestamp::with_year(2024).build().unwrap(),
        // YMD
        Timestamp::with_ymd(2024, 8, 12).build().unwrap(),
        // Second precision with UTC offset
        Timestamp::with_ymd(2024, 8, 12)
            .with_hms(14, 30, 45)
            .with_offset(0)
            .build()
            .unwrap(),
        // With milliseconds and positive offset
        Timestamp::with_ymd(2024, 8, 12)
            .with_hms(14, 30, 45)
            .with_milliseconds(123)
            .with_offset(330)
            .build()
            .unwrap(),
        // With nanoseconds and negative offset
        Timestamp::with_ymd(2024, 8, 12)
            .with_hms(14, 30, 45)
            .with_nanoseconds(123_456_789)
            .with_offset(-480)
            .build()
            .unwrap(),
        // Unknown offset (second precision)
        Timestamp::with_ymd(2024, 8, 12)
            .with_hms(14, 30, 45)
            .build()
            .unwrap(),
    ]
}

fn criterion_benchmark(c: &mut Criterion) {
    let timestamps = build_timestamps();

    // --- Construction benchmarks ---
    let mut construct_group = c.benchmark_group("timestamp construct");

    construct_group.bench_function("year only", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(Timestamp::with_year(black_box(2024)).build().unwrap());
            }
        })
    });

    construct_group.bench_function("ymd", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(
                    Timestamp::with_ymd(black_box(2024), black_box(8), black_box(12))
                        .build()
                        .unwrap(),
                );
            }
        })
    });

    construct_group.bench_function("second precision UTC", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(
                    Timestamp::with_ymd(black_box(2024), black_box(8), black_box(12))
                        .with_hms(black_box(14), black_box(30), black_box(45))
                        .with_offset(black_box(0))
                        .build()
                        .unwrap(),
                );
            }
        })
    });

    construct_group.bench_function("milliseconds +offset", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(
                    Timestamp::with_ymd(black_box(2024), black_box(8), black_box(12))
                        .with_hms(black_box(14), black_box(30), black_box(45))
                        .with_milliseconds(black_box(123))
                        .with_offset(black_box(330))
                        .build()
                        .unwrap(),
                );
            }
        })
    });

    construct_group.bench_function("nanoseconds -offset", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(
                    Timestamp::with_ymd(black_box(2024), black_box(8), black_box(12))
                        .with_hms(black_box(14), black_box(30), black_box(45))
                        .with_nanoseconds(black_box(123_456_789))
                        .with_offset(black_box(-480))
                        .build()
                        .unwrap(),
                );
            }
        })
    });

    construct_group.finish();

    // --- Formatting benchmarks ---
    let mut format_group = c.benchmark_group("timestamp format");
    let mut buf = String::with_capacity(64);

    for ts in &timestamps {
        let label = format!("{}", ts);
        format_group.bench_function(&label, |b| {
            b.iter(|| {
                for _ in 0..ITERS {
                    buf.clear();
                    write!(buf, "{}", black_box(ts)).unwrap();
                    black_box(&buf);
                }
            })
        });
    }

    format_group.finish();

    // --- Equality, comparison, and hash benchmarks ---
    let ts_utc = Timestamp::with_ymd(2024, 8, 12)
        .with_hms(14, 30, 45)
        .with_nanoseconds(123_456_789)
        .with_offset(0)
        .build()
        .unwrap();
    let ts_utc_clone = ts_utc.clone();
    // Same instant, different offset (requires UTC normalization in Ord/PartialEq)
    let ts_positive_offset = Timestamp::with_ymd(2024, 8, 12)
        .with_hms(20, 0, 45)
        .with_nanoseconds(123_456_789)
        .with_offset(330)
        .build()
        .unwrap();
    // Different instant
    let ts_different = Timestamp::with_ymd(2024, 8, 13)
        .with_hms(14, 30, 45)
        .with_nanoseconds(123_456_789)
        .with_offset(0)
        .build()
        .unwrap();

    let mut cmp_group = c.benchmark_group("timestamp compare");

    cmp_group.bench_function("eq (identical)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ts_utc) == black_box(&ts_utc_clone));
            }
        })
    });

    cmp_group.bench_function("eq (same instant, different offset)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ts_utc) == black_box(&ts_positive_offset));
            }
        })
    });

    cmp_group.bench_function("eq (different instant)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ts_utc) == black_box(&ts_different));
            }
        })
    });

    cmp_group.bench_function("cmp (identical)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ts_utc).cmp(black_box(&ts_utc_clone)));
            }
        })
    });

    cmp_group.bench_function("cmp (same instant, different offset)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ts_utc).cmp(black_box(&ts_positive_offset)));
            }
        })
    });

    cmp_group.bench_function("cmp (different instant)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ts_utc).cmp(black_box(&ts_different)));
            }
        })
    });

    // IonData wrapper uses IonEq for equality and IonDataOrd for ordering
    let ion_data_utc = IonData::from(ts_utc.clone());
    let ion_data_utc_clone = IonData::from(ts_utc_clone.clone());
    let ion_data_positive_offset = IonData::from(ts_positive_offset.clone());
    let ion_data_different = IonData::from(ts_different.clone());

    cmp_group.bench_function("ion_eq (identical)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ion_data_utc) == black_box(&ion_data_utc_clone));
            }
        })
    });

    cmp_group.bench_function("ion_eq (same instant, different offset)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ion_data_utc) == black_box(&ion_data_positive_offset));
            }
        })
    });

    cmp_group.bench_function("ion_eq (different instant)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ion_data_utc) == black_box(&ion_data_different));
            }
        })
    });

    cmp_group.bench_function("ion_cmp (identical)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ion_data_utc).cmp(black_box(&ion_data_utc_clone)));
            }
        })
    });

    cmp_group.bench_function("ion_cmp (same instant, different offset)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ion_data_utc).cmp(black_box(&ion_data_positive_offset)));
            }
        })
    });

    cmp_group.bench_function("ion_cmp (different instant)", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(&ion_data_utc).cmp(black_box(&ion_data_different)));
            }
        })
    });

    cmp_group.bench_function("ion_data_hash", |b| {
        b.iter(|| {
            for _ in 0..ITERS {
                let mut hasher = DefaultHasher::new();
                black_box(&ion_data_utc).hash(&mut hasher);
                black_box(hasher.finish());
            }
        })
    });

    cmp_group.finish();

    // --- Clone benchmarks ---
    let mut clone_group = c.benchmark_group("timestamp clone");

    clone_group.bench_function("year only", |b| {
        let ts = &timestamps[0];
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(ts).clone());
            }
        })
    });

    clone_group.bench_function("nanoseconds with offset", |b| {
        let ts = &timestamps[4];
        b.iter(|| {
            for _ in 0..ITERS {
                black_box(black_box(ts).clone());
            }
        })
    });

    clone_group.finish();

    // --- Read/Write via Element (text Ion) ---
    let text_data = encode_timestamps_text(&timestamps).unwrap();
    let binary_data = encode_timestamps_binary(&timestamps).unwrap();

    println!("Timestamp text data: {} bytes", text_data.len());
    println!("Timestamp binary data: {} bytes", binary_data.len());

    let mut rw_group = c.benchmark_group("timestamp read/write element");

    rw_group.bench_function("write text", |b| {
        b.iter(|| {
            let mut out = Vec::with_capacity(text_data.len());
            for ts in &timestamps {
                let elem: Element = ts.clone().into();
                elem.encode_to(&mut out, v1_0::Text).unwrap();
            }
            black_box(out);
        })
    });

    rw_group.bench_function("write binary", |b| {
        b.iter(|| {
            let mut out = Vec::with_capacity(binary_data.len());
            for ts in &timestamps {
                let elem: Element = ts.clone().into();
                elem.encode_to(&mut out, v1_0::Binary).unwrap();
            }
            black_box(out);
        })
    });

    rw_group.bench_function("read text", |b| {
        b.iter(|| {
            let seq = Element::read_all(black_box(text_data.as_slice())).unwrap();
            black_box(seq);
        })
    });

    rw_group.bench_function("read binary", |b| {
        b.iter(|| {
            let seq = Element::read_all(black_box(binary_data.as_slice())).unwrap();
            black_box(seq);
        })
    });

    rw_group.finish();

    // --- Bulk read/write (many timestamps) for throughput signal ---
    let many_timestamps: Vec<Timestamp> = (0..1000)
        .map(|i| {
            Timestamp::with_ymd(2020 + (i % 10), 1 + (i % 12), 1 + (i % 28))
                .with_hms(i % 24, i % 60, i % 60)
                .with_nanoseconds(i * 1_000_000)
                .with_offset(((i as i32) % 25) * 60 - 720)
                .build()
                .unwrap()
        })
        .collect();

    let bulk_text = encode_timestamps_text(&many_timestamps).unwrap();
    let bulk_binary = encode_timestamps_binary(&many_timestamps).unwrap();

    println!(
        "Bulk timestamp text data: {} bytes ({} timestamps)",
        bulk_text.len(),
        many_timestamps.len()
    );
    println!(
        "Bulk timestamp binary data: {} bytes ({} timestamps)",
        bulk_binary.len(),
        many_timestamps.len()
    );

    let mut bulk_group = c.benchmark_group("timestamp bulk (1000)");

    bulk_group.bench_function("write text", |b| {
        b.iter(|| {
            let mut out = Vec::with_capacity(bulk_text.len());
            for ts in &many_timestamps {
                let elem: Element = ts.clone().into();
                elem.encode_to(&mut out, v1_0::Text).unwrap();
            }
            black_box(out);
        })
    });

    bulk_group.bench_function("write binary", |b| {
        b.iter(|| {
            let mut out = Vec::with_capacity(bulk_binary.len());
            for ts in &many_timestamps {
                let elem: Element = ts.clone().into();
                elem.encode_to(&mut out, v1_0::Binary).unwrap();
            }
            black_box(out);
        })
    });

    bulk_group.bench_function("read text", |b| {
        b.iter(|| {
            let seq = Element::read_all(black_box(bulk_text.as_slice())).unwrap();
            black_box(seq);
        })
    });

    bulk_group.bench_function("read binary", |b| {
        b.iter(|| {
            let seq = Element::read_all(black_box(bulk_binary.as_slice())).unwrap();
            black_box(seq);
        })
    });

    bulk_group.finish();
}

fn encode_timestamps_text(timestamps: &[Timestamp]) -> IonResult<Vec<u8>> {
    let mut out = Vec::new();
    for ts in timestamps {
        let elem: Element = ts.clone().into();
        elem.encode_to(&mut out, v1_0::Text)?;
    }
    Ok(out)
}

fn encode_timestamps_binary(timestamps: &[Timestamp]) -> IonResult<Vec<u8>> {
    let mut out = Vec::new();
    for ts in timestamps {
        let elem: Element = ts.clone().into();
        elem.encode_to(&mut out, v1_0::Binary)?;
    }
    Ok(out)
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
