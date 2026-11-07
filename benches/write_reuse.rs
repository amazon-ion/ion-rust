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
    use ion_rs::{v1_0, Element, Encoding, Reusable, WriteConfig, Writer};
    use std::hint::black_box;

    // One log record (~97 bytes encoded). Documents are lists of N of these, sized to hit the
    // target encoded sizes below.
    const RECORD: &str = r#"{ threadId: 418, threadName: "scheduler-thread-6",
        loggerName: "com.example.organization.product.component.ClassName",
        logLevel: "INFO", timestamp: 1670446800245 }"#;

    // A document = a list of `n` records. Larger `n` amortizes per-writer setup within one
    // document, so the reuse win shrinks with size.
    fn make_doc(n: usize) -> String {
        let mut s = String::from("[");
        for _ in 0..n {
            s.push_str(RECORD);
            s.push(',');
        }
        s.push(']');
        s
    }

    // An aggregate document: a top-level struct with nested sub-structs and an `items` list of `n`
    // structs. Each item has a `parts` list of two part sub-trees that alternate structs and lists
    // and vary in depth by item; the deepest container (an empty `children` list) is at depth 16.
    fn make_nested_doc(n: usize) -> String {
        let mut s = String::from(
            r#"{ order_id: 902211, created: 2022-12-07T20:59:59.744Z, status: shipped,
                customer: { id: 4182, name: "Example Customer", tier: gold,
                    address: { street: "123 Example Ave", city: "Seattle", postal_code: "98101",
                        geo: { lat: 47.6062e0, lon: -122.3321e0 } } },
                items: ["#,
        );
        for i in 0..n {
            s.push_str(&format!(
                r#"{{ sku: "SKU-{i:06}", quantity: {q}, unit_price: {p}.99, taxable: {t},
                    tags: [promo, seasonal], parts: [{a}, {b}] }},"#,
                q = 1 + i % 5,
                p = 10 + i % 90,
                t = i % 2 == 0,
                a = make_part(i, 5, 5 + 2 * (i % 6)),
                b = make_part(i + 1, 5, 5 + 2 * ((i + 3) % 6)),
            ));
        }
        s.push_str("] }");
        s
    }

    // A part struct at container depth `depth` whose `children` list holds one nested part, until
    // the part at `max_depth` (at most 15), whose `children` list is empty.
    fn make_part(id: usize, depth: usize, max_depth: usize) -> String {
        let children = if depth < max_depth {
            make_part(id, depth + 2, max_depth)
        } else {
            String::new()
        };
        format!(
            "{{ id: {id}, kind: component, weight: {w}e-1, children: [{children}] }}",
            w = 1 + id % 9
        )
    }

    // Benchmarks encoding `elem` as one `encoding_name` document: a fresh writer per document
    // (`main`'s behavior) vs a reused writer bound to a fresh sink per document via attach/detach.
    fn bench_doc<E>(
        c: &mut Criterion,
        encoding: E,
        encoding_name: &str,
        label: &str,
        elem: &Element,
    ) where
        E: Encoding + Into<WriteConfig<E>> + Copy,
        E::Writer<Vec<u8>>: Reusable,
    {
        // Encoded size of one document, for context / throughput.
        let encoded_len = {
            let mut buf = Vec::new();
            let mut w = Writer::new(encoding, &mut buf).unwrap();
            w.write(elem).unwrap();
            w.close().unwrap();
            buf.len()
        };

        let mut group = c.benchmark_group(format!("{encoding_name} encode/{label}"));
        group.throughput(Throughput::Bytes(encoded_len as u64));

        // Baseline: a fresh managed writer per document (the sub-writers, including their encoding
        // buffers, and the symbol table are constructed on every value).
        group.bench_function("fresh_writer_per_doc", |b| {
            let mut buf = Vec::with_capacity(64 * 1024);
            b.iter(|| {
                buf.clear();
                let mut w = Writer::new(encoding, &mut buf).unwrap();
                w.write(black_box(elem)).unwrap();
                w.close().unwrap();
                black_box(buf.len());
            });
        });

        // Reuse: one parked idle writer, bound to a fresh sink per document via attach/detach.
        group.bench_function("reused_writer", |b| {
            let mut buf = Vec::with_capacity(64 * 1024);
            let mut idle = Some(Writer::<E, ()>::idle(encoding).unwrap());
            b.iter(|| {
                buf.clear();
                let mut w = idle.take().unwrap().attach(&mut buf);
                w.write(black_box(elem)).unwrap();
                // `detach` writes nothing, so the document is emitted by `flush`; this keeps the
                // measured work equivalent to the `close()` in the baseline above.
                w.flush().unwrap();
                let (next_idle, _sink) = w.detach();
                idle = Some(next_idle);
                black_box(buf.len());
            });
        });

        group.finish();
        println!("\nencoded {encoding_name} '{label}' document size: {encoded_len} bytes\n");
    }

    // A document of `n` records, each with `fields` field names unique to document `doc_id`.
    fn make_symbol_heavy_doc(doc_id: usize, n: usize, fields: usize) -> String {
        let mut s = String::from("[");
        for record in 0..n {
            s.push('{');
            for field in 0..fields {
                let name = format!("doc{doc_id}_field{}", record * fields + field);
                s.push_str(&format!("{name}: {name},"));
            }
            s.push_str("},");
        }
        s.push(']');
        s
    }

    // Encodes a different document on each iteration, so no document's symbols are already in a
    // reused writer's table.
    fn bench_rotating_docs(c: &mut Criterion, label: &str, docs: &[Element]) {
        let mut group = c.benchmark_group(format!("binary 1.0 encode rotating/{label}"));

        group.bench_function("fresh_writer_per_doc", |b| {
            let mut buf = Vec::with_capacity(64 * 1024);
            let mut docs = docs.iter().cycle();
            b.iter(|| {
                buf.clear();
                let mut w = v1_0::BinaryWriter::new(v1_0::Binary, &mut buf).unwrap();
                w.write(black_box(docs.next().unwrap())).unwrap();
                w.close().unwrap();
                black_box(buf.len());
            });
        });

        group.bench_function("reused_writer", |b| {
            let mut buf = Vec::with_capacity(64 * 1024);
            let mut docs = docs.iter().cycle();
            let mut idle = Some(v1_0::BinaryWriter::<()>::idle(v1_0::Binary).unwrap());
            b.iter(|| {
                buf.clear();
                let mut w = idle.take().unwrap().attach(&mut buf);
                w.write(black_box(docs.next().unwrap())).unwrap();
                w.flush().unwrap();
                let (next_idle, _sink) = w.detach();
                idle = Some(next_idle);
                black_box(buf.len());
            });
        });

        group.finish();
    }

    // The binary encoding and the text encoding in its default, compact, format.
    const BINARY: &str = "binary 1.0";
    const COMPACT_TEXT: &str = "text 1.0 compact";

    pub fn criterion_benchmark(c: &mut Criterion) {
        // (label, records per document, fields per record): 100 and 1,000 distinct symbols.
        for (label, n, fields) in [("100 symbols", 10usize, 10usize), ("1000 symbols", 100, 10)] {
            let docs = (0..8)
                .map(|doc_id| {
                    Element::read_one(make_symbol_heavy_doc(doc_id, n, fields).as_str()).unwrap()
                })
                .collect::<Vec<_>>();
            // Binary only: the text writer writes symbol text inline and never interns it.
            bench_rotating_docs(c, label, &docs);
        }

        // (label, record count) chosen to land near ~100 B, ~1 KB, ~10 KB, ~100 KB, ~1 MB encoded.
        let sizes = [
            ("~100B", 1usize),
            ("~1KB", 10),
            ("~10KB", 103),
            ("~100KB", 1030),
            ("~1MB", 10300),
        ];
        for (label, n) in sizes {
            let elem = Element::read_one(make_doc(n).as_str()).unwrap();
            bench_doc(c, v1_0::Binary, BINARY, label, &elem);
            bench_doc(c, v1_0::Text, COMPACT_TEXT, label, &elem);
        }

        // A lone part chain (220 B encoded) that reaches the same container depth, 16, as the
        // aggregate documents below.
        let elem = Element::read_one(make_part(0, 1, 15).as_str()).unwrap();
        bench_doc(c, v1_0::Binary, BINARY, "nested ~100B", &elem);
        bench_doc(c, v1_0::Text, COMPACT_TEXT, "nested ~100B", &elem);

        // (label, item count) chosen to land near ~1 KB, ~10 KB, ~100 KB, ~1 MB encoded.
        let nested_sizes = [
            ("nested ~1KB", 4usize),
            ("nested ~10KB", 55),
            ("nested ~100KB", 563),
            ("nested ~1MB", 5650),
        ];
        for (label, n) in nested_sizes {
            let elem = Element::read_one(make_nested_doc(n).as_str()).unwrap();
            bench_doc(c, v1_0::Binary, BINARY, label, &elem);
            bench_doc(c, v1_0::Text, COMPACT_TEXT, label, &elem);
        }

        // Optionally benchmark a real document supplied via `ION_BENCH_FILE` (any Ion text/binary
        // file with a single top-level value), e.g. `ION_BENCH_FILE=bods.ion cargo bench ...`.
        if let Ok(path) = std::env::var("ION_BENCH_FILE") {
            let bytes = std::fs::read(&path).expect("could not read ION_BENCH_FILE");
            let elem = Element::read_one(bytes).expect("ION_BENCH_FILE is not a single Ion value");
            let label = std::path::Path::new(&path)
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("file");
            bench_doc(c, v1_0::Binary, BINARY, label, &elem);
            bench_doc(c, v1_0::Text, COMPACT_TEXT, label, &elem);
        }
    }
}

criterion_group!(benches, benchmark::criterion_benchmark);
criterion_main!(benches);
