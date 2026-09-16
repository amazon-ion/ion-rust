//! Benchmarks reading larger (~10KB and ~30KB) binary Ion 1.0 documents.
//!
//! The existing benchmarks read very large streams (millions of bytes) through a single
//! reader, which amortizes away both per-document fixed costs and mid-size scanning
//! behavior. This benchmark measures the "one reader per document" pattern on documents
//! large enough to be dominated by value scanning rather than reader construction.
//!
//! Each document is a single top-level list of structs, generated in two flavors:
//!   * `value_heavy`: a small set of field names is reused across many struct instances
//!     (log-record shaped). The local symbol table stays small; nearly all of the
//!     document is value content.
//!   * `symbol_heavy`: every field name and symbol value in the document is distinct,
//!     so the local symbol table grows with the document (hundreds to thousands of
//!     entries). Most of the read cost is symbol table processing.
//!
//! Cases:
//!   * `element_read_one`: materializes the document with `Element::read_one` — the
//!     stable, default-feature API.
//!   * `element_struct_get_by_name`: materializes the document once (outside the timed
//!     loop), then repeatedly looks up struct fields by name — mostly present names,
//!     plus ~15% absent names — a regression guard for the DOM's field-name index.
//!   * `lazy_any_read_all` / `lazy_binary_read_all`: visits every value in the document
//!     using the streaming `Reader` with `AnyEncoding` (encoding auto-detection) and
//!     with the concrete `v1_0::Binary` encoding. Like the other benchmarks' streaming
//!     cases, these require the `experimental-reader-writer` feature.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::{v1_0, Element, IonResult, Sequence};
use std::fmt::Write as _;

/// Produces the text for a list of `num_structs` log-record-shaped structs. The same
/// 20 field names appear in every struct, so the encoded document's symbol table stays
/// small while the value region grows with `num_structs`.
fn value_heavy_text(num_structs: usize) -> String {
    let mut text = String::from("[\n");
    for i in 0..num_structs {
        write!(
            text,
            r#"{{
                requestId: "req-{i:08x}-4f2a9b1c",
                sessionId: "sess-{:08x}",
                operation: "GetRecord",
                status: "SUCCESS",
                clientId: "client-{:03}",
                host: "host-{:02}.example.com",
                region: "us-east-1",
                tenant: "example-tenant",
                message: "processed request batch with standard options enabled",
                level: INFO,
                latencyMs: {},
                retries: {},
                itemCount: {},
                byteSize: {},
                epochMs: {},
                shard: {},
                cacheHit: {},
                throttled: false,
                score: 2.5e0,
                timestamp: 2024-06-15T12:34:56.789Z
            }},
            "#,
            i.wrapping_mul(0x9e37_79b9),
            i % 50,
            i % 20,
            (i * 7) % 900 + 3,
            i % 4,
            (i * 13) % 5000,
            (i * 131) % 100_000,
            1_718_000_000_000_u64 + i as u64,
            i % 16,
            i % 3 == 0,
        )
        .unwrap();
    }
    text.push(']');
    text
}

/// The field names used by `value_heavy_text`, for by-name lookups.
const VALUE_HEAVY_FIELD_NAMES: &[&str] = &[
    "requestId",
    "sessionId",
    "operation",
    "status",
    "clientId",
    "host",
    "region",
    "tenant",
    "message",
    "level",
    "latencyMs",
    "retries",
    "itemCount",
    "byteSize",
    "epochMs",
    "shard",
    "cacheHit",
    "throttled",
    "score",
    "timestamp",
];

/// Number of fields in each struct produced by `symbol_heavy_text`.
const SYMBOL_HEAVY_FIELDS_PER_STRUCT: usize = 10;

/// Produces the text for a list of `num_structs` structs in which every field name and
/// every (symbol) field value is distinct, so the encoded document's local symbol table
/// grows by 2 × `SYMBOL_HEAVY_FIELDS_PER_STRUCT` entries per struct.
fn symbol_heavy_text(num_structs: usize) -> String {
    let mut text = String::from("[\n");
    for i in 0..num_structs {
        text.push('{');
        for j in 0..SYMBOL_HEAVY_FIELDS_PER_STRUCT {
            let id = i * SYMBOL_HEAVY_FIELDS_PER_STRUCT + j;
            write!(text, "fieldName{id:05}: symValue{id:05},").unwrap();
        }
        text.pop(); // remove the trailing comma
        text.push_str("},\n");
    }
    text.push(']');
    text
}

/// The field name of the `index`th field of the `struct_index`th struct produced by
/// `symbol_heavy_text`.
fn symbol_heavy_field_name(struct_index: usize, index: usize) -> String {
    format!(
        "fieldName{:05}",
        struct_index * SYMBOL_HEAVY_FIELDS_PER_STRUCT + index
    )
}

/// Encodes the provided text Ion as binary Ion 1.0.
fn encode_binary_1_0(text: &str) -> IonResult<Vec<u8>> {
    Element::read_one(text)?.encode_as(v1_0::Binary)
}

/// Grows the number of structs produced by `flavor` until the binary-encoded document
/// reaches `target_num_bytes`. Returns the encoded document and the struct count.
fn make_document(flavor: Flavor, target_num_bytes: usize) -> IonResult<(Vec<u8>, usize)> {
    let mut num_structs = 8;
    let mut binary_data = encode_binary_1_0(&flavor.generate(num_structs))?;
    // Take one proportional jump toward the target size, then fine-tune linearly.
    num_structs = (num_structs * target_num_bytes / binary_data.len().max(1)).max(1);
    binary_data = encode_binary_1_0(&flavor.generate(num_structs))?;
    while binary_data.len() < target_num_bytes {
        num_structs += 1;
        binary_data = encode_binary_1_0(&flavor.generate(num_structs))?;
    }
    Ok((binary_data, num_structs))
}

/// Traverses a materialized document, visiting every nested value. Returns the number of
/// values visited.
fn visit_element(element: &Element) -> usize {
    use ion_rs::Value;
    match element.value() {
        Value::List(seq) | Value::SExp(seq) => 1 + seq.elements().map(visit_element).sum::<usize>(),
        Value::Struct(strukt) => {
            1 + strukt
                .fields()
                .map(|(_name, value)| visit_element(value))
                .sum::<usize>()
        }
        scalar => {
            let _ = black_box(scalar);
            1
        }
    }
}

/// A document flavor: which shape of test document to generate.
#[derive(Clone, Copy, Debug)]
enum Flavor {
    /// Log-record-shaped structs reusing a small set of field names; the symbol table
    /// stays small and nearly all of the document is value content.
    ValueHeavy,
    /// Structs in which every field name and symbol value is distinct; most of the read
    /// cost is symbol table processing.
    SymbolHeavy,
}

impl Flavor {
    /// A short name for this flavor, used in benchmark IDs.
    fn label(self) -> &'static str {
        match self {
            Flavor::ValueHeavy => "value_heavy",
            Flavor::SymbolHeavy => "symbol_heavy",
        }
    }

    /// Produces the text for a document of this flavor containing `num_structs` structs.
    fn generate(self, num_structs: usize) -> String {
        match self {
            Flavor::ValueHeavy => value_heavy_text(num_structs),
            Flavor::SymbolHeavy => symbol_heavy_text(num_structs),
        }
    }

    /// The field names to look up in the `struct_index`th struct of a document of this
    /// flavor: this struct's present field names followed by `num_absent` names that are
    /// absent from every struct.
    fn lookup_keys(self, struct_index: usize) -> Vec<String> {
        let absent_keys = |count: usize| {
            (0..count).map(move |index| format!("missingField{:02}", (struct_index + index) % 8))
        };
        match self {
            Flavor::ValueHeavy => VALUE_HEAVY_FIELD_NAMES
                .iter()
                .map(|name| (*name).to_owned())
                .chain(absent_keys(3))
                .collect(),
            Flavor::SymbolHeavy => (0..SYMBOL_HEAVY_FIELDS_PER_STRUCT)
                .map(|index| symbol_heavy_field_name(struct_index, index))
                .chain(absent_keys(2))
                .collect(),
        }
    }
}

/// Benchmarks that only require the crate's default features.
fn default_feature_benchmarks(
    c: &mut Criterion,
    flavor: Flavor,
    size_label: &str,
    binary_data: &[u8],
    num_structs: usize,
) {
    let case_id = format!("{}_{}", flavor.label(), size_label);

    // Materialize the whole document with the stable, default-feature API.
    let mut group = c.benchmark_group("large_doc_read/element_read_one");
    group.bench_function(&case_id, |b| {
        b.iter(|| {
            let element = Element::read_one(black_box(binary_data)).unwrap();
            black_box(element);
        })
    });
    group.finish();

    // Materialize the document once, then repeatedly look up struct fields by name.
    let document = Element::read_one(binary_data).unwrap();
    let structs: Vec<_> = document
        .as_sequence()
        .unwrap()
        .elements()
        .map(|element| element.as_struct().unwrap())
        .collect();
    // Precompute the lookup keys so the timed loop performs no allocations. Roughly
    // 15% of the keys are absent from every struct so that the index's miss path is
    // exercised alongside its hit path.
    let lookup_keys: Vec<Vec<String>> = (0..num_structs)
        .map(|struct_index| flavor.lookup_keys(struct_index))
        .collect();
    let mut group = c.benchmark_group("large_doc_read/element_struct_get_by_name");
    group.bench_function(&case_id, |b| {
        b.iter(|| {
            let mut num_found = 0_usize;
            for (strukt, keys) in structs.iter().zip(lookup_keys.iter()) {
                for key in keys {
                    if let Some(value) = strukt.get(key.as_str()) {
                        black_box(value);
                        num_found += 1;
                    }
                }
            }
            black_box(num_found);
        })
    });
    group.finish();
}

/// Benchmarks that require the `experimental-reader-writer` feature.
#[cfg(feature = "experimental-reader-writer")]
fn lazy_reader_benchmarks(c: &mut Criterion, flavor: Flavor, size_label: &str, binary_data: &[u8]) {
    use ion_rs::{AnyEncoding, Decoder, LazyStruct, LazyValue, Reader, ValueRef};

    /// Reads this value and, if it's a container, any nested values. Returns the number
    /// of values read.
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

    let case_id = format!("{}_{}", flavor.label(), size_label);

    let mut group = c.benchmark_group("large_doc_read/lazy_any_read_all");
    group.bench_function(&case_id, |b| {
        b.iter(|| {
            let mut reader = Reader::new(AnyEncoding, black_box(binary_data)).unwrap();
            let mut num_values = 0_usize;
            while let Some(item) = reader.next().unwrap() {
                num_values += count_value_and_children(&item).unwrap();
            }
            black_box(num_values);
        })
    });
    group.finish();

    let mut group = c.benchmark_group("large_doc_read/lazy_binary_read_all");
    group.bench_function(&case_id, |b| {
        b.iter(|| {
            let mut reader = Reader::new(v1_0::Binary, black_box(binary_data)).unwrap();
            let mut num_values = 0_usize;
            while let Some(item) = reader.next().unwrap() {
                num_values += count_value_and_children(&item).unwrap();
            }
            black_box(num_values);
        })
    });
    group.finish();
}

fn criterion_benchmark(c: &mut Criterion) {
    const SIZES: &[(usize, &str)] = &[(10 * 1024, "10KB"), (30 * 1024, "30KB")];
    const FLAVORS: &[Flavor] = &[Flavor::ValueHeavy, Flavor::SymbolHeavy];

    for &flavor in FLAVORS {
        for &(target_num_bytes, size_label) in SIZES {
            let (binary_data, num_structs) =
                make_document(flavor, target_num_bytes).expect("failed to generate document");
            println!(
                "{} {size_label}: {} bytes, {num_structs} structs",
                flavor.label(),
                binary_data.len()
            );

            // Sanity check: the document must round-trip as a single top-level list.
            let document: Sequence = Element::read_all(binary_data.as_slice()).unwrap();
            assert_eq!(document.len(), 1);
            let element = document.elements().next().unwrap();
            assert_eq!(element.as_sequence().unwrap().len(), num_structs);
            assert!(visit_element(element) > num_structs);

            default_feature_benchmarks(c, flavor, size_label, &binary_data, num_structs);
            #[cfg(feature = "experimental-reader-writer")]
            lazy_reader_benchmarks(c, flavor, size_label, &binary_data);
        }
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
