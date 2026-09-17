//! Threshold-model measurement bench (experimental / tuning — not part of the shipped crate API).
//!
//! Measures clean primitives of the `Struct` lifecycle so individual and amortized costs — and the
//! linear-vs-hash crossover per access pattern — can be *computed*, not eyeballed. Run it twice via
//! the compile-time threshold knob:
//!   * linear regime: `ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD=100000 cargo bench --bench struct_threshold_model`
//!   * hash regime:   `ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD=0      cargo bench --bench struct_threshold_model`
//!
//! Recovery (linear run = L-suffixed, hash run = H-suffixed):
//!   construct           C        = construct_drop[L] - drop[L]
//!   drop, no index      D_lin    = drop[L]
//!   drop, with index    D_hash   = drop[H]
//!   index drop          = D_hash - D_lin
//!   warm probe          P        = warm_probe[H]
//!   lazy index build    B        = first_lookup[H] - P
//!   per linear lookup            = access[L] / L
//! Fully-loaded crossover for pattern k (L = k*N): linear wins iff
//!   access_lin(kN)  <  access_hash(kN) + (D_hash - D_lin)
//! (the build is already inside access_hash; index-drop is the one added term).
use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use ion_rs::{Element, Struct, Symbol};

// Individual-cost groups include N=1 (anchors the fixed-cost intercept); access patterns do not
// (k=0.5 is meaningless at N=1, and 1 is already ruled out as a threshold).
const SIZES_ALL: &[usize] = &[1, 2, 4, 8, 12, 16, 24, 32, 40, 48, 64];
const SIZES_ACCESS: &[usize] = &[2, 4, 8, 12, 16, 24, 32, 40, 48, 64];

// A key guaranteed to exist, used to prime the lazy index in setup.
const PRIME_KEY: &str = "field_0";
// A key guaranteed to be absent, for the miss access pattern.
const MISS_KEY: &str = "definitely_absent";

#[derive(Clone, Copy)]
struct Pattern {
    label: &'static str,
    num: usize,
    den: usize,
}

const PATTERNS: &[Pattern] = &[
    Pattern {
        label: "0.5x",
        num: 1,
        den: 2,
    },
    Pattern {
        label: "1.0x",
        num: 1,
        den: 1,
    },
    Pattern {
        label: "2.0x",
        num: 2,
        den: 1,
    },
];

fn slots(field_count: usize) -> Vec<(Symbol, Element)> {
    (0..field_count)
        .map(|i| (format!("field_{i}").into(), (i as i64).into()))
        .collect()
}

fn struct_from(slots: &[(Symbol, Element)]) -> Struct {
    slots.iter().cloned().collect()
}

/// The `L = ceil-ish(k*N)` query strings for a pattern. Hits are spread uniformly across the field
/// range so the linear cost reflects the average position, not a front/back bias; misses are all the
/// same absent key (each a full scan for linear, a miss-probe for hash).
fn queries(field_count: usize, pattern: Pattern, miss: bool) -> Vec<String> {
    let lookups = (field_count * pattern.num / pattern.den).max(1);
    if miss {
        return vec![MISS_KEY.to_string(); lookups];
    }
    (0..lookups)
        .map(|j| format!("field_{}", j * field_count / lookups))
        .collect()
}

// 1. construct + drop of a no-index struct (both timed). Threshold-independent (construction never
//    builds the index); read from the linear run as C + D_lin.
fn bench_construct_drop(c: &mut Criterion) {
    let mut group = c.benchmark_group("construct_drop");
    for &n in SIZES_ALL {
        let s = slots(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &s, |b, s| {
            b.iter(|| {
                let built = struct_from(s);
                black_box(&built);
            })
        });
    }
    group.finish();
}

// 2. drop only (timed), struct primed in untimed setup. Linear run => D_lin (no index); hash run =>
//    D_hash (index built by the priming get).
fn bench_drop(c: &mut Criterion) {
    let mut group = c.benchmark_group("drop");
    group.sample_size(200);
    for &n in SIZES_ALL {
        let s = slots(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &s, |b, s| {
            b.iter_batched(
                || {
                    let built = struct_from(s);
                    let _ = built.get(PRIME_KEY);
                    built
                },
                |built| {
                    black_box(built.len());
                },
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

// 3. L lookups on a fresh struct (construct + drop excluded). Linear run => A_lin; hash run =>
//    A_hash (the first lookup builds the index, so the build is amortized across the L lookups).
fn bench_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("access");
    for &n in SIZES_ACCESS {
        let s = slots(n);
        for &pattern in PATTERNS {
            for (miss, kind) in [(false, "hit"), (true, "miss")] {
                let q = queries(n, pattern, miss);
                let id = format!("{kind}/{}/{n}", pattern.label);
                group.bench_with_input(BenchmarkId::from_parameter(id), &s, |b, s| {
                    b.iter_batched_ref(
                        || struct_from(s),
                        |built| {
                            let mut hits = 0usize;
                            for query in &q {
                                if built.get(query.as_str()).is_some() {
                                    hits += 1;
                                }
                            }
                            black_box(hits)
                        },
                        BatchSize::SmallInput,
                    )
                });
            }
        }
    }
    group.finish();
}

// 4. one lookup on a fresh (unprimed) struct, construct + drop excluded. Hash run => B + P.
fn bench_first_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("first_lookup");
    group.sample_size(200);
    for &n in SIZES_ALL {
        let s = slots(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &s, |b, s| {
            b.iter_batched_ref(
                || struct_from(s),
                |built| black_box(built.get(PRIME_KEY).is_some()),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

// 5. one lookup on a primed struct (index built in untimed setup), construct + drop excluded.
//    Hash run => P (warm probe).
fn bench_warm_probe(c: &mut Criterion) {
    let mut group = c.benchmark_group("warm_probe");
    group.sample_size(200);
    for &n in SIZES_ALL {
        let s = slots(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &s, |b, s| {
            b.iter_batched_ref(
                || {
                    let built = struct_from(s);
                    let _ = built.get(PRIME_KEY);
                    built
                },
                |built| black_box(built.get(PRIME_KEY).is_some()),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

criterion_group!(
    struct_threshold_model,
    bench_construct_drop,
    bench_drop,
    bench_access,
    bench_first_lookup,
    bench_warm_probe
);
criterion_main!(struct_threshold_model);
