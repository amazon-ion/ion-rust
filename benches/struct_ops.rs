//! Benchmarks the public `Struct` operations against the layout shipped in this crate: `get`,
//! `get_all`, construction (`FromIterator`), `PartialEq`, and the `IonData`-mediated `ion_eq`,
//! ordering, and hashing. Where a pre-index baseline is meaningful (`get`, `get_all`, construction)
//! an `FxHashMap<name, Vec<index>>` — the shape the old `Struct` maintained eagerly — is measured
//! alongside so the trade is visible.
//!
//! Lookup and equality/ordering/hashing fixtures are **primed** (the relevant lazy index is built
//! once before timing), so these measure the warm steady-state cost. Construction is measured cold
//! via `iter_batched`, since building the value is the thing under test.
use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use hashbrown::HashMap;
use ion_rs::{Element, IonData, Struct, Symbol};
use rustc_hash::FxBuildHasher;
use std::hash::{DefaultHasher, Hash, Hasher};

type FxHashIndex = HashMap<String, Vec<usize>, FxBuildHasher>;

// Field counts spanning the linear/hash crossover (48) and the largest size the plan calls out
// (100), plus the small sizes where a struct usually lives.
const FIELD_COUNTS: &[usize] = &[1, 4, 8, 16, 32, 48, 64, 100];
const TARGET_FIELD: &str = "target";
const MISSING_FIELD: &str = "missing";

#[derive(Clone, Copy)]
enum NameShape {
    Distinct,
    EveryEighthDuplicate,
}

impl NameShape {
    fn label(self) -> &'static str {
        match self {
            NameShape::Distinct => "distinct",
            NameShape::EveryEighthDuplicate => "every_8th_duplicate",
        }
    }

    fn slots(self, field_count: usize) -> Vec<(Symbol, Element)> {
        match self {
            NameShape::Distinct => build_distinct_slots(field_count),
            NameShape::EveryEighthDuplicate => {
                build_every_eighth_duplicate_slots(field_count, TARGET_FIELD)
            }
        }
    }
}

#[derive(Clone, Copy)]
enum GetScenario {
    HitAtFront,
    HitAtBack,
    Miss,
}

impl GetScenario {
    fn label(self) -> &'static str {
        match self {
            GetScenario::HitAtFront => "hit_front",
            GetScenario::HitAtBack => "hit_back",
            GetScenario::Miss => "miss",
        }
    }
}

// ---- fixture builders ------------------------------------------------------

fn build_distinct_slots(field_count: usize) -> Vec<(Symbol, Element)> {
    let mut slots = Vec::with_capacity(field_count);
    for index in 0..field_count {
        slots.push((format!("field_{index}").into(), (index as i64).into()));
    }
    slots
}

fn build_hit_front_slots(field_count: usize, query: &'static str) -> Vec<(Symbol, Element)> {
    let mut slots = Vec::with_capacity(field_count);
    if field_count > 0 {
        slots.push((query.into(), 0_i64.into()));
    }
    for index in 1..field_count {
        slots.push((format!("field_{index}").into(), (index as i64).into()));
    }
    slots
}

fn build_hit_back_slots(field_count: usize, query: &'static str) -> Vec<(Symbol, Element)> {
    let mut slots = Vec::with_capacity(field_count);
    if field_count == 0 {
        return slots;
    }
    for index in 0..field_count - 1 {
        slots.push((format!("field_{index}").into(), (index as i64).into()));
    }
    slots.push((query.into(), ((field_count - 1) as i64).into()));
    slots
}

fn build_every_eighth_duplicate_slots(
    field_count: usize,
    query: &'static str,
) -> Vec<(Symbol, Element)> {
    let mut slots = Vec::with_capacity(field_count);
    for index in 0..field_count {
        let name: Symbol = if index % 8 == 0 {
            query.into()
        } else {
            format!("field_{index}").into()
        };
        slots.push((name, (index as i64).into()));
    }
    slots
}

fn build_hash_index(slots: &[(Symbol, Element)]) -> FxHashIndex {
    let mut hash_index = FxHashIndex::with_capacity_and_hasher(slots.len(), FxBuildHasher);
    for (index, (field_name, _)) in slots.iter().enumerate() {
        let field_name = field_name
            .text()
            .expect("benchmark fixture uses known text");
        hash_index
            .entry(field_name.to_owned())
            .or_default()
            .push(index);
    }
    hash_index
}

fn struct_from(slots: &[(Symbol, Element)]) -> Struct {
    slots.iter().cloned().collect()
}

// ---- lookup ----------------------------------------------------------------

struct LookupFixture {
    slots: Vec<(Symbol, Element)>,
    ion_struct: Struct,
    hash_index: FxHashIndex,
    query: &'static str,
}

impl LookupFixture {
    fn new(slots: Vec<(Symbol, Element)>, query: &'static str) -> Self {
        let hash_index = build_hash_index(&slots);
        let ion_struct = struct_from(&slots);
        let _ = ion_struct.get(query); // prime the lazy hash index
        Self {
            slots,
            ion_struct,
            hash_index,
            query,
        }
    }

    fn hash_map_get(&self) -> Option<&Element> {
        self.hash_index
            .get(self.query)
            .and_then(|indices| indices.last())
            .map(|&index| &self.slots[index].1)
    }

    fn hash_map_get_all(&self) -> usize {
        let mut count = 0;
        if let Some(indices) = self.hash_index.get(self.query) {
            for &index in indices {
                black_box(&self.slots[index].1);
                count += 1;
            }
        }
        count
    }

    fn struct_get_all(&self) -> usize {
        let mut count = 0;
        for value in self.ion_struct.get_all(self.query) {
            black_box(value);
            count += 1;
        }
        count
    }
}

fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("struct_get");
    for scenario in [
        GetScenario::HitAtFront,
        GetScenario::HitAtBack,
        GetScenario::Miss,
    ] {
        for &field_count in FIELD_COUNTS {
            let (slots, query) = match scenario {
                GetScenario::HitAtFront => (
                    build_hit_front_slots(field_count, TARGET_FIELD),
                    TARGET_FIELD,
                ),
                GetScenario::HitAtBack => (
                    build_hit_back_slots(field_count, TARGET_FIELD),
                    TARGET_FIELD,
                ),
                GetScenario::Miss => (build_distinct_slots(field_count), MISSING_FIELD),
            };
            let fixture = LookupFixture::new(slots, query);
            let parameter = format!("{}/{}_fields", scenario.label(), field_count);
            group.bench_with_input(
                BenchmarkId::new("struct_current", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(fixture.ion_struct.get(fixture.query))),
            );
            group.bench_with_input(
                BenchmarkId::new("hash_map", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(fixture.hash_map_get())),
            );
        }
    }
    group.finish();
}

fn bench_get_all(c: &mut Criterion) {
    let mut group = c.benchmark_group("struct_get_all");
    for scenario in [NameShape::Distinct, NameShape::EveryEighthDuplicate] {
        for &field_count in FIELD_COUNTS {
            // Distinct puts a single hit at the back; the duplicate shape repeats the target.
            let slots = match scenario {
                NameShape::Distinct => build_hit_back_slots(field_count, TARGET_FIELD),
                NameShape::EveryEighthDuplicate => {
                    build_every_eighth_duplicate_slots(field_count, TARGET_FIELD)
                }
            };
            let fixture = LookupFixture::new(slots, TARGET_FIELD);
            let parameter = format!("{}/{}_fields", scenario.label(), field_count);
            group.bench_with_input(
                BenchmarkId::new("struct_current", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(fixture.struct_get_all())),
            );
            group.bench_with_input(
                BenchmarkId::new("hash_map", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(fixture.hash_map_get_all())),
            );
        }
    }
    group.finish();
}

// ---- construction ----------------------------------------------------------

fn bench_construct(c: &mut Criterion) {
    let mut group = c.benchmark_group("struct_construct");
    for scenario in [NameShape::Distinct, NameShape::EveryEighthDuplicate] {
        for &field_count in FIELD_COUNTS {
            let slots = scenario.slots(field_count);
            let parameter = format!("{}/{}_fields", scenario.label(), field_count);
            // The cloned slot list is produced outside the timed section.
            group.bench_with_input(
                BenchmarkId::new("struct_current", &parameter),
                &slots,
                |b, slots| {
                    b.iter_batched(
                        || slots.clone(),
                        |slots| black_box(slots.into_iter().collect::<Struct>()),
                        BatchSize::SmallInput,
                    )
                },
            );
            group.bench_with_input(
                BenchmarkId::new("hash_map", &parameter),
                &slots,
                |b, slots| b.iter(|| black_box(build_hash_index(slots))),
            );
        }
    }
    group.finish();
}

// ---- equality / ordering / hashing -----------------------------------------

struct PairFixture {
    a: Struct,
    b: Struct,
    ion_a: IonData<Struct>,
    ion_b: IonData<Struct>,
}

impl PairFixture {
    fn new(slots: Vec<(Symbol, Element)>) -> Self {
        // `b` is the same multiset in reverse insertion order, so equality/ordering do their full
        // work (no early length or first-field mismatch) and exercise the `by_field` sort.
        let mut reversed = slots.clone();
        reversed.reverse();
        let a = struct_from(&slots);
        let b = struct_from(&reversed);
        let _ = a == b; // prime both structs' lazy `by_field` order
        let ion_a = IonData::from(a.clone());
        let ion_b = IonData::from(b.clone());
        let _ = ion_a.cmp(&ion_b); // prime the wrapped clones' `by_field`
        Self { a, b, ion_a, ion_b }
    }
}

fn bench_eq_ord_hash(c: &mut Criterion) {
    let mut group = c.benchmark_group("struct_eq_ord_hash");
    for scenario in [NameShape::Distinct, NameShape::EveryEighthDuplicate] {
        for &field_count in FIELD_COUNTS {
            let fixture = PairFixture::new(scenario.slots(field_count));
            let parameter = format!("{}/{}_fields", scenario.label(), field_count);
            group.bench_with_input(
                BenchmarkId::new("partial_eq", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(fixture.a == fixture.b)),
            );
            group.bench_with_input(
                BenchmarkId::new("ion_eq", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(IonData::eq(&fixture.a, &fixture.b))),
            );
            group.bench_with_input(
                BenchmarkId::new("ion_cmp", &parameter),
                &fixture,
                |b, fixture| b.iter(|| black_box(fixture.ion_a.cmp(&fixture.ion_b))),
            );
            group.bench_with_input(
                BenchmarkId::new("ion_hash", &parameter),
                &fixture,
                |b, fixture| {
                    b.iter(|| {
                        let mut hasher = DefaultHasher::new();
                        fixture.ion_a.hash(&mut hasher);
                        black_box(hasher.finish())
                    })
                },
            );
        }
    }
    group.finish();
}

criterion_group!(
    struct_ops,
    bench_get,
    bench_get_all,
    bench_construct,
    bench_eq_ord_hash
);
criterion_main!(struct_ops);
