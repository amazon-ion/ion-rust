use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::prelude::StdRng;
use rand::{distributions::Uniform, Rng, SeedableRng};
use std::io;

use ion_rs::{FlexInt, FlexUInt, ImmutableBuffer, IonResult, VarInt, VarUInt};

// Rather than store a set of test values, we hardcode a seed value and generate the same set
// on each run.
const RNG_SEED: u64 = 1024;

// The number of values (signed or unsigned) that will be read or written in each benchmark.
const NUM_VALUES: usize = 10_000;

fn generate_unsigned_values(min: u64, max: u64) -> Vec<u64> {
    let mut rng = StdRng::seed_from_u64(RNG_SEED);
    let range = Uniform::new(min, max);

    (0..NUM_VALUES).map(|_| rng.sample(range)).collect()
}

fn generate_signed_values(min: i64, max: i64) -> Vec<i64> {
    let mut rng = StdRng::seed_from_u64(RNG_SEED);
    let range = Uniform::new(min, max);

    (0..NUM_VALUES).map(|_| rng.sample(range)).collect()
}

pub fn criterion_benchmark(c: &mut Criterion) {
    println!("# Values: {NUM_VALUES}");

    // TODO: For now, these benchmarks only write values that can be serialized in 8 bytes or fewer.
    // This is because `VarUInt` has a bug[1] that causes it to encode very large u64s incorrectly.
    // [1]: https://github.com/amazon-ion/ion-rust/issues/689
    let unsigned_values = generate_unsigned_values(u64::MIN, (2 << 49) - 1);
    let signed_values = generate_signed_values(-2 << 49, (2 << 49) - 1);

    // Roundtrip all of the values as 1.1 encoding primitives as a correctness/sanity check.
    // Save the encoded bytes of each value sequence; we'll check its length at the end of each
    // benchmark as another sanity check. VarUInt/FlexUint and VarInt/FlexInt are the same size.
    let encoded_var_uints = roundtrip_var_uint_test(&unsigned_values).unwrap();
    let encoded_var_ints = roundtrip_var_int_test(&signed_values).unwrap();
    let encoded_flex_uints = roundtrip_flex_uint_test(&unsigned_values).unwrap();
    let encoded_flex_ints = roundtrip_flex_int_test(&signed_values).unwrap();

    let mut binary_1_0_group = c.benchmark_group("binary 1.0");
    binary_1_0_group.bench_function("write VarUInt", |b| {
        // `io::sink()` is an implementation of `io::Write` that simply discards the provided bytes
        // and declares success, analogous to `/dev/null`. This minimizes the I/O logic being
        // measured in each benchmark.
        let mut output = io::sink();
        b.iter(|| {
            let mut encoded_length: usize = 0;
            for value in &unsigned_values {
                encoded_length += black_box(VarUInt::write_u64(&mut output, *value).unwrap());
            }
            assert_eq!(encoded_length, encoded_flex_uints.len());
        })
    });
    binary_1_0_group.bench_function("read VarUInt", |b| {
        b.iter(|| {
            let mut decoded_length: usize = 0;
            let mut input = ImmutableBuffer::new(encoded_var_uints.as_slice());
            for _ in 0..unsigned_values.len() {
                let (var_uint, remaining) = input.read_var_uint().unwrap();
                input = remaining;
                decoded_length += var_uint.size_in_bytes();
            }
            assert_eq!(decoded_length, encoded_var_uints.len());
        })
    });
    binary_1_0_group.bench_function("write VarInt", |b| {
        let mut output = io::sink();
        b.iter(|| {
            let mut encoded_length: usize = 0;
            for value in &signed_values {
                encoded_length += black_box(VarInt::write_i64(&mut output, *value).unwrap());
            }
            assert_eq!(encoded_length, encoded_flex_ints.len());
        })
    });
    binary_1_0_group.bench_function("read VarInt", |b| {
        b.iter(|| {
            let mut decoded_length: usize = 0;
            let mut input = ImmutableBuffer::new(encoded_var_ints.as_slice());
            for _ in 0..unsigned_values.len() {
                let (var_int, remaining) = input.read_var_int().unwrap();
                input = remaining;
                decoded_length += var_int.size_in_bytes();
            }
            assert_eq!(decoded_length, encoded_var_ints.len());
        })
    });
    binary_1_0_group.finish();

    let mut binary_1_1_group = c.benchmark_group("binary 1.1");
    binary_1_1_group.bench_function("write FlexUInt", |b| {
        let mut output = io::sink();
        b.iter(|| {
            let mut encoded_length: usize = 0;
            for value in &unsigned_values {
                encoded_length += black_box(FlexUInt::write_u64(&mut output, *value).unwrap());
            }
            assert_eq!(encoded_length, encoded_flex_uints.len());
        })
    });
    binary_1_1_group.bench_function("read FlexUInt", |b| {
        b.iter(|| {
            let mut decoded_length: usize = 0;
            let mut input = ImmutableBuffer::new(encoded_flex_uints.as_slice());
            for _ in 0..unsigned_values.len() {
                let (flex_uint, remaining) = input.read_flex_uint().unwrap();
                input = remaining;
                decoded_length += flex_uint.size_in_bytes();
            }
            assert_eq!(decoded_length, encoded_flex_uints.len());
        })
    });
    binary_1_1_group.bench_function("write FlexInt", |b| {
        let mut output = io::sink();
        b.iter(|| {
            let mut encoded_length: usize = 0;
            for value in &signed_values {
                encoded_length += black_box(FlexInt::write_i64(&mut output, *value).unwrap());
            }
            assert_eq!(encoded_length, encoded_flex_ints.len());
        })
    });
    binary_1_1_group.bench_function("read FlexInt", |b| {
        b.iter(|| {
            let mut decoded_length: usize = 0;
            let mut input = ImmutableBuffer::new(encoded_flex_ints.as_slice());
            for _ in 0..unsigned_values.len() {
                let (flex_int, remaining) = input.read_flex_int().unwrap();
                input = remaining;
                decoded_length += flex_int.size_in_bytes();
            }
            assert_eq!(decoded_length, encoded_flex_ints.len());
        })
    });
    binary_1_1_group.finish();
}

fn roundtrip_var_uint_test(unsigned_values: &[u64]) -> IonResult<Vec<u8>> {
    println!("Roundtripping unsigned values as VarUInts to check for correctness.");
    let mut encoded_values_buffer = Vec::new();
    for value in unsigned_values {
        VarUInt::write_u64(&mut encoded_values_buffer, *value)?;
    }
    let mut decoded_values = Vec::new();
    let mut input = ImmutableBuffer::new(encoded_values_buffer.as_slice());
    for _ in 0..unsigned_values.len() {
        let (var_uint, remaining) = input.read_var_uint()?;
        input = remaining;
        decoded_values.push(var_uint.value() as u64);
    }
    assert_eq!(decoded_values.as_slice(), unsigned_values);
    Ok(encoded_values_buffer)
}

fn roundtrip_var_int_test(signed_values: &[i64]) -> IonResult<Vec<u8>> {
    println!("Roundtripping signed values as VarInts to check for correctness.");
    let mut encoded_values_buffer = Vec::new();
    for value in signed_values {
        VarInt::write_i64(&mut encoded_values_buffer, *value)?;
    }
    let mut decoded_values = Vec::new();
    let mut input = ImmutableBuffer::new(encoded_values_buffer.as_slice());
    for _ in 0..signed_values.len() {
        let (var_int, remaining) = input.read_var_int()?;
        input = remaining;
        decoded_values.push(var_int.value());
    }
    assert_eq!(decoded_values.as_slice(), signed_values);
    Ok(encoded_values_buffer)
}

fn roundtrip_flex_uint_test(unsigned_values: &[u64]) -> IonResult<Vec<u8>> {
    println!("Roundtripping unsigned values as FlexUInts to check for correctness.");
    let mut encoded_values_buffer = Vec::new();
    for value in unsigned_values {
        FlexUInt::write_u64(&mut encoded_values_buffer, *value)?;
    }
    let mut decoded_values = Vec::new();
    let mut input = ImmutableBuffer::new(encoded_values_buffer.as_slice());
    for _ in 0..unsigned_values.len() {
        let (flex_uint, remaining) = input.read_flex_uint()?;
        input = remaining;
        decoded_values.push(flex_uint.value());
    }
    assert_eq!(decoded_values.as_slice(), unsigned_values);
    Ok(encoded_values_buffer)
}

fn roundtrip_flex_int_test(signed_values: &[i64]) -> IonResult<Vec<u8>> {
    println!("Roundtripping signed values as FlexInts to check for correctness.");
    let mut encoded_values_buffer = Vec::new();
    for value in signed_values {
        FlexInt::write_i64(&mut encoded_values_buffer, *value)?;
    }
    let mut decoded_values = Vec::new();
    let mut input = ImmutableBuffer::new(encoded_values_buffer.as_slice());
    for _ in 0..signed_values.len() {
        let (flex_int, remaining) = input.read_flex_int()?;
        input = remaining;
        decoded_values.push(flex_int.value());
    }
    assert_eq!(decoded_values.as_slice(), signed_values);
    Ok(encoded_values_buffer)
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
