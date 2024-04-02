use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::lazy::encoder::binary::v1_0::writer::LazyRawBinaryWriter_1_0;
use nom::AsBytes;

use ion_rs::lazy::encoder::binary::v1_1::writer::LazyRawBinaryWriter_1_1;
use ion_rs::lazy::encoder::value_writer::StructWriter;
use ion_rs::lazy::encoder::value_writer::{SequenceWriter, ValueWriter};
use ion_rs::{IonResult, RawSymbolTokenRef};

fn write_struct_with_string_values(value_writer: impl ValueWriter) -> IonResult<()> {
    let mut struct_ = value_writer.struct_writer()?;
    struct_
        // $10 = timestamp
        .write(10, black_box(1670446800245i64))?
        // $11 = threadId
        .write(11, black_box(418))?
        // $12 = threadName
        .write(12, black_box("scheduler-thread-6"))?
        // $13 = loggerName
        .write(
            13,
            black_box("com.example.organization.product.component.ClassName"),
        )?
        // $14 = logLevel
        .write(14, black_box("INFO"))?
        // $15 = format
        .write(
            15,
            black_box(
                "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
            ),
        )?
        // $16 = parameters
        .write(
            16,
            &[
                black_box("SUCCESS"),
                black_box("example-client-1"),
                black_box("aws-us-east-5f-18b4fa"),
                black_box("region 4"),
                black_box("2022-12-07T20:59:59.744000Z"),
            ],
        )?;
    struct_.end()
}

fn write_struct_with_symbol_values(value_writer: impl ValueWriter) -> IonResult<()> {
    let mut struct_ = value_writer.struct_writer()?;
    struct_
        // $10 = timestamp
        .write(10, black_box(1670446800245i64))?
        // $11 = threadId
        .write(11, black_box(418))?
        // $12 = threadName, $17 = scheduler-thread-6
        .write(12, symbol_id(black_box(17)))?
        // $13 = loggerName, $18 = com.example.organization.product.component.ClassName
        .write(13, symbol_id(black_box(18)))?
        // $14 = logLevel, $19 = INFO
        .write(14, symbol_id(black_box(19)))?
        // $15 = format, $20 = Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}
        .write(15, symbol_id(black_box(20)))?
        // $16 = parameters
        .write(
            16,
            &[
                // $21 = SUCCESS
                symbol_id(black_box(21)),
                // $22 = example-client-1
                symbol_id(black_box(22)),
                // $23 = aws-us-east-5f-18b4fa
                symbol_id(black_box(23)),
                // $24 = region 4
                symbol_id(black_box(24)),
                // $25 = 2022-12-07T20:59:59.744000Z (string, not timestamp)
                symbol_id(black_box(25)),
            ],
        )?;
    struct_.end()
}

fn write_eexp_with_symbol_values(value_writer: impl ValueWriter) -> IonResult<()> {
    let mut eexp = value_writer.eexp_writer(0)?;
    eexp.write(black_box(1670446800245i64))? // timestamp
        .write(black_box(418))? // thread_id
        // These are still strings because they're so short that using symbols to represent
        // them wouldn't be beneficial.
        .write(black_box("6"))? // thread_name
        .write(black_box("1"))? // client_num
        .write(symbol_id(black_box(10)))?; // host_id: "18b4fa" ($10)
    let mut nested_eexp = eexp.eexp_writer(1)?;
    nested_eexp
        // $11 = region 4
        .write(symbol_id(black_box(11)))?
        // $12 = "2022-12-07T20:59:59.744000Z" (string, not timestamp)
        .write(symbol_id(black_box(12)))?;
    nested_eexp.end()?;
    eexp.end()
}

fn write_eexp_with_string_values(value_writer: impl ValueWriter) -> IonResult<()> {
    let mut eexp = value_writer.eexp_writer(0)?;
    eexp.write(black_box(1670446800245i64))? // timestamp
        .write(black_box(418))? // thread_id
        .write(black_box("6"))? // thread_name
        .write(black_box("1"))? // client_num
        .write(black_box("18b4fa"))?; // host_id
    let mut nested_eexp = eexp.eexp_writer(1)?;
    nested_eexp
        .write(black_box("region 4"))?
        .write(black_box("2022-12-07T20:59:59.744000Z"))?;
    nested_eexp.end()?;
    eexp.end()
}

fn symbol_id(sid: usize) -> RawSymbolTokenRef<'static> {
    RawSymbolTokenRef::SymbolId(sid)
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut buffer = Vec::with_capacity(1024 * 1024);

    let mut binary_1_0_group = c.benchmark_group("binary 1.0");
    binary_1_0_group.bench_function("write structs with string values", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_0::new(&mut buffer).unwrap();
            write_struct_with_string_values(writer.value_writer()).unwrap();
            writer.flush().unwrap();
            black_box(buffer.as_bytes());
        });
    });
    // The runner allows the user to specify which benchmarks to run. If the benchmark above ran,
    // then the buffer will not be empty.
    // This print statement cannot live within the benchmark itself, as both `bench_function` and
    // `iter` are called several times.
    if !buffer.is_empty() {
        println!("\nencoded 1.0 size with string values: {}\n", buffer.len());
        buffer.clear();
    }

    binary_1_0_group.bench_function("write structs with symbol values", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_0::new(&mut buffer).unwrap();
            write_struct_with_symbol_values(writer.value_writer()).unwrap();
            writer.flush().unwrap();

            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!("\nencoded 1.0 size with symbol values: {}\n", buffer.len());
        buffer.clear()
    }
    binary_1_0_group.finish();

    let mut binary_1_1_group = c.benchmark_group("binary 1.1");
    binary_1_1_group.bench_function("write structs with string values", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer).unwrap();
            write_struct_with_string_values(writer.value_writer()).unwrap();
            writer.flush().unwrap();
            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!("\nencoded 1.1 size with string values: {}\n", buffer.len());
        buffer.clear()
    }

    binary_1_1_group.bench_function("write structs with symbol values", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer).unwrap();
            write_struct_with_symbol_values(writer.value_writer()).unwrap();
            writer.flush().unwrap();

            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!("\nencoded 1.1 size with symbol values: {}\n", buffer.len());
        buffer.clear()
    }

    binary_1_1_group.bench_function("write delimited structs with string values", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer).unwrap();
            write_struct_with_string_values(writer.value_writer().with_delimited_containers())
                .unwrap();
            writer.flush().unwrap();
            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!(
            "\nencoded 1.1 size, delimited structs with string values: {}\n",
            buffer.len()
        );
        buffer.clear()
    }

    binary_1_1_group.bench_function("write delimited structs with symbol values", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer).unwrap();
            write_struct_with_symbol_values(writer.value_writer().with_delimited_containers())
                .unwrap();
            writer.flush().unwrap();

            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!("\nencoded 1.1 size with symbol values: {}\n", buffer.len());
        buffer.clear()
    }

    binary_1_1_group.bench_function("write structs with string values using macros", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer).unwrap();
            write_eexp_with_string_values(writer.value_writer()).unwrap();
            writer.flush().unwrap();
            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!(
            "\nencoded 1.1 size with string values using macros: {}\n",
            buffer.len()
        );
        buffer.clear()
    }

    binary_1_1_group.bench_function("write structs with symbol values using macros", |b| {
        b.iter(|| {
            buffer.clear();
            let mut writer = LazyRawBinaryWriter_1_1::new(&mut buffer).unwrap();
            write_eexp_with_symbol_values(writer.value_writer()).unwrap();
            writer.flush().unwrap();
            black_box(buffer.as_bytes());
        });
    });
    if !buffer.is_empty() {
        println!(
            "\nencoded 1.1 size with symbol values using macros: {}\n",
            buffer.len()
        );
        buffer.clear()
    }

    binary_1_1_group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
