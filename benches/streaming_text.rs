use criterion::{criterion_group, criterion_main, Criterion};

#[cfg(feature = "experimental-reader-writer")]
fn streaming_text(c: &mut Criterion) {
    use criterion::{black_box, BenchmarkId, Throughput};
    use ion_rs::{AnyEncoding, Element, ElementReader, IonData, IonStream, Reader};
    use std::io::{self, Read};

    struct ShortReads<'a> {
        remaining: &'a [u8],
        chunk_size: usize,
    }
    impl Read for ShortReads<'_> {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            let count = output.len().min(self.remaining.len()).min(self.chunk_size);
            output[..count].copy_from_slice(&self.remaining[..count]);
            self.remaining = &self.remaining[count..];
            Ok(count)
        }
    }

    let records: Vec<_> = (0..2000)
        .map(|index| format!(
            r#"{{timestamp:{},threadId:{},threadName:"scheduler-thread-{}",logLevel:INFO,parameters:["SUCCESS","client-{}","us-east-1",{}]}}"#,
            1670446800245u64 + index, index % 32, index % 8, index, index * 17,
        ))
        .collect();
    for (name, data) in [
        ("list", format!("[{}]", records.join(","))),
        ("records", records.join("\n")),
    ] {
        let expected = Element::read_all(&data).unwrap();
        let mut group = c.benchmark_group(format!("streaming text/{name}"));
        group.throughput(Throughput::Bytes(data.len() as u64));
        for chunk_size in [1024, 8192, 65536, usize::MAX] {
            let read = || {
                Reader::new(
                    AnyEncoding,
                    IonStream::new(ShortReads {
                        remaining: data.as_bytes(),
                        chunk_size,
                    }),
                )
                .unwrap()
                .read_all_elements()
                .unwrap()
            };
            assert_eq!(IonData::from(read()), IonData::from(expected.clone()));
            group.bench_with_input(
                BenchmarkId::from_parameter(chunk_size),
                &chunk_size,
                |b, _| {
                    b.iter(|| black_box(read()));
                },
            );
        }
        group.finish();
    }
}

#[cfg(not(feature = "experimental-reader-writer"))]
fn streaming_text(_: &mut Criterion) {
    panic!("Enable experimental-reader-writer to run this benchmark");
}

criterion_group!(benches, streaming_text);
criterion_main!(benches);
