use std::io;
use std::io::Write;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::binary::var_uint::VarUInt;
use ion_rs::result::IonResult;

pub fn criterion_benchmark(c: &mut Criterion) {
    let value: u64 = 202233312022;
    let mut buffer1 = Vec::with_capacity(64);
    c.bench_function("Classic write VarUInt",
                     |b| b.iter(|| {
                         buffer1.clear();
                         let bytes_written = VarUInt::write_u64(&mut buffer1, value).unwrap();
                         black_box(bytes_written);
                     }));
    let mut var_uint = Default::default();
    c.bench_function("Classic read VarUInt",
                     |b| b.iter(|| {
                         var_uint = VarUInt::read(&mut io::Cursor::new(buffer1.as_slice())).unwrap();
                     }));
    println!("{buffer1:x?} => {value}");
    assert_eq!(value, var_uint.value() as u64);

    let mut buffer3 = Vec::with_capacity(64);
    c.bench_function("New write VarUInt",
                     |b| b.iter(|| {
                         buffer3.clear();
                         let bytes_written = VarUInt::write_new_var_uint(&mut buffer3, value).unwrap();
                         black_box(bytes_written);
                     }));
    c.bench_function("New read VarUInt",
                     |b| b.iter(|| {
                         var_uint= VarUInt::read_new_var_uint(&mut io::Cursor::new(buffer3.as_slice())).unwrap();
                     }));
    println!("{buffer3:x?} => {value}");
    assert_eq!(value, var_uint.value() as u64);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);