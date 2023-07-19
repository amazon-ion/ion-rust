# Amazon Ion Rust

[![Crate](https://img.shields.io/crates/v/ion-rs.svg)](https://crates.io/crates/ion-rs)
[![Docs](https://docs.rs/ion-rs/badge.svg)](https://docs.rs/ion-rs)
[![License](https://img.shields.io/hexpm/l/plug.svg)](https://github.com/amazon-ion/ion-rust/blob/main/LICENSE)
[![CI Build](https://github.com/amazon-ion/ion-rust/workflows/CI%20Build/badge.svg)](https://github.com/amazon-ion/ion-rust/actions?query=workflow%3A%22CI+Build%22)
[![codecov](https://codecov.io/gh/amazon-ion/ion-rust/branch/main/graph/badge.svg?token=GB20BDE48S)](https://codecov.io/gh/amazon-ion/ion-rust)

A Rust implementation of the [Amazon Ion][spec] data format.

## Example

For more information, please see our [official documentation](https://docs.rs/ion-rs). 

```rust
use ion_rs::{Element, IonResult, IonType, ion_seq};

fn main() -> IonResult<()> {

    // Read a single value from a string/slice/Vec
    let element = Element::read_one("\"Hello, world!\"")?;
    let text = element.expect_string()?;
    assert_eq!(text, "Hello, world!");

    // Read a series of values from a string/slice/Vec
    let elements = Element::read_all("1 2 3")?;
    let mut sum = 0;
    for element in elements {
        sum += element.expect_i64()?;
    }
    assert_eq!(sum, 6);

    // Iterate over values in a file
    let ion_file = std::fs::File::open("/foo/bar/baz.ion").unwrap();
    for element in Element::iter(ion_file)? {
        println!("{}", element?)
    }
    
    // Construct a sequence of Ion elements from Rust values
    let values = ion_seq!(
        "foo",
        Timestamp::with_ymd(2016, 5, 11).build(),
        3.1416f64,
        true
    );

    // Write values to a buffer in generously-spaced text
    let mut text_buffer: Vec<u8> = Vec::new();
    Element::write_all_as(&values, Format::Text(TextKind::Pretty), &mut text_buffer)?;
    assert_eq!(values, Element::read_all(text_buffer)?);

    // Write values to a buffer in compact binary
    let mut binary_buffer: Vec<u8> = Vec::new();
    Element::write_all_as(&values, Format::Binary, &mut binary_buffer)?;
    assert_eq!(values, Element::read_all(binary_buffer)?);
    
    Ok(())
}
```

## Experimental features

The `ion_rs` library has a number of features that users can opt into. While the following features
are complete and well-tested, their APIs are not stable and are subject to change without notice
between minor versions of the library.

1. `experimental-ion-hash`, an implementation of [Ion Hash][ion-hash-spec].
2. `experimental-reader`, a streaming reader API.
3. `experimental-writer`, a streaming writer API.

Features that are defined in `Cargo.toml` but not listed above have not been thoroughly tested.

## Development

This project uses a submodule to pull in [Ion Tests][ion-tests] and [Ion Hash Tests][ion-hash-tests].
The easiest way to pull everything in is to clone the repository recursively:

```bash
$ git clone --recursive https://github.com/amazon-ion/ion-rust
```

You can also initialize the submodules as follows:

```bash
$ git submodule update --init --recursive
```

Building the project:

```bash
$ cargo build --all-features
```

Running all tests for `ion-rust`:

```bash
$ cargo test --all-features
```

Our continuous integration builds/tests, checks formatting, builds all API docs including private,
and clippy linting, you will likely want to check most of these to avoid having to wait until the
CI finds it:

```bash
$ ./clean-rebuild.sh
```

[spec]: https://amazon-ion.github.io/ion-docs/docs/spec.html
[ion-tests]: https://github.com/amazon-ion/ion-tests
[ion-hash-spec]: https://amazon-ion.github.io/ion-hash/docs/spec.html
[ion-hash-tests]: https://github.com/amazon-ion/ion-hash-tests
