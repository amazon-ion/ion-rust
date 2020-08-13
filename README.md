# Amazon Ion Rust

[![Crate](https://img.shields.io/crates/v/ion-rs.svg)](https://crates.io/crates/ion-rs)
[![Docs](https://docs.rs/ion-rs/badge.svg)](https://docs.rs/ion-rs)
[![License](https://img.shields.io/crates/l/ion-rs)](https://crates.io/crates/ion-rs)
[![CI Build](https://github.com/amzn/ion-rust/workflows/CI%20Build/badge.svg)](https://github.com/amzn/ion-rust/actions?query=workflow%3A%22CI+Build%22)


A Rust implementation of the [Amazon Ion][spec] data format.

***This package is considered experimental, under active/early development, and the API is subject to change.***

## Development

This project uses a submodule to pull in [Ion C][ion-c] and [Ion Tests][ion-tests].  The easiest way to pull
everything in is to clone the repository recursively:

```bash
$ git clone --recursive https://github.com/amzn/ion-rust
```

You can also initialize the submodules as follows:

```bash
$ git submodule update --init --recursive
```

Furthermore, you will need the [pre-requisties for `bindgen`][bindgen-req] installed which is basically
`libclang`.

Building the project:

```bash
$ cargo build --workspace --all-targets
```

Running all tests for `ion-rust` and `ion-c-sys`:

```bash
$ cargo test --workspace
```

[spec]: https://amzn.github.io/ion-docs/docs/spec.html
[ion-c]: https://github.com/amzn/ion-c
[ion-tests]: https://github.com/amzn/ion-tests
[bindgen-req]: https://rust-lang.github.io/rust-bindgen/requirements.html
