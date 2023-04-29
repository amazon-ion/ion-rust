# Amazon Ion Rust

[![Crate](https://img.shields.io/crates/v/ion-rs.svg)](https://crates.io/crates/ion-rs)
[![Docs](https://docs.rs/ion-rs/badge.svg)](https://docs.rs/ion-rs)
[![License](https://img.shields.io/hexpm/l/plug.svg)](https://github.com/amazon-ion/ion-rust/blob/main/LICENSE)
[![CI Build](https://github.com/amazon-ion/ion-rust/workflows/CI%20Build/badge.svg)](https://github.com/amazon-ion/ion-rust/actions?query=workflow%3A%22CI+Build%22)
[![codecov](https://codecov.io/gh/amazon-ion/ion-rust/branch/main/graph/badge.svg?token=GB20BDE48S)](https://codecov.io/gh/amazon-ion/ion-rust)

A Rust implementation of the [Amazon Ion][spec] data format.

Includes the feature `ion-hash` which is an implementation of [Ion Hash][ion-hash-spec].

***This package is considered experimental, under active/early development, and the API is subject to change.***

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
$ cargo build --workspace --all-features
```

Running all tests for `ion-rust`:

```bash
$ cargo test --workspace --all-features
```

Our continuous integration builds/tests, checks formatting, builds all API docs including private,
and clippy linting, you will likely want to check most of these to avoid having to wait until the
CI finds it:

```bash
$ ./clean-rebuild.sh
```

[spec]: https://amazon-ion.github.io/ion-docs/docs/spec.html
[ion-tests]: https://github.com/amazon-ion/ion-tests
[bindgen-req]: https://rust-lang.github.io/rust-bindgen/requirements.html
[ion-hash-spec]: https://amazon-ion.github.io/ion-hash/docs/spec.html
[ion-hash-tests]: https://github.com/amazon-ion/ion-hash-tests
