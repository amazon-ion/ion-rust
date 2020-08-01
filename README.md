# Amazon Ion Rust

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

[ion-c]: https://github.com/amzn/ion-c
[ion-tests]: https://github.com/amzn/ion-tests
[bindgen-req]: https://rust-lang.github.io/rust-bindgen/requirements.html
