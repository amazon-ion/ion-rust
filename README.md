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

Building the project:

```bash
$ cargo build
```

Running tests for `ion-rust` and `ionc-sys`:

```bash
$ (cd ionc-sys && cargo test) && cargo test
```

[ion-c]: https://github.com/amzn/ion-c
[ion-tests]: https://github.com/amzn/ion-tests
