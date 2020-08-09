# `ion-c-sys`

[![build](https://github.com/amzn/ion-rust/workflows/Build/badge.svg)](https://github.com/amzn/ion-rust/actions)

A Rust binding to [Ion C][ion-c] which implements the [Amazon Ion][spec] data format.

***This package is considered experimental, under active/early development, and the API is subject to change.***

## Development

See [Ion Rust][ion-rust] for details.  This crate is currently developed in concert with Ion Rust
as a [Cargo workspace][cargo-workspace].

Notably, building this crate requires [pre-requisites for `bindgen`][bindgen-req], a modern C/C++ compiler,
and [`cmake`][cmake].

[ion-rust]: https://github.com/amzn/ion-rust
[spec]: https://amzn.github.io/ion-docs/docs/spec.html
[ion-c]: https://github.com/amzn/ion-c
[bindgen-req]: https://rust-lang.github.io/rust-bindgen/requirements.html
[cargo-workspace]: https://doc.rust-lang.org/cargo/reference/workspaces.html
[cmake]: https://cmake.org/
