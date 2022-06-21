# Ion Rust FFI

This module provides the ion-rust implementation via C language bindings. The intention is that will
form the basis of a rust ion common language runtime, providing a performant core ion implementation
for Ruby, Python, PHP, etc.

In it's current state it is very much just a POC.

## Isn't it sort of whacky to have ion-rust depend on ion-c and then expose a C API?

At face value, yes. But work is underway to remove the dependency on ion-c and have a standalone ion-rust.
This POC is based on the assumption that we are more likely to build a performant and correct ion impl in
rust than in C, especially as we look to implement Ion 1.1. That may or may not prove true, but it is the
crucial assumption behind this POC.

## Header Generation

Header Generation is not _yet_ built-in to the standard build process.

A .h file can be generated with the following:
```sh
cbindgen --config cbindgen.toml --crate ion-rs-ffi --output ion_rs_ffi.h --lang c
```

You may need to install bindgen first:
```sh
cargo install --force cbindgen
```
