#!/bin/bash

set -e

# update the index
cargo update

# default build
cargo clean
cargo test --workspace

# all features
cargo clean
cargo test --workspace --all-features

# make sure formatting is good
cargo fmt -- --check

# make sure we deal with lints
cargo clippy --workspace --all-features --tests -- -Dwarnings

# general **all** rustdoc
cargo doc --document-private-items --all-features
