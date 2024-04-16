# Fail on error
$ErrorActionPreference = "Stop"

# Update the index
cargo update

# Default build
cargo clean
cargo test --workspace

# All features
cargo clean
cargo test --workspace --all-features

# Make sure formatting is good
cargo fmt -- --check

# Make sure we deal with lints
cargo clippy --workspace --all-features --tests -- -Dwarnings

# Generate **all** rustdoc
cargo doc --document-private-items --all-features