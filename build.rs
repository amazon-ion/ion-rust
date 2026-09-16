fn main() {
    // `Struct`'s linear-scan/hash-index threshold can be overridden at build time via this
    // environment variable (read with `option_env!` in `src/types/struct.rs`). Declaring it here
    // makes Cargo's fingerprint depend on it, so changing the value triggers a rebuild — without
    // this, `option_env!` alone is not tracked and a stale binary can be reused.
    println!("cargo:rerun-if-env-changed=ION_RS_STRUCT_LINEAR_SCAN_THRESHOLD");
}
