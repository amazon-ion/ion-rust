// Copyright Amazon.com, Inc. or its affiliates.

use std::env;
use std::path::PathBuf;

/// Makes it easier to construct PathBufs instead of format!() which doesn't
/// produce portable path separators.
macro_rules! mkpath {
    ( $($x:expr),* ) => {
        {
            let mut buf = PathBuf::new();
            $(
                buf.push($x);
            )*
            buf
        }
    };
}

fn main() {
    let ionc_path = cmake::Config::new("ion-c").build();
    let ionc_lib_path = mkpath!(&ionc_path, "lib");

    println!("cargo:rustc-link-search=native={}", ionc_lib_path.display());
    println!("cargo:rustc-link-lib=static=decNumber_static");
    println!("cargo:rustc-link-lib=static=ionc_static");

    let ionc_inc_path = mkpath!(&ionc_path, "include");
    let ionc_main_header_path = mkpath!(&ionc_inc_path, "ionc", "ion.h");

    let bindings = bindgen::Builder::default()
        .header(ionc_main_header_path.to_str().unwrap())
        // make sure we can find all the relevant headers
        .clang_arg(format!("-I{}", ionc_inc_path.display()))
        // defined in IonC's CMake configuration
        .clang_arg("-DDECNUMDIGITS=34")
        // invalidate the build whenever underlying headers change
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .derive_default(true)
        .generate()
        .expect("Unable to generate bindings");

    // emit the bindings
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("ionc_bindings.rs"))
        .expect("Couldn't write bindings");
}
