use std::env;
use std::path::PathBuf;

fn main() {
    let ionc_path = cmake::Config::new("ion-c").build();

    println!("cargo:rustc-link-search=native={}/lib", ionc_path.display());
    println!("cargo:rustc-link-lib=static=decNumber_static");
    println!("cargo:rustc-link-lib=static=ionc_static");

    let header_dir = format!("{}/include", ionc_path.display());
    let main_header = format!("{}/ionc/ion.h", header_dir);
    let bindings = bindgen::Builder::default()
        .header(main_header)
        // make sure we can find all the relevant headers
        .clang_arg(format!("-I{}", header_dir))
        // defined in IonC's CMake configuration
        .clang_arg("-DDECNUMDIGITS=34")
        // invalidate the build whenever underlying headers change
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    // emit the bindings
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("ionc.rs"))
        .expect("Couldn't write bindings");
}
