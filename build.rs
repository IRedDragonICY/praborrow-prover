fn main() {
    // Only attempt to link if the z3-backend feature is potentially active or generally desired.
    // However, since z3-sys usually handles vendoring or linking, this top-level build.rs
    // acts as a helper to ensure system libraries are found if not vendored.

    // Check if the "z3-backend" feature is enabled (cargo exposes this as CARGO_FEATURE_Z3_BACKEND)
    // Actually, checking pkg-config unconditionally is fine, if it fails we just warn specific to z3.

    if let Err(e) = pkg_config::probe_library("z3") {
        println!("cargo:warning=Z3 library not found via pkg-config: {}", e);
        println!(
            "cargo:warning=Ensure Z3 is installed and PKG_CONFIG_PATH is set if you intend to use the z3-backend."
        );
    } else {
        println!("cargo:rustc-link-lib=z3");
    }

    println!("cargo:rerun-if-changed=build.rs");
}
