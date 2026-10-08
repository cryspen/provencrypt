fn main() {
    println!("cargo:rerun-if-changed=c");
    cc::Build::new()
        .file("c/fips202.c")
        .include("c")
        .warnings(true)
        .compile("pqcrystals_fips202_ref");
}
