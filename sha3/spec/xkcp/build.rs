fn main() {
    println!("cargo:rerun-if-changed=c");
    println!("cargo:rerun-if-changed=config");

    // `KECCAK-p[1600]`, the sponge on top of it, and the FIPS 202 interfaces,
    // from the current XKCP.
    let x = "c/4affab4/lib";
    cc::Build::new()
        .file(format!(
            "{x}/low/KeccakP-1600/ref-64bits/KeccakP-1600-reference.c"
        ))
        .file(format!("{x}/high/Keccak/KeccakSponge.c"))
        .file(format!("{x}/high/Keccak/FIPS202/KeccakHash.c"))
        .file(format!("{x}/high/Keccak/FIPS202/SimpleFIPS202.c"))
        .include("config/4affab4")
        .include(format!("{x}/common"))
        .include(format!("{x}/low/KeccakP-1600/ref-64bits"))
        .include(format!("{x}/high/Keccak"))
        .include(format!("{x}/high/Keccak/FIPS202"))
        .warnings(true)
        .compile("xkcp_4affab4");

    // `KECCAK-p[200]`, `[400]` and `[800]` and the sponges on top of them,
    // from the last XKCP commit that has them.
    let x = "c/fa7033a/lib";
    let mut build = cc::Build::new();
    for w in [200, 400, 800] {
        build
            .file(format!("{x}/low/KeccakP-{w}/ref/KeccakP-{w}-reference.c"))
            .include(format!("{x}/low/KeccakP-{w}/ref"));
    }
    build
        .file(format!("{x}/high/Keccak/KeccakSponge.c"))
        .include("config/fa7033a")
        .include(format!("{x}/common"))
        .include(format!("{x}/high/Keccak"))
        .warnings(true)
        .compile("xkcp_fa7033a");
}
