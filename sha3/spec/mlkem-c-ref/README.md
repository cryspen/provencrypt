# `pedantic-sha3` against the ML-KEM C reference implementation

Tests of the FIPS 202 transcript in [`sha3/spec`](../README.md) against
`ref/fips202.c` of the ML-KEM C reference implementation,
<https://github.com/pq-crystals/kyber>. That file is the SHA-3 code the
reference's `G`, `H`, `J`, `PRF` and `XOF` are built from.

```
cargo test -p sha3-mlkem-c-ref-tests --release
```

`c/` holds `fips202.c` and `fips202.h` verbatim from commit
`3edd5af5991927164edd4aacebfcbee00b8064e7` of that repository, together with its
`LICENSE` (CC0 or Apache 2.0). `build.rs` compiles them with the `cc` crate, and
`src/lib.rs` binds every function `fips202.h` declares. This is a crate of its
own, rather than tests inside `sha3/spec`, so that the specification itself
does not need a C compiler.

`tests/c_ref.rs` compares, for `SHA3-256`, `SHA3-512`, `SHAKE128` and
`SHAKE256`:

* the one-shot functions at input lengths `0`, `1` and `k·rate - 1`, `k·rate`,
  `k·rate + 1` for `k = 1, 2`, and for the XOFs at the same output lengths;
* the incremental `absorb`/`finalize`/`squeeze` API, with the input and the
  output each split in two at every one of those lengths;
* `absorb_once` followed by `squeezeblocks`, one block at a time and several
  at once, followed by a `squeeze`;
* the inputs ML-KEM hands each function (FIPS 203, Sec. 4.1), for all three
  parameter sets: `G` on `d || k` and `m || H(ek)`, `H` on the encapsulation
  key, `J` on `z || c`, `PRF_η` for both `η`, and `XOF(ρ, i, j)` squeezed in
  blocks the way `ref/indcpa.c` samples the matrix;
* random messages of random length, and random output lengths, via `proptest`.
