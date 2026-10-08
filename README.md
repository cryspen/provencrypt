# provencrypt

A collection of specifications of cryptographic algorithms, written in Rust for
consumption via [hax](https://hax.cryspen.com/). Each specification follows its standard closely, so that
it can be read side by side with the document it transcribes, and it extracts
through hax so that it can serve as the specification in formal proofs.

Next to the specifications, the repository holds examples of realistic
implementations, together with proofs that they are equivalent to a
specification.

## Contents

| Specification | Example implementation |
|---|---|
| SHA-3 and SHAKE, as specified by FIPS 202: [`sha3/spec`](sha3/spec/README.md) | `libcrux-iot-sha3`, the implementation for embedded targets from [libcrux-iot](https://github.com/celabshq/libcrux-iot) at commit `5df472a`, with the patches hax extraction needs, proved equivalent in Lean: [`sha3/libcrux-iot-5df472a`](sha3/libcrux-iot-5df472a/README.md) |
