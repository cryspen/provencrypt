//! NIST's bit-oriented CAVP vectors, run against the Standard's functions on
//! bit strings directly.
//!
//! `cavp.rs` runs the byte-oriented files through the byte wrappers. The files
//! here are NIST's "BIT oriented" ones. The `ShortMsg` messages have every
//! length from zero to one block (two for the XOFs), most of them not a whole
//! number of bytes; the `LongMsg` ones run to about a hundred blocks, at
//! lengths that are not whole bytes either; and the `VariableOut` files ask
//! for output lengths that are not. Messages and outputs are read with
//! `h2b` and `b2h` of Appendix B.1, which is the convention the files use: the
//! bits of a trailing partial byte are its low-order ones.
//!
//! The Monte Carlo files chain each digest into the next message, a hundred
//! thousand times per file. That takes seconds with `--release` and minutes
//! without, so a debug build checks only the first few checkpoints. Each
//! checkpoint depends on all the ones before it, so those few are a prefix of
//! the full run.
//!
//! The files are not in the repository: NIST publishes them in two archives,
//! about 6 MB together, and the first run downloads both into Cargo's
//! temporary directory with `curl`, checks their SHA-256 against the hashes
//! below, and unpacks them with `unzip`. Without network access the tests here
//! report that and pass, unless `PEDANTIC_SHA3_REQUIRE_VECTORS` is set, in
//! which case they fail.

use pedantic::bits::{b2h, h2b, BitStr};
use pedantic::nat::Nat;
use pedantic_sha3 as pedantic;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// The archives on NIST's SHA-3 validation page,
/// <https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing>,
/// with the SHA-256 of each.
const ARCHIVES: [(&str, &str); 2] = [
    (
        "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bittestvectors.zip",
        "339454bb4b96e299fefcad403797523f1952462a28d2418c108aea30263643ae",
    ),
    (
        "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/shakebittestvectors.zip",
        "69338cb9cfb1e39b91f54f34bbb82a5d3b0403eb5d77213a669fafed87efebb4",
    ),
];

/// The directory the archives are unpacked into, fetching them on first use;
/// `Err` says why they could not be.
fn vectors() -> &'static Result<PathBuf, String> {
    static DIR: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    DIR.get_or_init(|| {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("nist-cavp-bit");
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        for (url, sha256) in ARCHIVES {
            let zip = dir.join(url.rsplit('/').next().unwrap());
            let unpacked = zip.with_extension("unpacked");
            if unpacked.exists() {
                continue;
            }
            let partial = zip.with_extension("partial");
            let status = Command::new("curl")
                .args([
                    "--fail",
                    "--silent",
                    "--show-error",
                    "--location",
                    "--output",
                ])
                .arg(&partial)
                .arg(url)
                .status()
                .map_err(|e| format!("running curl: {e}"))?;
            if !status.success() {
                return Err(format!("curl could not fetch {url}"));
            }
            let bytes = std::fs::read(&partial).map_err(|e| e.to_string())?;
            let got = hex::encode(Sha256::digest(&bytes));
            if got != sha256 {
                return Err(format!("{url} has SHA-256 {got}, expected {sha256}"));
            }
            std::fs::rename(&partial, &zip).map_err(|e| e.to_string())?;
            let status = Command::new("unzip")
                .args(["-o", "-q"])
                .arg(&zip)
                .arg("-d")
                .arg(&dir)
                .status()
                .map_err(|e| format!("running unzip: {e}"))?;
            if !status.success() {
                return Err(format!("unzip could not unpack {}", zip.display()));
            }
            std::fs::write(&unpacked, b"").map_err(|e| e.to_string())?;
        }
        Ok(dir)
    })
}

/// The response file `name`, or `None` (after saying why) when the archives
/// are unavailable and `PEDANTIC_SHA3_REQUIRE_VECTORS` is not set.
fn load(name: &str) -> Option<Rsp> {
    match vectors() {
        Ok(dir) => {
            let text = std::fs::read_to_string(dir.join(name))
                .unwrap_or_else(|e| panic!("reading {name}: {e}"));
            Some(Rsp::parse(&text))
        }
        Err(why) if std::env::var_os("PEDANTIC_SHA3_REQUIRE_VECTORS").is_some() => {
            panic!("NIST's bit-oriented vectors are unavailable: {why}")
        }
        Err(why) => {
            eprintln!("skipping {name}: NIST's bit-oriented vectors are unavailable: {why}");
            None
        }
    }
}

/// How many of a Monte Carlo file's hundred checkpoints to check.
const MONTE_CHECKPOINTS: usize = if cfg!(debug_assertions) { 3 } else { 100 };

/// A response file: the bracketed header values, and one record per
/// blank-line-separated group of `key = value` lines.
struct Rsp {
    header: Vec<(String, String)>,
    records: Vec<Vec<(String, String)>>,
}

impl Rsp {
    fn parse(text: &str) -> Rsp {
        let mut rsp = Rsp {
            header: Vec::new(),
            records: Vec::new(),
        };
        let mut record = Vec::new();
        for line in text.lines().map(str::trim) {
            if line.starts_with('#') {
                continue;
            }
            if let Some(inner) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
                if let Some((k, v)) = inner.split_once('=') {
                    rsp.header
                        .push((k.trim().to_string(), v.trim().to_string()));
                }
            } else if let Some((k, v)) = line.split_once('=') {
                record.push((k.trim().to_string(), v.trim().to_string()));
            } else if line.is_empty() && !record.is_empty() {
                rsp.records.push(std::mem::take(&mut record));
            }
        }
        if !record.is_empty() {
            rsp.records.push(record);
        }
        rsp
    }

    fn header(&self, key: &str) -> &str {
        lookup(&self.header, key)
    }
}

fn lookup<'a>(fields: &'a [(String, String)], key: &str) -> &'a str {
    fields
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
        .unwrap_or_else(|| panic!("no `{key}` in {fields:?}"))
}

fn num(s: &str) -> u128 {
    s.parse().unwrap()
}

/// `h2b(H, n)`: the first `n` bits of the bytes `H`.
fn message(hex: &str, len: u128) -> BitStr {
    h2b(&hex::decode(hex).unwrap(), Nat::new(len))
}

// ---------------------------------------------------------------------------
// Short messages, of every bit length up to one block (two for the XOFs),
// and long ones, of a hundred lengths up to about a hundred blocks
// ---------------------------------------------------------------------------

macro_rules! sha3_msg {
    ($name:ident, $file:literal, $hash:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            let Some(rsp) = load($file) else { return };
            assert!(!rsp.records.is_empty(), "empty test vector file");
            for r in &rsp.records {
                let len = num(lookup(r, "Len"));
                let digest = b2h(&$hash(&message(lookup(r, "Msg"), len)));
                assert_eq!(hex::encode(digest), lookup(r, "MD"), "Len = {len}");
            }
        }
    };
}

sha3_msg!(SHA3_224ShortMsg, "SHA3_224ShortMsg.rsp", pedantic::sha3_224);
sha3_msg!(SHA3_224LongMsg, "SHA3_224LongMsg.rsp", pedantic::sha3_224);
sha3_msg!(SHA3_256ShortMsg, "SHA3_256ShortMsg.rsp", pedantic::sha3_256);
sha3_msg!(SHA3_256LongMsg, "SHA3_256LongMsg.rsp", pedantic::sha3_256);
sha3_msg!(SHA3_384ShortMsg, "SHA3_384ShortMsg.rsp", pedantic::sha3_384);
sha3_msg!(SHA3_384LongMsg, "SHA3_384LongMsg.rsp", pedantic::sha3_384);
sha3_msg!(SHA3_512ShortMsg, "SHA3_512ShortMsg.rsp", pedantic::sha3_512);
sha3_msg!(SHA3_512LongMsg, "SHA3_512LongMsg.rsp", pedantic::sha3_512);

macro_rules! shake_msg {
    ($name:ident, $file:literal, $xof:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            let Some(rsp) = load($file) else { return };
            assert!(!rsp.records.is_empty(), "empty test vector file");
            let d = Nat::new(num(rsp.header("Outputlen")));
            for r in &rsp.records {
                let len = num(lookup(r, "Len"));
                let output = b2h(&$xof(&message(lookup(r, "Msg"), len), d));
                assert_eq!(hex::encode(output), lookup(r, "Output"), "Len = {len}");
            }
        }
    };
}

shake_msg!(SHAKE128ShortMsg, "SHAKE128ShortMsg.rsp", pedantic::shake128);
shake_msg!(SHAKE128LongMsg, "SHAKE128LongMsg.rsp", pedantic::shake128);
shake_msg!(SHAKE256ShortMsg, "SHAKE256ShortMsg.rsp", pedantic::shake256);
shake_msg!(SHAKE256LongMsg, "SHAKE256LongMsg.rsp", pedantic::shake256);

// ---------------------------------------------------------------------------
// Variable output: output lengths `d` that are not a whole number of bytes
// ---------------------------------------------------------------------------

macro_rules! shake_variable_out {
    ($name:ident, $file:literal, $xof:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            let Some(rsp) = load($file) else { return };
            assert!(!rsp.records.is_empty(), "empty test vector file");
            let len = num(rsp.header("Input Length"));
            for r in &rsp.records {
                let d = num(lookup(r, "Outputlen"));
                let output = b2h(&$xof(&message(lookup(r, "Msg"), len), Nat::new(d)));
                assert_eq!(
                    hex::encode(output),
                    lookup(r, "Output"),
                    "COUNT = {}, Outputlen = {d}",
                    lookup(r, "COUNT")
                );
            }
        }
    };
}

shake_variable_out!(
    SHAKE128VariableOut,
    "SHAKE128VariableOut.rsp",
    pedantic::shake128
);
shake_variable_out!(
    SHAKE256VariableOut,
    "SHAKE256VariableOut.rsp",
    pedantic::shake256
);

// ---------------------------------------------------------------------------
// Monte Carlo
// ---------------------------------------------------------------------------

/// The hash functions' Monte Carlo test of the SHA3VS: starting from the
/// seed, each message is the previous digest, and every thousandth digest is
/// a checkpoint.
macro_rules! sha3_monte {
    ($name:ident, $file:literal, $hash:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            let Some(rsp) = load($file) else { return };
            let mut md = hex::decode(lookup(&rsp.records[0], "Seed")).unwrap();
            let checkpoints = &rsp.records[1..];
            assert_eq!(checkpoints.len(), 100);
            for r in &checkpoints[..MONTE_CHECKPOINTS] {
                for _ in 0..1000 {
                    md = $hash(&md).to_vec();
                }
                assert_eq!(
                    hex::encode(&md),
                    lookup(r, "MD"),
                    "COUNT = {}",
                    lookup(r, "COUNT")
                );
            }
        }
    };
}

sha3_monte!(
    SHA3_224Monte,
    "SHA3_224Monte.rsp",
    pedantic::bytes::sha3_224
);
sha3_monte!(
    SHA3_256Monte,
    "SHA3_256Monte.rsp",
    pedantic::bytes::sha3_256
);
sha3_monte!(
    SHA3_384Monte,
    "SHA3_384Monte.rsp",
    pedantic::bytes::sha3_384
);
sha3_monte!(
    SHA3_512Monte,
    "SHA3_512Monte.rsp",
    pedantic::bytes::sha3_512
);

/// The XOFs' Monte Carlo test of the SHA3VS: each message is the first
/// 128 bits of the previous output, zero-padded if that output is shorter,
/// and each output length is drawn from the last 16 bits of the previous
/// output, within the file's bounds.
macro_rules! shake_monte {
    ($name:ident, $file:literal, $xof:path) => {
        #[test]
        #[allow(non_snake_case)]
        fn $name() {
            let Some(rsp) = load($file) else { return };
            let min = num(rsp.header("Minimum Output Length (bits)")) as usize / 8;
            let max = num(rsp.header("Maximum Output Length (bits)")) as usize / 8;
            let range = max - min + 1;
            let mut output = hex::decode(lookup(&rsp.records[0], "Msg")).unwrap();
            let mut out_bytes = max;
            let checkpoints = &rsp.records[1..];
            assert_eq!(checkpoints.len(), 100);
            for r in &checkpoints[..MONTE_CHECKPOINTS] {
                for _ in 0..1000 {
                    let mut msg = [0u8; 16];
                    let n = output.len().min(16);
                    msg[..n].copy_from_slice(&output[..n]);
                    output = $xof(&msg, out_bytes);
                    let last = output.len();
                    let rightmost =
                        usize::from(output[last - 2]) << 8 | usize::from(output[last - 1]);
                    out_bytes = min + rightmost % range;
                }
                assert_eq!(
                    (8 * output.len()).to_string(),
                    lookup(r, "Outputlen"),
                    "COUNT = {}",
                    lookup(r, "COUNT")
                );
                assert_eq!(
                    hex::encode(&output),
                    lookup(r, "Output"),
                    "COUNT = {}",
                    lookup(r, "COUNT")
                );
            }
        }
    };
}

shake_monte!(
    SHAKE128Monte,
    "SHAKE128Monte.rsp",
    pedantic::bytes::shake128
);
shake_monte!(
    SHAKE256Monte,
    "SHAKE256Monte.rsp",
    pedantic::bytes::shake256
);
