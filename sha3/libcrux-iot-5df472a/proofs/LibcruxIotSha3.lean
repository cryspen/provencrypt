-- Library root: the lakefile globs only this module, so its import tree is
-- what `lake build` compiles. `Verification.ProofObligations` discharges the
-- Rust contracts and imports every proof module on the way; the generated
-- `Extraction.ProofObligations` (sorries) is deliberately NOT imported, so it
-- stays on disk but out of the build.
import LibcruxIotSha3.Verification.ProofObligations
