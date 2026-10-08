-- External function definitions for `libcrux-iot-sha3` (hand-written).
-- CoreModels supplies every model the extraction references, so what is left
-- here is the `libcrux_secrets` helpers, which no spec provides.
--
-- This file is also where the spec package enters the generated extraction's import
-- tree: hax emits `Extraction/FunsExternal.lean` as a one-line shim onto this file
-- and never adds spec imports of its own, so the `#[ensures]` clauses'
-- `pedantic_sha3::bytes::*` are in scope in `Extraction/Specs.lean` only
-- because they are imported here.
import Aeneas
import CoreModels
import PedanticSha3
import LibcruxIotSha3.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open libcrux_iot_sha3

noncomputable section

/-! `libcrux_secrets` helpers used by `libcrux-iot-sha3`. -/

namespace libcrux_secrets

def U32.Insts.Libcrux_secretsIntCastOps.as_u64 (x : U32) : RustM U64 :=
  ok (UScalar.cast .U64 x)

def U64.Insts.Libcrux_secretsIntCastOps.as_u32 (x : U64) : RustM U32 :=
  ok (UScalar.cast .U32 x)

@[reducible] def traits.Scalar (_Self : Type) : Type := PUnit
@[reducible] def U8.Insts.Libcrux_secretsTraitsScalar : traits.Scalar Std.U8 :=
  PUnit.unit
@[reducible] def U32.Insts.Libcrux_secretsTraitsScalar : traits.Scalar Std.U32 :=
  PUnit.unit

/-! `classify` and `declassify` on public integers (`U8 = u8`, `U32 = u32`): the
    blanket impl for a scalar and the impl for an array of scalars. All are no-op
    identities. -/

def traits.Classify.Blanket.classify {T : Type} (_inst : traits.Scalar T) (a : T) :
    Aeneas.Std.RustM T := ok a

def Array.Insts.Libcrux_secretsTraitsClassifyArray.classify {T : Type} {N : Aeneas.Std.Usize}
    (_inst : traits.Scalar T) (a : Aeneas.Std.Array T N) :
    Aeneas.Std.RustM (Aeneas.Std.Array T N) := ok a

def Array.Insts.Libcrux_secretsTraitsDeclassifyArray.declassify {T : Type}
    {N : Aeneas.Std.Usize} (_inst : traits.Scalar T) (a : Aeneas.Std.Array T N) :
    Aeneas.Std.RustM (Aeneas.Std.Array T N) := ok a

/-! `declassify_ref` on a shared SLICE, needed because the contracts name the
    specification (which takes `&[u8]`, not `&[U8]`). No-op identity, mirroring
    ml-dsa's `SharedAT` variant. -/

def SharedASlice.Insts.Libcrux_secretsTraitsDeclassifyRefSharedASlice.declassify_ref
    {T : Type} (_inst : traits.Scalar T) (a : Aeneas.Std.Slice T) :
    Aeneas.Std.RustM (Aeneas.Std.Slice T) := ok a

end libcrux_secrets
end


/-! `Debug` for `UnknownAlgorithm`, the error `Algorithm::try_from` returns. The
    derived impl is opaque to the extraction, and no proof formats anything, so it
    is modelled as writing nothing and succeeding. -/

noncomputable section

def libcrux_iot_sha3.UnknownAlgorithm.Insts.CoreFmtDebug.fmt
    (_self : libcrux_iot_sha3.UnknownAlgorithm) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

end
