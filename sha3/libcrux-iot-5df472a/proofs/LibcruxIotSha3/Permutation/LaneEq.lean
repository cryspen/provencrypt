import LibcruxIotSha3.Permutation.PrcLift
import LibcruxIotSha3.Model.LaneModel
/-!
# `Permutation/`'s pure step semantics are the lane model

`Permutation/` names the five step mappings `theta_applied`, `rho_applied`,
`pi_applied`, `chi_applied` and `iota_applied`: twenty-five cells written out
one by one, which is the shape the implementation-side `mvcgen` proofs need to
see.  `LibcruxIotSha3/LaneModel.lean` names the same five as indexed functions,
which is the shape the FIPS-202 bit-level proofs need.

They are the same functions, and this file says so.  That is what joins the two
halves of the proof.
-/

open Aeneas Aeneas.Std
open LibcruxIotSha3.LaneModel

namespace libcrux_iot_sha3.Permutation

theorem theta_applied_eq (s : Lanes) : theta_applied s = thetaLanes s := by
  apply Subtype.ext
  unfold theta_applied thetaLanes mkArr cLane dLane
  rfl

theorem rho_applied_eq (s : Lanes) : rho_applied s = rhoLanes s := by
  apply Subtype.ext
  unfold rho_applied rhoLanes mkArr rot64 libcrux_iot_sha3.rhoOffsets
  rfl

theorem pi_applied_eq (s : Lanes) : pi_applied s = piLanes s := by
  apply Subtype.ext
  unfold pi_applied piLanes mkArr
  rfl

theorem chi_applied_eq (s : Lanes) : chi_applied s = chiLanes s := by
  apply Subtype.ext
  unfold chi_applied chiLanes mkArr
  rfl

theorem iota_applied_eq (s : Lanes) (r : Std.Usize) :
    iota_applied s r = iotaLanes s r.val := by
  unfold iota_applied iotaLanes
  rfl

/-- One round: `Permutation/`'s `prc_spec ∘ theta_applied` is `roundLanes`. -/
theorem prc_spec_theta_eq (s : Lanes) (r : Std.Usize) :
    prc_spec (theta_applied s) r = roundLanes s r.val := by
  rw [← prc_spec_eq_composed, theta_applied_eq, rho_applied_eq, pi_applied_eq,
    chi_applied_eq, iota_applied_eq]
  rfl

end libcrux_iot_sha3.Permutation
