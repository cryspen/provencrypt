/-
  Per-round functional equivalence (impl-side `keccakf1600_round{N}_*`
  composed against the spec-side round `prc_spec ∘ theta_applied`,
  i.e. `ι ∘ χ ∘ π ∘ ρ ∘ θ` written out cell by cell).

  This file composes `theta_lift_spec` and `prc_lift_spec` (round 0)
  into a single Triple establishing the full per-round equivalence.

  ## Proof shape

  `round{0,1,2,3}_equiv_spec` each build at 16M heartbeats. The four
  proofs follow the same shape (one `hax_mvcgen`, side-goal `scalar_tac`
  chain, `unfold round{k}_post` + `casesm` + `simp_all`).

  ### Key discipline (don't break)
  Each `round{k}_post` is declared `@[irreducible]`, so that `hax_mvcgen`
  advances only the implementation and leaves the post alone; we unfold
  it afterwards, with the chain hypotheses already in scope. The post is
  an equation between pure states (`prc_spec ∘ theta_applied` against the
  lifted implementation result), so once it is unfolded there is nothing
  left to advance and `simp_all` closes it.

  ## Architecture

  - `keccakf1600_round{k}_pi_rho_chi_chain` + `@[spec]` wrappers
    package `pi_rho_chi_1 ; pi_rho_chi_2` so the @[spec] matcher
    fires on a single named function in chain context.
  - `round{k}_post` (each `@[irreducible]`) names the spec-side
    `prc_spec (theta_applied …) s.i = lift_perm …` equation so that
    `hax_mvcgen` leaves it alone during impl
    advancement.

  ## Round dependencies

  Each `round{k}_equiv_spec` discharges via the underlying
  `theta_lift_spec_k` and `prc_lift_spec_k` lemmas (see
  `ThetaLiftRound{1,2,3}.lean`, `PrcLiftRound{1,2,3}.lean`). All four
  round specs are consumed by the 24-round composition in
  `Permutation/Keccakf1600.lean`.
-/
import LibcruxIotSha3.Permutation.ThetaLift
import LibcruxIotSha3.Permutation.ThetaLiftRound1
import LibcruxIotSha3.Permutation.ThetaLiftRound2
import LibcruxIotSha3.Permutation.ThetaLiftRound3
import LibcruxIotSha3.Permutation.PrcLift
import LibcruxIotSha3.Permutation.PrcLiftRound1
import LibcruxIotSha3.Permutation.PrcLiftRound2
import LibcruxIotSha3.Permutation.PrcLiftRound3
import LibcruxIotSha3.Permutation.Lift
import Hax

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3

namespace libcrux_iot_sha3.Permutation

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

/-! ## Chain wrapper for round-0 πρχι

`prc_lift_spec` is keyed on a 2-call do-block `(do prc_1; prc_2)`,
which mvcgen's `@[spec]` matcher does not auto-fire in chain context.
Wrapping the two calls in a named function lets the `@[spec]` matcher
fire on the chain inside `round0_equiv_spec`. -/

def keccakf1600_round0_pi_rho_chi_chain (s : state.KeccakState) :
    RustM state.KeccakState := do
  let r1 ← keccak.keccakf1600_round0_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round0_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round0_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round0_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      prc_spec (lift_theta_applied s) s.i
        = lift_perm r_impl impl_perm impl_swap ⌝ ⦄ := by
  unfold keccakf1600_round0_pi_rho_chi_chain
  exact prc_lift_spec s hi

/-- Spec-chain claim for round 0 (opaque to `mvcgen`). Naming the
    equation in this `def` keeps `mvcgen` from working on the post while
    it advances the implementation. -/
@[irreducible]
def round0_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  prc_spec (theta_applied (lift s)) s.i = lift_perm r_impl impl_perm impl_swap

set_option maxHeartbeats 16000000 in
theorem round0_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round0_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round0_post
       -- The chain hypotheses are already in scope from mvcgen's dispatch
       -- of `chain_spec`; the post is now an equation between pure states,
       -- so there is nothing left to advance.
       casesm* _ ∧ _
       simp_all)

/-! ## Chain wrappers + round equivs for rounds 1, 2, 3

Each round's chain wrapper packages `pi_rho_chi_1; pi_rho_chi_2` so the
`@[spec]` matcher can fire on a single named function. The post chains
the round-k spec via `theta_lift_spec_k` (auto-firing on the theta call)
+ `prc_lift_spec_k` (auto-firing via the chain wrapper).
-/

def keccakf1600_round1_pi_rho_chi_chain (s : state.KeccakState) :
    RustM state.KeccakState := do
  let r1 ← keccak.keccakf1600_round1_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round1_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round1_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round1_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      prc_spec (lift_theta_applied_perm s impl_perm (impl_swap_k 1)) s.i
        = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2) ⌝ ⦄ := by
  unfold keccakf1600_round1_pi_rho_chi_chain
  exact prc_lift_spec_1 s hi

def keccakf1600_round2_pi_rho_chi_chain (s : state.KeccakState) :
    RustM state.KeccakState := do
  let r1 ← keccak.keccakf1600_round2_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round2_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round2_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round2_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      prc_spec (lift_theta_applied_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) s.i
        = lift_perm r_impl (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⌝ ⦄ := by
  unfold keccakf1600_round2_pi_rho_chi_chain
  exact prc_lift_spec_2 s hi

def keccakf1600_round3_pi_rho_chi_chain (s : state.KeccakState) :
    RustM state.KeccakState := do
  let r1 ← keccak.keccakf1600_round3_pi_rho_chi_1 0#usize s
  keccak.keccakf1600_round3_pi_rho_chi_2 r1

@[spec]
theorem keccakf1600_round3_pi_rho_chi_chain_spec
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccakf1600_round3_pi_rho_chi_chain s
    ⦃ ⇓ r_impl => ⌜
      -- Round 3 output uses canonical `lift` (= `lift_perm _ id swZero`,
      -- via `impl_perm^[4] = id` and `impl_swap_k 4 = swZero`).
      prc_spec (lift_theta_applied_perm s
          (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) s.i
        = Permutation.lift r_impl ⌝ ⦄ := by
  unfold keccakf1600_round3_pi_rho_chi_chain
  exact prc_lift_spec_3 s hi

/-- Spec-chain claim for round 1 (input s is the round-0 impl output, so
    the spec lift uses `impl_perm` permutation + `impl_swap_k 1`, where
    `impl_swap_k 1 = impl_swap`). Output uses `impl_swap_k 2`. -/
@[irreducible]
def round1_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  prc_spec (theta_applied (lift_perm s impl_perm (impl_swap_k 1))) s.i
    = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2)

set_option maxHeartbeats 16000000 in
theorem round1_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round1_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round1_post
       casesm* _ ∧ _
       simp_all)

@[irreducible]
def round2_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  prc_spec (theta_applied (lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2))) s.i
    = lift_perm r_impl (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)

set_option maxHeartbeats 16000000 in
theorem round2_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round2_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round2_post
       casesm* _ ∧ _
       simp_all)

@[irreducible]
def round3_post (s : state.KeccakState) (r_impl : state.KeccakState) : Prop :=
  -- Output uses `impl_swap_k 4 = (fun _ => false)`, i.e. the canonical
  -- `lift` (after `impl_perm^[4] = id`). Equivalent to `lift r_impl`.
  prc_spec (theta_applied
      (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))) s.i
    = Permutation.lift r_impl

set_option maxHeartbeats 16000000 in
theorem round3_equiv_spec (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃ ⇓ r_impl => ⌜round3_post s r_impl⌝ ⦄ := by
  hax_mvcgen
  all_goals first
    | scalar_tac
    | (casesm* _ ∧ _; scalar_tac)
    | (unfold round3_post
       casesm* _ ∧ _
       simp_all)

end libcrux_iot_sha3.Permutation
