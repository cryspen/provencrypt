import LibcruxIotSha3.Permutation.RoundEquiv
import LibcruxIotSha3.Support.Triple
import LibcruxIotSha3.Permutation.LaneEq
/-!
# The implementation computes the lane model's `Keccak-f[1600]`

`Permutation/RoundEquiv.lean` relates each of the implementation's four round
bodies to one round of the lane model, through the bit-interleaved `lift_perm`
views that track the implementation's storage relabelling.  This file chains
them: four rounds bring the relabelling back to the canonical `lift`
(`impl_perm⁴ = id`, `impl_swap_k 4 = impl_swap_k 0`), and the implementation's
loop runs the four-round group six times.  The result, `keccakf1600_equiv_lanes`,
is what `Sponge/` is sealed on.

The one fact the per-round theorems leave out is the round counter `i`, which
selects ι's round constant; `prc_round_i_spec` and its siblings supply it.
-/

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 RustM ControlFlow
open LibcruxIotSha3.LaneModel

namespace libcrux_iot_sha3.Permutation

open libcrux_iot_sha3.Support (triple_exists_ok)
open Hax (triple_of_ok)

open libcrux_iot_sha3.Permutation libcrux_iot_sha3.Support

set_option mvcgen.warning false

/-! ## One round, with its counter -/

/-- θ leaves the counter alone and `π ρ χ ι` advances it, so a round
    advances it by one. -/
private theorem round_i_of {θ prc : state.KeccakState → RustM state.KeccakState}
    {Pθ : state.KeccakState → state.KeccakState → Prop}
    (hθ : ∀ s, ⦃ ⌜ True ⌝ ⦄ θ s ⦃ ⇓ r => ⌜ r.i = s.i ∧ Pθ s r ⌝ ⦄)
    (hprc : ∀ s, s.i.val < 24 → ⦃ ⌜ True ⌝ ⦄ prc s ⦃ ⇓ r => ⌜ r.i.val = s.i.val + 1 ⌝ ⦄)
    (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ (do let s1 ← θ s; prc s1) ⦃ ⇓ r => ⌜ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  apply Std.Do.Triple.bind _ _ (hθ s)
  intro s1
  apply triple_imp_intro
  rintro ⟨h_i, -⟩
  apply Std.Do.Triple.of_entails_right _ (hprc s1 (by rw [h_i]; exact hi))
  rw [PostCond.entails_noThrow]
  intro r hr
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hr ⊢
  rw [hr, h_i]

theorem round0_lanes (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round0_theta s
        keccakf1600_round0_pi_rho_chi_chain s1)
    ⦃ ⇓ r => ⌜ roundLanes (Permutation.lift s) s.i.val = lift_perm r impl_perm (impl_swap_k 1)
              ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  have hi_spec := round_i_of (prc := keccakf1600_round0_pi_rho_chi_chain)
    theta_lift_spec (fun s hs => by
      unfold keccakf1600_round0_pi_rho_chi_chain; exact prc_round_i_spec s hs) s hi
  apply Std.Do.Triple.of_entails_right _ (triple_conj_post (round0_equiv_spec s hi) hi_spec)
  rw [PostCond.entails_noThrow]
  intro r ⟨hpost, hr⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hpost hr ⊢
  unfold round0_post at hpost
  refine ⟨?_, hr⟩
  rw [← prc_spec_theta_eq, hpost, show (impl_swap_k 1 : Fin 25 → Bool) = impl_swap from
    funext impl_swap_k_one]

theorem round1_lanes (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round1_theta s
        keccakf1600_round1_pi_rho_chi_chain s1)
    ⦃ ⇓ r => ⌜ roundLanes (lift_perm s impl_perm (impl_swap_k 1)) s.i.val
                = lift_perm r (impl_perm ∘ impl_perm) (impl_swap_k 2)
              ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  have hi_spec := round_i_of (prc := keccakf1600_round1_pi_rho_chi_chain)
    theta_lift_spec_1 (fun s hs => by
      unfold keccakf1600_round1_pi_rho_chi_chain; exact prc_round_i_spec_1 s hs) s hi
  apply Std.Do.Triple.of_entails_right _ (triple_conj_post (round1_equiv_spec s hi) hi_spec)
  rw [PostCond.entails_noThrow]
  intro r ⟨hpost, hr⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hpost hr ⊢
  unfold round1_post at hpost
  exact ⟨by rw [← prc_spec_theta_eq, hpost], hr⟩

theorem round2_lanes (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round2_theta s
        keccakf1600_round2_pi_rho_chi_chain s1)
    ⦃ ⇓ r => ⌜ roundLanes (lift_perm s (impl_perm ∘ impl_perm) (impl_swap_k 2)) s.i.val
                = lift_perm r (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)
              ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  have hi_spec := round_i_of (prc := keccakf1600_round2_pi_rho_chi_chain)
    theta_lift_spec_2 (fun s hs => by
      unfold keccakf1600_round2_pi_rho_chi_chain; exact prc_round_i_spec_2 s hs) s hi
  apply Std.Do.Triple.of_entails_right _ (triple_conj_post (round2_equiv_spec s hi) hi_spec)
  rw [PostCond.entails_noThrow]
  intro r ⟨hpost, hr⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hpost hr ⊢
  unfold round2_post at hpost
  exact ⟨by rw [← prc_spec_theta_eq, hpost], hr⟩

theorem round3_lanes (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let s1 ← keccak.keccakf1600_round3_theta s
        keccakf1600_round3_pi_rho_chi_chain s1)
    ⦃ ⇓ r => ⌜ roundLanes (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
                  s.i.val = Permutation.lift r
              ∧ r.i.val = s.i.val + 1 ⌝ ⦄ := by
  have hi_spec := round_i_of (prc := keccakf1600_round3_pi_rho_chi_chain)
    theta_lift_spec_3 (fun s hs => by
      unfold keccakf1600_round3_pi_rho_chi_chain; exact prc_round_i_spec_3 s hs) s hi
  apply Std.Do.Triple.of_entails_right _ (triple_conj_post (round3_equiv_spec s hi) hi_spec)
  rw [PostCond.entails_noThrow]
  intro r ⟨hpost, hr⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hpost hr ⊢
  unfold round3_post at hpost
  exact ⟨by rw [← prc_spec_theta_eq, hpost], hr⟩

/-! ## Four rounds

After four rounds the storage relabelling is back where it started, so the
group reads through the canonical `lift` on both ends. -/

/-- `keccakf1600_4rounds` is the four round bodies in sequence. -/
private theorem keccakf1600_4rounds_grouped (s : state.KeccakState) :
    keccak.keccakf1600_4rounds 0#usize s =
      (do let a ← (do let s1 ← keccak.keccakf1600_round0_theta s
                      keccakf1600_round0_pi_rho_chi_chain s1)
          let b ← (do let s1 ← keccak.keccakf1600_round1_theta a
                      keccakf1600_round1_pi_rho_chi_chain s1)
          let c ← (do let s1 ← keccak.keccakf1600_round2_theta b
                      keccakf1600_round2_pi_rho_chi_chain s1)
          (do let s1 ← keccak.keccakf1600_round3_theta c
              keccakf1600_round3_pi_rho_chi_chain s1)) := by
  unfold keccak.keccakf1600_4rounds keccakf1600_round0_pi_rho_chi_chain
    keccakf1600_round1_pi_rho_chi_chain keccakf1600_round2_pi_rho_chi_chain
    keccakf1600_round3_pi_rho_chi_chain
  simp only [bind_assoc]

theorem keccakf1600_4rounds_lanes (s : state.KeccakState) (hi : s.i.val + 4 ≤ 24) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_4rounds 0#usize s
    ⦃ ⇓ r => ⌜ Permutation.lift r = roundLanes (roundLanes (roundLanes (roundLanes (Permutation.lift s) s.i.val)
                  (s.i.val + 1)) (s.i.val + 2)) (s.i.val + 3)
              ∧ r.i.val = s.i.val + 4 ⌝ ⦄ := by
  rw [keccakf1600_4rounds_grouped]
  apply Std.Do.Triple.bind _ _ (round0_lanes s (by omega))
  intro a
  apply triple_imp_intro
  rintro ⟨ha, ha_i⟩
  apply Std.Do.Triple.bind _ _ (round1_lanes a (by omega))
  intro b
  apply triple_imp_intro
  rintro ⟨hb, hb_i⟩
  apply Std.Do.Triple.bind _ _ (round2_lanes b (by omega))
  intro c
  apply triple_imp_intro
  rintro ⟨hc, hc_i⟩
  apply Std.Do.Triple.of_entails_right _ (round3_lanes c (by omega))
  rw [PostCond.entails_noThrow]
  intro r ⟨hr, hr_i⟩
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hr hr_i ⊢
  refine ⟨?_, by omega⟩
  rw [← hr, hc_i, ← hc, hb_i, ← hb, ha_i, ← ha]

/-! ## The loop: six groups of four -/

/-- At the boundary of group `k`, the counter is `4k` and the lifted state is
    the first `4k` rounds of the lane model. -/
private def loop_inv (s₀ : state.KeccakState) (k : Std.I32) (s : state.KeccakState) : Prop :=
  0 ≤ k.val ∧ k.val ≤ 6 ∧ s.i.val = 4 * k.val.toNat ∧
  Permutation.lift s = roundsUpTo (Permutation.lift s₀) (4 * k.val.toNat)

set_option maxHeartbeats 4000000 in
theorem keccakf1600_loop_lanes (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_loop { start := 0#i32, «end» := 6#i32 } s
    ⦃ ⇓ r => ⌜ Permutation.lift r = roundsUpTo (Permutation.lift s) 24 ⌝ ⦄ := by
  unfold keccak.keccakf1600_loop
  apply Std.Do.Triple.of_entails_right _
    (Hax.loop_range_spec
      (fun (iter1, s1) => keccak.keccakf1600_loop.body iter1 s1)
      s 0#i32 6#i32
      (fun k s_iter => pure (loop_inv s k s_iter))
      (by decide)
      (by
        apply pure_prop_holds
        refine ⟨by decide, by decide, ?_, rfl⟩
        rw [h_i]; rfl)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro s_final hinv
    dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at hinv ⊢
    have ⟨_, _, _, h_lift⟩ := of_pure_prop_holds hinv
    exact h_lift
  · intro acc k h_ge h_le hinv
    obtain ⟨h_ge_k, h_le_k, h_acc_i, h_acc_lift⟩ := of_pure_prop_holds hinv
    unfold keccak.keccakf1600_loop.body
    apply Std.Do.Triple.bind _ _
      (Hax.IteratorRange_next_spec k 6#i32
        (Q := PostCond.noThrow fun (oi : Option Std.I32 × _) => ⌜
          match oi.1 with
          | none => k.val ≥ (6#i32 : Std.I32).val ∧ oi.2 = { start := k, «end» := 6#i32 }
          | some i => i = k ∧ k.val < (6#i32 : Std.I32).val ∧
                      oi.2.«end» = 6#i32 ∧ oi.2.start.val = k.val + 1
        ⌝)
        (fun hlt s hs => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨rfl, hlt, rfl, hs⟩)
        (fun hge => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨hge, rfl⟩))
    intro ⟨o, iter1⟩
    apply triple_imp_intro
    have h6 : (6#i32 : Std.I32).val = 6 := by decide
    rcases o with _ | i
    · rintro ⟨hge, -⟩
      have hk_eq_i32 : k = 6#i32 := Std.IScalar.eq_of_val_eq (by omega)
      apply triple_of_ok rfl
      apply pure_prop_holds
      subst hk_eq_i32
      exact ⟨by decide, by decide, h_acc_i, h_acc_lift⟩
    · rintro ⟨hi_eq, hk_lt, hiter1_end, hiter1_start⟩
      cases hi_eq
      have hk_toNat_lt : k.val.toNat < 6 := by omega
      show ⦃⌜True⌝⦄
        (do let s1 ← keccak.keccakf1600_4rounds 0#usize acc
            Aeneas.Std.RustM.ok (cont (iter1, s1)))
        ⦃_⦄
      apply Std.Do.Triple.bind _ _
        (keccakf1600_4rounds_lanes acc (by rw [h_acc_i]; omega))
      intro s1
      apply triple_imp_intro
      rintro ⟨h_lift_s1, h_i_s1⟩
      apply triple_of_ok rfl
      refine ⟨hk_lt, hiter1_end, hiter1_start, ?_⟩
      apply pure_prop_holds
      have h_start_toNat : iter1.start.val.toNat = k.val.toNat + 1 := by
        rw [hiter1_start, Int.toNat_add (by omega) (by decide)]; rfl
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [h_i_s1, h_acc_i, h_start_toNat]; ring
      · rw [h_lift_s1, h_acc_lift, h_acc_i, h_start_toNat,
          show 4 * (k.val.toNat + 1) = 4 * k.val.toNat + 3 + 1 by ring]
        rfl

/-! ## `keccakf1600` -/

/-- The implementation's `keccakf1600` computes `keccakFLanes` on the lifted
    state. -/
theorem keccakf1600_equiv_lanes (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakFLanes (Permutation.lift s) = Permutation.lift r_impl ⌝ ⦄ := by
  unfold keccak.keccakf1600
  apply Std.Do.Triple.bind _ _ (keccakf1600_loop_lanes s h_i)
  intro s1
  apply triple_imp_intro
  intro h_loop
  -- `lift` reads only the lanes, which the counter reset leaves alone.
  apply triple_of_ok rfl
  exact h_loop.symm

end libcrux_iot_sha3.Permutation
