/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.StateCount
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The number of states

Lemma B.1 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. A state is a pair of
finite sets of natural numbers; `stateCount E` is the number of states of energy at most `E`.
There is `κ > 0` with `log (stateCount E) ≤ κ √E` for all `E` and
`log (stateCount E) ≥ (κ - ε) √E` for every `ε > 0` and all large `E`
(`exists_log_stateCount_asymptotic`). The proof follows the paper: interleaving `k` states gives
`stateCount E ^ k ≤ stateCount (k² E)`, and the generating function of the sets of bounded energy
gives the upper bound `10 √E`.

## Main definitions

* `stateCount`.

## Main results

* `exists_log_stateCount_asymptotic`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma B.1 of the paper; module `Paper.States` (`lem_count`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Filter

/-- The number `P(E)` of states of energy at most `E`. -/
@[expose] def stateCount (E : ℕ) : ℕ := (lowStates E).card

/-- Proof of Lemma B.1: interleaving `k` states (put `k i + r` into the first set for `i` in the
first set of the `r`-th state, and `k j + k - 1 - r` into the second set for `j` in its second
set) is injective and multiplies the total energy by `k`, so `P(E)^k ≤ P(k² E)`. -/
private theorem lem_count_interleave (k E : ℕ) : stateCount E ^ k ≤ stateCount (k ^ 2 * E) := by
  rw [pow_two]
  change (lowStates E).card ^ k ≤ (lowStates (k * k * E)).card
  have h1 : (Fintype.piFinset fun _ : Fin k => lowStates E).card = (lowStates E).card ^ k := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← h1]
  refine Finset.card_le_card_of_injOn
    (fun s => (interleave k fun r => (s r).1, interleave k fun r => (s r.rev).2)) ?_ ?_
  · intro s hs
    have hs' : ∀ r, (s r).1.card = (s r).2.card ∧ energy (s r).1 + energy (s r).2 ≤ E := fun r =>
      mem_lowStates.1 (Fintype.mem_piFinset.1 hs r)
    refine mem_coe.2 (mem_lowStates.2 ⟨?_, ?_⟩)
    · change (interleave k fun r => (s r).1).card = (interleave k fun r => (s r.rev).2).card
      rw [card_interleave, card_interleave]
      refine Eq.trans ?_
          (Fintype.sum_equiv Fin.revPerm (fun r => (s r.rev).2.card) (fun r => (s r).2.card)
        (fun r => by simp)).symm
      exact Finset.sum_congr rfl fun r _ => (hs' r).1
    · change energy (interleave k fun r => (s r).1) + energy (interleave k fun r => (s r.rev).2) ≤ _
      rw [energy_interleave s fun r => (hs' r).1, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      calc ∑ r, (energy (s r).1 + energy (s r).2) ≤ ∑ _r : Fin k,
          E := Finset.sum_le_sum fun r _ => (hs' r).2
        _ = k * E := by simp
  · intro s _ s' _ h
    have h1 := interleave_injective (Prod.ext_iff.1 h).1
    have h2 := interleave_injective (Prod.ext_iff.1 h).2
    funext r
    refine Prod.ext (congrFun h1 r) ?_
    have := congrFun h2 r.rev
    simpa using this

/-- Proof of Lemma B.1: for `0 < t < 1`, the number of sets `S` with `∑_{i ∈ S} (2 i + 1) ≤ E` is
at most `t^(-E) ∏_i (1 + t^(2 i + 1)) ≤ t^(-E) e^(1 / (1 - t))`. -/
private theorem lem_count_sets (E : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ((lowSets E).card : ℝ) * t ^ E ≤ Real.exp (1 / (1 - t)) := by
  calc ((lowSets E).card : ℝ) * t ^ E = ∑ _S ∈ lowSets E,
      t ^ E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ S ∈ lowSets E, ∏ i ∈ S, t ^ (2 * i + 1) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [Finset.prod_pow_eq_pow_sum]
        exact pow_le_pow_of_le_one h0.le h1.le (mem_filter.1 hS).2
    _ ≤ ∑ S ∈ (range E).powerset, ∏ i ∈ S, t ^ (2 * i + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ =>
          Finset.prod_nonneg fun i _ => by positivity
    _ = ∏ i ∈ range E, (1 + t ^ (2 * i + 1)) := (Finset.prod_one_add _).symm
    _ ≤ ∏ i ∈ range E, Real.exp (t ^ i) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        have h2 : t ^ (2 * i + 1) ≤ t ^ i := pow_le_pow_of_le_one h0.le h1.le (by omega)
        have h3 := Real.add_one_le_exp (t ^ i)
        linarith
    _ = Real.exp (∑ i ∈ range E, t ^ i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / (1 - t)) := by
        refine Real.exp_le_exp.2 ?_
        rw [geom_sum_eq h1.ne, one_div, ← neg_div_neg_eq, neg_sub, neg_sub, div_eq_mul_inv]
        have : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith)
        have h4 : 1 - t ^ E ≤ 1 := by
          have : 0 < t ^ E := by positivity
          linarith
        calc (1 - t ^ E) * (1 - t)⁻¹ ≤ 1 * (1 - t)⁻¹ := mul_le_mul_of_nonneg_right h4 this
          _ = _ := one_mul _

/-- Proof of Lemma B.1: a state is a pair of such sets, and `1 - t = 1 / (2 √E)` gives
`log P(E) ≤ 10 √E` for `E ≥ 1`. -/
private theorem lem_count_upper {E : ℕ} (hE : 1 ≤ E) : Real.log (stateCount E) ≤ 10 * √E := by
  have hs1 : 1 ≤ √(E : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hE
  have hs0 : 0 < √(E : ℝ) := by linarith
  have hss : √(E : ℝ) * √(E : ℝ) = E := Real.mul_self_sqrt (Nat.cast_nonneg E)
  set t : ℝ := 1 - 1 / (2 * √(E : ℝ)) with ht
  have hx : 1 / (2 * √(E : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hx0 : 0 < 1 / (2 * √(E : ℝ)) := by positivity
  have ht0 : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  have h3 : (t ^ E)⁻¹ ≤ Real.exp √(E : ℝ) := by
    have h4 : t⁻¹ ≤ Real.exp (1 / √(E : ℝ)) := by
      refine le_trans ?_ (Real.add_one_le_exp (1 / √(E : ℝ)))
      rw [inv_le_iff_one_le_mul₀ ht0, ht]
      have e : (1 - 1 / (2 * √(E : ℝ))) * (1 / √(E : ℝ) + 1) - 1 =
          (√(E : ℝ) - 1) / (2 * (√(E : ℝ) * √(E : ℝ))) := by
        field_simp
        ring
      have : 0 ≤ (√(E : ℝ) - 1) / (2 * (√(E : ℝ) * √(E : ℝ))) := div_nonneg (by linarith)
          (by positivity)
      linarith
    rw [← inv_pow]
    calc t⁻¹ ^ E ≤ Real.exp (1 / √(E : ℝ)) ^ E := pow_le_pow_left₀ (by positivity) h4 _
      _ = Real.exp (E * (1 / √(E : ℝ))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp √(E : ℝ) := by
          congr 1
          rw [mul_one_div, div_eq_iff hs0.ne', hss]
  have h2 : ((lowSets E).card : ℝ) ≤ Real.exp (5 * √(E : ℝ)) := by
    have h5 := lem_count_sets E ht0 ht1
    have h6 : 1 / (1 - t) = 2 * √(E : ℝ) := by
      rw [ht]
      field_simp
      ring
    rw [h6] at h5
    have htE : 0 < t ^ E := by positivity
    calc ((lowSets E).card : ℝ) = (lowSets E).card * t ^ E * (t ^ E)⁻¹ := by field_simp
      _ ≤ Real.exp (2 * √(E : ℝ)) * Real.exp √(E : ℝ) := mul_le_mul h5 h3 (by positivity)
          (Real.exp_pos _).le
      _ = Real.exp (3 * √(E : ℝ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (5 * √(E : ℝ)) := Real.exp_le_exp.2 (by linarith)
  change logLowStates E ≤ _
  rw [logLowStates, Real.log_le_iff_le_exp (by exact_mod_cast lowStates_card_pos E)]
  have h1 : ((lowStates E).card : ℝ) ≤ (lowSets E).card * (lowSets E).card :=
      by exact_mod_cast card_lowStates_le E
  refine h1.trans ?_
  calc ((lowSets E).card : ℝ) * (lowSets E).card ≤ Real.exp (5 * Real.sqrt E) *
      Real.exp (5 * Real.sqrt E) :=
        mul_le_mul h2 h2 (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- **Paper: Lemma B.1.** There is `κ > 0` with `log P(E) ≤ κ √E` for all `E`, and
`log P(E) ≥ (κ - ε) √E` for every `ε > 0` and all large `E`. -/
theorem exists_log_stateCount_asymptotic : ∃ κ : ℝ,
    0 < κ ∧ (∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop, (κ - ε) * √E ≤ Real.log (stateCount E) := by
  have mul_lp_le : ∀ k E : ℕ, k * logLowStates E ≤ logLowStates (k * k * E) := by
    intro k E
    rw [logLowStates, ← Real.log_pow, ← pow_two]
    refine Real.log_le_log (by have := lowStates_card_pos E; positivity) ?_
    exact_mod_cast lem_count_interleave k E
  change ∃ κ : ℝ, 0 < κ ∧ (∀ E : ℕ, logLowStates E ≤ κ * √E) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop,
      (κ - ε) * √E ≤ logLowStates E
  set S : Set ℝ := {z | ∃ E : ℕ, 1 ≤ E ∧ z = logLowStates E / Real.sqrt E} with hS
  have hb : BddAbove S := by
    refine ⟨10, ?_⟩
    rintro _ ⟨E, hE, rfl⟩
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hE))]
    exact lem_count_upper hE
  have hne : S.Nonempty := ⟨_, 1, le_rfl, rfl⟩
  have hle : ∀ E : ℕ, 1 ≤ E → logLowStates E ≤ sSup S * Real.sqrt E := by
    intro E hE
    rw [← div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hE))]
    exact le_csSup hb ⟨E, hE, rfl⟩
  have hpos : 0 < sSup S := by
    have h2 : 0 < logLowStates 2 := Real.log_pos (by exact_mod_cast two_le_card_lowStates)
    have : 0 < logLowStates 2 / Real.sqrt (2 : ℕ) := div_pos h2 (Real.sqrt_pos.2 (by norm_num))
    exact this.trans_le (le_csSup hb ⟨2, by norm_num, rfl⟩)
  refine ⟨sSup S, hpos, fun E => ?_, fun ε hε => eventually_atTop.2 ?_⟩
  · rcases Nat.eq_zero_or_pos E with rfl | hE
    · simp [logLowStates_zero]
    · exact hle E hE
  · obtain ⟨_, ⟨E₁, hE₁, rfl⟩, hlt⟩ :=
      exists_lt_of_lt_csSup hne (show sSup S - ε / 2 < sSup S by linarith)
    set c := sSup S with hc
    have hs1 : 0 < Real.sqrt E₁ := Real.sqrt_pos.2 (by exact_mod_cast hE₁)
    rw [lt_div_iff₀ hs1] at hlt
    refine ⟨⌈(2 * c * Real.sqrt E₁ / ε) ^ 2⌉₊, fun E hE => ?_⟩
    have hE' : 2 * c * Real.sqrt E₁ / ε ≤ Real.sqrt E := by
      refine Real.le_sqrt_of_sq_le ?_
      exact (Nat.le_ceil _).trans (by exact_mod_cast hE)
    rw [div_le_iff₀ hε] at hE'
    rcases le_or_gt c ε with hcε | hcε
    · have : (c - ε) * Real.sqrt E ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (Real.sqrt_nonneg _)
      exact this.trans (logLowStates_nonneg E)
    set k := Nat.sqrt (E / E₁) with hk
    have hk1 : k * k * E₁ ≤ E :=
      (Nat.mul_le_mul_right _ (Nat.sqrt_le _)).trans (Nat.div_mul_le_self _ _)
    have hk2 : E < (k + 1) * (k + 1) * E₁ := by
      have := Nat.lt_succ_sqrt (E / E₁)
      exact (Nat.div_lt_iff_lt_mul hE₁).1 this
    have hk3 : Real.sqrt E ≤ (k + 1) * Real.sqrt E₁ := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have : (E : ℝ) ≤ ((k + 1) * (k + 1) * E₁ : ℕ) := by exact_mod_cast hk2.le
      push_cast at this
      nlinarith
    have h5 : k * logLowStates E₁ ≤ logLowStates E := (mul_lp_le k E₁).trans (logLowStates_mono hk1)
    have h6 : (k : ℝ) * ((c - ε / 2) * Real.sqrt E₁) ≤ k * logLowStates E₁ :=
      mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg _)
    have h7 : (c - ε / 2) * Real.sqrt E ≤ (c - ε / 2) * ((k + 1) * Real.sqrt E₁) :=
      mul_le_mul_of_nonneg_left hk3 (by linarith)
    have h8 : 0 ≤ ε / 2 * Real.sqrt E₁ := by positivity
    nlinarith

end Cslib.Circuits.Arithmetic.Separation.Curvature
