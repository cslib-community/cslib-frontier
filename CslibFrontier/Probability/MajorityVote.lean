/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.UniformBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Majority votes over a uniform sample space at arbitrary advantage

Generalizes `Cslib.card_filter_card_filter_le_le` (the `(8 / 9) ^ r` bound for advantage `2 / 3`)
to any error fraction `ε < 1 / 2`, deriving the counting bound directly from the `PMF` majority
tail bound `Cslib.Probability.PMF.iid_card_ge_le`.

## Main results

* `Cslib.card_filter_card_filter_le_of_err_lt_half`: if at least `(1 - ε) * |Ω|` elements of `Ω`
  lie in `G` (`0 ≤ ε < 1 / 2`), at most a `(4 * ε * (1 - ε)) ^ r` fraction of `2 r`-tuples over `Ω`
  have at most `r` entries in `G`.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.4][AroraBarak09]
-/

public section

namespace Cslib

/-- **Majority-vote counting bound for any advantage `ε < 1 / 2`.** If at least `(1 - ε) * |Ω|`
elements of `Ω` lie in `G` (`0 ≤ ε < 1 / 2`), then among the `2 r`-tuples over `Ω`, those with at
most `r` entries in `G` make up at most a `(4 * ε * (1 - ε)) ^ r` fraction. -/
theorem card_filter_card_filter_le_of_err_lt_half {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (G : Finset Ω) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 2)
    (hG : (1 - ε) * (Fintype.card Ω : ℝ) ≤ G.card) (r : ℕ) :
    ((Finset.univ.filter fun ω : Fin (2 * r) → Ω =>
      (Finset.univ.filter fun i => ω i ∈ G).card ≤ r).card : ℝ) ≤
      (4 * ε * (1 - ε)) ^ r * (Fintype.card Ω : ℝ) ^ (2 * r) := by
  rcases r.eq_zero_or_pos with rfl | hr_pos
  · simp only [Nat.mul_zero, pow_zero, mul_one]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  rcases isEmpty_or_nonempty Ω with hEmpty | hNonempty
  · have : IsEmpty (Fin (2 * r) → Ω) := ⟨fun f => hEmpty.false (f ⟨0, by lia⟩)⟩
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (pow_nonneg (by nlinarith) r) (by positivity)
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  let bad : Ω → Bool := fun x => decide (x ∉ G)
  have hq_le : (((Probability.PMF.uniformOfFintype Ω).map bad) true).toReal ≤ ε := by
    have hbad : (Finset.univ.filter fun x => bad x = true) = Gᶜ := by
      ext x
      simp [bad]
    rw [Probability.PMF.toReal_uniformOfFintype_map_apply_true, hbad, Finset.dens_eq_card_div_card,
      NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, Finset.card_compl,
      Nat.cast_sub (Finset.card_le_univ G), div_le_iff₀ hN]
    linarith
  have hiid := Probability.PMF.iid_card_ge_le hq_le hε₁.le r
  rw [Probability.PMF.iid_map, Probability.PMF.iid_uniformOfFintype,
    PMF.toOuterMeasure_map_apply] at hiid
  have hpre : (fun (ω : Fin (2 * r) → Ω) i => bad (ω i)) ⁻¹'
      {v : Fin (2 * r) → Bool | r ≤ (Finset.univ.filter fun i => v i = true).card} =
      {ω | (Finset.univ.filter fun i => ω i ∈ G).card ≤ r} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, bad, decide_eq_true_eq]
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * r)))) (fun i => ω i ∈ G)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    lia
  rw [hpre] at hiid
  have hcount := Probability.PMF.card_filter_univ_le_of_toOuterMeasure_uniformOfFintype_le
    (fun (ω : Fin (2 * r) → Ω) => (Finset.univ.filter fun i => ω i ∈ G).card ≤ r) hiid
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hcount
  exact hcount.trans_eq (mul_comm _ _)

end Cslib
