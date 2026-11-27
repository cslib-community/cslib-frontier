/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
public import Mathlib.Analysis.Complex.Exponential
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpOneSubInvPow
import CslibFrontier.Probability.IID.Event
import CslibFrontier.Probability.PMF.Bool
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

/-!
# Marked coin events

When each of `k` indices is marked independently according to a Boolean distribution `μ`, the
probability that a designated index `ν ∉ R` is marked (`true`) while every index in `R` is
unmarked (`false`) equals `μ true * μ false ^ R.card`
(`Cslib.Probability.PMF.toOuterMeasure_iid_marked`). When `μ` marks with real probability `a⁻¹`
and `R.card + 1 ≤ a`, this probability is at least `Real.exp (-1) / a`
(`Cslib.Probability.PMF.exp_neg_one_div_le_toOuterMeasure_iid_marked`) and hence at least
`1 / (2.72 * a)` (`Cslib.Probability.PMF.one_div_le_toOuterMeasure_iid_marked`), formalizing the
Claim in the proof of Lemma 13.6 of [BonehShoup2023], §13.4.1 (p. 543, where `a = Q + 1`).

No client on `main` uses these lemmas yet; Lemma 13.6 (§13.4.1, pp. 541–543) and Theorem 13.4
(p. 538) are the intended clients and stay open.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_iid_marked`: exact probability of marking `ν` and leaving
  `R` unmarked.
* `Cslib.Probability.PMF.exp_neg_one_div_le_toOuterMeasure_iid_marked`: lower bound `e⁻¹ / a` when
  `(μ true).toReal = a⁻¹` and `(R.card : ℝ) + 1 ≤ a`.
* `Cslib.Probability.PMF.one_div_le_toOuterMeasure_iid_marked`: lower bound `1 / (2.72 * a)` using
  `e < 2.72`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 13.4.1, proof of Lemma 13.6 (p. 543).
-/

public section

namespace Cslib.Probability.PMF

/-- Mark each of `k` indices independently with the coin `μ`. A designated index is marked and a
set of other indices is unmarked with probability `μ true * μ false ^ |R|`. -/
theorem toOuterMeasure_iid_marked (μ : PMF Bool) {k : ℕ} (R : Finset (Fin k)) {ν : Fin k}
    (hν : ν ∉ R) :
    (iid μ k).toOuterMeasure {v | v ν = true ∧ ∀ i ∈ R, v i = false} =
      μ true * μ false ^ R.card := by
  let E : Fin k → Set Bool := fun i => if i = ν then {true} else if i ∈ R then {false} else Set.univ
  have hset : {v : Fin k → Bool | v ν = true ∧ ∀ i ∈ R, v i = false} = {v | ∀ i, v i ∈ E i} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hvν, hvR⟩ i
      by_cases hiν : i = ν
      · simp only [E, hiν, ↓reduceIte, Set.mem_singleton_iff, hvν]
      · by_cases hiR : i ∈ R
        · simp only [E, hiν, ↓reduceIte, hiR, Set.mem_singleton_iff, hvR i hiR]
        · simp only [E, hiν, ↓reduceIte, hiR, Set.mem_univ]
    · intro hv
      refine ⟨?_, fun i hi => ?_⟩
      · simpa only [E, ↓reduceIte, Set.mem_singleton_iff] using hv ν
      · have hne : i ≠ ν := fun h => hν (h ▸ hi)
        simpa only [E, hne, ↓reduceIte, hi, Set.mem_singleton_iff] using hv i
  rw [hset, ← piFin_const, toOuterMeasure_piFin_forall]
  have hEval (i : Fin k) : μ.toOuterMeasure (E i) =
      if i = ν then μ true else if i ∈ R then μ false else 1 := by
    by_cases hiν : i = ν
    · simp [E, hiν]
    · by_cases hiR : i ∈ R
      · simp [E, hiν, hiR]
      · simp [E, hiν, hiR, apply_true_add_apply_false]
  simp only [hEval]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ν)]
  simp only [↓reduceIte]
  congr 1
  have hsub : R ⊆ Finset.univ.erase ν := fun i hi =>
    Finset.mem_erase.mpr ⟨fun h => hν (h ▸ hi), Finset.mem_univ i⟩
  rw [← Finset.prod_subset hsub (fun i hi hiR => by
    have hne : i ≠ ν := (Finset.mem_erase.mp hi).1
    simp only [hne, ↓reduceIte, hiR])]
  have hconst : ∀ i ∈ R, (if i = ν then μ true else if i ∈ R then μ false else 1) = μ false := by
    intro i hi
    have hne : i ≠ ν := fun h => hν (h ▸ hi)
    simp only [hne, ↓reduceIte, hi]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const]

/-- Sharper bound passed through in the proof of the Claim in Lemma 13.6 ([BonehShoup2023],
§13.4.1, p. 543): with marking probability `a⁻¹` and at most `a - 1` indices to avoid, the
designated index is marked and no index of `R` is with probability at least `e⁻¹ / a`. The book
has `a = Q + 1`. -/
theorem exp_neg_one_div_le_toOuterMeasure_iid_marked (μ : PMF Bool) {a : ℝ}
    (hμ : (μ true).toReal = a⁻¹) {k : ℕ} (R : Finset (Fin k)) (hR : (R.card : ℝ) + 1 ≤ a)
    {ν : Fin k} (hν : ν ∉ R) :
    Real.exp (-1) / a ≤
      ((iid μ k).toOuterMeasure {v | v ν = true ∧ ∀ i ∈ R, v i = false}).toReal := by
  rw [toOuterMeasure_iid_marked μ R hν,
    ENNReal.toReal_mul, ENNReal.toReal_pow, hμ, toReal_false_eq_one_sub, hμ]
  have ha_nonneg : 0 ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) R.card]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_neg_one_le_one_sub_inv_pow hR) (inv_nonneg.mpr ha_nonneg)

/-- **The Claim** as printed in the proof of Lemma 13.6 ([BonehShoup2023], §13.4.1, p. 543, at
`a = Q + 1`): with marking probability `a⁻¹` and at most `a - 1` indices to avoid, the designated
index is marked and no index of `R` is with probability at least `1 / (2.72 * a)`. -/
theorem one_div_le_toOuterMeasure_iid_marked (μ : PMF Bool) {a : ℝ}
    (hμ : (μ true).toReal = a⁻¹) {k : ℕ} (R : Finset (Fin k)) (hR : (R.card : ℝ) + 1 ≤ a)
    {ν : Fin k} (hν : ν ∉ R) :
    1 / (2.72 * a) ≤
      ((iid μ k).toOuterMeasure {v | v ν = true ∧ ∀ i ∈ R, v i = false}).toReal := by
  have ha_pos : 0 < a := by linarith [Nat.cast_nonneg (α := ℝ) R.card]
  have hexp : 1 / 2.72 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos 1)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  calc 1 / (2.72 * a) = (1 / 2.72) / a := by ring
    _ ≤ Real.exp (-1) / a := div_le_div_of_nonneg_right hexp ha_pos.le
    _ ≤ ((iid μ k).toOuterMeasure {v | v ν = true ∧ ∀ i ∈ R, v i = false}).toReal :=
      exp_neg_one_div_le_toOuterMeasure_iid_marked μ hμ R hR hν

end Cslib.Probability.PMF
