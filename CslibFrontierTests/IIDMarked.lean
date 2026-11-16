/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Probability.IID.Marked
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Coin
import Mathlib.Tactic.NormNum

/-! # Marked coin events -/

set_option linter.privateModule false

namespace CslibFrontierTests.IIDMarked

open Cslib.Probability.PMF

/-- The coin of Figure 13.2 of [BonehShoup2023]: `true` with probability `1 / (Q + 1)`. -/
noncomputable def bookCoin (Q : ℕ) : PMF Bool :=
  coin ⟨((Q : ℝ) + 1)⁻¹, by positivity,
    inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg Q))⟩

theorem bookCoin_true_toReal (Q : ℕ) : (bookCoin Q true).toReal = ((Q : ℝ) + 1)⁻¹ := by
  simp [bookCoin, coin_apply_toReal]

/-- The Claim as printed ([BonehShoup2023], §13.4.1, p. 543): at most `Q` indices to avoid. -/
example (Q : ℕ) {k : ℕ} (R : Finset (Fin k)) (hR : R.card ≤ Q) {ν : Fin k} (hν : ν ∉ R) :
    1 / (2.72 * ((Q : ℝ) + 1)) ≤
      ((iid (bookCoin Q) k).toOuterMeasure {v | v ν = true ∧ ∀ i ∈ R, v i = false}).toReal :=
  one_div_le_toOuterMeasure_iid_marked (bookCoin Q) (bookCoin_true_toReal Q) R
    (by simpa using hR) hν

/-- The `exp (-1)` bound passed through in the proof of the Claim, at `a = Q + 1`. -/
example (Q : ℕ) {k : ℕ} (R : Finset (Fin k)) (hR : R.card ≤ Q) {ν : Fin k} (hν : ν ∉ R) :
    Real.exp (-1) / ((Q : ℝ) + 1) ≤
      ((iid (bookCoin Q) k).toOuterMeasure {v | v ν = true ∧ ∀ i ∈ R, v i = false}).toReal :=
  exp_neg_one_div_le_toOuterMeasure_iid_marked (bookCoin Q) (bookCoin_true_toReal Q) R
    (by simpa using hR) hν

/-- The fair coin (`Q = 1`) and one index to avoid: the probability is `1 / 4`. -/
example : ((iid (bookCoin 1) 3).toOuterMeasure
    {v | v 0 = true ∧ ∀ i ∈ ({1} : Finset (Fin 3)), v i = false}).toReal = 1 / 4 := by
  rw [toOuterMeasure_iid_marked _ {1} (by decide), ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_false_eq_one_sub, bookCoin_true_toReal]
  norm_num

/-- Edge case: empty `R` with `a = 1` (coin always marks). -/
example :
    1 / (2.72 * 1) ≤
      ((iid (PMF.pure true) 1).toOuterMeasure
        {v | v 0 = true ∧ ∀ i ∈ (∅ : Finset (Fin 1)), v i = false}).toReal :=
  one_div_le_toOuterMeasure_iid_marked (PMF.pure true) (a := 1) (by simp) (∅ : Finset (Fin 1))
    (by simp) (Finset.notMem_empty 0)

/-- The hypothesis `|R| + 1 ≤ a` is needed: the fair coin (`a = 2`) and two indices to avoid give
`1 / 8`, below `1 / (2.72 * 2)` and so below `e⁻¹ / 2`. -/
example : ¬ 1 / (2.72 * 2) ≤ ((iid (bookCoin 1) 3).toOuterMeasure
    {v | v 0 = true ∧ ∀ i ∈ ({1, 2} : Finset (Fin 3)), v i = false}).toReal := by
  have hcard : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  rw [toOuterMeasure_iid_marked _ {1, 2} (by decide), hcard, ENNReal.toReal_mul,
    ENNReal.toReal_pow, toReal_false_eq_one_sub, bookCoin_true_toReal]
  norm_num

/-- The hypothesis `ν ∉ R` is needed: for the fair coin and `ν ∈ R` the event is empty, while the
product is `1 / 4`. -/
example : (iid (bookCoin 1) 1).toOuterMeasure
    {v | v 0 = true ∧ ∀ i ∈ ({0} : Finset (Fin 1)), v i = false} ≠
      bookCoin 1 true * bookCoin 1 false ^ ({0} : Finset (Fin 1)).card := by
  have hset : {v : Fin 1 → Bool | v 0 = true ∧ ∀ i ∈ ({0} : Finset (Fin 1)), v i = false} = ∅ := by
    ext v
    simp
  intro h
  have h' := congrArg ENNReal.toReal h
  rw [hset, MeasureTheory.measure_empty, ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_false_eq_one_sub, bookCoin_true_toReal] at h'
  norm_num at h'

end CslibFrontierTests.IIDMarked
