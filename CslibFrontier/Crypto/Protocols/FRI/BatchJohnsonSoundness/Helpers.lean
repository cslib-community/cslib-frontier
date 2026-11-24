/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Internal Algebraic, Floor, and Ceiling Helpers for Batched FRI Soundness

Internal helper lemmas shared across the smooth and binary batched FRI soundness submodules
(imported privately by sibling submodules under `BatchJohnsonSoundness` and not re-exported by
`CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness`).
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

section Helpers

variable {F : Type} [Field F]

omit [Field F] in
/-- Combine an `ℝ≥0∞` ratio with a finite sum of ratios over a common denominator. -/
theorem add_sum_natCast_div_ennreal {ι : Type*} (B₀ : ℕ) (s : Finset ι)
    (x : ι → ℕ) (D : ℕ) :
    ((B₀ : ℝ≥0∞) / (D : ℝ≥0∞)) + (∑ i ∈ s, ((x i : ℕ) : ℝ≥0∞) / (D : ℝ≥0∞)) =
      ((B₀ + ∑ i ∈ s, x i : ℕ) : ℝ≥0∞) / (D : ℝ≥0∞) := by
  simp only [Nat.cast_add, Nat.cast_sum, div_eq_mul_inv, add_mul, Finset.sum_mul]

omit [Field F] in
/-- Nonnegativity of `1 - 1 / 2 ^ m`. -/
theorem one_sub_inv_two_pow_nonneg (m : ℕ) :
    0 ≤ 1 - (1 : ℝ) / (2 : ℝ) ^ m :=
  sub_nonneg.mpr <| div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)

omit [Field F] in
/-- Nonnegativity of `2 - 1 / 2 ^ m`. -/
theorem two_sub_inv_two_pow_nonneg (m : ℕ) :
    0 ≤ 2 - (1 : ℝ) / (2 : ℝ) ^ m := by
  linarith [one_sub_inv_two_pow_nonneg m]

/-- When `2 ^ d ≤ B`, strict threshold acceptance `B < card` in `friSmoothBatchCommitGame` has
probability zero. -/
theorem friSmoothBatchCommitGame_eq_zero_of_two_pow_le [Fintype F]
    (params : FRISmoothParams F) (t B : ℕ) (hB : 2 ^ params.d ≤ B)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friSmoothBatchCommitGame params t B stmt P true = 0 := by
  have hconst (pref πFinal) :
      letI : DecidablePred (fun s => friSmoothBatchFinalPasses params t stmt pref πFinal s) :=
        Classical.decPred _
      decide (B < (Finset.univ.filter fun s =>
        friSmoothBatchFinalPasses params t stmt pref πFinal s).card) = false :=
    decide_eq_false <| not_lt_of_ge <|
      ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _)).trans hB
  simp only [friSmoothBatchCommitGame, hconst]
  change ((iopRunRounds P (params.m + 1) []).bind fun pref =>
    (P pref).map (Function.const _ false)) true = 0
  simp only [PMF.map_const, PMF.bind_const, PMF.pure_apply, Bool.true_eq_false, ↓reduceIte]

/-- Real-to-integer floor threshold bridge for `friSmoothBatchCommitGame`. -/
theorem friSmoothBatchCommitGame_le_of_floor [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) {α α₀ : ℝ} {ε_C : ℝ≥0∞}
    (hα₀_nn : 0 ≤ α₀) (hα_le_α₀ : α ≤ α₀)
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hprox : ∀ e₀ : ℕ, stmt ∉ params.batchProximityLang t e₀ →
      (e₀ : ℝ) / (2 ^ params.d : ℝ) < 1 - α₀ →
      friSmoothBatchCommitGame params t (2 ^ params.d - e₀ - 1) stmt P true ≤ ε_C) :
    friSmoothBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤ ε_C := by
  by_cases hα₀_lt : α₀ < 1
  · obtain ⟨hiff, _, hB_eq, _, he_lt⟩ :=
      friBatchFloorThreshold_bounds params.initialCode t stmt hα₀_nn hα₀_lt
    rw [← hB_eq]
    exact hprox _ (hiff.mp fun D' v₀ hv₀ v hv hag =>
      (hagree_le D' v₀ hv₀ v hv hag).trans hα_le_α₀) he_lt
  · have h2le : 2 ^ params.d ≤ ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ := Nat.le_floor <| by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using
        mul_le_mul_of_nonneg_right (not_lt.mp hα₀_lt) (by positivity : (0 : ℝ) ≤ (2 ^ params.d : ℝ))
    simp [friSmoothBatchCommitGame_eq_zero_of_two_pow_le params t _ h2le stmt P]

/-- Cast and bound the query-round survival power `((2 ^ d - e - 1) / 2 ^ d) ^ q` by
`ENNReal.ofReal (α ^ q)`. -/
theorem query_pow_le_ofReal_pow {d e q : ℕ} {α : ℝ}
    (hq_lt : (((2 ^ d - e - 1 : ℕ) : ℝ) / (2 ^ d : ℝ)) < α) :
    (((2 ^ d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q ≤ ENNReal.ofReal (α ^ q) := by
  have hr_nn : 0 ≤ ((2 ^ d - e - 1 : ℕ) : ℝ) / (2 ^ d : ℝ) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_pow hr_nn q]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr_nn hq_lt.le q)

/-- Real-density `batchCorrAgreeLang` to integer `batchProximityLang` bridge for
`friSmoothBatchIOP`. -/
theorem friSmoothBatchIOP_interactiveGame_le_of_corrAgree_le [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {α ε_C : ℝ} (hε_nn : 0 ≤ ε_C)
    (hα_pos : 0 < α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hprox : ∀ e : ℕ, stmt ∉ params.batchProximityLang t e →
      (e : ℝ) / (2 ^ params.d : ℝ) ≤ 1 - α →
      iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
        ENNReal.ofReal ε_C + (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^
          params.q) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (ε_C + α ^ params.q) := by
  by_cases hα_le : α ≤ 1
  · rw [FRISmoothParams.batchCorrAgreeLang,
      friBatchCorrAgreeLang_eq_proximityLang params.initialCode t hα_le] at hfar
    obtain ⟨_, hq_lt, he_le⟩ := friBatchCeilThreshold_bounds params.d hα_pos hα_le
    refine (hprox _ hfar he_le).trans ?_
    rw [ENNReal.ofReal_add hε_nn (pow_nonneg hα_pos.le _)]
    exact add_le_add le_rfl (query_pow_le_ofReal_pow hq_lt)
  · have h1pow : (1 : ℝ) ≤ α ^ params.q := one_le_pow₀ (not_le.mp hα_le).le
    exact (PMF.coe_le_one _ true).trans <| ENNReal.ofReal_one.symm.trans_le <|
      ENNReal.ofReal_le_ofReal (by linarith)

/-- Upper-bound `friSmoothBatchRBRError` at the ceiling proximity threshold
`2 ^ d - ⌈α * 2 ^ d⌉₊`. -/
theorem friSmoothBatchRBRError_ceil_le [Fintype F] (params : FRISmoothParams F)
    (ε_batch : ℝ≥0∞) {α : ℝ} (hα_pos : 0 < α) (hα_le : α ≤ 1) (B_commit : ℕ) :
    friSmoothBatchRBRError params ε_batch (2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊) B_commit ≤
      max ε_batch
        (max ((B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) (ENNReal.ofReal (α ^ params.q))) := by
  obtain ⟨_, hq_lt, _⟩ := friBatchCeilThreshold_bounds params.d hα_pos hα_le
  simp only [friSmoothBatchRBRError, friSmoothRBRError]
  exact max_le_max le_rfl (max_le_max le_rfl (query_pow_le_ofReal_pow hq_lt))


/-- Arithmetic slack helper converting `√ρ * (1 + 1 / (2 * mJ)) ≤ α` and `x ≤ 1 - α` into the
Johnson bound condition. -/
theorem smooth_johnson_slack_of_le (params : FRISmoothParams F) {mJ : ℕ} (hmJ : 1 ≤ mJ)
    {α x : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    (hx : x ≤ 1 - α) :
    0 < α ∧
      x ≤ 1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hsq : 0 < Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hmJR : (0 : ℝ) < (mJ : ℝ) := by exact_mod_cast hmJ
  have hmul : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (1 + 1 / (2 * (mJ : ℝ))) =
      Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) +
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) := by ring
  exact ⟨lt_of_lt_of_le (by positivity) hα, by linarith⟩

end Helpers

end Cslib.Crypto.Protocols.FRI
