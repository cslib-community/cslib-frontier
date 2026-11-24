/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Probability.BernsteinPi
public import CslibFrontier.MachineLearning.OnlineLearning.BernsteinOnlineToBatch
public import CslibFrontier.Probability.Freedman
import CslibFrontier.Probability.PMF.Coin

/-!
# Checked tests for Bennett, Bernstein, and Freedman concentration inequalities

Exercises `CslibFrontier.Probability.BennettStep`, `CslibFrontier.Probability.Freedman`,
`CslibFrontier.Foundations.Probability.BernsteinPi`, and
`CslibFrontier.MachineLearning.OnlineLearning.BernsteinOnlineToBatch` on concrete instances and
subtle model boundaries:

1. **Scalar Bennett–Bernstein checks**: `sq_div_two_mul_le_klFun_one_add` at `u = 3` and
   one-sided `exp_sub_one_sub_le_mul_sq` at `u = -5 ≤ 2` (`|u| > b`).
2. **Stateful adaptive-variance martingale witness** (`adaptive_freedman_maximal_checked`):
   a 2-step zero-mean martingale whose step-1 conditional variance is `0` on the quiet branch
   (`h 0 = false`) and `36` on the volatile branch (`h 0 = true`), with worst-case step bound
   `b = 6`. Verifies that quiet trajectories carry total probability `1 / 2` with predictable
   variation `seqPredVar = 1`, and that Freedman's maximal bound gives `≤ exp (-9 / 14)` on
   `{∃ k ≤ 2, 3 ≤ X_k ∧ seqPredVar ≤ 1}`.
3. **Infinite outcome type & degenerate boundaries** (`freedman_infinite_and_boundaries_checked`):
   exercises `seqProcess_exists_prefix_ge_and_var_le` on `PMF ℕ` (no `Fintype` or
   `MeasurableSpace`) across `ε = 0`, `b = 0`, and `v = 0`.
4. **Zero-variance fast-rate online-to-batch check** (`bernstein_online_to_batch_zero_var_checked`):
   verifies `O(log (1 / δ) / T)` excess risk with zero `1 / √T` penalty when `s2 = 0`.
-/

public section

namespace CslibFrontierTests.BernsteinFreedman

open MeasureTheory ProbabilityTheory InformationTheory Cslib.Probability Cslib.Probability.PMF
open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning
open scoped BigOperators ENNReal unitInterval

/-! ### 1. Scalar Bennett and one-sided exponential checks -/

theorem bennett_scalar_checked :
    (9 / 4 : ℝ) ≤ klFun 4 ∧
      Real.exp (-5 : ℝ) - 1 - (-5) ≤ ((-5 : ℝ) ^ 2 / 2 ^ 2) * (Real.exp 2 - 1 - 2) := by
  refine ⟨?_, Real.exp_sub_one_sub_le_mul_sq (by norm_num) (by norm_num)⟩
  have h := sq_div_two_mul_le_klFun_one_add (u := 3) (by norm_num)
  norm_num at h ⊢
  exact h

/-! ### 2. Stateful adaptive-variance martingale on `seqProcess` -/

/-- Unbiased `Bool` coin transition kernel at every step. -/
noncomputable def fairCoinStep : ∀ t : ℕ, (Fin t → Bool) → PMF Bool :=
  fun _ _ => coin ⟨1 / 2, by norm_num⟩

/-- Zero-mean adaptive martingale:
* `k = 0`: `0`
* `k = 1`: `+1` on `true`, `-1` on `false` (conditional variance `1`)
* `k ≥ 2`: if `h 0 = false` ("quiet regime"), stays at `-1` (increment `0`, conditional variance
  `0`); if `h 0 = true` ("volatile regime"), steps by `±6` (conditional variance `36`). -/
def adaptiveMartingale : ∀ k : ℕ, (Fin k → Bool) → ℝ
  | 0, _ => 0
  | 1, h => if h 0 then 1 else -1
  | k + 2, h =>
    adaptiveMartingale (k + 1) (Fin.init h) +
      if h 0 then (if h (Fin.last (k + 1)) then 6 else -6) else 0

/-- Predictable conditional variance of `adaptiveMartingale` (`1` at step `0`, then `0` on the
quiet `false` branch and `36` on the volatile `true` branch). -/
def adaptivePredVar : ∀ k : ℕ, (Fin k → Bool) → ℝ
  | 0, _ => 1
  | _ + 1, h => if h 0 then 36 else 0

theorem adaptive_freedman_maximal_checked :
    seqPredVar adaptivePredVar 2 ![false, false] = 1 ∧
      (seqProcess fairCoinStep 2 ![false, false]).toReal +
        (seqProcess fairCoinStep 2 ![false, true]).toReal = 1 / 2 ∧
      ((seqProcess fairCoinStep 2).toOuterMeasure
        {h : Fin 2 → Bool | ∃ (k : ℕ) (hk : k ≤ 2),
          3 ≤ adaptiveMartingale k (Fin.take k hk h) ∧
            seqPredVar adaptivePredVar k (Fin.take k hk h) ≤ 1}).toReal ≤
        Real.exp (-9 / 14) := by
  have hpv : seqPredVar adaptivePredVar 2 ![false, false] = 1 := by
    simp [seqPredVar, Fin.sum_univ_two, adaptivePredVar, Fin.take_apply]
  have hmass : (seqProcess fairCoinStep 2 ![false, false]).toReal +
      (seqProcess fairCoinStep 2 ![false, true]).toReal = 1 / 2 := by
    simp only [seqProcess_apply, Fin.prod_univ_two, fairCoinStep, Matrix.cons_val_zero,
      Matrix.cons_val_one, ENNReal.toReal_mul, coin_apply_toReal, Bool.false_eq_true, ↓reduceIte]
    norm_num
  refine ⟨hpv, hmass, ?_⟩
  have hfreedman := seqProcess_bernstein_maximal_ge_le fairCoinStep adaptiveMartingale
    adaptivePredVar (b := 6) (v := 1) (ε := 3) (by norm_num) (by norm_num) (by norm_num) 2
    (fun k hk h _ => by
      interval_cases k
      · rw [tsum_fintype, Fintype.sum_bool]
        simp only [fairCoinStep, coin_apply_toReal, ↓reduceIte, Bool.false_eq_true,
          adaptiveMartingale, Fin.snoc_zero]
        norm_num
      · rw [tsum_fintype, Fintype.sum_bool]
        have hinit (b : Bool) :
            Fin.init (Fin.snoc (α := fun _ => Bool) h b) = h := by simp
        have h0 (b : Bool) : (Fin.snoc (α := fun _ => Bool) h b) 0 = h 0 := by simp
        have hlast (b : Bool) : (Fin.snoc (α := fun _ => Bool) h b) (Fin.last 1) = b := rfl
        simp only [fairCoinStep, coin_apply_toReal, ↓reduceIte, Bool.false_eq_true,
          adaptiveMartingale, hinit, h0, hlast]
        cases h 0 <;> norm_num)
    (fun k hk h _ x _ => by
      interval_cases k
      · simp only [adaptiveMartingale, Fin.snoc_zero]
        cases x <;> norm_num
      · have hinit : Fin.init (Fin.snoc (α := fun _ => Bool) h x) = h := by simp
        have h0 : (Fin.snoc (α := fun _ => Bool) h x) 0 = h 0 := by simp
        have hlast : (Fin.snoc (α := fun _ => Bool) h x) (Fin.last 1) = x := rfl
        simp only [adaptiveMartingale, hinit, h0, hlast]
        cases h 0 <;> cases x <;> norm_num)
    (fun k hk h _ => by
      interval_cases k
      · rw [tsum_fintype, Fintype.sum_bool]
        simp only [fairCoinStep, coin_apply_toReal, ↓reduceIte, Bool.false_eq_true,
          adaptiveMartingale, adaptivePredVar, Fin.snoc_zero]
        norm_num
      · rw [tsum_fintype, Fintype.sum_bool]
        have hinit (b : Bool) :
            Fin.init (Fin.snoc (α := fun _ => Bool) h b) = h := by simp
        have h0 (b : Bool) : (Fin.snoc (α := fun _ => Bool) h b) 0 = h 0 := by simp
        have hlast (b : Bool) : (Fin.snoc (α := fun _ => Bool) h b) (Fin.last 1) = b := rfl
        simp only [fairCoinStep, coin_apply_toReal, ↓reduceIte, Bool.false_eq_true,
          adaptiveMartingale, adaptivePredVar, hinit, h0, hlast]
        cases h 0 <;> norm_num)
  have h0_eq : adaptiveMartingale 0 Fin.elim0 + 3 = 3 := by simp [adaptiveMartingale]
  have hexp_eq : Real.exp (-(3 : ℝ) ^ 2 / (2 * (1 + 6 * 3 / 3))) = Real.exp (-9 / 14) := by
    congr 1; norm_num
  simpa only [h0_eq, hexp_eq] using hfreedman

/-! ### 3. Infinite outcome type (`ℕ`) and `ε = 0, b = 0, v = 0` boundaries -/

theorem freedman_infinite_and_boundaries_checked :
    let stepNat : ∀ t : ℕ, (Fin t → ℕ) → PMF ℕ := fun _ _ => PMF.pure 0
    let X : ∀ k : ℕ, (Fin k → ℕ) → ℝ := fun _ _ => 0
    let V : ∀ k : ℕ, (Fin k → ℕ) → ℝ := fun _ _ => 0
    ((seqProcess stepNat 3).toOuterMeasure
      {h : Fin 3 → ℕ | ∃ (k : ℕ) (hk : k ≤ 3),
        X 0 Fin.elim0 + 0 ≤ X k (Fin.take k hk h) ∧ seqPredVar V k (Fin.take k hk h) ≤ 0}).toReal ≤
        1 ∧
    ((seqProcess stepNat 3).toOuterMeasure
      {h : Fin 3 → ℕ | ∃ (k : ℕ) (hk : k ≤ 3),
        X 0 Fin.elim0 + 1 ≤ X k (Fin.take k hk h) ∧ seqPredVar V k (Fin.take k hk h) ≤ 1}).toReal ≤
        Real.exp (-1 / 2) ∧
    ((seqProcess stepNat 3).toOuterMeasure
      {h : Fin 3 → ℕ | ∃ (k : ℕ) (hk : k ≤ 3),
        X 0 Fin.elim0 + 3 ≤ X k (Fin.take k hk h) ∧ seqPredVar V k (Fin.take k hk h) ≤ 0}).toReal ≤
        Real.exp (-9 / 4) := by
  intro stepNat X V
  have hd1 (k : ℕ) (_ : k < 3) (h : Fin k → ℕ) (_ : h ∈ (seqProcess stepNat k).support) :
      Summable fun x : ℕ => (stepNat k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) := by
    simp [X]
  have hd2 (k : ℕ) (_ : k < 3) (h : Fin k → ℕ) (_ : h ∈ (seqProcess stepNat k).support) :
      Summable fun x : ℕ =>
        (stepNat k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 := by
    simp [X]
  refine ⟨?_, ?_, ?_⟩
  · simpa using seqProcess_exists_prefix_ge_and_var_le stepNat X V
      (b := 1) (v := 0) (ε := 0) (by norm_num) (by norm_num) (by norm_num) 3 hd1 hd2
      (fun _ _ _ _ => by simp [X]) (fun _ _ _ _ _ _ => by simp [X])
      (fun _ _ _ _ => by simp [X, V])
  · have h := seqProcess_exists_prefix_ge_and_var_le stepNat X V
      (b := 0) (v := 1) (ε := 1) (by norm_num) (by norm_num) (by norm_num) 3 hd1 hd2
      (fun _ _ _ _ => by simp [X]) (fun _ _ _ _ _ _ => by simp [X])
      (fun _ _ _ _ => by simp [X, V])
    refine h.trans_eq (congrArg Real.exp ?_)
    norm_num
  · have h := seqProcess_exists_prefix_ge_and_var_le stepNat X V
      (b := 2) (v := 0) (ε := 3) (by norm_num) (by norm_num) (by norm_num) 3 hd1 hd2
      (fun _ _ _ _ => by simp [X]) (fun _ _ _ _ _ _ => by simp [X])
      (fun _ _ _ _ => by simp [X, V])
    refine h.trans_eq (congrArg Real.exp ?_)
    norm_num

/-! ### 4. Zero-variance fast-rate (`O(log (1 / δ) / T)`) Bernstein online-to-batch check -/

theorem bernstein_online_to_batch_zero_var_checked {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) [IsProbabilityMeasure D] (T : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin T => D).real
      {_S : Fin T → Z | 2 * Real.log (1 / δ) / (3 * T) <
        (T : ℝ)⁻¹ * ∑ _ : Fin T, trueRisk (fun (_ : Unit) (_ : Z) => (1 / 2 : ℝ)) D () -
          (T : ℝ)⁻¹ * ∑ _ : Fin T, (1 / 2 : ℝ)} ≤ δ := by
  let ℓ : Unit → Z → ℝ := fun _ _ => 1 / 2
  let w : Fin T → (Fin T → Z) → Unit := fun _ _ => ()
  have h := measureReal_average_trueRisk_gt_le_bernstein (D := D) (T := T)
    (ℓ := ℓ) measurable_const (w := w) (fun _ => measurable_const)
    (fun _ _ _ _ _ => rfl) (a := 0) (b := 1)
    (fun _ _ _ => ⟨by norm_num [ℓ], by norm_num [ℓ]⟩) (s2 := 0) le_rfl
    (fun _ _ => by
      simp only [ℓ, w, trueRisk_def, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, le_rfl])
    hδ hδ1
  dsimp only at h
  refine le_trans (measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hS => ?_)) h
  have h0 : Real.sqrt (2 * 0 * Real.log (1 / δ) / T) = 0 := by simp
  have h1 : 2 * (1 - (0 : ℝ)) * Real.log (1 / δ) / (3 * T) =
      2 * Real.log (1 / δ) / (3 * T) := by ring
  dsimp only [ℓ, w]
  rw [h0, h1]
  linarith

end CslibFrontierTests.BernsteinFreedman
