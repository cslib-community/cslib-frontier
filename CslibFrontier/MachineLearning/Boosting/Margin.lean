/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Boosting.AdaBoost
public import CslibFrontier.MachineLearning.Rademacher.ConvexHull
public import CslibFrontier.MachineLearning.Rademacher.GrowthFunction
public import CslibFrontier.MachineLearning.Rademacher.UniformMargin
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Margin generalization bounds for boosting and AdaBoost

This module proves the margin-based generalization theory for voting methods and AdaBoost
[SchapireFreundBartlettLee1998] [MohriRostamizadehTalwalkar2018, Chapter 7]:

1. **Convex-hull generalization bounds (independent of ensemble size `T`).** Combining the
   convex-hull invariance of Rademacher complexity (`R̂_S(conv H) = R̂_S(H)`,
   `CslibFrontier.MachineLearning.Rademacher.ConvexHull`) with the fixed-`ρ` and uniform-in-`ρ`
   margin bounds (`Margin` and `UniformMargin`) yields risk bounds for every scoring function
   `f ∈ convexHull ℝ H` directly in terms of the base class `H` (`R_m(H)`, `R̂_{S_X}(H)`, or the VC
   dimension of a binary base class `B`). None of these bounds depends on the number of base
   hypotheses combined.
2. **Normalized score of AdaBoost.** `normalizedScore S A T` normalizes `-score S A T` by
   `totalVote S A T = ∑ t < T, (rounds S A t).vote S` (matching `Rademacher/Margin`'s sign
   convention `signVal true = -1`, `signVal false = +1`, and falling back to the stopped round's
   sign function if some round achieves weighted error `0`). Whenever every round `t < T` returns
   a hypothesis in `B` with weighted error `< 1/2` (`T > 0`), `normalizedScore S A T` belongs to
   `convexHull ℝ (signClass B)`, and every point misclassified by `adaBoost S A T` has nonpositive
   signed margin `signVal y * normalizedScore S A T x ≤ 0`. Thus the uniform margin bound applies
   simultaneously to **all** weak learners `A` valued in `B`, **all** round counts `T > 0`, and
   **all** margins `ρ ∈ (0, 1]`.
3. **AdaBoost empirical margin distribution bound** [SchapireFreundBartlettLee1998, Theorem 5].
   The fraction of training examples on which `normalizedScore S A T` has margin at most `ρ` is
   at most `∏ t < T, 2 εₜ ^ ((1 - ρ) / 2) (1 - εₜ) ^ ((1 + ρ) / 2)`. Against edge `γ ∈ (0, 1/2)`
   (`εₜ ≤ 1/2 - γ`) and margin `0 ≤ ρ ≤ 2 γ`, this is at most
   `((1 - 2 γ) ^ (1 - ρ) * (1 + 2 γ) ^ (1 + ρ)) ^ (T / 2)`. For `0 ≤ ρ ≤ γ`, the base factor
   is strictly less than `1` and bounded by `exp (-2 γ (γ - ρ))`, recovering AdaBoost's
   `exp (-2 γ² T)` training-error bound at `ρ = 0` and driving the `ρ`-margin loss exponentially
   to zero for all `ρ < γ`.
4. **End-to-end AdaBoost margin generalization bound.** Combining the uniform VC margin bound with
   the exponential training-margin decay bounds the true error of `adaBoost S A T` simultaneously
   for all weak learners `A` valued in `B`, all `T > 0`, and all `ρ ∈ (0, γ]`.

## Sign convention note

In `Cslib.BitString`, `signVal true = -1` and `signVal false = +1`. In `AdaBoost.lean`, `score`
negates the weighted sum of `signVal ((rounds S A t).hyp x)` so that `0 < score` predicts `true`.
Here `normalizedScore` reverses that negation (`-score / totalVote`) so it equals the convex
combination `∑ t < T, (wₜ / Z) * signVal (hₜ x) ∈ convexHull ℝ (signClass B)` matching
`Rademacher/Margin`'s signed margin `signVal y * f x`.

## Main definitions

* `Cslib.MachineLearning.Boosting.totalVote`: sum `∑ t ∈ range T, (rounds S A t).vote S` of vote
  weights across the first `T` rounds.
* `Cslib.MachineLearning.Boosting.normalizedScore`: normalized ensemble scoring function in
  `convexHull ℝ (signClass B)`.

## Main results

* `Cslib.MachineLearning.Boosting.convexHull_margin_bound`: fixed-`ρ` margin bound over
  `convexHull ℝ H` [MohriRostamizadehTalwalkar2018, Section 7.3.3, Corollary 7.5, p. 158].
* `Cslib.MachineLearning.Boosting.convexHull_uniform_margin_bound`,
  `Cslib.MachineLearning.Boosting.convexHull_uniform_empirical_margin_bound`: uniform-in-`ρ`
  margin bounds over `convexHull ℝ H`
  [MohriRostamizadehTalwalkar2018, Theorem 5.9 and Lemma 7.4].
* `Cslib.MachineLearning.Boosting.convexHull_signClass_vc_uniform_margin_bound`: uniform margin
  bound for `convexHull ℝ (signClass B)` in terms of the VC dimension `d` of `B`
  [SchapireFreundBartlettLee1998, Theorem 2]
  [MohriRostamizadehTalwalkar2018, Section 7.3.3, Corollary 7.6 fixed-`ρ` VC bound with
  uniform-in-`ρ` remark via Theorem 5.9, p. 158].
* `Cslib.MachineLearning.Boosting.normalizedScore_mem_convexHull`: `normalizedScore S A T` lies in
  `convexHull ℝ (signClass B)`.
* `Cslib.MachineLearning.Boosting.adaBoost_uniform_margin_bound_vc`: `T`-independent uniform
  margin bound for the output classifier `adaBoost S A T`
  [SchapireFreundBartlettLee1998, Theorem 2].
* `Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_prod`,
  `Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_pow`,
  `Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_exp`: exponential decay of the
  empirical margin distribution of AdaBoost [SchapireFreundBartlettLee1998, Theorem 5].
* `Cslib.MachineLearning.Boosting.adaBoost_generalization_bound_of_edge`: end-to-end true-error
  bound for AdaBoost under an edge hypothesis `εₜ ≤ 1/2 - γ` (for `ρ ∈ (0, γ]`).

## References

* [R. E. Schapire, Y. Freund, P. Bartlett, W. S. Lee, *Boosting the Margin: A New Explanation for
  the Effectiveness of Voting Methods*][SchapireFreundBartlettLee1998], Theorem 2 (uniform VC
  margin bound, §2.3, author PDF pp. 9–10) and Theorem 5 (empirical margin distribution bound, §3,
  author PDF p. 12)
* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Section 5.4, p. 96 (Theorem 5.9) and Section 7.3.3,
  pp. 157–160 (Lemma 7.4, Corollary 7.5 fixed-`ρ` Rademacher margin bound, Corollary 7.6 fixed-`ρ`
  VC margin bound with uniform-in-`ρ` remark via Theorem 5.9, and Theorem 7.7 AdaBoost empirical
  margin decay)
* [V. Koltchinskii, D. Panchenko, *Empirical margin distributions and bounding the generalization
  error of combined classifiers*][KoltchinskiiPanchenko2002]
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.MachineLearning.Boosting

open Cslib.BitString Cslib.MachineLearning Cslib.MachineLearning.PACLearning

/-! ### Convex-hull margin bounds (independent of ensemble size) -/

/-- **Fixed-margin generalization bound for convex combinations**
[MohriRostamizadehTalwalkar2018, Section 7.3.3, Corollary 7.5, p. 158]: for a
uniformly bounded base class `H : Set (α → ℝ)` on a finite domain `α`, fixed margin `ρ > 0`,
`m > 0` independent draws from `D : PMF (α × Bool)`, and `δ > 0`, with probability at least
`1 - δ` every `f ∈ convexHull ℝ H` satisfies
`Pr_D[signVal y * f x ≤ 0] ≤ R̂_{S, ρ}(f) + (2 / ρ) R_m(H) + √(log (1 / δ) / (2 m))`. -/
theorem convexHull_margin_bound {α : Type*} [Fintype α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ convexHull ℝ H, empiricalMarginLoss ρ f S +
        2 / ρ * rademacherComplexity (D.map Prod.fst) H m +
          √(Real.log (1 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * f p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  simpa only [rademacherComplexity_convexHull (D.map Prod.fst) hH m] using
    rademacherComplexity_margin_bound D hm (fun _ => abs_le_of_mem_convexHull hH) hρ hδ

/-- **Uniform margin generalization bound for convex combinations**
[MohriRostamizadehTalwalkar2018, Theorem 5.9 and Lemma 7.4] (uniform-in-`ρ` counterpart of
Corollary 7.5, Section 7.3.3, pp. 157–158): with probability at least `1 - δ`, simultaneously for
every `f ∈ convexHull ℝ H` and every `ρ ∈ (0, r]`,
```
Pr_D[signVal y * f x ≤ 0] ≤ R̂_{S, ρ}(f) + (4 / ρ) R_m(H)
  + √(log (log₂ (2 r / ρ)) / m) + √(log (2 / δ) / (2 m)).
``` -/
theorem convexHull_uniform_margin_bound {α : Type*} [Fintype α] (D : PMF (α × Bool)) {m : ℕ}
    (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ convexHull ℝ H, ∃ ρ ∈ Set.Ioc 0 r, empiricalMarginLoss ρ f S +
        4 / ρ * rademacherComplexity (D.map Prod.fst) H m +
          √(Real.log (Real.logb 2 (2 * r / ρ)) / m) +
          √(Real.log (2 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * f p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  simpa only [rademacherComplexity_convexHull (D.map Prod.fst) hH m] using
    uniform_rademacherComplexity_margin_bound D hm (fun _ => abs_le_of_mem_convexHull hH) hr hδ

/-- **Data-dependent uniform margin generalization bound for convex combinations**
[MohriRostamizadehTalwalkar2018, Theorem 5.9 and Lemma 7.4] (uniform-in-`ρ` counterpart of
Corollary 7.5, Section 7.3.3, pp. 157–158): same guarantee with the empirical Rademacher complexity
`R̂_{S_X}(H)` of the base class `H` on the unlabeled sample. -/
theorem convexHull_uniform_empirical_margin_bound {α : Type*} [Finite α] (D : PMF (α × Bool))
    {m : ℕ} (hm : 0 < m) {H : Set (α → ℝ)} {B : ℝ} (hH : ∀ h ∈ H, ∀ x, |h x| ≤ B)
    {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ convexHull ℝ H, ∃ ρ ∈ Set.Ioc 0 r, empiricalMarginLoss ρ f S +
        4 / ρ * empiricalRademacherComplexity H (fun i => (S i).1) +
          3 * √(Real.log (Real.logb 2 (2 * r / ρ)) / m) +
          3 * √(Real.log (4 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * f p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans
    (uniform_empiricalRademacherComplexity_margin_bound D hm
      (fun _ => abs_le_of_mem_convexHull hH) hr hδ)
  rintro S ⟨f, hf, ρ, hρ, hlt⟩
  exact ⟨f, hf, ρ, hρ, by rwa [empiricalRademacherComplexity_convexHull hH (fun i => (S i).1)]⟩

/-- **Uniform VC-dimension margin bound for convex combinations of binary classifiers**
[SchapireFreundBartlettLee1998, Theorem 2] [MohriRostamizadehTalwalkar2018, Section 7.3.3,
Corollary 7.6 fixed-`ρ` VC bound with uniform-in-`ρ` remark via Theorem 5.9, p. 158]: if every
finite set shattered by `C : ConceptClass α Bool` has size at most `d ≤ m`, then on a finite domain
`α`, with probability at least `1 - δ` over `S ~ D^m`, every `f ∈ convexHull ℝ (signClass C)` and
every margin `ρ ∈ (0, 1]` satisfy
```
Pr_D[signVal y * f x ≤ 0] ≤ R̂_{S, ρ}(f) + (4 / ρ) √(2 d log (e m / d) / m)
  + √(log (log₂ (2 / ρ)) / m) + √(log (2 / δ) / (2 m)).
``` -/
theorem convexHull_signClass_vc_uniform_margin_bound {α : Type*} [Finite α] (D : PMF (α × Bool))
    {m d : ℕ} (hm : 0 < m) {C : ConceptClass α Bool}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (hdm : d ≤ m)
    {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ f ∈ convexHull ℝ (signClass C), ∃ ρ ∈ Set.Ioc (0 : ℝ) 1,
        empiricalMarginLoss ρ f S +
          4 / ρ * √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) +
          √(Real.log (Real.logb 2 (2 / ρ)) / m) +
          √(Real.log (2 / δ) / (2 * m)) <
        (D.toOuterMeasure {p | signVal p.2 * f p.1 ≤ 0}).toReal}).toReal ≤ δ := by
  have := Fintype.ofFinite α
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans
    (convexHull_uniform_margin_bound (H := signClass C) D hm
      (fun _ hf => abs_le_one_of_mem_signClass hf) zero_lt_one hδ)
  rintro S ⟨f, hf, ρ, hρ, hlt⟩
  have hmul := mul_le_mul_of_nonneg_left
    (rademacherComplexity_signClass_le_vc (D.map Prod.fst) hC hdm)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hρ.1.le)
  exact ⟨f, hf, ρ, hρ, by rw [mul_one]; linarith⟩

/-! ### Normalized AdaBoost score and convex-hull membership -/

section AdaBoostScore

variable {α : Type*} {m : ℕ}

/-- Total vote weight `∑ t < T, (rounds S A t).vote S` across the first `T` rounds of AdaBoost. -/
noncomputable def totalVote (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, (rounds S A t).vote S

/-- Defining equation for `totalVote`. -/
theorem totalVote_def (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (T : ℕ) :
    totalVote S A T = ∑ t ∈ range T, (rounds S A t).vote S := by rw [totalVote]

open Classical in
/-- The **normalized scoring function** of `T` rounds of AdaBoost, scaled into `[-1, 1]` using the
`signVal` convention (`signVal true = -1`, `signVal false = +1`): if some round `t < T` has
weighted error `0`, it returns `signVal ∘ hₜ` for the first such round; otherwise it returns
`-score S A T / totalVote S A T`, i.e., `∑ t < T, (wₜ / Z) · signVal (hₜ x)`. -/
noncomputable def normalizedScore (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool)
    (T : ℕ) : α → ℝ :=
  if h : ∃ t < T, (rounds S A t).error S = 0 then
    fun x => signVal ((rounds S A (Nat.find h)).hyp x)
  else
    fun x => -score S A T x / totalVote S A T

open Classical in
/-- When some round `t < T` achieves weighted error `0`, `normalizedScore` is the sign of that
first consistent round's hypothesis. -/
theorem normalizedScore_of_exists_error_zero (S : Fin m → α × Bool)
    (A : (Fin m → ℝ) → α → Bool) {T : ℕ} (hz : ∃ t < T, (rounds S A t).error S = 0) :
    normalizedScore S A T = fun x => signVal ((rounds S A (Nat.find hz)).hyp x) := by
  rw [normalizedScore, dite_eq_left hz]

/-- When no round `t < T` has weighted error `0`, `normalizedScore` equals
`-score S A T / totalVote S A T`. -/
theorem normalizedScore_of_not_exists_error_zero (S : Fin m → α × Bool)
    (A : (Fin m → ℝ) → α → Bool) {T : ℕ} (hz : ¬ ∃ t < T, (rounds S A t).error S = 0) :
    normalizedScore S A T = fun x => -score S A T x / totalVote S A T := by
  classical
  rw [normalizedScore, dite_eq_right hz]

/-- On a round with weighted error `ε ∈ (0, 1/2]`, `voteWeight ε ≥ 0`. -/
private theorem voteWeight_nonneg {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) : 0 ≤ voteWeight ε := by
  rw [voteWeight]
  exact div_nonneg (Real.log_nonneg ((one_le_div hε₀).2 (by linarith))) zero_le_two

/-- On a round with weighted error `ε ∈ (0, 1/2)`, `voteWeight ε > 0`. -/
private theorem voteWeight_pos {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 2) : 0 < voteWeight ε := by
  rw [voteWeight]
  exact div_pos (Real.log_pos ((one_lt_div hε₀).2 (by linarith))) zero_lt_two

/-- Total vote weight is strictly positive when `T > 0` and every round has weighted error in
`(0, 1/2)`. -/
theorem totalVote_pos (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) {T : ℕ} (hT : 0 < T)
    (hε₀ : ∀ t < T, 0 < (rounds S A t).error S) (hε : ∀ t < T, (rounds S A t).error S < 1 / 2) :
    0 < totalVote S A T := by
  rw [totalVote_def]
  exact sum_pos (fun t ht => Round.vote_def _ _ ▸
    voteWeight_pos (hε₀ t (mem_range.mp ht)) (hε t (mem_range.mp ht))) ⟨0, mem_range.mpr hT⟩

/-- When `T > 0` and every round `t < T` chooses a hypothesis in `C` with weighted error `< 1/2`,
`normalizedScore S A T` lies in `convexHull ℝ (signClass C)`. -/
theorem normalizedScore_mem_convexHull {S : Fin m → α × Bool} {A : (Fin m → ℝ) → α → Bool}
    {C : ConceptClass α Bool} {T : ℕ} (hT : 0 < T)
    (hC : ∀ t < T, (rounds S A t).hyp ∈ C)
    (hε : ∀ t < T, (rounds S A t).error S < 1 / 2) :
    normalizedScore S A T ∈ convexHull ℝ (signClass C) := by
  classical
  by_cases hz : ∃ t < T, (rounds S A t).error S = 0
  · rw [normalizedScore_of_exists_error_zero S A hz]
    exact subset_convexHull ℝ (signClass C)
      (mem_signClass.2 ⟨(rounds S A (Nat.find hz)).hyp, hC _ (Nat.find_spec hz).1, rfl⟩)
  · have hε₀ : ∀ t < T, 0 < (rounds S A t).error S := fun t ht =>
      (rounds_error_nonneg S A t).lt_of_ne fun h => hz ⟨t, ht, h.symm⟩
    have hZ : 0 < totalVote S A T := totalVote_pos S A hT hε₀ hε
    have heq : normalizedScore S A T =
        ∑ t ∈ range T, ((rounds S A t).vote S / totalVote S A T) •
          fun x => signVal ((rounds S A t).hyp x) := by
      ext x
      simp only [normalizedScore_of_not_exists_error_zero S A hz, score_def, neg_neg,
        Finset.sum_apply, Finset.sum_div, Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    rw [heq]
    exact (convex_convexHull ℝ (signClass C)).sum_mem
      (fun t ht => Round.vote_def _ _ ▸ div_nonneg (voteWeight_nonneg (hε₀ t (mem_range.mp ht))
        (hε t (mem_range.mp ht)).le) hZ.le)
      (by rw [← Finset.sum_div, ← totalVote_def, div_self hZ.ne'])
      fun t ht => subset_convexHull ℝ (signClass C)
        (mem_signClass.2 ⟨(rounds S A t).hyp, hC t (mem_range.mp ht), rfl⟩)

/-- Every point misclassified by `adaBoost S A T` has nonpositive signed margin under
`normalizedScore S A T` (provided `0 < totalVote S A T` when no round has zero error). -/
theorem signVal_mul_normalizedScore_nonpos_of_adaBoost_ne {S : Fin m → α × Bool}
    {A : (Fin m → ℝ) → α → Bool} {T : ℕ} (hZ : (¬ ∃ t < T, (rounds S A t).error S = 0) →
      0 < totalVote S A T) {x : α} {y : Bool} (hne : adaBoost S A T x ≠ y) :
    signVal y * normalizedScore S A T x ≤ 0 := by
  classical
  by_cases hz : ∃ t < T, (rounds S A t).error S = 0
  · rw [adaBoost_of_exists_error_zero S A hz] at hne
    rw [normalizedScore_of_exists_error_zero S A hz, mul_comm, signVal_mul_signVal,
      ite_eq_right hne]
    norm_num
  · rw [adaBoost_of_not_exists_error_zero S A hz] at hne
    have hscore : signVal y * -score S A T x ≤ 0 := by
      cases y <;> simp only [ne_eq, decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not,
        signVal_false, signVal_true] at hne ⊢ <;> linarith
    rw [normalizedScore_of_not_exists_error_zero S A hz, ← mul_div_assoc]
    exact div_nonpos_of_nonpos_of_nonneg hscore (hZ hz).le

/-- **Uniform `T`-independent margin bound for AdaBoost**
[SchapireFreundBartlettLee1998, Theorem 2] [MohriRostamizadehTalwalkar2018, Section 7.3.3,
Corollary 7.6 fixed-`ρ` VC bound with uniform-in-`ρ` remark via Theorem 5.9, p. 158]: on a finite
domain `α`, for a base class
`C : ConceptClass α Bool` with every shattered finite set of size at most
`d ≤ m`, with probability at least `1 - δ` over `S ~ D^m`, **every** weak learner `A` whose
first `T > 0` rounds lie in `C` with weighted errors `< 1/2` and **every** margin `ρ ∈ (0, 1]`
satisfy
```
Pr_D[adaBoost S A T x ≠ y] ≤ R̂_{S, ρ}(normalizedScore S A T)
  + (4 / ρ) √(2 d log (e m / d) / m) + √(log (log₂ (2 / ρ)) / m) + √(log (2 / δ) / (2 m)).
```
Note the bound does not depend on the number of boosting rounds `T`. -/
theorem adaBoost_uniform_margin_bound_vc {α : Type*} [Finite α] (D : PMF (α × Bool))
    {m d : ℕ} (hm : 0 < m) {C : ConceptClass α Bool}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (hdm : d ≤ m)
    {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ (A : (Fin m → ℝ) → α → Bool) (T : ℕ), 0 < T ∧
        (∀ t < T, (rounds S A t).hyp ∈ C) ∧
        (∀ t < T, (rounds S A t).error S < 1 / 2) ∧
        ∃ ρ ∈ Set.Ioc (0 : ℝ) 1,
          empiricalMarginLoss ρ (normalizedScore S A T) S +
            4 / ρ * √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) +
            √(Real.log (Real.logb 2 (2 / ρ)) / m) +
            √(Real.log (2 / δ) / (2 * m)) <
          (D.toOuterMeasure {p | adaBoost S A T p.1 ≠ p.2}).toReal}).toReal ≤ δ := by
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans
    (convexHull_signClass_vc_uniform_margin_bound D hm hC hdm hδ)
  rintro S ⟨A, T, hT, hmem, hε, ρ, hρ, hlt⟩
  refine ⟨normalizedScore S A T, normalizedScore_mem_convexHull hT hmem hε, ρ, hρ, ?_⟩
  have hZ : (¬ ∃ t < T, (rounds S A t).error S = 0) → 0 < totalVote S A T := fun hz =>
    totalVote_pos S A hT
      (fun t ht => (rounds_error_nonneg S A t).lt_of_ne fun h => hz ⟨t, ht, h.symm⟩) hε
  exact lt_of_lt_of_le hlt (Probability.PMF.toOuterMeasure_toReal_mono D fun _ =>
    signVal_mul_normalizedScore_nonpos_of_adaBoost_ne hZ)

end AdaBoostScore

/-! ### Empirical margin distribution of AdaBoost (Schapire–Freund–Bartlett–Lee 1998, Thm. 5) -/

section TrainingMargin

variable {α : Type*} {m : ℕ}

/-- One-round factor identity: for `0 < ε < 1`,
`exp (ρ * voteWeight ε) * (2 * √(ε * (1 - ε))) = 2 * ε ^ ((1 - ρ) / 2) * (1 - ε) ^ ((1 + ρ) / 2)`.
-/
private theorem exp_mul_voteWeight_mul_two_sqrt {ε ρ : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    exp (ρ * voteWeight ε) * (2 * √(ε * (1 - ε))) =
      2 * ε ^ ((1 - ρ) / 2) * (1 - ε) ^ ((1 + ρ) / 2) := by
  have h1m : 0 < 1 - ε := by linarith
  have harg : ρ * (Real.log ((1 - ε) / ε) / 2) = Real.log ((1 - ε) / ε) * (ρ / 2) := by ring
  have hexp : exp (ρ * voteWeight ε) = (1 - ε) ^ (ρ / 2) * ε ^ (-(ρ / 2)) := by
    rw [voteWeight, harg, ← Real.rpow_def_of_pos (div_pos h1m hε₀),
      Real.div_rpow h1m.le hε₀.le, div_eq_mul_inv, Real.rpow_neg hε₀.le]
  have hsqrt : √(ε * (1 - ε)) = ε ^ ((1 : ℝ) / 2) * (1 - ε) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hε₀.le h1m.le]
  rw [hexp, hsqrt]
  calc (1 - ε) ^ (ρ / 2) * ε ^ (-(ρ / 2)) *
        (2 * (ε ^ ((1 : ℝ) / 2) * (1 - ε) ^ ((1 : ℝ) / 2)))
      = 2 * (ε ^ ((1 : ℝ) / 2) * ε ^ (-(ρ / 2))) *
          ((1 - ε) ^ ((1 : ℝ) / 2) * (1 - ε) ^ (ρ / 2)) := by ring
    _ = 2 * ε ^ ((1 - ρ) / 2) * (1 - ε) ^ ((1 + ρ) / 2) := by
        rw [← Real.rpow_add hε₀, ← Real.rpow_add h1m]
        ring_nf

/-- Monotonicity of `ε ↦ ε ^ p * (1 - ε) ^ (1 - p)` on `(0, p]`, by `log t ≤ t - 1`. -/
private theorem rpow_mul_one_sub_rpow_le {ε b p : ℝ} (hε₀ : 0 < ε) (hεb : ε ≤ b)
    (hbp : b ≤ p) (hp : p < 1) :
    ε ^ p * (1 - ε) ^ (1 - p) ≤ b ^ p * (1 - b) ^ (1 - p) := by
  have hb₀ : 0 < b := lt_of_lt_of_le hε₀ hεb
  have hb₁ : 0 < 1 - b := by linarith
  have hε₁ : 0 < 1 - ε := by linarith
  have hlog : p * Real.log (ε / b) + (1 - p) * Real.log ((1 - ε) / (1 - b)) ≤ 0 := by
    have h2 := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hε₁ hb₁)) (by linarith : 0 ≤ 1 - p)
    refine (add_le_add
      (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hε₀ hb₀)) (hb₀.le.trans hbp))
      h2).trans ?_
    rw [show p * (ε / b - 1) + (1 - p) * ((1 - ε) / (1 - b) - 1) =
      (b - ε) * (b - p) / (b * (1 - b)) by field_simp; ring]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by positivity)
  rw [Real.log_div hε₀.ne' hb₀.ne', Real.log_div hε₁.ne' hb₁.ne'] at hlog
  rw [Real.rpow_def_of_pos hε₀, Real.rpow_def_of_pos hε₁, Real.rpow_def_of_pos hb₀,
    Real.rpow_def_of_pos hb₁, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- For `y > 1`, `2 * log y < y - y⁻¹`, since `(y - y⁻¹ - 2 log y)' = (1 - y⁻¹)² > 0`. -/
private theorem two_mul_log_lt_sub_inv {y : ℝ} (hy : 1 < y) : 2 * Real.log y < y - y⁻¹ := by
  let g : ℝ → ℝ := fun t => t - t⁻¹ - 2 * Real.log t
  have hmono : StrictMonoOn g (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1)
      ((continuousOn_id.sub (continuousOn_inv₀.mono fun _ ht => ( zero_lt_one.trans_le ht).ne')).sub
        ((Real.continuousOn_log.mono fun _ ht => (zero_lt_one.trans_le ht).ne').const_mul 2))
      fun t ht => ?_
    rw [interior_Ici] at ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
    have hd : HasDerivAt g (1 - -(t ^ 2)⁻¹ - 2 * t⁻¹) t :=
      ((hasDerivAt_id t).sub (hasDerivAt_inv ht0)).sub ((Real.hasDerivAt_log ht0).const_mul 2)
    rw [hd.deriv, show 1 - -(t ^ 2)⁻¹ - 2 * t⁻¹ = (1 - t⁻¹) ^ 2 by field_simp; ring]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ ht).ne')
  have hlt : g 1 < g y := hmono le_rfl hy.le hy
  simp only [g, inv_one, sub_self, Real.log_one, mul_zero] at hlt
  linarith

/-- For `x ∈ (0, 1)`, `(1 - x / 2) * log (1 - x) + (1 + x / 2) * log (1 + x) < 0`. -/
private theorem log_margin_factor_neg {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    (1 - x / 2) * Real.log (1 - x) + (1 + x / 2) * Real.log (1 + x) < 0 := by
  let f : ℝ → ℝ := fun t => (1 - t / 2) * Real.log (1 - t) + (1 + t / 2) * Real.log (1 + t)
  have hdf {t : ℝ} (h1m : 0 < 1 - t) (h1p : 0 < 1 + t) : HasDerivAt f
      ((2 * Real.log ((1 + t) / (1 - t)) -
        ((1 + t) / (1 - t) - ((1 + t) / (1 - t))⁻¹)) / 4) t := by
    have hd1 := ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const 2)).mul
      ((Real.hasDerivAt_log h1m.ne').comp t ((hasDerivAt_const t 1).sub (hasDerivAt_id t)))
    have hd2 := ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).div_const 2)).mul
      ((Real.hasDerivAt_log h1p.ne').comp t ((hasDerivAt_const t 1).add (hasDerivAt_id t)))
    convert (show HasDerivAt f _ t from hd1.add hd2) using 1
    rw [Real.log_div h1p.ne' h1m.ne']
    simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, id_eq]
    field_simp
    ring
  have hanti : StrictAntiOn f (Set.Icc 0 x) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 x)
      (fun t ht => (hdf (sub_pos.mpr (ht.2.trans_lt hx₁))
        (add_pos_of_pos_of_nonneg zero_lt_one ht.1)).continuousAt.continuousWithinAt)
      fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hdf (sub_pos.mpr (ht.2.trans hx₁)) (add_pos zero_lt_one ht.1)).deriv]
    have hy : 1 < (1 + t) / (1 - t) :=
      (one_lt_div (sub_pos.mpr (ht.2.trans hx₁))).2 (by linarith [ht.1])
    exact div_neg_of_neg_of_pos (sub_neg.mpr (two_mul_log_lt_sub_inv hy)) (by norm_num)
  simpa [f] using hanti ⟨le_rfl, hx₀.le⟩ ⟨hx₀.le, le_rfl⟩ hx₀

/-- Rewrite `((1 - 2 γ) ^ (1 - ρ)) * ((1 + 2 γ) ^ (1 + ρ))` as `exp` of a log combination. -/
private theorem exp_log_marginFactor {γ ρ : ℝ} (h1m : 0 < 1 - 2 * γ) (h1p : 0 < 1 + 2 * γ) :
    exp ((1 - ρ) * Real.log (1 - 2 * γ) + (1 + ρ) * Real.log (1 + 2 * γ)) =
      (1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ) := by
  rw [Real.exp_add, mul_comm (1 - ρ), Real.rpow_def_of_pos h1m,
    mul_comm (1 + ρ), Real.rpow_def_of_pos h1p]

/-- Convex-combination identity splitting the log margin factor between `ρ = 0` and `ρ = γ`. -/
private theorem log_marginFactor_affine {γ ρ : ℝ} (hγ : γ ≠ 0) :
    (1 - ρ) * Real.log (1 - 2 * γ) + (1 + ρ) * Real.log (1 + 2 * γ) =
      (1 - ρ / γ) * (Real.log (1 - 2 * γ) + Real.log (1 + 2 * γ)) +
        (ρ / γ) * ((1 - γ) * Real.log (1 - 2 * γ) + (1 + γ) * Real.log (1 + 2 * γ)) := by
  field_simp
  ring

private theorem log_marginFactor_at_edge_neg {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1 / 2) :
    (1 - γ) * Real.log (1 - 2 * γ) + (1 + γ) * Real.log (1 + 2 * γ) < 0 := by
  simpa [show (2 * γ) / 2 = γ by ring] using
    log_margin_factor_neg (by linarith : 0 < 2 * γ) (by linarith : 2 * γ < 1)

/-- For `0 < γ < 1/2` and `0 ≤ ρ ≤ γ`, the per-round AdaBoost margin factor
`(1 - 2 γ) ^ (1 - ρ) * (1 + 2 γ) ^ (1 + ρ)` is strictly less than `1`. -/
theorem marginFactor_lt_one {γ ρ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1 / 2)
    (hρ₀ : 0 ≤ ρ) (hργ : ρ ≤ γ) :
    (1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ) < 1 := by
  have h1m : 0 < 1 - 2 * γ := by linarith
  have h1p : 0 < 1 + 2 * γ := by linarith
  have hzero : Real.log (1 - 2 * γ) + Real.log (1 + 2 * γ) < 0 := by
    rw [← Real.log_mul h1m.ne' h1p.ne']
    exact Real.log_neg (by positivity) (by nlinarith)
  have hsum_neg : (1 - ρ) * Real.log (1 - 2 * γ) + (1 + ρ) * Real.log (1 + 2 * γ) < 0 := by
    rw [log_marginFactor_affine hγ₀.ne']
    rcases eq_or_lt_of_le hρ₀ with rfl | hρ_pos
    · simpa using hzero
    · have h1 := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr ((div_le_one hγ₀).2 hργ)) hzero.le
      have h2 := mul_neg_of_pos_of_neg (div_pos hρ_pos hγ₀) (log_marginFactor_at_edge_neg hγ₀ hγ₁)
      linarith
  simpa only [exp_log_marginFactor h1m h1p, Real.exp_zero] using Real.exp_lt_exp.mpr hsum_neg

/-- Exponential upper bound for the per-round margin factor: for `0 < γ < 1/2` and `0 ≤ ρ ≤ γ`,
`√((1 - 2 γ) ^ (1 - ρ) * (1 + 2 γ) ^ (1 + ρ)) ≤ exp (-2 γ (γ - ρ))`. At `ρ = 0`, this recovers
`exp (-2 γ²)`. -/
theorem sqrt_marginFactor_le_exp {γ ρ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1 / 2)
    (hρ₀ : 0 ≤ ρ) (hργ : ρ ≤ γ) :
    √((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ)) ≤ exp (-(2 * γ * (γ - ρ))) := by
  have h1m : 0 < 1 - 2 * γ := by linarith
  have h1p : 0 < 1 + 2 * γ := by linarith
  have hzero : Real.log (1 - 2 * γ) + Real.log (1 + 2 * γ) ≤ -(4 * γ ^ 2) := by
    rw [← Real.log_mul h1m.ne' h1p.ne']
    have hlog := Real.log_le_sub_one_of_pos (mul_pos h1m h1p)
    linarith [show (1 - 2 * γ) * (1 + 2 * γ) - 1 = -(4 * γ ^ 2) by ring]
  have hle : (1 - ρ) * Real.log (1 - 2 * γ) + (1 + ρ) * Real.log (1 + 2 * γ) ≤
      -(4 * γ * (γ - ρ)) := by
    rw [log_marginFactor_affine hγ₀.ne']
    have h1 := mul_le_mul_of_nonneg_left hzero (sub_nonneg.mpr ((div_le_one hγ₀).2 hργ))
    have h2 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hρ₀ hγ₀.le)
      (log_marginFactor_at_edge_neg hγ₀ hγ₁).le
    have h3 : (1 - ρ / γ) * (-(4 * γ ^ 2)) = -(4 * γ * (γ - ρ)) := by field_simp
    linarith
  rw [Real.sqrt_le_left (by positivity), ← Real.exp_nat_mul, ← exp_log_marginFactor h1m h1p]
  exact Real.exp_le_exp.mpr (hle.trans_eq (by push_cast; ring))

open OnlineLearning.Experts in
/-- **AdaBoost empirical margin distribution bound, product form**
[SchapireFreundBartlettLee1998, Theorem 5]: for any `ρ < 1`, if every round `t < T` has weighted
error `εₜ < 1/2` (so positive vote weight `wₜ > 0`, and if some round hits `εₜ = 0` every point
has margin `+1`), the fraction of sample points with signed margin at most `ρ` under
`normalizedScore S A T` is at most
`∏ t < T, 2 εₜ ^ ((1 - ρ) / 2) (1 - εₜ) ^ ((1 + ρ) / 2)`. -/
theorem marginCount_normalizedScore_le_prod (S : Fin m → α × Bool)
    (A : (Fin m → ℝ) → α → Bool) {T : ℕ} (hT : 0 < T) {ρ : ℝ} (hρ : ρ < 1)
    (hε : ∀ t < T, (rounds S A t).error S < 1 / 2) :
    ((univ.filter fun i : Fin m =>
      signVal (S i).2 * normalizedScore S A T (S i).1 ≤ ρ).card : ℝ) / m ≤
      ∏ t ∈ range T, 2 * (rounds S A t).error S ^ ((1 - ρ) / 2) *
        (1 - (rounds S A t).error S) ^ ((1 + ρ) / 2) := by
  have hprod_nonneg : 0 ≤ ∏ t ∈ range T,
      2 * (rounds S A t).error S ^ ((1 - ρ) / 2) *
        (1 - (rounds S A t).error S) ^ ((1 + ρ) / 2) :=
    prod_nonneg fun t ht => mul_nonneg
      (mul_nonneg zero_le_two (Real.rpow_nonneg (rounds_error_nonneg S A t) _))
      (Real.rpow_nonneg (by linarith [hε t (mem_range.mp ht)]) _)
  by_cases hz : ∃ t < T, (rounds S A t).error S = 0
  · rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr fun i _ hle => ?_), Nat.cast_zero, zero_div]
    · exact hprod_nonneg
    · simp only [normalizedScore_of_exists_error_zero S A hz,
        hyp_eq_of_error_eq_zero S A (Nat.find_spec hz).2 i, signVal_mul_self] at hle
      linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hprod_nonneg
  have : NeZero m := ⟨hm.ne'⟩
  have hε₀ : ∀ t < T, 0 < (rounds S A t).error S := fun t ht =>
    (rounds_error_nonneg S A t).lt_of_ne fun h => hz ⟨t, ht, h.symm⟩
  have hε₁ : ∀ t < T, (rounds S A t).error S < 1 := fun t ht => by linarith [hε t ht]
  have hZ : 0 < totalVote S A T := totalVote_pos S A hT hε₀ hε
  have hcount : ((univ.filter fun i : Fin m =>
      signVal (S i).2 * normalizedScore S A T (S i).1 ≤ ρ).card : ℝ) *
      exp (-(ρ * totalVote S A T)) ≤ potential exp (lossSeq S A) T := by
    rw [card_filter, Nat.cast_sum, sum_mul, potential]
    refine sum_le_sum fun i _ => ?_
    split_ifs with hi
    · rw [Nat.cast_one, one_mul, weight, ← exp_sum, sum_lossSeq]
      rw [normalizedScore_of_not_exists_error_zero S A hz, ← mul_div_assoc, div_le_iff₀ hZ,
        mul_neg, mul_comm] at hi
      exact Real.exp_le_exp.mpr (by linarith)
    · simpa only [Nat.cast_zero, zero_mul] using (weight_pos (fun _ _ _ => exp_pos _) i).le
  have hpot : potential exp (lossSeq S A) T =
      m * ∏ t ∈ range T, 2 * √((rounds S A t).error S * (1 - (rounds S A t).error S)) :=
    potential_lossSeq_eq S A hz hε₁
  have hfac : exp (ρ * totalVote S A T) *
      ∏ t ∈ range T, 2 * √((rounds S A t).error S * (1 - (rounds S A t).error S)) =
      ∏ t ∈ range T, 2 * (rounds S A t).error S ^ ((1 - ρ) / 2) *
        (1 - (rounds S A t).error S) ^ ((1 + ρ) / 2) := by
    rw [totalVote_def, mul_sum, exp_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun t ht => ?_
    rw [Round.vote_def]
    exact exp_mul_voteWeight_mul_two_sqrt (hε₀ t (mem_range.mp ht)) (hε₁ t (mem_range.mp ht))
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [div_le_iff₀ hm_pos, ← hfac]
  calc ((univ.filter fun i : Fin m =>
        signVal (S i).2 * normalizedScore S A T (S i).1 ≤ ρ).card : ℝ)
      = ((univ.filter fun i : Fin m =>
          signVal (S i).2 * normalizedScore S A T (S i).1 ≤ ρ).card : ℝ) *
          exp (-(ρ * totalVote S A T)) * exp (ρ * totalVote S A T) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ potential exp (lossSeq S A) T * exp (ρ * totalVote S A T) :=
        mul_le_mul_of_nonneg_right hcount (exp_pos _).le
    _ = (exp (ρ * totalVote S A T) *
          ∏ t ∈ range T, 2 * √((rounds S A t).error S * (1 - (rounds S A t).error S))) * m := by
        rw [hpot]; ring

/-- **AdaBoost empirical margin distribution bound, edge form**
[SchapireFreundBartlettLee1998, Theorem 5]: if every round `t < T` has weighted error at most
`1/2 - γ` with `0 < γ < 1/2`, then for every margin `ρ ∈ [0, 2 γ]`,
```
Pr_{i ∼ S}[yᵢ · normalizedScore(xᵢ) ≤ ρ] ≤ ((1 - 2 γ)^(1 - ρ) (1 + 2 γ)^(1 + ρ))^(T / 2).
``` -/
theorem marginCount_normalizedScore_le_pow (S : Fin m → α × Bool)
    (A : (Fin m → ℝ) → α → Bool) {T : ℕ} (hT : 0 < T) {γ ρ : ℝ}
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1 / 2) (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ 2 * γ)
    (hε : ∀ t < T, (rounds S A t).error S ≤ 1 / 2 - γ) :
    ((univ.filter fun i : Fin m =>
      signVal (S i).2 * normalizedScore S A T (S i).1 ≤ ρ).card : ℝ) / m ≤
      (√((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ))) ^ T := by
  have hρ_lt : ρ < 1 := by linarith
  have hε_lt : ∀ t < T, (rounds S A t).error S < 1 / 2 := fun t ht => by linarith [hε t ht]
  refine (marginCount_normalizedScore_le_prod S A hT hρ_lt hε_lt).trans ?_
  have hterm : ∀ t ∈ range T,
      2 * (rounds S A t).error S ^ ((1 - ρ) / 2) *
        (1 - (rounds S A t).error S) ^ ((1 + ρ) / 2) ≤
      √((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ)) := by
    intro t ht
    rcases eq_or_lt_of_le (rounds_error_nonneg S A t) with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith), mul_zero, zero_mul]
      exact Real.sqrt_nonneg _
    · set ε := (rounds S A t).error S
      have hmono := rpow_mul_one_sub_rpow_le hpos (hε t (mem_range.mp ht))
        (show 1 / 2 - γ ≤ (1 - ρ) / 2 by linarith) (show (1 - ρ) / 2 < 1 by linarith)
      rw [show 1 - (1 - ρ) / 2 = (1 + ρ) / 2 by ring] at hmono
      have h1m : 0 < 1 - 2 * γ := by linarith
      have h1p : 0 < 1 + 2 * γ := by linarith
      have hhalf_eq : 2 * (1 / 2 - γ) ^ ((1 - ρ) / 2) * (1 - (1 / 2 - γ)) ^ ((1 + ρ) / 2) =
          √((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ)) := by
        rw [show 1 - (1 / 2 - γ : ℝ) = (1 + 2 * γ) / 2 by ring,
          show (1 / 2 - γ : ℝ) = (1 - 2 * γ) / 2 by ring,
          Real.div_rpow h1m.le zero_le_two, Real.div_rpow h1p.le zero_le_two,
          Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg h1m.le _)
            (Real.rpow_nonneg h1p.le _),
          ← Real.rpow_mul h1m.le, ← Real.rpow_mul h1p.le]
        have h2pow : (2 : ℝ) ^ ((1 - ρ) / 2) * (2 : ℝ) ^ ((1 + ρ) / 2) = 2 := by
          rw [← Real.rpow_add zero_lt_two,
            show (1 - ρ) / 2 + (1 + ρ) / 2 = 1 by ring, Real.rpow_one]
        rw [mul_assoc, ← mul_div_mul_comm, h2pow, mul_div_cancel₀ _ two_ne_zero]
        ring_nf
      calc 2 * ε ^ ((1 - ρ) / 2) * (1 - ε) ^ ((1 + ρ) / 2)
          = 2 * (ε ^ ((1 - ρ) / 2) * (1 - ε) ^ ((1 + ρ) / 2)) := by ring
        _ ≤ 2 * ((1 / 2 - γ) ^ ((1 - ρ) / 2) * (1 - (1 / 2 - γ)) ^ ((1 + ρ) / 2)) :=
            mul_le_mul_of_nonneg_left hmono zero_le_two
        _ = √((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ)) := by
            rw [← mul_assoc, hhalf_eq]
  calc ∏ t ∈ range T, 2 * (rounds S A t).error S ^ ((1 - ρ) / 2) *
        (1 - (rounds S A t).error S) ^ ((1 + ρ) / 2)
      ≤ ∏ _t ∈ range T, √((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ)) :=
        prod_le_prod₀ (fun t ht => by
          have he0 : 0 ≤ (rounds S A t).error S := rounds_error_nonneg S A t
          have he1 : 0 ≤ 1 - (rounds S A t).error S := by linarith [hε t (mem_range.mp ht)]
          exact mul_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg he0 _))
            (Real.rpow_nonneg he1 _)) hterm
    _ = (√((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ))) ^ T := by
        rw [prod_const, card_range]

/-- **Exponential decay of AdaBoost's empirical margin loss**: if every round `t < T` has
weighted error at most `1/2 - γ` (`0 < γ < 1/2`), then for every margin `ρ ∈ [0, γ]`, the fraction
of training examples with margin at most `ρ` is at most `exp (-2 γ (γ - ρ) T)`. Setting `ρ = 0`
recovers `exp (-2 γ² T)`. -/
theorem marginCount_normalizedScore_le_exp (S : Fin m → α × Bool)
    (A : (Fin m → ℝ) → α → Bool) {T : ℕ} (hT : 0 < T) {γ ρ : ℝ}
    (hγ₀ : 0 < γ) (hγ₁ : γ < 1 / 2) (hρ₀ : 0 ≤ ρ) (hργ : ρ ≤ γ)
    (hε : ∀ t < T, (rounds S A t).error S ≤ 1 / 2 - γ) :
    ((univ.filter fun i : Fin m =>
      signVal (S i).2 * normalizedScore S A T (S i).1 ≤ ρ).card : ℝ) / m ≤
      exp (-(2 * γ * (γ - ρ) * T)) := by
  refine (marginCount_normalizedScore_le_pow S A hT hγ₀ hγ₁ hρ₀ (by linarith) hε).trans ?_
  calc (√((1 - 2 * γ) ^ (1 - ρ) * (1 + 2 * γ) ^ (1 + ρ))) ^ T
      ≤ (exp (-(2 * γ * (γ - ρ)))) ^ T :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_marginFactor_le_exp hγ₀ hγ₁ hρ₀ hργ) T
    _ = exp (-(2 * γ * (γ - ρ) * T)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **End-to-end margin generalization bound for AdaBoost under an edge assumption**
[SchapireFreundBartlettLee1998, Theorems 2 and 5] [MohriRostamizadehTalwalkar2018, Section 7.3.3,
Corollary 7.6 fixed-`ρ` VC bound with uniform-in-`ρ` remark via Theorem 5.9 and Theorem 7.7,
pp. 158–160]: combines `adaBoost_uniform_margin_bound_vc` with
`marginCount_normalizedScore_le_exp` (`R̂_{S, ρ} ≤ #{i | margin ≤ ρ} / m ≤
exp (-2 γ (γ - ρ) T)`). On a finite domain `α`, for a base class `C` of VC dimension at most
`d ≤ m`, with probability at least `1 - δ` over `S ~ D^m`, for every weak learner `A` returning
hypotheses in `C` with round errors `≤ 1/2 - γ` (`0 < γ < 1/2`), every `T > 0`, and every margin
`ρ ∈ (0, γ]`,
```
Pr_D[adaBoost S A T x ≠ y] ≤ exp (-2 γ (γ - ρ) T)
  + (4 / ρ) √(2 d log (e m / d) / m) + √(log (log₂ (2 / ρ)) / m) + √(log (2 / δ) / (2 m)).
``` -/
theorem adaBoost_generalization_bound_of_edge {α : Type*} [Finite α] (D : PMF (α × Bool))
    {m d : ℕ} (hm : 0 < m) {C : ConceptClass α Bool}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (hdm : d ≤ m)
    {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ (A : (Fin m → ℝ) → α → Bool) (T : ℕ) (γ ρ : ℝ),
        0 < T ∧ 0 < γ ∧ γ < 1 / 2 ∧ 0 < ρ ∧ ρ ≤ γ ∧
        (∀ t < T, (rounds S A t).hyp ∈ C) ∧
        (∀ t < T, (rounds S A t).error S ≤ 1 / 2 - γ) ∧
          exp (-(2 * γ * (γ - ρ) * T)) +
            4 / ρ * √(2 * (d * Real.log (Real.exp 1 * m / d)) / m) +
            √(Real.log (Real.logb 2 (2 / ρ)) / m) +
            √(Real.log (2 / δ) / (2 * m)) <
          (D.toOuterMeasure {p | adaBoost S A T p.1 ≠ p.2}).toReal}).toReal ≤ δ := by
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans
    (adaBoost_uniform_margin_bound_vc D hm hC hdm hδ)
  rintro S ⟨A, T, γ, ρ, hT, hγ₀, hγ₁, hρ₀, hργ, hmem, hε, hlt⟩
  have hε_lt : ∀ t < T, (rounds S A t).error S < 1 / 2 := fun t ht => by linarith [hε t ht]
  have hloss := (empiricalMarginLoss_le_count_div hρ₀ (normalizedScore S A T) S).trans
    (marginCount_normalizedScore_le_exp S A hT hγ₀ hγ₁ hρ₀.le hργ hε)
  refine ⟨A, T, hT, hmem, hε_lt, ρ, ⟨hρ₀, by linarith⟩, ?_⟩
  linarith

end TrainingMargin

end Cslib.MachineLearning.Boosting
