/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound
public import CslibFrontier.MachineLearning.PACLearning.UniformConvergenceProperty
import CslibFrontier.MachineLearning.PACLearning.AgnosticVCSharp
import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The agnostic upper bound for multiclass PAC learning on countable domains

This module proves the countable-domain agnostic upper-bound step toward the multiclass fundamental
theorem [ShalevShwartzBenDavid2014, Theorem 29.3] (#5084). If a multiclass concept class `C` on a
countable domain `α` with `k` labels N-shatters no finite set of more than `d` points, then its
Boolean loss class `lossClass C` on `α × β` shatters no finite set of more than
`6 d (log k + 1)` labeled points (`card_le_of_setShatters_lossClass_of_natarajan`): a shattered set
of `n` labeled points realizes `2 ^ n` loss patterns, while Natarajan's lemma bounds them by
`k ^ (2 d) exp (n / 3) 3 ^ d`.

Feeding this VC bound for `lossClass C` into the chaining-based uniform-convergence theorem of
`AgnosticVCSharp.lean` [Vershynin2018, Section 8.3] yields uniform convergence without a
`log (1 / ε)` factor, empirical-risk-minimization learning from

`natarajanAgnosticSampleSize d k (ε / 2) δ = (393216 d (log k + 1) + 128 log (4 / δ)) / ε²`

examples (rate `O((d (log k + 1) + log (1 / δ)) / ε²)`, matching the
`O((d log k + log (1 / δ)) / ε²)` rate of Theorem 29.3 once `k ≥ 2`), the uniform convergence
property, and agnostic PAC learnability for every class of finite Natarajan dimension on a
countable domain with finitely many labels.

The domain is assumed countable with measurable singletons and the labels finite with measurable
singletons; learners are arbitrary semantic maps without running-time claims. General measurable
domains (#2868, #3297) and the sample-complexity lower bounds of Theorem 29.3 remain open in #5084.

## Main definitions

- `natarajanAgnosticSampleSize d k ε δ`: the chaining sample size
  `(98304 d (log k + 1) + 32 log (4 / δ)) / ε²` for `ε`-representative samples.

## Main results

- `card_le_of_setShatters_lossClass_of_natarajan`: the Boolean loss class shatters at most
  `6 d (log k + 1)` labeled points.
- `measure_pi_not_isRepresentative_le_exp_of_natarajan`,
  `measure_pi_not_isRepresentative_le_of_natarajanAgnosticSampleSize_le`: uniform convergence tail
  bounds on countable domains.
- `IsERM.measure_pi_lt_error_le_exp_of_natarajan`,
  `IsERM.measure_pi_lt_error_le_of_natarajanAgnosticSampleSize_le`: agnostic ERM tail bounds on
  countable domains (agnostic step toward Theorem 29.3).
- `isPACLearnerFor_univ_of_natarajanAgnosticSampleSize_le`,
  `sampleComplexity_univ_le_of_hasFiniteNatarajanDim`,
  `hasUniformConvergence_univ_of_hasFiniteNatarajanDim`,
  `isPACLearnable_univ_of_hasFiniteNatarajanDim`: agnostic PAC learnability, sample complexity, and
  the uniform convergence property on countable domains.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.3
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- **Shattering bound for the multiclass loss class**: if `C` N-shatters no finite set of more
than `d` points and has `k ≥ 1` labels, then its Boolean loss class shatters no finite set of more
than `6 d (log k + 1)` labeled points. -/
theorem card_le_of_setShatters_lossClass_of_natarajan [Fintype β] [DecidableEq β] [Nonempty β]
    {C : ConceptClass α β} {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d)
    {W : Finset (α × β)} (hW : SetShatters (lossClass C) ↑W) :
    (W.card : ℝ) ≤ 6 * d * (Real.log (Fintype.card β) + 1) := by
  set n := W.card
  set k := Fintype.card β
  have hk : 0 < k := Fintype.card_pos
  have hpow : (2 : ℝ) ^ n ≤ (k : ℝ) ^ (2 * d) * (Real.exp (n / 3) * 3 ^ d) := calc
    (2 : ℝ) ^ n = (growthFunction (lossClass C) n : ℝ) := by
      rw [growthFunction_eq_two_pow_of_setShatters hW]
      push_cast
      rfl
    _ ≤ natarajanSum n k d := mod_cast growthFunction_lossClass_le_natarajanSum hC n
    _ ≤ (k : ℝ) ^ (2 * d) * (Real.exp (n / 3) * 3 ^ d) :=
      natarajanSum_le_pow_mul_exp_mul_pow n d hk (by norm_num)
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (3 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      _ = Real.exp 2 := by
        rw [← Real.exp_add]
        norm_num
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (mod_cast hk)
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hlog2.le (Nat.cast_nonneg n),
    mul_le_mul_of_nonneg_left hlog3 (Nat.cast_nonneg d)]

/-- The chaining sample size `(98304 d (log k + 1) + 32 log (4 / δ)) / ε²` for `ε`-representative
multiclass samples (`98304 = 16384 · 6`). -/
@[expose] noncomputable def natarajanAgnosticSampleSize (d k : ℕ) (ε δ : ℝ) : ℝ :=
  (98304 * d * (Real.log k + 1) + 32 * Real.log (4 / δ)) / ε ^ 2

private theorem mul_floor_lossDim_le (d : ℕ) {k : ℕ} (hk : 0 < k) :
    16384 * (⌊6 * (d : ℝ) * (Real.log k + 1)⌋₊ : ℝ) ≤ 98304 * d * (Real.log k + 1) := by
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have := Nat.floor_le (a := 6 * (d : ℝ) * (Real.log k + 1)) (by positivity)
  linarith

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

section Fintype

variable [Fintype β]

section Decidable

variable [DecidableEq β]

/-- Countable-domain multiclass uniform convergence without a `log (1 / ε)` factor (step toward
[ShalevShwartzBenDavid2014, Theorem 29.3], #5084): if every finite set N-shattered by `C` has at
most `d` points and `98304 d (log k + 1) ≤ m ε²`, then `m` i.i.d. examples fail to be
`ε`-representative for `C` with probability at most `4 exp (-m ε² / 32)`. -/
theorem measure_pi_not_isRepresentative_le_exp_of_natarajan (D : Measure (α × β))
    [IsProbabilityMeasure D] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 98304 * d * (Real.log (Fintype.card β) + 1) ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 32))) := by
  have : Nonempty β := (nonempty_of_isProbabilityMeasure D).map Prod.snd
  exact measure_pi_not_isRepresentative_le_exp_of_lossClass D
    (fun W hW => Nat.le_floor (card_le_of_setShatters_lossClass_of_natarajan hC hW)) hε
    ((mul_floor_lossDim_le d Fintype.card_pos).trans hm)

/-- Countable-domain multiclass uniform convergence at `natarajanAgnosticSampleSize` (step toward
[ShalevShwartzBenDavid2014, Theorem 29.3], #5084): if every finite set N-shattered by `C` has at
most `d` points and `m ≥ natarajanAgnosticSampleSize d k ε δ`, then `m` i.i.d. examples fail to be
`ε`-representative for `C` with probability at most `δ`. -/
theorem measure_pi_not_isRepresentative_le_of_natarajanAgnosticSampleSize_le (D : Measure (α × β))
    [IsProbabilityMeasure D] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hm : natarajanAgnosticSampleSize d (Fintype.card β) ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤ ENNReal.ofReal δ := by
  have : Nonempty β := (nonempty_of_isProbabilityMeasure D).map Prod.snd
  refine measure_pi_not_isRepresentative_le_of_chainingSampleSize_le_of_lossClass D
    (fun W hW => Nat.le_floor (card_le_of_setShatters_lossClass_of_natarajan hC hW)) hε hδ
    (le_trans ?_ hm)
  rw [chainingSampleSize, natarajanAgnosticSampleSize]
  exact div_le_div_of_nonneg_right
    (add_le_add_left (mul_floor_lossDim_le d Fintype.card_pos) _) (sq_nonneg ε)

/-- Countable-domain agnostic ERM exponential tail bound (step toward
[ShalevShwartzBenDavid2014, Theorem 29.3], #5084): if every finite set N-shattered by `C` has at
most `d` points and `393216 d (log k + 1) ≤ m ε²`, then under every distribution an empirical risk
minimizer for `C` misses `optimalError D C + ε` with probability at most `4 exp (-m ε² / 128)`. -/
theorem IsERM.measure_pi_lt_error_le_exp_of_natarajan (D : Measure (α × β))
    [IsProbabilityMeasure D] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} {A : Learner α β m}
    (hA : IsERM A C) {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 393216 * d * (Real.log (Fintype.card β) + 1) ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 128))) := by
  refine (measure_mono fun S hS => ?_).trans
    ((measure_pi_not_isRepresentative_le_exp_of_natarajan D hC (ε := ε / 2) (by positivity)
      (by rw [show (m : ℝ) * (ε / 2) ^ 2 = m * ε ^ 2 / 4 by ring]; linarith)).trans_eq
      (by rw [show (m : ℝ) * (ε / 2) ^ 2 / 32 = m * ε ^ 2 / 128 by ring]))
  exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)

/-- Countable-domain agnostic ERM sample-size bound (step toward [ShalevShwartzBenDavid2014,
Theorem 29.3], #5084): if every finite set N-shattered by `C` has at most `d` points and
`m ≥ natarajanAgnosticSampleSize d k (ε / 2) δ = (393216 d (log k + 1) + 128 log (4 / δ)) / ε²`,
then under every distribution an empirical risk minimizer for `C` misses `optimalError D C + ε`
with probability at most `δ`. -/
theorem IsERM.measure_pi_lt_error_le_of_natarajanAgnosticSampleSize_le (D : Measure (α × β))
    [IsProbabilityMeasure D] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} {A : Learner α β m}
    (hA : IsERM A C) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : natarajanAgnosticSampleSize d (Fintype.card β) (ε / 2) δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_not_isRepresentative_le_of_natarajanAgnosticSampleSize_le D hC
      (by positivity) hδ hm)
  exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)

end Decidable

/-- Countable-domain agnostic PAC learner step toward [ShalevShwartzBenDavid2014, Theorem 29.3]
(#5084): a class whose N-shattered finite sets have at most `d` points is agnostically `(ε, δ)`-PAC
learnable from `m ≥ natarajanAgnosticSampleSize d k (ε / 2) δ` examples, which is
`O((d (log k + 1) + log (1 / δ)) / ε²)`. -/
theorem isPACLearnerFor_univ_of_natarajanAgnosticSampleSize_le [Nonempty β] {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ}
    {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : natarajanAgnosticSampleSize d (Fintype.card β) ((ε.val : ℝ) / 2) δ.val ≤ m) :
    IsPACLearnerFor m ε δ C Set.univ := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => Classical.arbitrary β, fun D _ _ => by simp [optimalError]⟩
  obtain ⟨A, hA⟩ := exists_isERM (m := m) hne
  refine ⟨A, fun D _ _ => ?_⟩
  have h := hA.measure_pi_lt_error_le_of_natarajanAgnosticSampleSize_le D hC
    (by exact_mod_cast ε.prop.1) (by exact_mod_cast δ.prop.1) hm
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h

/-- Countable-domain agnostic sample-complexity step toward [ShalevShwartzBenDavid2014,
Theorem 29.3] (#5084): a class of finite Natarajan dimension `d` with `k` labels has agnostic
sample complexity at most `⌈natarajanAgnosticSampleSize d k (ε / 2) δ⌉`. -/
theorem sampleComplexity_univ_le_of_hasFiniteNatarajanDim [Nonempty β] {C : ConceptClass α β}
    (hC : HasFiniteNatarajanDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ Set.univ ≤
      ⌈natarajanAgnosticSampleSize ((natarajanDim C).untop hC) (Fintype.card β)
        ((ε.val : ℝ) / 2) δ.val⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_univ_of_natarajanAgnosticSampleSize_le
    (fun _ hW => hW.card_le_untop_natarajanDim hC) (Nat.le_ceil _))

end Fintype

/-- Countable-domain uniform-convergence step toward [ShalevShwartzBenDavid2014, Theorem 29.3]
(#5084): every class of finite Natarajan dimension on a countable domain with finitely many labels
has the uniform convergence property over all distributions. -/
theorem hasUniformConvergence_univ_of_hasFiniteNatarajanDim [Finite β] [DecidableEq β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) :
    HasUniformConvergence C Set.univ := by
  have := Fintype.ofFinite β
  intro ε δ hε _ hδ _
  refine ⟨⌈natarajanAgnosticSampleSize ((natarajanDim C).untop hC) (Fintype.card β) ε δ⌉₊,
    fun m hm D _ _ => measure_pi_not_isRepresentative_le_of_natarajanAgnosticSampleSize_le D
      (fun _ hW => hW.card_le_untop_natarajanDim hC) hε hδ
      ((Nat.le_ceil _).trans (by exact_mod_cast hm))⟩

/-- Countable-domain agnostic learnability step toward [ShalevShwartzBenDavid2014, Theorem 29.3]
(#5084): every class of finite Natarajan dimension on a countable domain with finitely many labels
is agnostically PAC learnable. -/
theorem isPACLearnable_univ_of_hasFiniteNatarajanDim [Finite β] [Nonempty β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) :
    IsPACLearnable C Set.univ := by
  have := Fintype.ofFinite β
  intro ε δ
  obtain ⟨d, hd⟩ := hasFiniteNatarajanDim_iff.1 hC
  exact ⟨_, isPACLearnerFor_univ_of_natarajanAgnosticSampleSize_le hd (Nat.le_ceil _)⟩

end Cslib.MachineLearning.PACLearning
