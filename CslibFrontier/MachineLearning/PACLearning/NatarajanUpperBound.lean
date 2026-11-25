/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.MachineLearning.PACLearning.ERM

/-!
# The realizable upper bound for multiclass PAC learning on countable domains

This module proves the countable-domain realizable upper-bound step toward the multiclass
fundamental theorem [ShalevShwartzBenDavid2014, Theorem 29.3] (#5084). Let `C` be a concept class
on a countable domain `α` with labels in a finite type `β` of size `k`, all of whose N-shattered
finite sets have at most `d` points. Then every consistent learner (in particular every empirical
risk minimizer) learns `C` to accuracy `ε` with confidence `1 - δ` over every distribution
realizable by `C` from

`m ≥ (8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))`

examples. Consequently every class of finite Natarajan dimension with finitely many labels on a
countable domain is PAC learnable in the realizable setting, with realizable sample complexity
`O((d log (k / ε) + log (1 / δ)) / ε)`.

The proof reuses the binary ε-net machinery (`EpsilonNet.lean` and `VCUpperBound.lean`) on the
Boolean loss class `{(x, y) ↦ [h x ≠ y] | h ∈ C}`. The misclassification pattern on labeled points
is determined by the labeling of their domain points, so Natarajan's lemma bounds the growth
function of the loss class by `natarajanSum m k d ≤ k ^ (2 d) exp (m / T) T ^ d`. Running the
binary sample-size bound (`le_of_vcSampleSize_le`) at confidence `δ / k ^ (2 d)` absorbs the
factor `k ^ (2 d)`.

The domain is assumed countable with measurable singletons and the labels finite with measurable
singletons, so every set of samples is measurable; learners are arbitrary semantic maps without
running-time claims. General measurable domains (#2868) and the sample-complexity lower bounds of
Theorem 29.3 remain open in #5084; the agnostic countable-domain upper bound is in
`NatarajanAgnostic.lean`.

## Main definitions

- `natarajanSampleSize d k ε δ`: the realizable multiclass sample size
  `(8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))`.

## Main results

- `growthFunction_lossClass_le_natarajanSum`: the loss class of a class whose N-shattered finite
  sets have at most `d` points has growth function at most `natarajanSum m k d`.
- `natarajanSum_le_pow_mul_exp_mul_pow`: `natarajanSum n k d ≤ k ^ (2 d) exp (n / T) T ^ d`.
- `natarajanSampleSize_eq_vcSampleSize`: `natarajanSampleSize` equals `vcSampleSize` at confidence
  `δ / k ^ (2 d)`.
- `IsConsistent.measure_pi_lt_error_le_of_natarajanSampleSize_le`: consistent-learner tail bound on
  countable domains (realizable step toward Theorem 29.3).
- `isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le`,
  `sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim`,
  `isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim`: realizable PAC learnability
  and sample-complexity bound on countable domains.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- **Natarajan's lemma for the loss class**: if `C` N-shatters no finite set of more than `d`
points, its Boolean loss class has growth function at most `∑_{i ≤ d} (m choose i) (k choose 2)^i`.
The misclassification pattern on labeled points is determined by the labeling of their domain
points. -/
theorem growthFunction_lossClass_le_natarajanSum [Fintype β] [DecidableEq β] {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) (m : ℕ) :
    growthFunction (lossClass C) m ≤ natarajanSum m (Fintype.card β) d := by
  refine growthFunction_le fun x => ?_
  have hsub : restriction (lossClass C) x ⊆
      (fun v i => decide (v i ≠ (x i).2)) '' ((· ∘ fun i => (x i).1) '' C) := by
    intro w hw
    obtain ⟨_, hl, hw⟩ := mem_restriction.1 hw
    obtain ⟨h, hh, rfl⟩ := mem_lossClass.1 hl
    exact ⟨h ∘ fun i => (x i).1, ⟨h, hh, rfl⟩, funext hw⟩
  calc (restriction (lossClass C) x).ncard
      ≤ ((fun v i => decide (v i ≠ (x i).2)) '' ((· ∘ fun i => (x i).1) '' C)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((· ∘ fun i => (x i).1) '' C).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ natarajanSum m (Fintype.card β) d := ncard_restriction_le_natarajanSum hC _

/-- Real-exponential form of Natarajan's lemma for sample-size bounds: with at least one label,
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i ≤ k ^ (2 d) exp (n / T) T ^ d` for every `T ≥ 1`. -/
theorem natarajanSum_le_pow_mul_exp_mul_pow (n d : ℕ) {k : ℕ} (hk : 0 < k) {T : ℝ} (hT : 1 ≤ T) :
    (natarajanSum n k d : ℝ) ≤ (k : ℝ) ^ (2 * d) * (Real.exp (n / T) * T ^ d) :=
  calc (natarajanSum n k d : ℝ)
      ≤ (∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ)) * (k : ℝ) ^ (2 * d) := by
        exact_mod_cast natarajanSum_le_sum_choose_mul n d hk
    _ ≤ Real.exp (n / T) * T ^ d * (k : ℝ) ^ (2 * d) := by
        gcongr
        exact Cslib.sum_choose_le_exp_mul_pow n d T hT
    _ = (k : ℝ) ^ (2 * d) * (Real.exp (n / T) * T ^ d) := mul_comm _ _

/-- The realizable multiclass sample size `(8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))` for
`k` labels. It equals `vcSampleSize d ε (δ / k ^ (2 d))` (`natarajanSampleSize_eq_vcSampleSize`). -/
@[expose] noncomputable def natarajanSampleSize (d k : ℕ) (ε δ : ℝ) : ℝ :=
  8 / ε * (d * Real.log (48 / ε) + 2 * d * Real.log k + Real.log (4 / δ))

/-- The realizable multiclass sample size is the binary VC sample size at confidence
`δ / k ^ (2 d)`. -/
theorem natarajanSampleSize_eq_vcSampleSize (d : ℕ) {k : ℕ} (hk : 0 < k) (ε : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : natarajanSampleSize d k ε δ = vcSampleSize d ε (δ / k ^ (2 * d)) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hK : (4 : ℝ) * k ^ (2 * d) ≠ 0 := by positivity
  rw [natarajanSampleSize, vcSampleSize, div_div_eq_mul_div, Real.log_div hK hδ.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_div (by norm_num) hδ.ne']
  push_cast; ring

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

section Fintype

variable [Fintype β]

/-- Countable-domain realizable upper-bound step toward [ShalevShwartzBenDavid2014, Theorem 29.3]
(#5084): if every finite set N-shattered by `C` has at most `d` points, `D` is realizable by `C`,
`A` is consistent with `C`, and `m ≥ (8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))` with `k`
labels, then `A` on `m` i.i.d. examples has error greater than `ε` with probability at most `δ`. -/
theorem IsConsistent.measure_pi_lt_error_le_of_natarajanSampleSize_le {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ}
    {A : Learner α β m} (hA : IsConsistent A C) {D : Measure (α × β)} [IsProbabilityMeasure D]
    (hD : IsRealizableBy D C) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : natarajanSampleSize d (Fintype.card β) ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  classical
  have : Nonempty β := (nonempty_of_isProbabilityMeasure D).map Prod.snd
  have hk : 0 < Fintype.card β := Fintype.card_pos
  set K : ℝ := (Fintype.card β : ℝ) ^ (2 * d)
  have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast hk)
  have hK : 0 < K := by positivity
  have hT : 1 ≤ 48 / ε := by rw [le_div_iff₀ hε]; linarith
  rw [natarajanSampleSize_eq_vcSampleSize d hk ε hδ] at hm
  obtain ⟨h8, hN⟩ := le_of_vcSampleSize_le hε hε1 (div_pos hδ hK)
    ((div_le_one hK).2 (hδ1.trans hK1)) hm le_rfl
  have hgrowth : 2 * (growthFunction (lossClass C) (m + m) : ℝ) ≤ δ * 2 ^ ⌈ε * m / 2⌉₊ :=
    calc 2 * (growthFunction (lossClass C) (m + m) : ℝ)
        ≤ 2 * (natarajanSum (m + m) (Fintype.card β) d : ℝ) := by
          gcongr
          exact_mod_cast growthFunction_lossClass_le_natarajanSum hC _
      _ ≤ 2 * (K * (Real.exp (((m + m : ℕ) : ℝ) / (48 / ε)) * (48 / ε) ^ d)) := by
          gcongr
          exact natarajanSum_le_pow_mul_exp_mul_pow _ _ hk hT
      _ = K * (2 * (Real.exp (((m + m : ℕ) : ℝ) / (48 / ε)) * (48 / ε) ^ d)) := by ring
      _ ≤ K * (δ / K * 2 ^ ⌈ε * m / 2⌉₊) := by gcongr
      _ = δ * 2 ^ ⌈ε * m / 2⌉₊ := by field_simp
  calc Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)}
      ≤ Measure.pi (fun _ : Fin m => D) {S | ¬ IsEpsNet D (lossClass C) ε S} :=
        measure_mono_ae (hA.ae_not_isEpsNet_of_lt_error hD ε)
    _ ≤ ENNReal.ofReal δ :=
        measure_pi_not_isEpsNet_le_of_growthFunction_le D (lossClass C) h8 hgrowth

/-- Countable-domain realizable PAC learner step toward [ShalevShwartzBenDavid2014, Theorem 29.3]
(#5084): a class whose N-shattered finite sets have at most `d` points is `(ε, δ)`-PAC learnable
over the distributions it realizes from `m ≥ natarajanSampleSize d k ε δ` examples. -/
theorem isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le [Nonempty β]
    {C : ConceptClass α β} {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d)
    {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : natarajanSampleSize d (Fintype.card β) ε.val δ.val ≤ m) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact isPACLearnerFor_realizableDistributions_empty (fun _ _ => Classical.arbitrary β) ε δ
  obtain ⟨A, hA⟩ := exists_isConsistent (m := m) hne
  refine ⟨A, fun D _ hD => ?_⟩
  simpa only [ENNReal.ofReal_coe_nnreal, IsRealizableBy.optimalError_eq_zero hD, zero_add] using
    hA.measure_pi_lt_error_le_of_natarajanSampleSize_le hC hD
      (by exact_mod_cast ε.prop.1) (by exact_mod_cast ε.prop.2.le) (by exact_mod_cast δ.prop.1)
      (by exact_mod_cast δ.prop.2.le) hm

/-- Countable-domain realizable sample-complexity step toward [ShalevShwartzBenDavid2014,
Theorem 29.3] (#5084): a class of finite Natarajan dimension `d` with `k` labels has realizable
sample complexity at most `⌈(8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))⌉`. -/
theorem sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim [Nonempty β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ (realizableDistributions C) ≤
      ⌈natarajanSampleSize ((natarajanDim C).untop hC) (Fintype.card β) ε.val δ.val⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le
    (fun _ hW => hW.card_le_untop_natarajanDim hC) (Nat.le_ceil _))

end Fintype

/-- Countable-domain realizable learnability step toward [ShalevShwartzBenDavid2014, Theorem 29.3]
(#5084): every class of finite Natarajan dimension on a countable domain with finitely many labels
is PAC learnable over the distributions it realizes. -/
theorem isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim [Finite β] [Nonempty β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) :
    IsPACLearnable C (realizableDistributions C) := by
  have := Fintype.ofFinite β
  intro ε δ
  obtain ⟨d, hd⟩ := hasFiniteNatarajanDim_iff.1 hC
  exact ⟨_, isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le hd (Nat.le_ceil _)⟩

end Cslib.MachineLearning.PACLearning
