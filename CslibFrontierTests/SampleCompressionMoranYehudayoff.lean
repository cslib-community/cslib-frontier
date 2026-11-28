/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.MachineLearning.PACLearning.Compression.Agnostic
import CslibFrontier.MachineLearning.PACLearning.Compression.MoranYehudayoff
import CslibFrontier.MachineLearning.PACLearning.Compression.Thresholds

/-!
# Tests for Moran–Yehudayoff sample compression and agnostic compression bounds

Ordinary-import client (no `import all`) exercising:
1. Algebraic bounds and positivity of `moranYehudayoffSubsampleSize`,
   `moranYehudayoffMajoritySize`, `moranYehudayoffCompressionSize`, and
   `moranYehudayoffVCCompressionSize`.
2. Boundary instantiations of `moranYehudayoffScheme` and
   `exists_sampleCompressionScheme_iff_hasFiniteVCDim`:
   - the empty domain `Empty` and empty class `∅`,
   - the singleton class `{fun _ => false}` (`d = 0, d* = 0`),
   - an **uncountable** domain (`ℝ`) with non-trivial threshold concepts (`d = 1`, no measurability
     or countability assumption),
   - an explicit **negative witness** showing `(Set.univ : ConceptClass ℕ Bool)` has **no** finite
     sample compression scheme (`¬ ∃ k, Nonempty (SampleCompressionScheme Set.univ k)`).
3. Unordered-subset plus side-information decoder (`exists_finset_compression_of_dualVCDim`) and
   majority voting (`exists_majority_subsamples_of_dualVCDim`).
4. Seven-way fundamental theorem TFAE (`tfae_hasFiniteVCDim_compression`) on `ℕ`.
5. Agnostic (`GeneralCompressionScheme`) checks on a concrete non-realizable noisy distribution on
   `Bool × Bool`, instantiating `heldOutError_le_one`, `heldOutError_le_empiricalMiscount_div`,
   Hoeffding (`measure_pi_abs_sub_heldOutError_le`, `measure_pi_hoeffding_gt_le`), Bernstein
   (`measure_pi_bernstein_tail_le`, `measure_pi_bernstein_gt_le`), relaxed fast rate
   (`measure_pi_fastRate_gt_le`), zero held-out error (`measure_pi_zero_heldOut_gt_le`),
   `SampleCompressionScheme.toGeneral`, and a numerical separation verifying that the fast rate
   beats Hoeffding near `q = 0`.
-/

set_option linter.privateModule false

open MeasureTheory Set Cslib.MachineLearning.OnlineLearning.MistakeBound
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning.Tests

/-! ### Explicit compression-size bounds -/

example : 0 < moranYehudayoffSubsampleSize 0 := moranYehudayoffSubsampleSize_pos 0
example : 0 < moranYehudayoffMajoritySize 0 := moranYehudayoffMajoritySize_pos 0
example : moranYehudayoffSubsampleSize 0 ≤ 60 := by
  simpa using moranYehudayoffSubsampleSize_le 0
example : moranYehudayoffSubsampleSize 1 ≤ 180 := by
  simpa using moranYehudayoffSubsampleSize_le 1
example : moranYehudayoffMajoritySize 0 ≤ 1440 := by
  simpa using moranYehudayoffMajoritySize_le 0
example : moranYehudayoffCompressionSize 1 1 ≤ 6624 * 180 := by
  simpa using moranYehudayoffCompressionSize_le 1 1
example : moranYehudayoffVCCompressionSize 1 ≤ (5184 * 4 + 1440) * 180 := by
  simpa using moranYehudayoffVCCompressionSize_le 1

/-! ### Boundary cases: empty domain, empty class, singleton class -/

example : ∃ k : ℕ, Nonempty (SampleCompressionScheme (∅ : ConceptClass Empty Bool) k) :=
  (exists_sampleCompressionScheme_iff_hasFiniteVCDim _).2 <|
    hasFiniteVCDim_iff.2 ⟨0, fun W hW => by
      have : W = ∅ := by ext x; exact x.elim
      simp [this]⟩

noncomputable example : SampleCompressionScheme (∅ : ConceptClass ℝ Bool)
    (moranYehudayoffVCCompressionSize 0) :=
  moranYehudayoffSchemeOfVCDim fun W hW => by
    obtain ⟨c, hc, -⟩ := hW ∅ (empty_subset _)
    exact False.elim (notMem_empty c hc)

noncomputable example : SampleCompressionScheme ({fun _ : ℝ => false} : ConceptClass ℝ Bool)
    (moranYehudayoffCompressionSize 0 0) :=
  moranYehudayoffScheme
    (hC := fun W hW => by
      by_contra h
      have hne : W.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨x, hx⟩ := hne
      obtain ⟨c, hc, hcx⟩ := hW {x} (singleton_subset_iff.2 hx)
      have hcf : c = fun _ => false := mem_singleton_iff.1 hc
      have : x ∈ c ⁻¹' {true} ∩ (W : Set ℝ) := hcx ▸ mem_singleton x
      simp [hcf] at this)
    (hdual := fun F hF => by
      by_contra h
      have hne : F.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨c, hc⟩ := hne
      obtain ⟨g, hg, hgc⟩ := hF {c} (singleton_subset_iff.2 hc)
      obtain ⟨x, rfl⟩ := mem_dualClass.1 hg
      have hcf : (c : ℝ → Bool) = fun _ => false := mem_singleton_iff.1 c.property
      have : c ∈ (fun d : ↥({fun _ : ℝ => false} : ConceptClass ℝ Bool) => d.val x) ⁻¹' {true} ∩
          (F : Set _) := hgc ▸ mem_singleton c
      simp [hcf] at this)

/-! ### Uncountable domain ℝ: half-line thresholds (`vcDim ≤ 1`, zero measurability!) -/

private noncomputable def realThresholds : ConceptClass ℝ Bool :=
  Set.range fun θ : ℝ => fun x : ℝ => decide (x ≤ θ)

private theorem realThresholds_shatters_le_one (W : Finset ℝ)
    (hW : SetShatters realThresholds ↑W) : W.card ≤ 1 := by
  by_contra hgt
  have h2 : 2 ≤ W.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < W.card)
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · obtain ⟨c, ⟨θ, rfl⟩, hcb⟩ := hW {b} (singleton_subset_iff.2 hb)
    have hmem_b : b ∈ (fun x => decide (x ≤ θ)) ⁻¹' {true} ∩ (W : Set ℝ) :=
      hcb ▸ mem_singleton b
    have hble : b ≤ θ := by simpa using hmem_b.1
    have hale : a ≤ θ := hlt.le.trans hble
    have hmem_a : a ∈ (fun x => decide (x ≤ θ)) ⁻¹' {true} ∩ (W : Set ℝ) :=
      ⟨by simpa using hale, ha⟩
    have : a = b := mem_singleton_iff.1 (hcb ▸ hmem_a)
    exact hab this
  · obtain ⟨c, ⟨θ, rfl⟩, hca⟩ := hW {a} (singleton_subset_iff.2 ha)
    have hmem_a : a ∈ (fun x => decide (x ≤ θ)) ⁻¹' {true} ∩ (W : Set ℝ) :=
      hca ▸ mem_singleton a
    have hale : a ≤ θ := by simpa using hmem_a.1
    have hble : b ≤ θ := hlt.le.trans hale
    have hmem_b : b ∈ (fun x => decide (x ≤ θ)) ⁻¹' {true} ∩ (W : Set ℝ) :=
      ⟨by simpa using hble, hb⟩
    have : b = a := mem_singleton_iff.1 (hca ▸ hmem_b)
    exact hab this.symm

example : Nonempty (SampleCompressionScheme realThresholds (moranYehudayoffVCCompressionSize 1)) :=
  ⟨moranYehudayoffSchemeOfVCDim realThresholds_shatters_le_one⟩

example : ∃ k : ℕ, Nonempty (SampleCompressionScheme realThresholds k) :=
  (exists_sampleCompressionScheme_iff_hasFiniteVCDim realThresholds).2
    (hasFiniteVCDim_iff.2 ⟨1, realThresholds_shatters_le_one⟩)

/-! ### Negative witness: `Set.univ : ConceptClass ℕ Bool` has NO compression scheme -/

example : ¬ ∃ k : ℕ, Nonempty (SampleCompressionScheme (Set.univ : ConceptClass ℕ Bool) k) := by
  rw [exists_sampleCompressionScheme_iff_hasFiniteVCDim, hasFiniteVCDim_iff]
  rintro ⟨d, hd⟩
  have hsh : SetShatters (Set.univ : ConceptClass ℕ Bool) ↑(Finset.range (d + 1)) := by
    intro A _
    classical
    refine ⟨fun n => decide (n ∈ A), Set.mem_univ _, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
      Finset.mem_coe]
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, by
        have := ‹A ⊆ ↑(Finset.range (d + 1))› hx
        exact this⟩
  have hle := hd (Finset.range (d + 1)) hsh
  simp only [Finset.card_range] at hle
  omega

/-! ### Unordered subset + fixed side-information decoder on `realThresholds` -/

example :
    let s := moranYehudayoffSubsampleSize 1
    let t := moranYehudayoffMajoritySize (2 ^ 2 - 1)
    Fintype.card (Fin t → Fin s → Fin (t * s)) = (t * s) ^ (t * s) ∧
    ∃ ρ : Finset (ℝ × Bool) → (Fin t → Fin s → Fin (t * s)) → ℝ → Bool,
      ∀ {m : ℕ} (S : LabeledSample ℝ Bool m), Realizable realThresholds S →
        ∃ (T : Finset (ℝ × Bool)) (info : Fin t → Fin s → Fin (t * s)),
          (∀ z ∈ T, ∃ i : Fin m, S i = z) ∧ T.card ≤ t * s ∧
          ∀ i : Fin m, ρ T info (S i).1 = (S i).2 := by
  intro s t
  refine ⟨?_, ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul, mul_comm s t]
  · let A : Learner ℝ Bool s := fun T =>
      letI := Classical.propDecidable
      if h : Realizable realThresholds T then Classical.choose h else fun _ => false
    have hA : IsConsistent A realThresholds := fun T hT => by
      have : A T = Classical.choose hT := by
        unfold A; split_ifs; rfl
      rw [this]
      exact ⟨(Classical.choose_spec hT).1, fun i => ((Classical.choose_spec hT).2 i).symm⟩
    exact exists_finset_compression_of_dualVCDim
      realThresholds_shatters_le_one
      (fun _ hF => card_le_of_setShatters_dualClass realThresholds_shatters_le_one hF)
      hA (Nat.le_ceil _) (Nat.le_ceil _)

/-! ### Seven-way Fundamental Theorem bridge on `ℕ` -/

example : IsPACLearnable (thresholdClass ℕ) Set.univ := by
  have hcomp : ∃ k : ℕ, Nonempty (SampleCompressionScheme (thresholdClass ℕ) k) :=
    ⟨1, ⟨(lowerSetScheme (α := ℕ)).ofSubset thresholdClass_subset_lowerSetClass⟩⟩
  exact ((tfae_hasFiniteVCDim_compression (α := ℕ) (C := thresholdClass ℕ)).out 7 3).mp hcomp

/-! ### Agnostic `GeneralCompressionScheme` & noisy non-realizable distribution checks -/

/-- Simple size-`1` general compression scheme on `Bool → Bool`: keeps index `0` (when `m > 0`)
and outputs the constant function equal to that example's label. -/
private def firstLabelScheme : GeneralCompressionScheme Bool Bool 1 where
  compress {m} _ := if h : 0 < m then [⟨0, h⟩] else []
  reconstruct xs _ := match xs with | (_, y) :: _ => y | [] => false
  length_compress_le {m} _ := by split_ifs <;> simp

/-- Non-realizable (noisy) probability distribution on `Bool × Bool`: puts mass `3/4` on
`(false, true)` and mass `1/4` on `(false, false)`, so no deterministic hypothesis has zero
error (`optimalError = 1/4`). -/
private noncomputable def noisyBoolMeasure : Measure (Bool × Bool) :=
  ((3 / 4 : ℝ≥0∞) • Measure.dirac (false, true)) +
    ((1 / 4 : ℝ≥0∞) • Measure.dirac (false, false))

private instance : IsProbabilityMeasure noisyBoolMeasure := by
  constructor
  rw [noisyBoolMeasure, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, FunLike.coe_smul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.dirac_apply_of_mem (Set.mem_univ _),
    mul_one, mul_one, ← ENNReal.add_div]
  have h4 : (3 : ℝ≥0∞) + 1 = 4 := by norm_num
  rw [h4]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Check `heldOutMiscount` and `heldOutError` on a concrete 4-point sample. -/
example :
    let S : LabeledSample Bool Bool 4 := fun i =>
      if i.val = 2 then (false, false) else (false, true)
    let J := firstLabelScheme.keptSet S
    heldOutMiscount J (firstLabelScheme.learner S) S = 1 ∧
      heldOutError J (firstLabelScheme.learner S) S = 1 / 3 := by
  intro S J
  have hkeep : J = ({0} : Finset (Fin 4)) := by
    simp [J, GeneralCompressionScheme.keptSet, firstLabelScheme]
  have hlearn : firstLabelScheme.learner S = fun _ => true := by
    funext x
    simp [GeneralCompressionScheme.learner, firstLabelScheme, S]
  have hcard : Jᶜ.card = 3 := by rw [hkeep]; decide
  have hmis : heldOutMiscount J (firstLabelScheme.learner S) S = 1 := by
    rw [heldOutMiscount, hkeep, hlearn]
    decide
  refine ⟨hmis, ?_⟩
  rw [heldOutError, hmis, hcard]
  norm_num

/-- Check `heldOutError_le_one` and `heldOutError_le_empiricalMiscount_div` on the 4-point
sample (also linking `heldOutError` back to the full-sample `empiricalMiscount`). -/
example (S : LabeledSample Bool Bool 4) :
    heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S ≤ 1 ∧
      heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S ≤
        (empiricalMiscount (firstLabelScheme.learner S) S : ℝ) / (4 - 1 : ℕ) :=
  ⟨heldOutError_le_one _ _ _,
    heldOutError_le_empiricalMiscount_div (firstLabelScheme.card_keptSet_le S) (by omega) _ _⟩

/-- Check `SampleCompressionScheme.toGeneral` preserves `learner` on realizable samples. -/
example (S : LabeledSample ℕ Bool 3) (hS : Realizable (thresholdClass ℕ) S) :
    let κ := (lowerSetScheme (α := ℕ)).ofSubset thresholdClass_subset_lowerSetClass
    κ.toGeneral.learner S = κ.learner S :=
  ((lowerSetScheme (α := ℕ)).ofSubset thresholdClass_subset_lowerSetClass).toGeneral_learner_eq hS

/-- Instantiate the two-sided Hoeffding compression bound (`m = 10, k = 1`). -/
example :
    Measure.pi (fun _ : Fin 10 => noisyBoolMeasure)
        {S | Real.sqrt ((1 * Real.log (10 + 1 : ℝ) + Real.log (2 / (1 / 10 : ℝ))) /
            (2 * ((10 - 1 : ℕ) : ℝ))) ≤
          |heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S -
            (error noisyBoolMeasure (firstLabelScheme.learner S)).toReal|} ≤
      ENNReal.ofReal (1 / 10) := by
  have hm : MeasurableReconstruction firstLabelScheme.reconstruct :=
    measurableReconstruction_of_countable _
  simpa using firstLabelScheme.measure_pi_hoeffding_gt_le hm noisyBoolMeasure
    (m := 10) (by omega) (δ := 1 / 10) (by norm_num)

/-- Instantiate the sharp quadratic Bernstein bound (`measure_pi_bernstein_gt_le`) on
`noisyBoolMeasure`. -/
example :
    let c := ((1 : ℕ) * Real.log ((10 : ℕ) + 1) + Real.log (1 / (1 / 10 : ℝ))) / (10 - 1 : ℕ)
    Measure.pi (fun _ : Fin 10 => noisyBoolMeasure)
        {S | heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S + c +
            Real.sqrt (c ^ 2 +
              2 * heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S * c) <
          (error noisyBoolMeasure (firstLabelScheme.learner S)).toReal} ≤
      ENNReal.ofReal (1 / 10) :=
  firstLabelScheme.measure_pi_bernstein_gt_le (measurableReconstruction_of_countable _)
    noisyBoolMeasure (m := 10) (by omega) (δ := 1 / 10) (by norm_num)

/-- Instantiate the relaxed fast-rate bound (`measure_pi_fastRate_gt_le`) and the zero
held-out error corollary (`measure_pi_zero_heldOut_gt_le`). -/
example :
    let c := ((1 : ℕ) * Real.log ((10 : ℕ) + 1) + Real.log (1 / (1 / 10 : ℝ))) / (10 - 1 : ℕ)
    Measure.pi (fun _ : Fin 10 => noisyBoolMeasure)
        {S | heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S +
            Real.sqrt
              (2 * heldOutError (firstLabelScheme.keptSet S) (firstLabelScheme.learner S) S * c) +
            2 * c <
          (error noisyBoolMeasure (firstLabelScheme.learner S)).toReal} ≤
      ENNReal.ofReal (1 / 10) :=
  firstLabelScheme.measure_pi_fastRate_gt_le (measurableReconstruction_of_countable _)
    noisyBoolMeasure (m := 10) (by omega) (δ := 1 / 10) (by norm_num)

example :
    Measure.pi (fun _ : Fin 10 => noisyBoolMeasure)
        {S | (∀ i ∉ firstLabelScheme.keptSet S,
            firstLabelScheme.learner S (S i).1 = (S i).2) ∧
          2 * ((1 : ℕ) * Real.log ((10 : ℕ) + 1) + Real.log (1 / (1 / 10 : ℝ))) / (10 - 1 : ℕ) <
            (error noisyBoolMeasure (firstLabelScheme.learner S)).toReal} ≤
      ENNReal.ofReal (1 / 10) :=
  firstLabelScheme.measure_pi_zero_heldOut_gt_le (measurableReconstruction_of_countable _)
    noisyBoolMeasure (m := 10) (by omega) (δ := 1 / 10) (by norm_num)

/-- Check `noisyBoolMeasure` is non-realizable: every binary hypothesis has error at least `1/4`. -/
example (h : Bool → Bool) : (1 / 4 : ℝ≥0∞) ≤ error noisyBoolMeasure h := by
  rw [error, noisyBoolMeasure, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, FunLike.coe_smul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  cases hb : h false
  · have h1 : (false, true) ∈ {q : Bool × Bool | h q.1 ≠ q.2} := by simp [hb]
    rw [Measure.dirac_apply_of_mem h1, mul_one]
    have h13 : (1 / 4 : ℝ≥0∞) ≤ 3 / 4 := ENNReal.div_le_div_right (by norm_num) 4
    exact h13.trans le_self_add
  · have h2 : (false, false) ∈ {q : Bool × Bool | h q.1 ≠ q.2} := by simp [hb]
    rw [Measure.dirac_apply_of_mem h2, mul_one]
    exact le_add_self

/-- Instantiate the single-hypothesis Chernoff bound (`measure_pi_bernstein_single_le`). -/
example :
    Measure.pi (fun _ : Fin 8 => noisyBoolMeasure)
        {S | (empiricalMiscount (fun _ : Bool => true) S : ℝ) / 8 + (1 / 10 : ℝ) +
            Real.sqrt ((1 / 10 : ℝ) ^ 2 +
              2 * ((empiricalMiscount (fun _ : Bool => true) S : ℝ) / 8) * (1 / 10)) <
          (error noisyBoolMeasure (fun _ : Bool => true)).toReal} ≤
      ENNReal.ofReal (Real.exp (-(8 * (1 / 10 : ℝ)))) :=
  measure_pi_bernstein_single_le noisyBoolMeasure (Set.toFinite _).measurableSet
    (by norm_num) (by norm_num)

/-- Numerical separation: at `q = 0, c = 1/20`, the fast-rate upper slack `2 c = 0.1` is strictly
smaller than the Hoeffding slack `√(c / 2) = √0.025 ≈ 0.158`. -/
example : let c : ℝ := 1 / 20
    (0 : ℝ) + c + Real.sqrt (c ^ 2 + 2 * 0 * c) < Real.sqrt (c / 2) := by
  have h : (1 / 20 : ℝ) + Real.sqrt ((1 / 20 : ℝ) ^ 2) = 1 / 10 := by
    rw [Real.sqrt_sq (by norm_num)]; norm_num
  calc (0 : ℝ) + 1 / 20 + Real.sqrt ((1 / 20) ^ 2 + 2 * 0 * (1 / 20))
      = 1 / 10 := by simpa using h
    _ = Real.sqrt ((1 / 10 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ < Real.sqrt ((1 / 20 : ℝ) / 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end Cslib.MachineLearning.PACLearning.Tests
