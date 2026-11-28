/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds
import CslibFrontier.MachineLearning.PACLearning.OneInclusionGraph
import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Checks for the Haussler–Littlestone–Warmuth one-inclusion graph predictor and its transductive
and realizable PAC bounds:

1. Exact edge counts and bounded-outdegree orientations on concrete Boolean hypercube subgraphs
   (`cornerL` of VC dimension `1` with an undirected degree-`2` corner, and the full square of VC
   dimension `2`).
2. Concrete evaluations of `oneInclusionLearner` on `thresholdClass` (`vcDim = 1`,
   `littlestoneDim = ⊤`): sample consistency on training examples, unanimous forced interpolation
   below and above observed bracket points, and at most `1` mistake across the leave-one-out folds
   of any realizable sample.
3. Quantitative PAC sample-complexity checks on `thresholdClass`: `3` examples suffice at accuracy
   and confidence `1 / 2` (while `0` examples fail), and at accuracy `1 / 100` and confidence
   `1 / 2` the one-inclusion sample complexity is at most `200`, strictly beating the ERM bound
   `⌈vcSampleSize 1 (1 / 100) (1 / 2)⌉₊` that carries the `log (48 / ε)` factor. -/

namespace CslibFrontierTests.OneInclusionGraph

open Cslib.MachineLearning.OnlineLearning.MistakeBound
open Cslib.MachineLearning.PACLearning MeasureTheory
open scoped ENNReal NNReal

/-! ### 1. Concrete one-inclusion subgraphs and bounded-outdegree orientations -/

/-- Three corners of the square `{0, 1}²`, omitting `![true, true]`. -/
def cornerL : Finset (Fin 2 → Bool) :=
  {![false, false], ![false, true], ![true, false]}

theorem card_cornerL : cornerL.card = 3 := by
  decide

/-- `cornerL` has exactly two hypercube edges incident to `![false, false]`. -/
theorem card_oneInclusionEdges_cornerL : (oneInclusionEdges cornerL).card = 2 := by
  decide

/-- The full square `{0, 1}²` has four hypercube edges. -/
theorem card_oneInclusionEdges_square :
    (oneInclusionEdges (Finset.univ : Finset (Fin 2 → Bool))).card = 4 := by
  decide

/-- `cornerL` shatters no `2`-element subset of `Fin 2`, since `![true, true] ∉ cornerL`. -/
theorem card_le_one_of_setShatters_cornerL (W : Finset (Fin 2))
    (hW : SetShatters (cornerL : Set (Fin 2 → Bool)) ↑W) : W.card ≤ 1 := by
  by_contra hlt
  have hW_univ : W = Finset.univ := Finset.eq_univ_of_card W <| by
    have hle := W.card_le_univ
    rw [Fintype.card_fin] at hle ⊢
    omega
  subst hW_univ
  obtain ⟨c, hc, hcT⟩ := hW Set.univ (by simp)
  have h0 : (0 : Fin 2) ∈ c ⁻¹' {true} ∩ ↑(Finset.univ : Finset (Fin 2)) := hcT ▸ trivial
  have h1 : (1 : Fin 2) ∈ c ⁻¹' {true} ∩ ↑(Finset.univ : Finset (Fin 2)) := hcT ▸ trivial
  have hc_mem : c ∈ cornerL := hc
  have hc0 : c 0 = true := h0.1
  have hc1 : c 1 = true := h1.1
  clear hW hc hcT h0 h1
  revert c
  decide

/-- Although `![false, false]` has undirected degree `2` in `cornerL`, its edges admit an
orientation in which every vertex has outdegree at most `1`, whereas no orientation achieves
outdegree `0` everywhere because `(oneInclusionEdges cornerL).Nonempty`. -/
theorem exists_orientation_cornerL :
    (∃ orient, ∀ g, oneInclusionOutdegree cornerL orient g ≤ 1) ∧
      ¬ ∃ orient, ∀ g, oneInclusionOutdegree cornerL orient g ≤ 0 := by
  refine ⟨exists_orientation_outdegree_le card_le_one_of_setShatters_cornerL, ?_⟩
  rintro ⟨orient, h0⟩
  have he : ((0 : Fin 2), ![false, false]) ∈ oneInclusionEdges cornerL := by decide
  have hpos : 0 < oneInclusionOutdegree cornerL orient
      (tailEndpoint orient (0, ![false, false])) :=
    Finset.card_pos.mpr ⟨(0, ![false, false]), Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  exact absurd (h0 (tailEndpoint orient (0, ![false, false]))) (by omega)

/-! ### 2. Concrete predictions and leave-one-out bound on infinite-Littlestone thresholds -/

/-- `thresholdClass ℕ` shatters no two points (`vcDim = 1`), even though
`littlestoneDim (thresholdClass ℕ) = ⊤`. -/
theorem card_le_one_of_setShatters_thresholdClass (W : Finset ℕ)
    (hW : SetShatters (thresholdClass ℕ) ↑W) : W.card ≤ 1 :=
  not_lt.mp fun h => not_setShatters_thresholdClass h hW

theorem hasFiniteVCDim_thresholdClass : HasFiniteVCDim (thresholdClass ℕ) :=
  hasFiniteVCDim_iff.mpr ⟨1, card_le_one_of_setShatters_thresholdClass⟩

/-- Concrete bracket sample `(2, true), (5, false)`, realized by `thresholdConcept 4`. -/
def bracketSample : LabeledSample ℕ Bool 2 := ![(2, true), (5, false)]

theorem realizable_bracketSample : Realizable (thresholdClass ℕ) bracketSample :=
  ⟨thresholdConcept 4, ⟨4, rfl⟩, by intro j; fin_cases j <;> decide⟩

/-- `oneInclusionLearner` reproduces the observed labels on `bracketSample`. -/
example : oneInclusionLearner (thresholdClass ℕ) bracketSample 2 = true ∧
    oneInclusionLearner (thresholdClass ℕ) bracketSample 5 = false :=
  ⟨oneInclusionLearner_apply_sample_of_realizable realizable_bracketSample 0,
    oneInclusionLearner_apply_sample_of_realizable realizable_bracketSample 1⟩

/-- Every threshold consistent with `(2, true)` and `(5, false)` has `3 ≤ θ ≤ 5`, so
`oneInclusionLearner` deterministically predicts `true` at `1` and `false` at `6`. -/
theorem oneInclusionLearner_bracketSample_forced :
    oneInclusionLearner (thresholdClass ℕ) bracketSample 1 = true ∧
      oneInclusionLearner (thresholdClass ℕ) bracketSample 6 = false := by
  constructor
  · refine oneInclusionLearner_eq_of_forall_consistent realizable_bracketSample ?_
    rintro _ ⟨θ, rfl⟩ hS
    have h2 : 2 < θ := by simpa [bracketSample] using (hS 0).symm
    simp only [thresholdConcept_apply, decide_eq_true_eq]
    omega
  · refine oneInclusionLearner_eq_of_forall_consistent realizable_bracketSample ?_
    rintro _ ⟨θ, rfl⟩ hS
    have h5 : ¬ 5 < θ := by simpa [bracketSample] using (hS 1).symm
    simp only [thresholdConcept_apply, decide_eq_false_iff_not]
    omega

/-- Across all four leave-one-out folds of the realizable sample
`![(0, true), (2, true), (5, false), (8, false)]`, `oneInclusionLearner (thresholdClass ℕ)` makes at
most `1` mistake, despite `littlestoneDim (thresholdClass ℕ) = ⊤`. -/
theorem leaveOneOut_threshold_four :
    littlestoneDim (thresholdClass ℕ) = ⊤ ∧
      (Finset.univ.filter fun t : Fin 4 =>
        oneInclusionLearner (thresholdClass ℕ)
          (t.removeNth ![(0, true), (2, true), (5, false), (8, false)])
          (![(0, true), (2, true), (5, false), (8, false)] t).1 ≠
          (![(0, true), (2, true), (5, false), (8, false)] t).2).card ≤ 1 := by
  refine ⟨littlestoneDim_thresholdClass,
    card_leaveOneOut_mistakes_le card_le_one_of_setShatters_thresholdClass ?_⟩
  exact ⟨thresholdConcept 4, ⟨4, rfl⟩, by intro j; fin_cases j <;> decide⟩

/-- Realizable sample with duplicate points (`2` and `5` each repeated twice), exercising the
observed-label reuse branch `∃ j, (S j).1 = x` of `oneInclusionLearner` inside leave-one-out:
folds `0` and `1` (held-out `2`) see `(2, true)` in the remaining folds and make `0` mistakes, and
total leave-one-out mistakes across all `5` folds remain at most `1`. -/
def dupSample : LabeledSample ℕ Bool 5 := ![(2, true), (2, true), (4, true), (5, false), (5, false)]

theorem realizable_dupSample : Realizable (thresholdClass ℕ) dupSample :=
  ⟨thresholdConcept 5, ⟨5, rfl⟩, by intro j; fin_cases j <;> decide⟩

theorem leaveOneOut_dupSample :
    oneInclusionLearner (thresholdClass ℕ) (Fin.removeNth 0 dupSample) (dupSample 0).1 = true ∧
      oneInclusionLearner (thresholdClass ℕ)
        (Fin.removeNth 4 dupSample) (dupSample 4).1 = false ∧
      (Finset.univ.filter fun t : Fin 5 =>
        oneInclusionLearner (thresholdClass ℕ) (t.removeNth dupSample) (dupSample t).1 ≠
          (dupSample t).2).card ≤ 1 := by
  have hrem : ∀ t : Fin 5, Realizable (thresholdClass ℕ) (t.removeNth dupSample) := fun t =>
    ⟨thresholdConcept 5, ⟨5, rfl⟩, fun j => by
      have h := realizable_dupSample
      rcases h with ⟨_, _, _⟩
      exact (show ∀ k : Fin 5, (dupSample k).2 = thresholdConcept 5 (dupSample k).1 by
        intro k; fin_cases k <;> decide) (t.succAbove j)⟩
  refine ⟨?_, ?_, card_leaveOneOut_mistakes_le card_le_one_of_setShatters_thresholdClass
    realizable_dupSample⟩
  · simpa [dupSample, Fin.removeNth] using oneInclusionLearner_apply_sample_of_realizable (hrem 0) 0
  · have h := oneInclusionLearner_apply_sample_of_realizable (hrem 4) 3
    have h3 : Fin.removeNth 4 dupSample 3 = (5, false) := by decide
    rw [h3] at h
    exact h

/-! ### 3. Expected error bound and PAC sample-complexity separation from `vcSampleSize` -/

/-- Concrete instantiation of `lintegral_error_oneInclusionLearner_le`: on any `thresholdClass ℕ`-
realizable distribution `D` (for instance `Measure.dirac (2, true)`), `3` i.i.d. examples achieve
expected true error at most `1 / 4`. -/
theorem lintegral_error_thresholdClass_three_le_quarter :
    let D : Measure (ℕ × Bool) := Measure.dirac (2, true)
    ∫⁻ S, error D (oneInclusionLearner (thresholdClass ℕ) S) ∂Measure.pi (fun _ : Fin 3 => D) ≤
      1 / 4 := by
  intro D
  have hD : IsRealizableBy D (thresholdClass ℕ) :=
    ⟨thresholdConcept 4, ⟨4, rfl⟩, by simp [D, error, thresholdConcept]⟩
  have h := lintegral_error_oneInclusionLearner_le (m := 3)
    card_le_one_of_setShatters_thresholdClass (measurable_of_countable _) hD
  exact h.trans_eq (by norm_num)

/-- `1 / 2` and `1 / 100` in `(0, 1)`. -/
noncomputable def half : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

noncomputable def hundredth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 100, by norm_num, by norm_num⟩

/-- Three i.i.d. examples already learn `thresholdClass ℕ` to accuracy and confidence `1 / 2` via
`oneInclusionLearner`, since `1 ≤ (1 / 2) * (1 / 2) * (3 + 1)`. -/
theorem isPACLearnerFor_thresholdClass_three :
    IsPACLearnerFor 3 half half (thresholdClass ℕ) (realizableDistributions (thresholdClass ℕ)) :=
  isPACLearnerFor_oneInclusionLearner card_le_one_of_setShatters_thresholdClass
    (measurable_of_countable _) (by simp only [half]; norm_num)

/-- Non-vacuity: `0` examples do not learn `thresholdClass ℕ` to accuracy and confidence `1 / 2`. -/
theorem not_isPACLearnerFor_thresholdClass_zero :
    ¬ IsPACLearnerFor 0 half half (thresholdClass ℕ)
        (realizableDistributions (thresholdClass ℕ)) := by
  rintro ⟨A, hA⟩
  set h0 := A Fin.elim0
  set θ : ℕ := if h0 0 then 0 else 1
  set D : Measure (ℕ × Bool) := Measure.dirac (0, !h0 0)
  have hD : D ∈ realizableDistributions (thresholdClass ℕ) := by
    refine ⟨thresholdConcept θ, ⟨θ, rfl⟩, ?_⟩
    cases h : h0 0 <;> simp [D, error, θ, h]
  have key := hA D hD
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add] at key
  have hset : {S : LabeledSample ℕ Bool 0 | (half.val : ℝ≥0∞) < error D (A S)} = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    have hS : S = Fin.elim0 := Subsingleton.elim _ _
    rw [Set.mem_ofPred_eq, hS]
    have herr : error D h0 = 1 := by simp [D, error]
    rw [herr]
    simp [half]
  rw [hset, measure_univ] at key
  exact absurd key (by simp [half])

/-- At accuracy `1 / 100` and confidence `1 / 2`, `thresholdClass ℕ` has realizable PAC sample
complexity at most `200`, strictly smaller than the ERM sample-size bound
`⌈vcSampleSize 1 (1 / 100) (1 / 2)⌉₊`. -/
theorem sampleComplexity_thresholdClass_hundredth_lt_vcSampleSize :
    sampleComplexity IsPACLearnerFor (thresholdClass ℕ) hundredth half
        (realizableDistributions (thresholdClass ℕ)) ≤ 200 ∧
      200 < ⌈vcSampleSize 1 (1 / 100) (1 / 2)⌉₊ := by
  constructor
  · have h := sampleComplexity_realizableDistributions_le_div_vcDim
      hasFiniteVCDim_thresholdClass hundredth half
    rw [vcDim_thresholdClass] at h
    exact h.trans (by simp only [hundredth, half]; norm_num)
  · refine Nat.lt_ceil.mpr ?_
    have hlog4800 : 1 ≤ Real.log 4800 := by
      have hexp : Real.exp 1 ≤ 4800 :=
        (Real.exp_one_lt_d9.le).trans (by norm_num)
      exact (Real.le_log_iff_exp_le (by norm_num)).mpr hexp
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    rw [vcSampleSize, show (48 : ℝ) / (1 / 100) = 4800 by norm_num,
      show (4 : ℝ) / (1 / 2) = 8 by norm_num]
    push_cast
    linarith

end CslibFrontierTests.OneInclusionGraph
