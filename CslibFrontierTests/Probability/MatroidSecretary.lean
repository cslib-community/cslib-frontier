/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.OptimalStopping.MatroidSecretary
import CslibFrontier.Probability.OptimalStopping.TransversalSecretary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-! Concrete witnesses, nonvacuity checks, and sharp `n = 1` boundaries for
`Cslib.Probability.OptimalStopping.MatroidSecretary` and
`Cslib.Probability.OptimalStopping.TransversalSecretary`. -/

namespace CslibFrontierTests.Probability.MatroidSecretary

open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.Lean.Matroid
open Cslib.Probability.OptimalStopping
open Cslib.Probability.OptimalStopping.MatroidSecretary
open Cslib.Probability.OptimalStopping.TransversalSecretary

/-! ### Sampling splits and optimal classical cutoff -/

local instance instNonemptyPermTest (α : Type*) [Fintype α] :
    Nonempty (Fin (Fintype.card α) ≃ α) :=
  ⟨(Fintype.equivFin α).symm⟩

example :
    (Finset.univ.filter fun σ : Fin (Fintype.card (Fin 4)) ≃ Fin 4 =>
      (0 : Fin 4) ∈ sampleSet σ 2 ∧ (1 : Fin 4) ∉ sampleSet σ 2).card = 8 := by
  rw [card_filter_mem_sample_not_mem_sample (by decide : (0 : Fin 4) ≠ 1) (by decide)]
  norm_num

example :
    (1 / 4 : ℝ) ≤
      ((Cslib.Probability.PMF.uniformOfFintype (Fin (Fintype.card (Fin 2)) ≃ Fin 2)).toOuterMeasure
        {σ | (0 : Fin 2) ∈ sampleSet σ 1 ∧ (1 : Fin 2) ∉ sampleSet σ 1}).toReal := by
  simpa using one_fourth_le_prob_split (by decide : (0 : Fin 2) ≠ 1) (by decide)

example :
    Real.exp (-1) ≤ Secretary.successProb (Secretary.cutoffRule (Secretary.optimalCutoff 1)) 1 :=
  exp_neg_one_le_successProb_optimalCutoff le_rfl

/-! ### Partition matroid (`e`-competitive copies with tied weights) -/

private def part3 : Fin 3 → Fin 2 := ![0, 0, 1]

private def wPart3 : Fin 3 → ℝ := ![3, 3, 5]

example (σ : Fin 3 ≃ Fin 3) :
    (unitPartitionMatroid part3).Indep
      ((partitionSelect part3 wPart3 σ : Finset (Fin 3)) : Set _) :=
  partitionSelect_indep part3 wPart3 σ

example : Real.exp (-1) * 8 ≤ expectedPartitionSecretary part3 wPart3 := by
  have hw : ∀ x : Fin 3, 0 ≤ wPart3 x := fun x => by fin_cases x <;> norm_num [wPart3]
  have hI : (unitPartitionMatroid part3).Indep (({0, 2} : Finset (Fin 3)) : Set _) := by
    rw [unitPartitionMatroid_indep_iff]
    intro a ha b hb hab
    fin_cases a <;> fin_cases b <;> simp_all [part3]
  have hbound := exp_neg_one_mul_sum_le_expectedPartitionSecretary part3 wPart3 hw hI
  have hsum : ∑ x ∈ ({0, 2} : Finset (Fin 3)), wPart3 x = 8 := by
    norm_num [wPart3, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]
  rwa [hsum] at hbound

/-! ### General matroid Threshold Price (Theorem 3.2) and sharp `n = 1` boundary -/

private noncomputable def rankTwoMatroid : Matroid (Fin 3) :=
  unitPartitionMatroid (![0, 0, 1] : Fin 3 → Fin 2)

private def wRankTwo : Fin 3 → ℝ := ![1, 4, 2]

private lemma rankTwoMatroid_loopless (x : Fin 3) : rankTwoMatroid.Indep ({x} : Set (Fin 3)) := by
  rw [rankTwoMatroid, unitPartitionMatroid_indep_iff]
  intro a ha b hb _
  simp only [Set.mem_singleton_iff] at ha hb
  exact ha.trans hb.symm

private lemma rankTwoMatroid_eRank_eq_two : rankTwoMatroid.eRank.toNat = 2 := by
  have hI : rankTwoMatroid.Indep (({1, 2} : Finset (Fin 3)) : Set _) := by
    rw [rankTwoMatroid, unitPartitionMatroid_indep_iff]
    intro a ha b hb hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hge : (2 : ℕ∞) ≤ rankTwoMatroid.eRank := by
    calc (2 : ℕ∞) = (({1, 2} : Finset (Fin 3)) : Set (Fin 3)).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_pair (by decide : (1 : Fin 3) ≠ 2)]
          rfl
      _ = rankTwoMatroid.eRk (({1, 2} : Finset (Fin 3)) : Set (Fin 3)) := hI.eRk_eq_encard.symm
      _ ≤ rankTwoMatroid.eRank := rankTwoMatroid.eRk_le_eRank _
  have hle : rankTwoMatroid.eRank ≤ (2 : ℕ∞) := by
    rw [Matroid.eRank_def, Matroid.eRk_le_iff]
    intro I _ hI'
    rw [rankTwoMatroid, unitPartitionMatroid_indep_iff] at hI'
    have hcard := Set.encard_le_encard_of_injOn (Set.mapsTo_univ _ I) hI'
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hcard
    exact hcard
  have heq : rankTwoMatroid.eRank = 2 := le_antisymm hle hge
  simp [heq]

open scoped Classical in
example :
    6 ≤ 64 * (Nat.clog 2 rankTwoMatroid.eRank.toNat : ℝ) *
        expectedThresholdPrice rankTwoMatroid wRankTwo ∧
      0 < expectedThresholdPrice rankTwoMatroid wRankTwo := by
  have hw : ∀ x : Fin 3, 0 ≤ wRankTwo x := fun x => by
    fin_cases x <;> norm_num [wRankTwo]
  have hwb : ∀ x y : Fin 3, x ≠ y → wRankTwo x = wRankTwo y → wRankTwo x = 0 := by
    intro x y hne heq
    fin_cases x <;> fin_cases y <;> simp [wRankTwo] at hne heq
  have hr : 2 ≤ rankTwoMatroid.eRank.toNat := by
    rw [rankTwoMatroid_eRank_eq_two]
  have hI : rankTwoMatroid.Indep (({1, 2} : Finset (Fin 3)) : Set _) := by
    rw [rankTwoMatroid, unitPartitionMatroid_indep_iff]
    intro a ha b hb hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hbound := sum_le_sixtyFour_clog_mul_expectedThresholdPrice rankTwoMatroid wRankTwo
    hw hwb rankTwoMatroid_loopless (by decide) hr hI
  have hsum : ∑ x ∈ ({1, 2} : Finset (Fin 3)), wRankTwo x = 6 := by
    norm_num [wRankTwo, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  rw [hsum] at hbound
  have hclog_pos : (0 : ℝ) < 64 * (Nat.clog 2 rankTwoMatroid.eRank.toNat : ℝ) := by
    rw [rankTwoMatroid_eRank_eq_two]
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.clog_pos one_lt_two one_lt_two))
  have hexp_pos : 0 < expectedThresholdPrice rankTwoMatroid wRankTwo := by
    by_contra hle
    push Not at hle
    have : 64 * (Nat.clog 2 rankTwoMatroid.eRank.toNat : ℝ) *
        expectedThresholdPrice rankTwoMatroid wRankTwo ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hclog_pos.le hle
    linarith
  exact ⟨hbound, hexp_pos⟩

private noncomputable def unit1Matroid : Matroid (Fin 1) :=
  unitPartitionMatroid (fun _ : Fin 1 => ())

-- Sharpness witness: for `|α| = 1`, `s = ⌈1/2⌉ = 1` leaves an empty suffix, so
-- `thresholdPriceRun` always returns `∅` and cannot be `c`-competitive for any finite `c`.
open scoped Classical in
example (σ : Fin (Fintype.card (Fin 1)) ≃ Fin 1)
    (j : Fin (Nat.clog 2 unit1Matroid.eRank.toNat + 1)) :
    thresholdPriceRun unit1Matroid ![5] σ j = ∅ ∧ expectedThresholdPrice unit1Matroid ![5] = 0 := by
  have hempty : ∀ (σ' : Fin (Fintype.card (Fin 1)) ≃ Fin 1) j',
      thresholdPriceRun unit1Matroid ![5] σ' j' = ∅ := by
    intro σ' j'
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    have hpost := (thresholdPriceRun_subset_post unit1Matroid ![5] σ' j' hx).1
    rw [mem_postSampleList_iff] at hpost
    have hlt := (σ'.symm x).isLt
    have hc : Fintype.card (Fin 1) ≤ (Fintype.card (Fin 1) + 1) / 2 := by simp
    exact absurd (hlt.trans_le (hc.trans hpost)) (lt_irrefl _)
  refine ⟨hempty σ j, ?_⟩
  simp only [expectedThresholdPrice, hempty, Finset.sum_empty, mul_zero, Finset.sum_const_zero]

/-! ### Transversal matroids (Theorem 4.1), sharp `n = 1` boundary, and USV mechanism (Theorem 4.2)
-/

private def transGraph : Fin 3 × Fin 2 → Bool := fun e =>
  decide (e.1 = 1 ∨ e.1 = 2 ∨ e.2 = 0)

private def transWeights : Fin 3 → ℝ := ![1, 3, 5]

example (σ : Fin 3 ≃ Fin 3) :
    IsMatching transGraph (priceSamplingMatch transGraph transWeights σ) :=
  priceSamplingMatch_isMatching transGraph transWeights σ

example : 1 ≤ expectedPriceSamplingWeight transGraph transWeights := by
  have hw : ∀ l : Fin 3, 0 ≤ transWeights l := fun l => by
    fin_cases l <;> norm_num [transWeights]
  have hwb : ∀ x y : Fin 3, x ≠ y → transWeights x = transWeights y → transWeights x = 0 := by
    intro x y hne heq
    fin_cases x <;> fin_cases y <;> simp [transWeights] at hne heq
  have hd : ∀ l : Fin 3,
      (Finset.univ.filter fun r : Fin 2 => transGraph (l, r) = true).card ≤ 2 := fun l =>
    (Finset.card_filter_le _ _).trans (by simp)
  let Mopt : Finset (Fin 3 × Fin 2) := {(1, 0), (2, 1)}
  have hM : IsMatching transGraph Mopt := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      fin_cases e <;> simp_all [Mopt, transGraph]
    · intro u v₁ v₂ h₁ h₂
      fin_cases u <;> fin_cases v₁ <;> fin_cases v₂ <;> simp_all [Mopt]
    · intro u₁ u₂ v h₁ h₂
      fin_cases u₁ <;> fin_cases u₂ <;> fin_cases v <;> simp_all [Mopt]
  have hbound := sum_le_four_mul_degree_mul_expectedPriceSampling transGraph transWeights
    hw hwb hd (by decide) hM
  have hsum : ∑ e ∈ Mopt, transWeights e.1 = 8 := by
    have hne : ((1 : Fin 3), (0 : Fin 2)) ≠ ((2 : Fin 3), (1 : Fin 2)) := by decide
    simp only [Mopt, Finset.sum_pair hne, transWeights]
    norm_num
  rw [hsum] at hbound
  norm_num at hbound
  linarith

-- Sharpness witness for transversal price sampling:
-- at `|L| = 1`, `postSampleList` is empty.
example (σ : Fin (Fintype.card (Fin 1)) ≃ Fin 1) :
    priceSamplingMatch (fun _ : Fin 1 × Fin 1 => true) ![5] σ = ∅ := by
  have hnil : postSampleList σ ((Fintype.card (Fin 1) + 1) / 2) = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
    rw [mem_postSampleList_iff] at hx
    have hlt := (σ.symm x).isLt
    have hc : Fintype.card (Fin 1) ≤ (Fintype.card (Fin 1) + 1) / 2 := by simp
    exact absurd (hlt.trans_le (hc.trans hx)) (lt_irrefl _)
  simp only [priceSamplingMatch, hnil, List.foldl_nil]

private def usvProfile : Fin 3 → USVType (Fin 2)
  | 0 => ⟨1, fun r => decide (r = 0)⟩
  | 1 => ⟨3, fun _ => true⟩
  | 2 => ⟨5, fun _ => true⟩

example (σ : Fin 3 ≃ Fin 3) (l : Fin 3) :
    0 ≤ priceSamplingUSVUtility (usvProfile l)
      (priceSamplingUSVAlloc usvProfile σ l) (priceSamplingUSVPayment usvProfile σ l) :=
  priceSamplingUSV_ir usvProfile σ l

example (σ : Fin 3 ≃ Fin 3) :
    let misreport : USVType (Fin 2) := ⟨10, fun _ => true⟩
    priceSamplingUSVUtility (usvProfile 0)
        (priceSamplingUSVAlloc (Function.update usvProfile 0 misreport) σ 0)
        (priceSamplingUSVPayment (Function.update usvProfile 0 misreport) σ 0) ≤
      priceSamplingUSVUtility (usvProfile 0)
        (priceSamplingUSVAlloc (Function.update usvProfile 0 (usvProfile 0)) σ 0)
        (priceSamplingUSVPayment (Function.update usvProfile 0 (usvProfile 0)) σ 0) :=
  priceSamplingUSV_truthful usvProfile σ 0 (usvProfile 0) ⟨10, fun _ => true⟩ fun l' _ => by
    fin_cases l' <;> norm_num [usvProfile]

end CslibFrontierTests.Probability.MatroidSecretary
