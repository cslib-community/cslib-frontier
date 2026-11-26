/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Network.InfluenceMaximization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Network Influence Models and Influence Submodularity

Concrete kernel-checked instances exercising `CslibFrontier.GameTheory.Network.InfluenceModels`
and `CslibFrontier.GameTheory.Network.InfluenceMaximization` ([Kleinberg2007], Sections 24.3–24.4,
pp. 618–627):

1. **Strict Separation of Theorem 24.6 over Theorem 24.4** ([Kleinberg2007], Section 24.4, p. 626):
   on the 3-vertex V-digraph `0 → 2 ← 1` (`veeDigraph`), the equal-weight `LinearThresholdModel`
   (`weight 0 2 = weight 1 2 = 1 / 2`) has submodular local thresholds and submodular global
   influence (`veeLinear_submodular_and_not_diminishingReturns`), yet its equivalent cascade model
   `veeLinear.toGeneralThresholdModel.toCascadeModel` strictly violates `HasDiminishingReturns`
   (`p_2(1, ∅) = 1 / 2 < 1 = p_2(1, {0})`).
2. **Critical-Mass Counterexample to Submodularity** ([Kleinberg2007], Section 24.3 case (i),
   p. 621, and Section 24.4, p. 624): when vertex `2` requires *both* neighbors `0` and `1`
   (`criticalMassTwo`), neither `criticalMassTwo.thresholdFn 2` nor `criticalMassTwo.influence`
   is submodular (`not_isSubmodular_criticalMassTwo_influence`, witnessing
   `f({0, 1}) + f(∅) = 3 > 2 = f({0}) + f({1})`).
3. **Kempe–Kleinberg–Tardos Equivalence & Schedule Invariance**: explicit verification of round-trip
   model translation and agreement across distinct valid edge-attempt schedules.
4. **Independent Cascade Live-Edge Formula & `(1 - 1/e)` Greedy Guarantee** (Theorems 24.3–24.5):
   concrete `veeIC` instance checking `influence_eq_sum_liveGraphWeight`, `isSubmodular_influence`,
   diminishing-returns submodularity, and `one_sub_exp_neg_one_mul_le_greedy_influence`.
5. **Nonprogressive Oscillation vs Time-Layered DAG (`swapDigraph`)**: 2-cycle `0 ↔ 1` where seed
   `{0}` oscillates `{0} ↦ {1} ↦ {0}` across steps `0, 1, 2`, matching progressive activation on
   `timeLayeredDigraph swapDigraph 2` slice by slice with submodular `nonprogStepInfluence`.
-/

public section

namespace CslibFrontierTests.GameTheory.NetworkInfluence

open Cslib.Algorithms.Lean.Submodular
open Cslib.GameTheory.Network

/-! ## 1. 3-vertex V-digraph `0 → 2 ← 1` and Linear Threshold separation -/

/-- Three-vertex directed graph with incoming edges `(0, 2)` and `(1, 2)` into sink `2`. -/
abbrev veeDigraph : Digraph (Fin 3) :=
  Digraph.mk' fun u v => decide ((u = 0 ∨ u = 1) ∧ v = 2)

private theorem inNeighbors_veeDigraph_zero : inNeighbors veeDigraph 0 = ∅ := by
  ext u
  simp [veeDigraph]

private theorem inNeighbors_veeDigraph_one : inNeighbors veeDigraph 1 = ∅ := by
  ext u
  simp [veeDigraph]

private theorem inNeighbors_veeDigraph_two : inNeighbors veeDigraph 2 = {0, 1} := by
  ext u
  fin_cases u <;> simp [veeDigraph]

/-- Equal-weight Linear Threshold Model on `veeDigraph` with `b_{2,0} = b_{2,1} = 1 / 2`. -/
noncomputable def veeLinear : LinearThresholdModel veeDigraph where
  weight u v := if (u = 0 ∨ u = 1) ∧ v = 2 then (1 / 2 : ℝ) else 0
  weight_nonneg u v := by
    split_ifs <;> norm_num
  weight_eq_zero_of_not_adj u v hnot := by
    have h : ¬ ((u = 0 ∨ u = 1) ∧ v = 2) := by
      simpa [veeDigraph] using hnot
    simp [h]
  sum_inNeighbors_le_one v := by
    fin_cases v
    · simp [inNeighbors_veeDigraph_zero]
    · simp [inNeighbors_veeDigraph_one]
    · change (∑ u ∈ inNeighbors veeDigraph 2,
        if (u = 0 ∨ u = 1) ∧ (2 : Fin 3) = 2 then (1 / 2 : ℝ) else 0) ≤ 1
      rw [inNeighbors_veeDigraph_two, Finset.sum_pair (by decide)]
      norm_num

/-- **Separation witness ([Kleinberg2007], Section 24.4, p. 626):** `veeLinear` has submodular
expected influence by Theorem 24.6, even though its KKT-equivalent `CascadeModel` violates
`HasDiminishingReturns` (`p_2(1, ∅) = 1 / 2 < 1 = p_2(1, {0})`). -/
theorem veeLinear_submodular_and_not_diminishingReturns :
    IsSubmodular veeLinear.toGeneralThresholdModel.influence ∧
      ¬ veeLinear.toGeneralThresholdModel.toCascadeModel.HasDiminishingReturns := by
  refine ⟨veeLinear.isSubmodular_influence, fun hdim => ?_⟩
  have hle := hdim 2 1 (Finset.empty_subset ({0} : Finset (Fin 3))) (by decide)
  have hg_empty : veeLinear.toGeneralThresholdModel.thresholdFn 2 ∅ = 0 :=
    veeLinear.toGeneralThresholdModel.thresholdFn_empty 2
  have hg_zero : veeLinear.toGeneralThresholdModel.thresholdFn 2 {0} = 1 / 2 := by
    simp [veeLinear]
  have hg_one : veeLinear.toGeneralThresholdModel.thresholdFn 2 (insert 1 ∅) = 1 / 2 := by
    simp [veeLinear]
  have hg_pair : veeLinear.toGeneralThresholdModel.thresholdFn 2 {1, 0} = 1 := by
    rw [veeLinear.toGeneralThresholdModel_thresholdFn, Finset.sum_pair (by decide)]
    norm_num [veeLinear]
  simp only [GeneralThresholdModel.toCascadeModel_prob] at hle
  rw [hg_empty, hg_zero, hg_one, hg_pair] at hle
  norm_num at hle

/-! ## 2. Critical-mass (`k = 2`) counterexample to local and global submodularity -/

/-- Critical-mass threshold model on `veeDigraph` ([Kleinberg2007], p. 621 case (i) and p. 624):
vertex `2` activates iff *both* incoming neighbors `0` and `1` are active. -/
def criticalMassTwo : GeneralThresholdModel veeDigraph where
  thresholdFn v X := if v = 2 ∧ (0 : Fin 3) ∈ X ∧ (1 : Fin 3) ∈ X then 1 else 0
  thresholdFn_empty v := by simp
  thresholdFn_le_one v X := by
    split_ifs <;> norm_num
  monotone v A B hAB := by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, hAB h1.2.1, hAB h1.2.2⟩ h2
    · norm_num
    · exact le_rfl
  inNeighbors_congr v X := by
    have h0 : (0 : Fin 3) ∈ inNeighbors veeDigraph 2 := by simp [veeDigraph]
    have h1 : (1 : Fin 3) ∈ inNeighbors veeDigraph 2 := by simp [veeDigraph]
    by_cases hv : v = 2
    · subst hv
      simp [h0, h1]
    · simp [hv]

theorem not_isSubmodular_criticalMassTwo_local :
    ¬ IsSubmodular (criticalMassTwo.thresholdFn 2) := by
  intro hsub
  have h := hsub ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3))
  have hinter : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by decide
  have hunion : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by decide
  rw [hinter, hunion] at h
  norm_num [criticalMassTwo] at h

/-- **Global non-submodularity witness ([Kleinberg2007], Section 24.4, p. 624):** without local
submodularity, `criticalMassTwo.influence` satisfies
`f({0, 1}) + f(∅) = 3 > 1 + 1 = f({0}) + f({1})`. -/
theorem not_isSubmodular_criticalMassTwo_influence :
    ¬ IsSubmodular criticalMassTwo.influence := by
  have hf0 : criticalMassTwo.influence ({0} : Finset (Fin 3)) = 1 := by
    simpa using criticalMassTwo.influence_eq_card_of_forall_eq_zero (S := {0}) fun v hv => by
      fin_cases v <;> simp_all [criticalMassTwo]
  have hf1 : criticalMassTwo.influence ({1} : Finset (Fin 3)) = 1 := by
    simpa using criticalMassTwo.influence_eq_card_of_forall_eq_zero (S := {1}) fun v hv => by
      fin_cases v <;> simp_all [criticalMassTwo]
  have hf01 : criticalMassTwo.influence ({0, 1} : Finset (Fin 3)) = 3 := by
    simpa using criticalMassTwo.influence_eq_card_univ_of_forall_eq_one (S := {0, 1}) fun v hv => by
      fin_cases v <;> simp_all [criticalMassTwo]
  intro hsub
  have h := hsub ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3))
  have hinter : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by decide
  have hunion : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by decide
  rw [hinter, hunion, criticalMassTwo.influence_empty, hf0, hf1, hf01] at h
  norm_num at h

/-! ## 3. Two distinct valid schedules and KKT active-set equivalence -/

/-- Valid schedule trying edge `(0, 2)` first whenever available. -/
noncomputable def preferZeroNextEdge (active : Finset (Fin 3))
    (tried : Fin 3 → Finset (Fin 3)) : Option (Fin 3 × Fin 3) :=
  if (0, 2) ∈ CascadeModel.untriedEdges veeDigraph active tried then some (0, 2)
  else CascadeModel.defaultNextEdge veeDigraph active tried

/-- Valid schedule trying edge `(1, 2)` first whenever available. -/
noncomputable def preferOneNextEdge (active : Finset (Fin 3))
    (tried : Fin 3 → Finset (Fin 3)) : Option (Fin 3 × Fin 3) :=
  if (1, 2) ∈ CascadeModel.untriedEdges veeDigraph active tried then some (1, 2)
  else CascadeModel.defaultNextEdge veeDigraph active tried

theorem validNextEdge_preferZeroNextEdge :
    CascadeModel.ValidNextEdge veeDigraph preferZeroNextEdge := by
  intro active tried
  unfold preferZeroNextEdge
  by_cases h02 : (0, 2) ∈ CascadeModel.untriedEdges veeDigraph active tried
  · simp only [h02, ↓reduceIte]
    exact ⟨fun _ => ⟨(0, 2), h02, rfl⟩, fun hemp => absurd (hemp ▸ h02) (Finset.notMem_empty _)⟩
  · simp only [h02, ↓reduceIte]
    exact CascadeModel.validNextEdge_defaultNextEdge active tried

theorem validNextEdge_preferOneNextEdge :
    CascadeModel.ValidNextEdge veeDigraph preferOneNextEdge := by
  intro active tried
  unfold preferOneNextEdge
  by_cases h12 : (1, 2) ∈ CascadeModel.untriedEdges veeDigraph active tried
  · simp only [h12, ↓reduceIte]
    exact ⟨fun _ => ⟨(1, 2), h12, rfl⟩, fun hemp => absurd (hemp ▸ h12) (Finset.notMem_empty _)⟩
  · simp only [h12, ↓reduceIte]
    exact CascadeModel.validNextEdge_defaultNextEdge active tried

/-- `preferZeroNextEdge` and `preferOneNextEdge` select distinct edges from initial state `{0, 1}`,
yet induce identical final active-set probabilities matching
`veeLinear.toGeneralThresholdModel.activeSetProb`. -/
theorem veeLinear_schedule_invariance (A : Finset (Fin 3)) :
    preferZeroNextEdge ({0, 1} : Finset (Fin 3)) (fun _ => ∅) ≠
      preferOneNextEdge ({0, 1} : Finset (Fin 3)) (fun _ => ∅) ∧
    veeLinear.toGeneralThresholdModel.toCascadeModel.activeSetProb
        preferZeroNextEdge {0, 1} A =
      veeLinear.toGeneralThresholdModel.toCascadeModel.activeSetProb
        preferOneNextEdge {0, 1} A ∧
    veeLinear.toGeneralThresholdModel.toCascadeModel.activeSetProb
        preferZeroNextEdge {0, 1} A =
      veeLinear.toGeneralThresholdModel.activeSetProb {0, 1} A := by
  have h02 : (0, 2) ∈ CascadeModel.untriedEdges veeDigraph {0, 1} (fun _ => ∅) := by
    simp [veeDigraph]
  have h12 : (1, 2) ∈ CascadeModel.untriedEdges veeDigraph {0, 1} (fun _ => ∅) := by
    simp [veeDigraph]
  refine ⟨by simp [preferZeroNextEdge, preferOneNextEdge, h02, h12], ?_, ?_⟩
  · exact veeLinear.toGeneralThresholdModel.toCascadeModel.activeSetProb_congr_schedule
      validNextEdge_preferZeroNextEdge validNextEdge_preferOneNextEdge {0, 1} A
  · exact veeLinear.toGeneralThresholdModel.activeSetProb_toCascadeModel
      validNextEdge_preferZeroNextEdge {0, 1} A

/-- Saturation boundary (`g_v(X) = 1`, `1 - g_v(X) = 0`) witness: entering saturation on `veeLinear`
has conditional probability `prob 2 1 {0} = 1`, while at `X = {0, 1}` both
`veeLinear.toGeneralThresholdModel` and `criticalMassTwo` satisfy `thresholdFn 2 {0, 1} = 1`,
hitting the `0 / 0 = 0` division-by-zero boundary in `toCascadeModel.prob` with zero survival
probability and exact round-trip recovery via `toGeneralThresholdModel_toCascadeModel`. -/
theorem saturation_boundary_toCascadeModel (u : Fin 3) :
    veeLinear.toGeneralThresholdModel.toCascadeModel.prob 2 1 {0} = 1 ∧
    veeLinear.toGeneralThresholdModel.thresholdFn 2 {0, 1} = 1 ∧
    veeLinear.toGeneralThresholdModel.toCascadeModel.prob 2 u {0, 1} = 0 ∧
    veeLinear.toGeneralThresholdModel.toCascadeModel.survivalProb 2 {0, 1} = 0 ∧
    veeLinear.toGeneralThresholdModel.toCascadeModel.toGeneralThresholdModel =
      veeLinear.toGeneralThresholdModel ∧
    criticalMassTwo.thresholdFn 2 {0, 1} = 1 ∧
    criticalMassTwo.toCascadeModel.prob 2 u {0, 1} = 0 ∧
    criticalMassTwo.toCascadeModel.toGeneralThresholdModel = criticalMassTwo := by
  have hg_zero : veeLinear.toGeneralThresholdModel.thresholdFn 2 {0} = 1 / 2 := by
    simp [veeLinear]
  have hg_10 : veeLinear.toGeneralThresholdModel.thresholdFn 2 {1, 0} = 1 := by
    rw [veeLinear.toGeneralThresholdModel_thresholdFn, Finset.sum_pair (by decide)]
    norm_num [veeLinear]
  have hg_01 : veeLinear.toGeneralThresholdModel.thresholdFn 2 {0, 1} = 1 := by
    rw [veeLinear.toGeneralThresholdModel_thresholdFn, Finset.sum_pair (by decide)]
    norm_num [veeLinear]
  have hprob_enter : veeLinear.toGeneralThresholdModel.toCascadeModel.prob 2 1 {0} = 1 := by
    rw [GeneralThresholdModel.toCascadeModel_prob, hg_zero, hg_10]
    norm_num
  have hprob_sat_vee : veeLinear.toGeneralThresholdModel.toCascadeModel.prob 2 u {0, 1} = 0 := by
    rw [GeneralThresholdModel.toCascadeModel_prob, hg_01, sub_self, div_zero]
  have hsurv_sat_vee :
      veeLinear.toGeneralThresholdModel.toCascadeModel.survivalProb 2 {0, 1} = 0 := by
    have h := congrArg (fun M => M.thresholdFn 2 ({0, 1} : Finset (Fin 3)))
      veeLinear.toGeneralThresholdModel.toGeneralThresholdModel_toCascadeModel
    simp only [CascadeModel.toGeneralThresholdModel_thresholdFn, hg_01] at h
    linarith
  have hg_cm : criticalMassTwo.thresholdFn 2 {0, 1} = 1 := by
    simp [criticalMassTwo]
  have hprob_sat_cm : criticalMassTwo.toCascadeModel.prob 2 u {0, 1} = 0 := by
    rw [GeneralThresholdModel.toCascadeModel_prob, hg_cm, sub_self, div_zero]
  exact ⟨hprob_enter, hg_01, hprob_sat_vee, hsurv_sat_vee,
    veeLinear.toGeneralThresholdModel.toGeneralThresholdModel_toCascadeModel,
    hg_cm, hprob_sat_cm, criticalMassTwo.toGeneralThresholdModel_toCascadeModel⟩

/-! ## 4. Independent Cascade live-edge decomposition and `(1 - 1/e)` greedy bound -/

/-- Independent Cascade Model on `veeDigraph` with `p_{0,2} = 1 / 2` and `p_{1,2} = 1 / 3`. -/
noncomputable def veeIC : IndependentCascadeModel veeDigraph where
  edgeProb u v :=
    if u = 0 ∧ v = 2 then (1 / 2 : ℝ)
    else if u = 1 ∧ v = 2 then (1 / 3 : ℝ)
    else 0
  edgeProb_nonneg u v := by
    split_ifs <;> norm_num
  edgeProb_le_one u v := by
    split_ifs <;> norm_num
  edgeProb_eq_zero_of_not_adj u v hnot := by
    have h0 : ¬ (u = 0 ∧ v = 2) := fun ⟨hu, hv⟩ => by simp [veeDigraph, hu, hv] at hnot
    have h1 : ¬ (u = 1 ∧ v = 2) := fun ⟨hu, hv⟩ => by simp [veeDigraph, hu, hv] at hnot
    simp [h0, h1]

theorem veeIC_submodular_and_greedy :
    IsSubmodular veeIC.influence ∧
    IsSubmodular veeIC.toCascadeModel.influence ∧
    veeIC.influence {0, 1} =
      (∑ H : Digraph (Fin 3),
        liveGraphWeight veeIC H * ((liveReachable H ({0, 1} : Finset (Fin 3))).card : ℝ)) ∧
    (1 - Real.exp (-1)) * veeIC.influence ({0, 1} : Finset (Fin 3)) ≤
      veeIC.influence (submodularGreedy veeIC.influence ([0, 1, 2] : List (Fin 3)) 2) := by
  refine ⟨veeIC.isSubmodular_influence,
    veeIC.toCascadeModel.isSubmodular_influence_of_diminishingReturns
      veeIC.hasDiminishingReturns_toCascadeModel,
    veeIC.influence_eq_sum_liveGraphWeight {0, 1},
    veeIC.one_sub_exp_neg_one_mul_le_greedy_influence ([0, 1, 2] : List (Fin 3)) 2
      (OPT := ({0, 1} : Finset (Fin 3))) (by decide) (by decide)⟩

/-! ## 5. Nonprogressive 2-cycle oscillation and time-layered DAG correspondence -/

/-- Directed 2-cycle `0 ↔ 1`. -/
abbrev swapDigraph : Digraph (Fin 2) :=
  Digraph.mk' fun u v => decide (u ≠ v)

/-- Copy-other-vertex threshold model on `swapDigraph`: `g_0(X) = 1` iff `1 ∈ X`, and `g_1(X) = 1`
iff `0 ∈ X`. -/
def swapThreshold : GeneralThresholdModel swapDigraph where
  thresholdFn v X := if (1 - v) ∈ X then 1 else 0
  thresholdFn_empty v := by simp
  thresholdFn_le_one v X := by
    split_ifs <;> norm_num
  monotone v A B hAB := by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (hAB h1) h2
    · norm_num
    · exact le_rfl
  inNeighbors_congr v X := by
    have hmem : (1 - v) ∈ inNeighbors swapDigraph v := by
      fin_cases v <;> simp [swapDigraph]
    simp [hmem]

theorem isSubmodular_swapThreshold (v : Fin 2) : IsSubmodular (swapThreshold.thresholdFn v) := by
  intro A B
  dsimp only [swapThreshold]
  by_cases hA : (1 - v) ∈ A <;> by_cases hB : (1 - v) ∈ B <;> simp [hA, hB]

/-- Starting from `{0}` under constant threshold `θ = 1 / 2`, the synchronous nonprogressive
process on `swapDigraph` oscillates `{0} ↦ {1} ↦ {0}` across steps `0, 1, 2` (vertex `0` switches
back to inactive at step `1`), while matching `swapThreshold.toTimeLayered 2` at every layer and
satisfying submodularity of `nonprogStepInfluence`. -/
theorem swapThreshold_oscillation_and_layered :
    let θ : Fin 2 × Fin 3 → ℝ := fun _ => (1 / 2 : ℝ)
    swapThreshold.nonprogActive θ ({0} : Finset (Fin 2)) 0 = {0} ∧
    swapThreshold.nonprogActive θ ({0} : Finset (Fin 2)) 1 = {1} ∧
    swapThreshold.nonprogActive θ ({0} : Finset (Fin 2)) 2 = {0} ∧
    (∀ (v : Fin 2) (t : Fin 3),
      (v, t) ∈ (swapThreshold.toTimeLayered 2).thresholdFinal θ
          (seedLayer0 2 ({0} : Finset (Fin 2))) ↔
        v ∈ swapThreshold.nonprogActive θ ({0} : Finset (Fin 2)) t) ∧
    IsSubmodular (swapThreshold.nonprogStepInfluence 2 2) := by
  intro θ
  have hθ0 : ∀ v : Fin 2, 0 < θ (v, 0) := fun _ => by norm_num [θ]
  have hstep1 : swapThreshold.nonprogActive θ ({0} : Finset (Fin 2)) 1 = {1} := by
    ext v
    have hm := swapThreshold.mem_nonprogActive_succ θ ({0} : Finset (Fin 2)) (k := 0) (by omega) v
    change v ∈ swapThreshold.nonprogActive θ {0} 1 ↔
      θ (v, 1) ≤ swapThreshold.thresholdFn v (swapThreshold.nonprogActive θ {0} 0) at hm
    rw [hm, swapThreshold.nonprogActive_zero]
    fin_cases v <;> norm_num [θ, swapThreshold]
  have hstep2 : swapThreshold.nonprogActive θ ({0} : Finset (Fin 2)) 2 = {0} := by
    ext v
    have hm := swapThreshold.mem_nonprogActive_succ θ ({0} : Finset (Fin 2)) (k := 1) (by omega) v
    change v ∈ swapThreshold.nonprogActive θ {0} 2 ↔
      θ (v, 2) ≤ swapThreshold.thresholdFn v (swapThreshold.nonprogActive θ {0} 1) at hm
    rw [hm, hstep1]
    fin_cases v <;> norm_num [θ, swapThreshold]
  exact ⟨swapThreshold.nonprogActive_zero θ ({0} : Finset (Fin 2)), hstep1, hstep2,
    swapThreshold.mem_thresholdFinal_toTimeLayered_iff hθ0 ({0} : Finset (Fin 2)),
    swapThreshold.isSubmodular_nonprogStepInfluence isSubmodular_swapThreshold 2 2⟩

end CslibFrontierTests.GameTheory.NetworkInfluence
