/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.StageContext
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyEstimatedMean

/-!
# Actual conditional child-cost reserves from normalized child roots

The finite reserve uses actual incoming children and genuine canonical requests bundled in a
`ResidualStage`. Bounded routed cutoffs supply ranges for the normalized outputs; equality on true
inputs preserves the genuine canonical family. Root budgets are imposed on each lower request's
own full terminal rank and source, with fixed structural `HP.k`.
This original finite payment does not construct recursively accurate children.
-/
public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual bounded normalized children pay the conditional reserve from their own rooted
row moments. Usage-to-rank transport, midpoint/reset transport and both ranges are derived.
The integrated allocation retains explicit vertex, call-count and source-rate costs. -/
theorem actual_conditionalChildCost_le_of_root_budgets
    {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (j : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hroot : ∀ i r, (i, r) ∈ s.errorCalls →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains s.channelsV σ x)
        (fun σ y => r.terminal.retains s.channelsV σ y)
        (fun σ => s.estimated children (j + 1) i σ r)
        (fun σ => s.canonical i σ r) ≤
      (δ / (1 + (Fintype.card (ZMod P) : ℝ) ^ 2 / ((P : ℝ) * rate s.sourceExponent) *
        s.costCoefficient)) /
        (1 + (4 * (max (2 * HP.Q HP.toHierarchyParams.atomCap)
          (2 * max s.bins.densityCap 16)) ^ ((3 : ℝ) / 4)) ^ 4 *
          ((P : ℝ) * r.source.rate)) /
        (1 + #s.errorCalls)) :
    rowNormPow 4 P (rate s.sourceExponent) s.sourceMask s.terminalMask
      (fun _ => s.cost children j) ≤ δ := by
  let CA := 2 * HP.Q HP.toHierarchyParams.atomCap
  let CB := 2 * max s.bins.densityCap 16
  let B := max CA CB
  have hCA : 0 ≤ CA := by positivity
  have hCB : 0 ≤ CB := by dsimp only [CB]; positivity
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hbounded (i : ℕ) (v : ℝ) : s.bounded i v ∈ Set.Icc 0 (max s.bins.densityCap 16) :=
    s.bins.bounded_mem_Icc s.cutoffs i v
  have hsource (i : ℕ) (r : HierarchyTask.Request HP.k (Fin J) (ZMod P))
      (hc : (i, r) ∈ s.errorCalls) : 0 < r.source.rate := by
    simp only [ResidualStage.errorCalls, HierarchyTask.residualErrorCalls, mem_union, mem_biUnion,
      mem_insert, mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ⟨_, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl⟩ <;>
      first | exact rate_pos s.sourceExponent | exact rate_pos s.midpointExponent
  have hmin (k : ℕ) (A : FrameChannel P 4 1) (y : ZMod P) :
      coordinate s.direction
        ⟨s.roles.terminal, min (rate s.terminalExponent) (rate k), s.terminalSuffix⟩ A y →
      coordinate s.direction
        (gridChannel s.roles.terminal k s.terminalSuffix) A y := by
    rw [min_comm]
    exact coordinate_min_grid s.direction s.roles.terminal s.terminalSuffix
      k s.terminalExponent A y
  have hsub (i : ℕ) (r : HierarchyTask.Request HP.k (Fin J) (ZMod P))
      (hc : (i, r) ∈ s.errorCalls) (σ : Environment P J) (y : ZMod P) :
      r.usage.retains s.channelsV σ y → r.terminal.retains s.channelsV σ y := by
    simp only [ResidualStage.errorCalls, HierarchyTask.residualErrorCalls, mem_union, mem_biUnion,
      mem_insert, mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ⟨_, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl⟩
    · exact hmin (s.bins.binExponent i) _ y
    · exact id
    · exact hmin (s.bins.binExponent i) _ y
    · exact hmin s.midpointExponent _ y
  have hcanon (i : ℕ) (r : HierarchyTask.Request HP.k (Fin J) (ZMod P))
      (hc : (i, r) ∈ s.errorCalls) (σ : Environment P J) :
      s.canonical i σ r = canonicalRequestChild HP s.direction id s.kernel (s.bounded i)
        (s.bins.preparationCutoff i) s.cutoffs.requestGate s.cutoffs.requestRank r σ := by
    simp only [ResidualStage.errorCalls, HierarchyTask.residualErrorCalls, mem_union, mem_biUnion,
      mem_insert, mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ⟨_, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl⟩
    · exact denseChild_congr_cutoff s.direction id _ s.kernel _ _
        (s.bins.preparationCutoff i) s.cutoffs.requestGate s.cutoffs.requestRank
        (fun x y => (boundedRoutedBinCutoff_div_eq (fun k => rate_pos (s.bins.binExponent k))
          (s.kernel_nonneg x y) (s.kernel_cap x y) i).symm) σ
    · simp only [ResidualStage.canonical, HierarchyTask.rawRequests]
      rw [HierarchyTask.correctionAtomTask_last HP.k_pos]
      rfl
    · exact denseChild_congr_cutoff s.direction id _ s.kernel _ _
        (s.bins.preparationCutoff i) s.cutoffs.requestGate s.cutoffs.requestRank
        (fun x y => (boundedRoutedBinCutoff_div_eq (fun k => rate_pos (s.bins.binExponent k))
          (s.kernel_nonneg x y) (s.kernel_cap x y) i).symm) σ
    · simp only [ResidualStage.canonical]
      rw [HierarchyTask.correctionAtomTask_last HP.k_pos]
      rfl
  rw [← rowNormPow_congr_masks s.source_retains_iff s.terminal_retains_iff]
  refine HierarchyTask.conditionalChildCost_le_of_root_budgets (B := B) s.channelsV
    s.bins.activeBins s.level s.source s.midpoint s.terminal s.bins.rates
    hCA hCB hP (rate_pos s.sourceExponent) hδ (s.estimated children (j + 1)) s.canonical
    hsource ?_ ?_ ?_
  · intro i r hc σ x y
    constructor
    · exact incomingChildren_mem_Icc HP s.direction id s.correctionRank (s.bounded i)
        (s.bins.densityCap_nonneg.trans (le_max_left s.bins.densityCap 16))
        (hbounded i) (children.raw (j + 1) i) (children.prep (j + 1) i)
        (children.maximum (j + 1) i) r σ x y
    · rw [hcanon i r hc σ]
      exact canonicalRequestChild_mem_Icc HP s.direction id s.kernel (s.bounded i)
        (s.bins.preparationCutoff i) s.cutoffs.requestGate s.cutoffs.requestRank
        (by positivity) (hbounded i) s.cutoffs.requestGate_mem_Icc r σ x y
  · intro i r _ σ x y hy
    exact ⟨incomingChildren_zero_off_usage HP s.direction id s.correctionRank (s.bounded i)
      (children.raw (j + 1) i) (children.prep (j + 1) i) (children.maximum (j + 1) i) r σ x y hy,
      canonicalRequestChild_zero_off_usage HP s.direction id s.kernel (s.cutoff i)
        (s.bins.preparationCutoff i) s.cutoffs.requestGate s.cutoffs.requestRank r σ x y hy⟩
  · intro i r hc
    exact (rowNormPow_mono_terminal (mul_pos hP (hsource i r hc)).le
      (hsub i r hc) (fun σ x y => s.estimated children (j + 1) i σ r x y ^ (4⁻¹ : ℝ) -
        s.canonical i σ r x y ^ (4⁻¹ : ℝ))).trans (hroot i r hc)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
