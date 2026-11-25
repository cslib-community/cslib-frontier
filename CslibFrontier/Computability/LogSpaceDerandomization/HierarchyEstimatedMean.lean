/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.StageContext

/-!
# Estimated-child mean error against the genuine finite residual

Actual bounded incoming children are compared to canonical requests, after proving that
bounded routed cutoffs preserve their true inputs. The top cap and adjacent ratio 16
provide the genuine dense range; the actual correction range pays the other coefficient.
The joint source × terminal mean subtracts the proved canonical residual mean, with positive
bins summed and exactly one negative error. No independence or desired-reference field is
used. Finite coverage, narrower source, all suffixes and horizons remain explicit, bundled
through `CutoffProfile`, `BinSchedule`, and `ResidualStage`.
This original finite absolute theorem does not establish recursive budgets or copy routing.
-/
public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)

/-- Actual finite absolute propagation from four per-request errors under a `CutoffProfile` and
`BinSchedule`. The special negative payment occurs once, and the target is the genuine residual. -/
theorem estimated_residual_bins_mean_error
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
    (l ks km kt : ℕ) (ksH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (ss sm st : List (ZMod P)) (c : CutoffProfile) (b : BinSchedule)
    (hbH : ∀ i ∈ b.activeBins, b.binExponent i ≤ H.maxExponent)
    (hkh : ∀ i ∈ b.activeBins, ∀ v, b.cutoff c i v ≠ 0 → b.preparationCutoff i v = 1)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate km)
    (hCcap : ∀ z w, C z w ≤ b.densityCap * rate (b.binExponent 0))
    (Kc : ℕ)
    (raw prep : ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → V → ℝ)
    (x y : V) (hcover : ∀ z, C z y = 0 ∨ rate (b.binExponent b.lastBin) ≤ C z y) :
    let source := gridChannel R.source ks ss
    let mid := gridChannel R.midpoint km sm
    let terminal := gridChannel R.terminal kt st
    let estimated := fun i σ r => incomingChildren HP D ident Kc (b.bounded c i)
      (raw i) (prep i) (maximum i) r σ
    let canonical := fun i σ r => canonicalRequestChild HP D ident C
      (b.cutoff c i) (b.preparationCutoff i) c.requestGate c.requestRank r σ
    let channelsV := fun role b suffix σ v => channels D role b suffix σ (ident v)
    let S := ({σ : Environment P J | source.retains (channels D) σ (ident x) ∧
      terminal.retains (channels D) σ (ident y)} : Finset _)
    |(𝔼 σ ∈ S, estimatedResidualInput HP D ident R l ks km kt b.lastBin ss sm st b.binExponent Kc
      (b.bounded c) (fun _ => raw) (fun _ => prep) (fun _ => maximum) 0 σ x y) -
      HP.toHierarchyParams.residual (canonicalChannel ident (rate km))
        (canonicalChannel ident (rate km)) (rate km) C x y| ≤
    𝔼 σ ∈ S, ((∑ i ∈ b.activeBins, HierarchyTask.positiveChildError channelsV
      l i .residual source mid terminal (b.rates i)
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max b.densityCap 16)
      (estimated i σ) (canonical i σ) x y) +
      HierarchyTask.negativeChildError channelsV l 0 .residual source mid terminal
        (b.rates 0) (estimated 0 σ) (canonical 0 σ) x y) := by
  dsimp only [estimatedResidualInput]
  have hm := canonical_residual_bins_mean HP D ident hD hid H R l ks km kt b.lastBin ksH hms
    ss sm st b.binExponent hbH C hC hC1 hCf c.binCutoff c.cutoff_one b.preparationCutoff
    c.requestGate c.requestRank hkh c.requestGate_nonneg c.requestGate_le_one
    c.gateThreshold_pos c.gate_one c.rank_bound x y hcover
  dsimp only at hm; rw [← hm]
  apply HierarchyTask.residual_bins_sub_le
  · intro i _ σ _ z
    exact incomingChildren_final_range HP D ident Kc _ (raw i) (prep i) (maximum i) _ l rfl σ x z
  · intro i _ σ _ z
    change |denseChild D ident _ _ (b.preparationCutoff i) c.requestGate c.requestRank C σ z y| ≤
      2 * max b.densityCap 16
    let r := (HierarchyTask.rawRequests (k := HP.k) l i .residual
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (b.rates i)).right
    rw [denseChild_congr_cutoff D ident r C (b.cutoff c i) (b.bounded c i)
      (b.preparationCutoff i) c.requestGate c.requestRank
      (fun u w => (boundedRoutedBinCutoff_div_eq
        (fun j => rate_pos (b.binExponent j)) (hC u w) (hCcap u w) i).symm) σ]
    exact denseChild_range D ident r C _ (b.preparationCutoff i) c.requestGate c.requestRank
      (b.densityCap_nonneg.trans (le_max_left _ _))
      (b.bounded_mem_Icc c i) c.requestGate_mem_Icc σ z y

/-- Pointwise slice-mean error of `s.input children (j + 1)` against `s.residual`, bounded by
`s.cost children j`. -/
theorem ResidualStage.mean_sub_le {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (j : ℕ) (x y : ZMod P) :
    |rowSliceMean s.sourceMask s.terminalMask
        (s.input children (j + 1)) x y - s.residual x y| ≤
      s.cost children j x y := by
  have he := estimated_residual_bins_mean_error HP s.direction id s.direction_ne_zero
    Function.injective_id s.horizon s.roles s.level s.sourceExponent s.midpointExponent
    s.terminalExponent s.source_in_horizon s.midpoint_le_source s.sourceSuffix s.midpointSuffix
    s.terminalSuffix s.cutoffs s.bins s.bins_in_horizon s.preparation_one s.kernel
    s.kernel_nonneg s.kernel_row_mass s.kernel_rate s.kernel_cap s.correctionRank
    (children.raw (j + 1)) (children.prep (j + 1)) (children.maximum (j + 1)) x y
    fun z => s.kernel_cover z y
  dsimp only at he
  refine Eq.trans_le (congrArg (|· - s.residual x y|) ?_) (he.trans_eq ?_)
  · unfold rowSliceMean ResidualStage.input
    refine expect_congr ?_ fun _ _ => rfl
    ext σ
    simp only [mem_filter, mem_univ, true_and, ← s.source_retains_iff, ← s.terminal_retains_iff]
  · symm
    unfold ResidualStage.cost HierarchyTask.conditionalChildCost rowSliceMean
    refine expect_congr ?_ fun _ _ => rfl
    ext σ; simp only [mem_filter, mem_univ, true_and]

end Matrix.HierarchyParams.H4RankEnvironment
