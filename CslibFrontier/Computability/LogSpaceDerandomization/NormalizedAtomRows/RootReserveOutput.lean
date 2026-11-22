/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ReserveOutput
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ChildRootReserve

/-!
# Actual finite output from lower-child rooted errors

This discharges the conditional cost premise of `ReserveOutput` using bounded normalized
lower-child rooted moments on their own source and full terminal rank. The finite sufficient
allocation displays its vertex width, call-count, bin, rate and density costs.
There is no environment-cardinality or minimum-atom-probability payment.
It does not prove recursive accuracy, copy routing, parameter/workspace growth or RL=L.
The finite geometric, routing and cutoff hypotheses are supplied in `ReserveOutputContext`
(extending `ResidualStage`), with the independent raw, preparation and maximum families in
`ReserveOutputChildren`. Their named constructions are defined in `StageContext` and
`OutputContext`; the error premise and output bound remain explicit in the theorem statement.
The output constant is chosen after HP, ζ, scale and the positive floor, before the
prime, environment width, horizon, prefix length or child families. Child accuracies may
therefore be chosen using that constant without depending circularly on those families.
This uniformity concerns the final output coefficient only; the displayed allocation and
walk lengths still retain their P, rate, bin and finite-horizon factors.
The underlying row/normalization assembly is adapted from Samuel Schlesinger.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual finite output from explicit per-request rooted-error budgets on bounded
normalized children. The lower-child conditional cost reserve is discharged. The allocation
is finite and conservative; recursive accuracy and parameter/workspace closure remain open. -/
theorem actualEstimatedResidual_output_from_root_budgets
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale floor : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hsmall : ζ ≤ scale / 2) (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000)
    (hfloor : 0 < floor) (hfloors : floor ≤ scale) (hfloor1 : floor ≤ 1) (hfloorθ : floor ≤ HP.θ) :
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ (P J : ℕ) [Fact P.Prime] (ctx : ReserveOutputContext HP P J)
    (children : ReserveOutputChildren HP P J) (ε : ℝ), 0 < ε →
    let amplification := ctx.amplification ζ
    let tolerance := ctx.tolerance ε
    (∀ j < ctx.prefixLength, ∀ i r,
      (i, r) ∈ ctx.errorCalls →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains ctx.channelsV σ x)
        (fun σ y => r.terminal.retains ctx.channelsV σ y)
        (fun σ => ctx.estimated children (j + 1) i σ r) (fun σ => ctx.canonical i σ r) ≤
      ((tolerance ^ 4 / (1 + (rate ctx.terminalExponent)⁻¹ ^ 4 + amplification)) /
        (1 + (Fintype.card (ZMod P) : ℝ) ^ 2 / ((P : ℝ) * rate ctx.sourceExponent) *
          ctx.costCoefficient)) /
        (1 + (4 * (max (2 * HP.Q HP.toHierarchyParams.atomCap)
          (2 * max ctx.bins.densityCap 16)) ^ ((3 : ℝ) / 4)) ^ 4 *
          ((P : ℝ) * r.source.rate)) /
        (1 + #ctx.errorCalls)) →
    rowNormPow 4 P (rate ctx.sourceExponent) ctx.sourceMask ctx.usageMask
      (fun σ x y => actualNormalizedCompatible HP ζ floor ctx.roles.terminal
        (side P ctx.usageExponent) ctx.direction ctx.terminalSuffix ctx.terminalExponent
        ctx.prefixLength (ctx.increment children ζ ε) (fun _ _ _ _ => 0) σ x y ^ (4⁻¹ : ℝ) -
        genuineNormalizedRecipe HP ctx.roles.source ctx.roles.terminal
          (side P ctx.sourceExponent) (side P ctx.usageExponent) ctx.direction ctx.sourceSuffix
          ctx.terminalSuffix ctx.terminalExponent ctx.residual σ x y ^ (4⁻¹ : ℝ)) ≤
      Cbound * ε ^ 4 := by
  obtain ⟨Cbound, hCbound, hout⟩ := actualEstimatedResidual_output_from_cost_reserves
    HP hζ hs hmargin hsmall hcapscale hfloor hfloors hfloor1 hfloorθ
  refine ⟨Cbound, hCbound, fun P J _ ctx children ε hε hroot =>
    hout P J ctx children ε hε fun j hj =>
      actual_conditionalChildCost_le_of_root_budgets ctx.toResidualStage children j
        (by dsimp only [ReserveOutputContext.amplification]; positivity) (hroot j hj)⟩

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
