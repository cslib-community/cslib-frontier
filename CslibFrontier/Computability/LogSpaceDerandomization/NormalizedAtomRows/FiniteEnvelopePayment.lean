/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.StageContext
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.CommonEnvelope

/-!
# Common-envelope payment for the actual finite estimated residual

The lower-child conditional-error costs pay one common deterministic B for each channel.
The RAW walk requirement is a numerical spectral payment from the actual finite input
range, rather than a hypothesis about the final noise or common B. Finite coverage,
true-input cutoff/gate agreement and the narrower usage horizon remain explicit via
`ResidualStage`. The original finite allocation costs m times the larger channel payment;
it makes no claim of convergent recursive reserves or parameter/workspace growth.
The row/normalization proof patterns are adapted from Samuel Schlesinger.

## Main results

* `actualEstimatedResidual_common_envelope_payment`: conditional lower-child costs and
  the actual finite RAW spectral payment pay both common deterministic matrices.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Actual finite once-negative residual payment on a `ResidualStage`, deriving both common-`B`
row moments from actual conditional lower-child costs and a numerical RAW spectral payment.
Correction `s.midpointExponent` and parent rank/normalization `s.terminalExponent` remain
distinct. -/
theorem actualEstimatedResidual_common_envelope_payment
    {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (s : ResidualStage HP P J) (children : ReserveOutputChildren HP P J)
    (steps : ℕ → ℕ) (ku : ℕ) (husage : s.terminalExponent ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ) (m : ℕ)
    (childBudget rawBudget : ℝ)
    (hc : ∀ i < m, rowNormPow 4 P (rate s.sourceExponent) s.sourceMask s.terminalMask
      (fun _ => s.cost children i) ≤ childBudget)
    (hz : ∀ i < m, 32 * reserveOutputContraction J ^ (2 * steps (i + 1)) * s.payment ≤ rawBudget)
    (ν : Fin 2) :
    rowNormPow 4 P (rate s.sourceExponent) s.sourceMask
      (s.terminalMaskAt (if ν = 0 then s.terminalExponent else ku))
      (fun _ => commonMeanEnvelope s.roles s.direction s.sourceSuffix s.terminalSuffix
        s.sourceExponent s.terminalExponent ku m Lh Lρ ζ (s.input children)
        (s.walkSteps children steps) s.residual ν) ≤
      m * max ((rate s.terminalExponent)⁻¹ ^ 4 * childBudget)
        (P * (|ζ| * (Lh + Lρ) / rate s.terminalExponent) ^ 4 *
          (8 * (rawBudget + childBudget))) :=
  commonMeanEnvelope_moment_le_cost s.roles s.direction s.sourceSuffix s.terminalSuffix
    s.sourceExponent s.terminalExponent ku m husage hLh hLρ ζ (s.input children)
    (s.walkSteps children steps) s.residual s.residual_nonneg (s.cost children)
    (fun j _ => s.mean_sub_le children j) (by positivity) hc
    (fun i hi => (s.input_noise_le children steps (i + 1)).trans (hz i hi)) ν

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
