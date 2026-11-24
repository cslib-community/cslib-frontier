/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.StageContext
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.SecondSignal

/-!
# Shared finite context for reserve-output bounds

`ReserveOutputContext` extends `ResidualStage` (from `StageContext`, which composes `CutoffProfile`
and `BinSchedule`) with the narrower endpoint usage exponent, hierarchy preparation/gate Lipschitz
constants, and finite compression prefix horizon used by both reserve-output theorems.
`ReserveOutputChildren` (also exported from `StageContext`) records the raw, preparation and
maximum families. Their named constructions define the same finite allocation, full-terminal raw
walk, selected preparation, usage-terminal preparation walk and two-signal increment as the
explicit assembly in `ReserveOutput`.

These objects are quantified after the output constant: the constant depends only on the fixed
hierarchy, `ζ`, `scale` and positive `floor`, before the prime, environment width, finite horizon
or child families. The allocation and walk lengths still depend on the finite instance, with no
claim of recursive accuracy, copy routing, parameter/workspace bounds or RL=L. The underlying
row/normalization assembly is adapted from Samuel Schlesinger.

## Main definitions

* `ReserveOutputContext`: extends `ResidualStage` with usage-horizon, Lipschitz, and finite-prefix
  hypotheses for the reserve-output bounds.
* `ReserveOutputContext.rawSteps`, `ReserveOutputContext.prepSteps`: the explicit spectral walk
  allocations; `amplification` and `tolerance` display their width/rate and horizon losses.
* `ReserveOutputContext.rawWalk`, `ReserveOutputContext.prepWalk`,
  `ReserveOutputContext.increment`: the two actual walks and their compression signal.

The constructions are reducible abbreviations so applications of the existing component lemmas
retain the unbundled terms directly, without compatibility wrappers or extra hypotheses.
-/

public section
noncomputable section

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite stage instance and two-signal compression hypotheses shared by the two reserve-output
theorems, extending `ResidualStage` with the narrower usage mask, hierarchy Lipschitz bounds, and
compression prefix horizon. Supplied only after the uniform output coefficient has been chosen. -/
structure ReserveOutputContext (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P J : ℕ) [Fact P.Prime] extends ResidualStage HP P J where
  /-- Exponent of the narrower final usage mask. -/
  usageExponent : ℕ
  /-- Usage is contained in the full terminal rank. -/
  terminal_le_usage : terminalExponent ≤ usageExponent
  /-- The full terminal grid lies in the admitted horizon. -/
  terminal_in_horizon : terminalExponent ≤ horizon.maxExponent
  /-- Lipschitz constant for the hierarchy preparation cutoff. -/
  preparationLipschitz : ℝ
  /-- Lipschitz constant for the hierarchy row gate. -/
  gateLipschitz : ℝ
  /-- The preparation Lipschitz constant is nonnegative. -/
  preparationLipschitz_nonneg : 0 ≤ preparationLipschitz
  /-- The gate Lipschitz constant is nonnegative. -/
  gateLipschitz_nonneg : 0 ≤ gateLipschitz
  /-- The hierarchy preparation cutoff has the supplied Lipschitz bound. -/
  preparation_lipschitz : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤
    preparationLipschitz * |a - b|
  /-- The hierarchy row gate has the supplied Lipschitz bound. -/
  gate_lipschitz : ∀ a b, |HP.ρ a - HP.ρ b| ≤ gateLipschitz * |a - b|
  /-- Positive finite prefix horizon of the actual compression iterate. -/
  prefixLength : ℕ
  /-- The prefix horizon is positive. -/
  prefixLength_pos : 0 < prefixLength

namespace ReserveOutputContext

variable {HP : FourthRootHierarchyParams 16 1 16 32 8} {P J : ℕ} [Fact P.Prime]

/-- Retained narrower usage mask at `side P ctx.usageExponent`. -/
abbrev usageMask (ctx : ReserveOutputContext HP P J) : Environment P J → ZMod P → Prop :=
  ctx.terminalMaskAt ctx.usageExponent

/-- Full B1 width and inverse-terminal-rate amplification. -/
abbrev amplification (ctx : ReserveOutputContext HP P J) (ζ : ℝ) : ℝ :=
  P * (|ζ| * (ctx.preparationLipschitz + ctx.gateLipschitz) / rate ctx.terminalExponent) ^ 4

/-- Uniform child tolerance, retaining the finite prefix horizon. -/
abbrev tolerance (ctx : ReserveOutputContext HP P J) (ε : ℝ) : ℝ :=
  ε / (2 * (ctx.prefixLength + 1))

/-- Raw walk length satisfying both the first-noise and amplified B1 requirements. -/
abbrev rawSteps (ctx : ReserveOutputContext HP P J) (ζ ε : ℝ) : ℕ → ℕ :=
  fun j => max
    (spectralWalkLength (reserveOutputContraction J)
      ((rate ctx.terminalExponent)⁻¹ ^ 4 * 32 * ctx.payment)
      ε (dyadicSlack ctx.prefixLength (j - 1)))
    (spectralWalkLength (reserveOutputContraction J)
      ((1 + ctx.amplification ζ) * 32 * ctx.payment) (ctx.tolerance ε) 0)

/-- Preparation walk length for the sixteen-rank payment. -/
abbrev prepSteps (ctx : ReserveOutputContext HP P J) (ζ ε : ℝ) : ℕ → ℕ :=
  fun j => spectralWalkLength (reserveOutputContraction J) (ζ ^ 4 * 512 * HP.K)
    ε (dyadicSlack ctx.prefixLength (j - 1))

/-- Completed raw walk on the source and full terminal-rank masks. -/
abbrev rawWalk (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  ctx.walkSteps children (ctx.rawSteps ζ ε)

/-- Selected preparation of the completed raw walk. -/
abbrev preparation (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  fun j σ x y => selectedPreparation HP ctx.direction ctx.roles ctx.terminalSuffix
    ctx.terminalExponent (ctx.rawWalk children ζ ε j) σ x y

/-- Preparation walk on the source and narrower usage masks. -/
abbrev prepWalk (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  fun j => conditionalWalk ctx.sourceMask ctx.usageMask
    (ctx.walkGraphAt ctx.usageExponent) (fun _ _ => ctx.prepSteps ζ ε j)
    (ctx.preparation children ζ ε j)

/-- Two-signal increment passed to the actual compatible-capacity iterate. -/
abbrev increment (ctx : ReserveOutputContext HP P J) (children : ReserveOutputChildren HP P J)
    (ζ ε : ℝ) :=
  firstSignalIncrement (ctx.rawWalk children ζ ε) ctx.terminalExponent
    (secondSignalIncrement (ctx.prepWalk children ζ ε) ζ)

end ReserveOutputContext

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
