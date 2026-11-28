/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import CslibFrontier.Probability.StatisticalDistance.Coupling

/-!
# Sequential composition of approximate couplings

Two approximate couplings compose sequentially across `PMF.bind` (`CoupledWithin.bind`): if `μ` and
`ν` are coupled within `ε` and, for every `a ∈ ν.support`, the continuations `f a` and `g a` are
coupled within `δ`, then `μ.bind f` and `ν.bind g` are coupled within `ε + δ`, with no finiteness
assumptions and across independent sample-space universes. The equivalence of `CoupledWithin` and
all-event statistical closeness `CloseTo` lets this operation reuse the statistical-closeness
composition theorem without constructing a separate joint kernel.

## Main results

* `Cslib.Probability.PMF.CoupledWithin.bind`: sequential composition of couplings across `PMF.bind`
  adds disagreement bounds.
* `Cslib.Probability.PMF.CoupledWithin.bind_left`,
  `Cslib.Probability.PMF.CoupledWithin.bind_right`: shared-continuation and pointwise-continuation
  specializations.
-/

public section

open scoped ENNReal

namespace Cslib.Probability.PMF.CoupledWithin

universe u v

/-- Sequential composition of couplings across `PMF.bind`: if `μ` and `ν` are coupled within `ε`
and `f a` and `g a` are coupled within `δ` for every `a ∈ ν.support`, then `μ.bind f` and
`ν.bind g` are coupled within `ε + δ`. -/
theorem bind {α : Type u} {β : Type v} {μ ν : PMF α} {f g : α → PMF β} {ε δ : ℝ≥0∞}
    (h₁ : CoupledWithin μ ν ε) (h₂ : ∀ a ∈ ν.support, CoupledWithin (f a) (g a) δ) :
    CoupledWithin (μ.bind f) (ν.bind g) (ε + δ) :=
  (h₁.closeTo.bind fun a ha => (h₂ a ha).closeTo).coupledWithin

/-- Postprocessing two coupled distributions by a shared randomized continuation `f` preserves
`CoupledWithin` with the same disagreement bound. -/
theorem bind_left {α : Type u} {β : Type v} {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CoupledWithin μ ν ε) (f : α → PMF β) :
    CoupledWithin (μ.bind f) (ν.bind f) ε := by
  simpa only [add_zero] using h.bind fun a _ => refl (f a)

/-- Pointwise `δ`-coupled continuations on `μ.support` lift across `PMF.bind` with disagreement
bound `δ`. -/
theorem bind_right {α : Type u} {β : Type v} (μ : PMF α) {f g : α → PMF β} {δ : ℝ≥0∞}
    (h : ∀ a ∈ μ.support, CoupledWithin (f a) (g a) δ) :
    CoupledWithin (μ.bind f) (μ.bind g) δ := by
  simpa only [zero_add] using (refl μ).bind h

end Cslib.Probability.PMF.CoupledWithin
