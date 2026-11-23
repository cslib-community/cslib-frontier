/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.StableInfluence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity

/-!
# Stable influences are bounded by influences

For a Boolean function read as signs `F` and `0 ≤ ρ ≤ 1`, the `ρ`-stable influence of coordinate
`i` is the noise stability of the derivative `Dᵢ F`, which by the `(1 + ρ, 2)`-Hypercontractivity
Theorem is at most `‖Dᵢ F‖_{1+ρ}²`; since `Dᵢ F` takes values in `{-1, 0, 1}`, this is
`Infᵢ[F]^{2/(1+ρ)}` (`BitString.stableInfluence_signVal_le_influence_rpow`)
[O'Donnell, Corollary 9.25][ODonnell2014]. The case `ρ = 1/3`, with exponent `3/2`, is
[O'Donnell, Corollary 9.12][ODonnell2014], through which the proof of the Kahn–Kalai–Linial
theorem in `CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial` uses hypercontractivity.

## Main results

* `Cslib.BitString.stableInfluence_signVal_le_influence_rpow`: Corollary 9.25.

## Usage

For `f : (ι → Bool) → Bool` and `0 ≤ ρ ≤ 1`, `stableInfluence_signVal_le_influence_rpow hρ hρ1 f i`
bounds `stableInfluence ρ i (fun x => signVal (f x))` by
`influence i (fun x => signVal (f x)) ^ (2 / (1 + ρ))`, a real power. For a concrete rate, rewrite
the exponent with `norm_num` (at `ρ = 1/3` it is `3/2`, Corollary 9.12); to reach the Fourier
side, rewrite the stable influence with `BitString.stableInfluence_eq_sum` or, for the noise
stability of the derivative, `BitString.stableInfluence_eq_noiseStability_derivative`. The checked
clients in
[CslibFrontierTests/BooleanAnalysisStableInfluenceBound.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisStableInfluenceBound.lean)
evaluate both sides on the conjunction of two bits, where each coordinate has influence `1/2` and
`ρ`-stable influence `(1 + ρ)/4`: the bound reads `1/3 ≤ (1/2) ^ (3/2)` at `ρ = 1/3` and is
attained at `ρ = 0`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Stable influences are bounded by influences** [O'Donnell, Corollary 9.25][ODonnell2014]: for a
Boolean function read as signs and `0 ≤ ρ ≤ 1`, `Infᵢ^{(ρ)}[F] ≤ Infᵢ[F]^{2/(1+ρ)}`. -/
theorem stableInfluence_signVal_le_influence_rpow {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    stableInfluence ρ i (fun x => signVal (f x)) ≤
      influence i (fun x => signVal (f x)) ^ (2 / (1 + ρ)) := by
  have h := noiseStability_le_lpNorm_sq hρ hρ1 (derivative i fun x => signVal (f x))
  rwa [lpNorm_derivative_signVal f i (by positivity), ← rpow_natCast,
    ← rpow_mul (influence_nonneg i _), Nat.cast_ofNat, inv_mul_eq_div,
    ← stableInfluence_eq_noiseStability_derivative] at h

end Cslib.BitString
