/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity

/-!
# Small subsets of the cube are noise-sensitive

Let `A` be a set of the cube `ι → Bool` with indicator `1_A = A.indicator 1` and volume
`α = 𝔼 x, 1_A x`. The noise stability `Stab_ρ[1_A] = 𝔼_x 1_A x · T_ρ 1_A x`
(`BitString.noiseStability`) is the probability that a uniform `x` and a `ρ`-correlated `y` both
lie in `A`; it is the case `B = A` of the probability in the Reverse Small-Set Expansion Theorem
(`BitString.exp_le_expect_indicator_mul_noiseOp_indicator`). The `(p, 2)`-Hypercontractivity
Theorem `Stab_ρ[f] ≤ ‖f‖_{1 + ρ} ^ 2` (`BitString.noiseStability_le_lpNorm_sq`) applied to `1_A`,
whose `L^p` norm is `α ^ (1 / p)` (`Cslib.lpNorm_indicator_one`), gives the **Small-Set
Expansion Theorem** `Stab_ρ[1_A] ≤ α ^ (2 / (1 + ρ))` for `0 ≤ ρ ≤ 1`
(`BitString.noiseStability_indicator_le`)
[O'Donnell, Small-Set Expansion Theorem, Section 9.5, p. 264][ODonnell2014]. At `ρ = 1 / 3` it is
`Stab_{1/3}[1_A] ≤ α ^ (3 / 2)` (`BitString.noiseStability_one_third_indicator_le`)
[O'Donnell, Corollary 9.8, Section 9.2, p. 254][ODonnell2014].

The book also states both results in an equivalent conditional form for `α > 0`: for `x` uniform
on `A` and `y` `ρ`-correlated with `x`, `Pr[y ∈ A] ≤ α ^ ((1 - ρ) / (1 + ρ))`. That form and the
two-set Generalized Small-Set Expansion Theorem (Section 10.1) are not formalized here; they are
tracked on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). The Level-k
Inequalities (Section 9.5), which follow from these bounds, are in
`CslibFrontier.Foundations.BooleanAnalysis.LevelK`.

## Usage

Open `Cslib` and `Cslib.BitString`. A set `A : Set (ι → Bool)` enters through its indicator
`A.indicator 1`, with volume `𝔼 x, A.indicator 1 x`, so the theorems apply directly to any set
whose volume has been computed. For a function other than an indicator, use the `(p, 2)` bound
`BitString.noiseStability_le_lpNorm_sq` itself, imported from
`CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity` (not re-exported here). Checked
clients compute the noise stability `(1 + ρ) / 4` of a one-bit subcube of volume `1 / 2`, apply
the theorem at `ρ = 1 / 2`, check that its bound is attained at `ρ = 1` and by every set at
`ρ = 0`, and apply Corollary 9.8 to the one-bit subcube and to a point of the three-bit cube, in
[`CslibFrontierTests/BooleanAnalysisSmallSetExpansion.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisSmallSetExpansion.lean).

## Main results

* `Cslib.BitString.noiseStability_indicator_le`: the Small-Set Expansion Theorem.
* `Cslib.BitString.noiseStability_one_third_indicator_le`: its case `ρ = 1 / 3`, Corollary 9.8.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Small-Set Expansion Theorem**: for a set `A` of volume `α` and `0 ≤ ρ ≤ 1`,
`Stab_ρ[1_A] ≤ α ^ (2 / (1 + ρ))`, so a uniform point and a `ρ`-correlated point both lie in `A`
with probability at most `α ^ (2 / (1 + ρ))`
[O'Donnell, Small-Set Expansion Theorem, Section 9.5, p. 264][ODonnell2014]. -/
theorem noiseStability_indicator_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (A : Set (ι → Bool)) :
    noiseStability ρ (A.indicator 1) ≤
      (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (2 / (1 + ρ)) := by
  have hα : 0 ≤ 𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x :=
    expect_nonneg fun x _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  refine (noiseStability_le_lpNorm_sq hρ hρ' _).trans_eq ?_
  rw [lpNorm_indicator_one (by linarith : (0 : ℝ) < 1 + ρ).ne', ← Real.rpow_two,
    ← Real.rpow_mul hα, inv_mul_eq_div]

/-- **Small subsets are noise-sensitive**: for a set `A` of volume `α`,
`Stab_{1/3}[1_A] ≤ α ^ (3 / 2)` [O'Donnell, Corollary 9.8, Section 9.2, p. 254][ODonnell2014]. -/
theorem noiseStability_one_third_indicator_le (A : Set (ι → Bool)) :
    noiseStability (1 / 3) (A.indicator 1) ≤
      (𝔼 x, A.indicator (1 : (ι → Bool) → ℝ) x) ^ (3 / 2 : ℝ) := by
  refine (noiseStability_indicator_le (by norm_num) (by norm_num) A).trans_eq ?_
  norm_num

end Cslib.BitString
