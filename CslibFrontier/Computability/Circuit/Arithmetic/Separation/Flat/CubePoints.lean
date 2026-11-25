/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Sign.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The points `u / 2` of the cube

For a sign vector `u ∈ {-1, 0, 1} ^ k`, the point `u / 2` of `ℝ ^ k` (`Flat.cubePoint`) is a vertex,
the centre of a facet or another point of the cube `[-1/2, 1/2] ^ k`. The contracting case of the
lower bounds of [AnthropicVPVNP2026] (module `Nc.CaseI.Cube`, used in the proof of the convexity of
prices) places the parties at such points; opposite vertices are at distance `√k`
(`Flat.dist_cubePoint_neg`).

## Main definitions

* `Flat.boolSign`: the sign `1` of `true` and `-1` of `false`.
* `Flat.cubePoint`: the point `u / 2` of `ℝ ^ k`.

## Main results

* `Flat.dist_cubePoint_neg`: opposite vertices of the cube are at distance `√k`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix E (the cube in the contracting case); module `Nc.CaseI.Cube`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

variable {k : ℕ}

/-- The sign `1` of `true` and `-1` of `false`. -/
@[expose] def boolSign (b : Bool) : SignType := if b then 1 else -1

/-- The point `u / 2` of `ℝ ^ k` for a sign vector `u`. -/
noncomputable def cubePoint (u : Fin k → SignType) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun x => ((u x : SignType) : ℝ) / 2

/-- The coordinates of `u / 2`. -/
@[simp] theorem cubePoint_apply (u : Fin k → SignType) (x : Fin k) :
    cubePoint u x = ((u x : SignType) : ℝ) / 2 := by
  rfl

/-- Opposite vertices of the cube are at distance `√k`. -/
theorem dist_cubePoint_neg (π : Fin k → Bool) :
    dist (cubePoint fun x => boolSign (π x)) (cubePoint fun x => -boolSign (π x)) = √k := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h (x : Fin k) :
      dist (cubePoint (fun x => boolSign (π x)) x) (cubePoint (fun x => -boolSign (π x)) x) ^ 2 =
        1 := by
    rw [cubePoint_apply, cubePoint_apply, Real.dist_eq]
    cases π x <;> norm_num [boolSign]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Cslib.Circuits.Arithmetic.Separation.Flat
