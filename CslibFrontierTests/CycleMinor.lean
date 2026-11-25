/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.CycleMinor
public import Mathlib.Data.ZMod.Basic

/-! Concrete `module` clients for the cycle-and-minor function at `d = 4`: the two branches, the
multilinear representatives and the identities used for the lower bounds. -/

public section

namespace CslibFrontierTests.CycleMinor

open Cslib.Circuits MvPolynomial Cslib.BitString

/-- The function is the cycle test for `b = 0` and the minor bit for `b = 1`. -/
example (x : Fin 4 → Bool) (Y : Fin 4 × Fin 4 → Bool) :
    cycleMinor false x Y = (open Classical in decide (IsCycleMatrix Y)) ∧
      cycleMinor true x Y = minorBit x Y := by
  simp

/-- The component of degree `4` of the cycle branch is the Hamiltonian cycle sum. -/
example : homogeneousComponent 4 (cyclePoly (d := 4) ℤ) =
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin 4 × Fin 4) ℤ)).hamiltonianCycleSum :=
  homogeneousComponent_cyclePoly

/-- Over `F₂` the generic minor is multilinear and is the minor bit on the Boolean matrices. -/
example (x : Fin 4 → Bool) (Y : Fin 4 × Fin 4 → Bool) :
    minorPoly (ZMod 2) x ∈ restrictDegree (Fin 4 × Fin 4) (ZMod 2) 1 ∧
      eval (bitPoint Y) (minorPoly (ZMod 2) x) = bitVal (ZMod 2) (minorBit x Y) :=
  ⟨minorPoly_mem_restrictDegree x, eval_bitPoint_minorPoly x Y⟩

/-- At a padded `2 × 4` matrix the generic minor is the minor of the matrix at the columns
of `x`. -/
example (C : Matrix (Fin (4 / 2)) (Fin 4) ℤ) (x : Fin 4 → Bool) :
    eval (padRows C) (minorPoly ℤ x) = if h : (selected x).card = 4 / 2 then
      (C.submatrix id ((selected x).orderEmbOfFin h)).det else 0 :=
  eval_padRows_minorPoly C x

end CslibFrontierTests.CycleMinor
