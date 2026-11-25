/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.CubePoints
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.UnitExponent
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Tests of the cube points and of the unit exponents of a spectral point, as a client: a vertex
of the square and its distance to the opposite vertex; the support point, whose unit exponents at
legs on two parties are at most `0`; the unit exponent of a pull-back. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatCube

open Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.Flat

/-- The vertex `(1/2, -1/2)` of the square. -/
example : cubePoint (fun x : Fin 2 => boolSign (x = 0)) 1 = -1 / 2 := by
  rw [cubePoint_apply]
  norm_num [boolSign]

/-- Opposite vertices of the square are at distance `√2`. -/
example : dist (cubePoint fun x : Fin 2 => boolSign (x = 0))
    (cubePoint fun x : Fin 2 => -boolSign (x = 0)) = √2 := by
  simpa using dist_cubePoint_neg (k := 2) fun x => decide (x = 0)

/-- At the support point, legs on two parties have unit exponent at most `0`. -/
example (π : Fin 3 → Bool) (h : ∀ a, π a = true ∨ π a = false) :
    (SpectralPoint.support ℚ Bool).unitExponent π ≤ 0 :=
  ((SpectralPoint.support ℚ Bool).unitExponent_le_of_two π true false h).trans_eq
    (SpectralPoint.wireExponent_support true false)

/-- The unit exponents of a pull-back along `Bool.not`. -/
example (F : SpectralPoint ℚ Bool) (π : Fin 2 → Bool) :
    (F.pull not).unitExponent π = F.unitExponent (not ∘ π) :=
  F.pull_unitExponent not π

end CslibFrontierTests.SeparationFlatCube
