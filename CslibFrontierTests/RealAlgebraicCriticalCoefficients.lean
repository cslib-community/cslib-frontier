/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoefficientEvaluation
import Mathlib.Tactic.NormNum

/-! # Constructed critical coefficient certificates and edge cases -/

public section
namespace CslibFrontierTests.RealAlgebraicCriticalCoefficients

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM
open MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

-- Above-dimension addresses return zero even for arbitrary evaluators and nonprime moduli.
example (p n ell B m : ℕ) (hm : ell ^ n < m)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) :
    quotientCharacteristicValue p n ell B m v J r = 0 := by
  simp [quotientCharacteristicValue, traceExponentialCoefficient, Nat.not_le.mpr hm]

-- A single certificate handles binary deformation parameters and coefficient addresses.
example : (fun q : ℕ × ℕ => criticalCoefficientValue 101 1 1 q.1 q.2 (fun _ => 0)) ∈
    CountingFunction 9 (encPair encNat encNat) encNat := by
  simpa using criticalCoefficientValue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (p := fun _ => 101) (n := fun _ => 1) (d := fun _ => 1)
    (u := fun q : ℕ × ℕ => q.1) (m := fun q => q.2) (value := fun _ => 0)
    (.const 101) (.const 1) (.const 1) (by fun_prop) (by fun_prop)
    (CountingFunction.of_polyTime (.const 0))

-- A positive-dimensional instance satisfies all cutoffs, including at zero deformation.
theorem positiveDimensionalInstance (u m : ℕ) : criticalCoefficientValue 101 1 1 u m (fun _ => 0) =
    ((multiplicationMatrix (by decide : 1 ≤ 2)
      (criticalLower 2 (fun i : Fin 1 => ((separatedCenters 2 i : ℕ) : ZMod 101))
        (u : ZMod 101) 0)
      (criticalLower_degree 2 (by decide) _ _ 0 (by simp))
      (deformedPolynomial 2 (fun i : Fin 1 => ((separatedCenters 2 i : ℕ) : ZMod 101))
        (u : ZMod 101) 0)).charpoly.coeff m).val := by
  apply criticalCoefficientValue_eq 1 (by decide) u 0 (by simp) (by decide) (by decide)
  intro y
  simp

end CslibFrontierTests.RealAlgebraicCriticalCoefficients
