/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CharacteristicCoefficients
import Mathlib.Tactic.NormNum

/-! # Characteristic-coefficient evaluator edge cases and uniform certificates -/

public section
namespace CslibFrontierTests.RealAlgebraicCharacteristic

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM Polynomial

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The logarithm's zero slot is masked before inversion, including at the smallest prime.
example (t : ℕ) : traceLogarithmResidue 2 0 t = 0 := by
  simp [traceLogarithmResidue]

-- The total default above the dimension does not depend on any primality hypothesis.
example (p : ℕ) (t : ℕ → ℕ) : traceExponentialCoefficient p 0 1 t = 0 := by
  simp [traceExponentialCoefficient]

-- The factorial evaluator includes 0!, and the below-prime denominator is invertible.
example : (factorialResidue 2 0 : ZMod 2) = 1 := by
  rw [factorialResidue_cast]
  norm_num

example : (powMod 3 (factorialResidue 3 2) (3 - 2) : ZMod 3) = (2 : ZMod 3)⁻¹ := by
  simpa using (factorialResidue_inverse (p := 3) (j := 2) (by decide))

-- The empty matrix works at p=2 with an arbitrary, ignored trace slot zero.
theorem emptyMatrix (t : ℕ → ℕ) : traceExponentialCoefficient 2 0 0 t = 1 := by
  have h := traceExponentialCoefficient_eq_charpoly
    (p := 2) (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) (by decide) 0 t
    (by intro k hk h; simp only [Fintype.card_fin] at h; omega)
  simpa [Matrix.charpoly_isEmpty, ZMod.val_one_eq_one_mod] using h

-- For a 1-by-1 identity matrix over F_3, the characteristic polynomial is X-1.
example : traceExponentialCoefficient 3 1 0 (fun _ => 1) = 2 := by
  have h := traceExponentialCoefficient_eq_charpoly
    (p := 3) (1 : Matrix (Fin 1) (Fin 1) (ZMod 3)) (by decide) 0 (fun _ => 1)
    (by intro k _ _; simp)
  simpa [Matrix.charpoly_one, ZMod.val_neg_one] using h

example : traceExponentialCoefficient 3 1 1 (fun _ => 1) = 1 := by
  have h := traceExponentialCoefficient_eq_charpoly
    (p := 3) (1 : Matrix (Fin 1) (Fin 1) (ZMod 3)) (by decide) 1 (fun _ => 1)
    (by intro k _ _; simp)
  simpa [Matrix.charpoly_one, AddMonoidAlgebra.one_def, ZMod.val_one_eq_one_mod] using h

-- One fixed machine handles every binary coefficient address, including the zero default.
example : (fun d : ℕ => traceExponentialCoefficient 3 1 d (fun _ => 1)) ∈
    CountingFunction 5 encNat encNat := by
  simpa using (traceExponentialCoefficient_mem (a := 0) Decoder.nat
    (p := fun _ : ℕ => 3) (D := fun _ => 1) (d := fun d => d) (t := fun _ => 1)
    (ComputableInPolyTime.const 3) (ComputableInPolyTime.const 1) (by fun_prop)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1)))

end CslibFrontierTests.RealAlgebraicCharacteristic
