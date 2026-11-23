/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Circuit.Boolean.InnerProductApproximation
import CslibFrontier.Computability.Circuit.Pi
import Mathlib.Tactic.NormNum

/-!
# Tests for optimal inner-product approximation

The one-gate budget on two coordinate pairs has attainable correlation `1/2`, and the same
endpoint bounds every circuit within that budget. Zero coordinates and zero budget give
correlation one. Concrete circuits check that the cost counts syntactically nonlinear gates,
including gates reading repeated wires, while XOR and sharing remain free.
-/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.InnerProductApproximation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString Finset
open scoped BigOperators

/-- A circuit with at most one nonlinear gate attains correlation `1/2` with two input pairs. -/
theorem one_nonlinear_gate_two_pairs :
    ∃ c : Circuit (fullSignature 2 Bool) (2 + 2) 1,
      c.program.cost (nonlinearCost fullInterpretation) ≤ 1 ∧
      (𝔼 x, signVal (fstBits x ⬝ᵥ sndBits x) * signVal (c.eval fullInterpretation x 0)) =
        (1 : ℝ) / 2 := by
  have h := (isGreatest_innerProduct_correlation (n := 2) (m := 1) (by decide)).1
  simpa only [Set.mem_ofPred_eq, pow_one, pow_two, div_mul_eq_div_div,
    div_self (by norm_num : (2 : ℝ) ≠ 0)] using h

-- The second component of the endpoint applies to every circuit under the same budget.
example (c : Circuit (fullSignature 2 Bool) (2 + 2) 1)
    (hc : c.program.cost (nonlinearCost fullInterpretation) ≤ 1) :
    (𝔼 x, signVal (fstBits x ⬝ᵥ sndBits x) * signVal (c.eval fullInterpretation x 0)) ≤
      (1 : ℝ) / 2 := by
  have h := (isGreatest_innerProduct_correlation (n := 2) (m := 1) (by decide)).2
    ⟨c, hc, rfl⟩
  simpa only [pow_one, pow_two, div_mul_eq_div_div,
    div_self (by norm_num : (2 : ℝ) ≠ 0)] using h

-- The empty instance is attained by a circuit of exactly zero nonlinear cost.
example :
    ∃ c : Circuit (fullSignature 2 Bool) (0 + 0) 1,
      c.program.cost (nonlinearCost fullInterpretation) = 0 ∧
      (𝔼 x, signVal (fstBits x ⬝ᵥ sndBits x) * signVal (c.eval fullInterpretation x 0)) = 1 := by
  obtain ⟨c, hc, hcorr⟩ :=
    (isGreatest_innerProduct_correlation (n := 0) (m := 0) (by decide)).1
  exact ⟨c, Nat.eq_zero_of_le_zero hc, by simpa only [pow_zero, div_one] using hcorr⟩

private def repeatedAnd : Circuit (fullSignature 2 Bool) 1 1 :=
  Circuit.oneGate (.fn fun x => x 0 * x 1) (fun _ => 0)

-- Duplicating an AND input does not make its syntactic gate cost disappear.
example (x : BitString 1) :
    repeatedAnd.program.cost (nonlinearCost fullInterpretation) = 1 ∧
      repeatedAnd.eval fullInterpretation x 0 = x 0 := by
  constructor
  · decide +kernel
  · change x 0 * x 0 = x 0
    cases x 0 <;> rfl

private def sharedAndCancellation : Circuit (fullSignature 2 Bool) 2 1 :=
  (Circuit.oneGate (σ := fullSignature 2 Bool) (n := 1)
    (.fn fun x => x 0 + x 1) (fun _ => 0)).comp
    (Circuit.oneGate (.fn fun x => x 0 * x 1) id)

-- One AND result feeds both XOR inputs: it is charged once and cancels semantically.
example (x : BitString 2) :
    sharedAndCancellation.program.cost (nonlinearCost fullInterpretation) = 1 ∧
      sharedAndCancellation.eval fullInterpretation x 0 = false := by
  constructor
  · decide +kernel
  · change (x 0 * x 1) + (x 0 * x 1) = false
    cases x 0 <;> cases x 1 <;> rfl

private def xorOnly : Circuit (fullSignature 2 Bool) 2 1 :=
  Circuit.oneGate (.fn fun x => x 0 + x 1) id

-- A nonconstant affine output consumes no nonlinear gates.
example (x : BitString 2) :
    xorOnly.program.cost (nonlinearCost fullInterpretation) = 0 ∧
      xorOnly.eval fullInterpretation x 0 = (x 0 ^^ x 1) := by
  constructor
  · decide +kernel
  · rfl

-- A matching Fourier mask has negative coefficient; flatness concerns absolute values.
example :
    Cslib.BitString.fourierCoeff
      (fun z : BitString (2 + 2) => signVal (fstBits z ⬝ᵥ sndBits z)) {0, 2} =
        -(1 : ℝ) / 4 := by
  rw [fourierCoeff_signVal_dotProduct_fstBits_sndBits]
  norm_num [dotProduct, Fin.sum_univ_two, Bool.mul_eq_and, Bool.add_eq_xor, signVal]

end CslibFrontierTests.Computability.Circuit.Boolean.InnerProductApproximation
