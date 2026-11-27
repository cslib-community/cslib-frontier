/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalJacobianEvaluation
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Mixed partials, singular determinants and the actual critical Jacobian -/

public section

namespace CslibFrontierTests.RealAlgebraicCriticalEvaluation

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic
open Turing.MultiTapeTM MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- First derivatives also work at prime 3; the larger cutoff belongs to second derivatives.
example : (firstPartialResidue 3 1 0 [2] (fun z => z[0]?.getD 0) : ZMod 3) = 1 := by
  change (firstPartialResidue 3 1 (0 : Fin 1).val [2]
    (fun z => z[0]?.getD 0) : ZMod 3) = 1
  rw [firstPartialResidue_cast (X 0 : MvPolynomial (Fin 1) (ZMod 3)) 0 [2]
    (fun z => z[0]?.getD 0) ((totalDegree_X_le 0).trans_lt (by decide)) (by decide)
    (by intro z; simp)]
  simp

private noncomputable def inputPolynomial : MvPolynomial (Fin 2) (ZMod 7) :=
  X 0 ^ 2 + X 0 * X 1

private def inputValue (z : List ℕ) : ℕ :=
  ((z[0]?.getD 0) ^ 2 + (z[0]?.getD 0) * (z[1]?.getD 0)) % 7

private theorem input_degree : inputPolynomial.totalDegree < 7 - 1 := by
  have h0 : (X 0 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree ≤ 1 := totalDegree_X_le 0
  have h1 : (X 1 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree ≤ 1 := totalDegree_X_le 1
  have hp := totalDegree_pow (X 0 : MvPolynomial (Fin 2) (ZMod 7)) 2
  have hm := totalDegree_mul (X 0 : MvPolynomial (Fin 2) (ZMod 7)) (X 1)
  have hs := totalDegree_add (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 7)) (X 0 * X 1)
  change (X 0 ^ 2 + X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree < 7 - 1
  omega

private theorem input_correct (z : List ℕ) :
    (inputValue z : ZMod 7) =
      eval (fun i : Fin 2 => (z[i.val]?.getD 0 : ZMod 7)) inputPolynomial := by
  simp [inputValue, inputPolynomial]

private theorem derivative_two (i : Fin 2) :
    pderiv i (2 : MvPolynomial (Fin 2) (ZMod 7)) = 0 := by
  simpa only [Nat.cast_ofNat] using (Derivation.map_natCast (pderiv i) 2)

-- Repeating the differentiation coordinate contributes the explicit factor two.
example : (secondPartialResidue 7 2 0 0 [2, 3] inputValue : ZMod 7) = 2 := by
  change (secondPartialResidue 7 2 (0 : Fin 2).val (0 : Fin 2).val
    [2, 3] inputValue : ZMod 7) = 2
  rw [secondPartialResidue_cast inputPolynomial (0 : Fin 2) (0 : Fin 2)
    [2, 3] inputValue input_degree (by decide) input_correct]
  norm_num [inputPolynomial, pderiv_pow, pderiv_mul, derivative_two]

example : (secondPartialResidue 7 2 0 1 [2, 3] inputValue : ZMod 7) = 1 := by
  change (secondPartialResidue 7 2 (0 : Fin 2).val (1 : Fin 2).val
    [2, 3] inputValue : ZMod 7) = 1
  rw [secondPartialResidue_cast inputPolynomial (0 : Fin 2) (1 : Fin 2)
    [2, 3] inputValue input_degree (by decide) input_correct]
  norm_num [inputPolynomial, pderiv_pow, pderiv_mul, derivative_two]

-- Empty and singular matrices exercise the genuine integer determinant program.
example : (modularMatrixDeterminant 7 0 (fun _ => 3) : ZMod 7) = 1 := by
  rw [modularMatrixDeterminant_cast (Matrix.of (fun _ _ : Fin 0 => (0 : ZMod 7)))
    (fun _ => 3) (by intro i; exact i.elim0)]
  simp

example : (modularMatrixDeterminant 7 2 (fun _ => 1) : ZMod 7) = 0 := by
  rw [modularMatrixDeterminant_cast (Matrix.of (fun _ _ : Fin 2 => (1 : ZMod 7)))
    (fun _ => 1) (by intro i j; rfl)]
  simp [Matrix.det_fin_two]

-- For this coupled polynomial the derivative matrix is [[0,1],[1,6]], with determinant 6.
example : (criticalJacobianValue 7 2 3 1 [2, 3] inputValue : ZMod 7) = 6 := by
  rw [criticalJacobianValue_cast inputPolynomial 3 1 [2, 3] inputValue
    input_degree (by decide) input_correct]
  norm_num [jacobian, criticalLower, inputPolynomial, Matrix.det_fin_two,
    pderiv_pow, pderiv_mul, derivative_two]
  decide

example : (criticalLowerValue 7 2 3 1 0 [2, 3] inputValue : ZMod 7) = 6 := by
  change (criticalLowerValue 7 2 3 1 (0 : Fin 2).val [2, 3] inputValue : ZMod 7) = 6
  rw [criticalLowerValue_cast inputPolynomial 3 1 (0 : Fin 2) [2, 3] inputValue
    input_degree (by decide) input_correct]
  norm_num [criticalLower, separatedCenters, inputPolynomial, pderiv_pow, pderiv_mul]
  decide

example : (criticalObjectiveValue 7 2 3 1 [2, 3] inputValue : ZMod 7) = 3 := by
  rw [criticalObjectiveValue_cast inputPolynomial 3 1 [2, 3] inputValue input_correct]
  norm_num [deformedPolynomial, potentialPolynomial, separatedCenters, inputPolynomial,
    Fin.sum_univ_succ]
  decide

-- One certificate handles all binary moduli and powers, including total default inputs.
theorem uniform_jacobian_mem :
    (fun w : ℕ × ℕ => criticalJacobianValue w.1 0 w.2 1 [] (fun _ => 0)) ∈
      CountingFunction 1 (encPair encNat encNat) encNat := by
  apply criticalJacobianValue_mem (a := 0) (p := fun w : ℕ × ℕ => w.1)
    (n := fun _ => 0) (ell := fun w => w.2) (u := fun _ => 1)
    (z := fun _ => []) (value := fun _ => 0) (Decoder.pair Decoder.nat Decoder.nat)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact CountingFunction.of_polyTime (ComputableInPolyTime.const 0)

end CslibFrontierTests.RealAlgebraicCriticalEvaluation
