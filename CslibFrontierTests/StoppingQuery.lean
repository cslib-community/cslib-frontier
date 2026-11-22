/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Rank

/-!
The stopping compiler is exercised through actual local input routing, padding and a complete
extension-ring product. The nonconstant test squares `X^3` modulo `X^6 + X^3 + 1` over
`ZMod 8`, so every bit of both negative coordinates must survive the composed circuit.
-/

namespace CslibFrontierTests.StoppingQuery

open Polynomial Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Frontier.FastContraction StoppingQuery
open Cslib.Circuits.Frontier LocalValueGame GaloisRingArith

private def network : DescribedNetwork ℕ := ⟨3, [([2, 0, 5], 7)]⟩

-- Only the addressed vertex's ports are read, in their original order.
example : entryRequest network ⟨4, 0, 4, 9⟩ = some ⟨7, [true, false, false], 4, 9⟩ := rfl

-- A large binary assignment never gives an out-of-range port an input bit.
example : entryRequest network ⟨2 ^ 100 + 4, 0, 4, 9⟩ =
    some ⟨7, [true, false, false], 4, 9⟩ := rfl

-- A large binary vertex index returns no terminal request.
example : entryRequest network ⟨5, 2 ^ 100, 4, 9⟩ = none := rfl

-- Entry terminals expose their label, independently of their stored local formula.
example (m p edges vertices : ℕ) (e : Entry) :
    operation m p edges vertices ⟨.entry e, Formula.const true⟩ = .inl e := rfl

-- The same physical diagonal path routes to different operands and adjacent product blocks.
private def operandPath : List Bool := [false, false, false, false, true, false, true]

example : source 0 3 3 16 (.product 5 4 2 3 (.port operandPath false 2 0)) 0 =
    some (.value 5 4 2 1 1) := rfl

example : source 0 3 3 16 (.product 5 4 2 3 (.port operandPath false 2 1)) 0 =
    some (.value 5 8 2 2 1) := rfl

-- Zero precision and an invalid assignment path both compile to explicit constants.
example : template 0 0 0 0 (.value 0 0 0 0 0) = Formula.const false := rfl

example : template 0 3 1 2 (.sumTree 0 ⟨[true, true], 0, false, 0⟩) =
    Formula.const false := rfl

-- The empty network has one empty product when there are no edges.
example (m p : ℕ) (coefficient : Fin (modulus m).length) (bit : Fin p)
    (entry : ℕ → ℕ → Ring p (modulus m)) :
    value m p 0 0 entry (root m p 0 0 coefficient bit) =
      decide (coefficient.val = 0 ∧ bit.val = 0) := by
  rw [value_root]
  simp only [Nat.pow_zero, Finset.prod_range_zero, Finset.sum_range_one]
  simpa [InterpolationGrid.factorBit, InterpolationGrid.factor] using
    (InterpolationGrid.factorBit_eq m p 0 0 0 coefficient bit).symm

private noncomputable def operand : Ring 3 (modulus 0) := val 3 (modulus 0) [0, 0, 0, 1]

private theorem representative_operand : representative 0 3 operand = X ^ 3 := by
  ext i
  simp only [representative, operand, coeff_modByMonicHom_val]
  have hlen : (modulus 0).length = 6 := rfl
  rw [hlen]
  by_cases hi : i < 6
  · interval_cases i <;> norm_num [Polynomial.coeff_X_pow]
  · have hne : i ≠ 3 := by omega
    simp [hi, Polynomial.coeff_X_pow, hne]

private theorem root_square (coefficient : Fin (modulus 0).length) (bit : Fin 3) :
    value 0 3 0 2 (fun _ _ => operand) (root 0 3 0 2 coefficient bit) =
      ((representative 0 3 (operand * operand)).coeff coefficient.val).val.testBit bit.val := by
  rw [value_root]
  simp [pow_two]

-- A nonconstant extension coordinate participates in the actual stopping sum/product compiler.
example (bit : Fin 3) :
    value 0 3 0 2 (fun _ _ => operand) (root 0 3 0 2 ⟨0, by decide⟩ bit) = true ∧
      value 0 3 0 2 (fun _ _ => operand) (root 0 3 0 2 ⟨3, by decide⟩ bit) = true := by
  rw [root_square, root_square, representative_mul_coeff, representative_mul_coeff]
  simp_rw [convolutionCircuit_eq_coeff _ _ _ _ _ (natDegree_representative_lt 0 3 operand)]
  rw [representative_operand]
  have hsquare : (X : (ZMod (2 ^ 3))[X]) ^ 3 * X ^ 3 = X ^ 6 := by ring
  rw [hsquare]
  fin_cases bit <;> norm_num [SparseTrinomial.reducedCoeff, modulusExp, Polynomial.coeff_X_pow] <;>
    decide

-- The circuit's every edge decreases rank even for arbitrary interpreted terminal bits.
example (m p edges vertices : ℕ) (input : Entry → Bool) :
    (decoder m p edges vertices input).Descends (rank m p edges vertices) :=
  descends m p edges vertices input

end CslibFrontierTests.StoppingQuery
