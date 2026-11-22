/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedValueGame

/-!
The complete compiled product is tested on modular underflow: over `ZMod 8`, reducing
`X^2 * X^2` modulo `X^4 + X^2 + 1` gives `-X^2 - 1`. Both negative coordinates must
therefore have all three bits set; the intervening coordinate is zero. The tests exercise
the finishing adder, signed carry-save tree, and operand routing through the public theorem.
-/

namespace CslibFrontierTests.SignedValueGame

open Polynomial Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Frontier.FastContraction
open Cslib.SparseTrinomial SignedValueGame
open Turing.MultiTapeATM.WordGame

private noncomputable def operand : (ZMod (2 ^ 3))[X] := X ^ 2

private theorem degree_operand : operand.natDegree < 2 * 2 := by
  exact (natDegree_X_pow_le (R := ZMod (2 ^ 3)) 2).trans_lt (by decide)

private theorem square_operand : operand * operand = (X : (ZMod (2 ^ 3))[X]) ^ 4 := by
  unfold operand
  ring

-- Negative terms occur in both halves of the reduced coefficient array.
example (bit : Fin 3) :
    value 2 0 operand operand (root 2 0 operand operand bit) = true ∧
      value 2 2 operand operand (root 2 2 operand operand bit) = true := by
  rw [value_root_eq_reducedCoeff 2 0 operand operand degree_operand degree_operand,
    value_root_eq_reducedCoeff 2 2 operand operand degree_operand degree_operand,
    square_operand]
  fin_cases bit <;> norm_num [reducedCoeff, coeff_X_pow] <;> decide

-- The adjacent zero coefficient remains zero through the same compiled circuit.
example (bit : Fin 3) :
    value 2 1 operand operand (root 2 1 operand operand bit) = false := by
  rw [value_root_eq_reducedCoeff 2 1 operand operand degree_operand degree_operand,
    square_operand]
  fin_cases bit <;> norm_num [reducedCoeff, coeff_X_pow]

-- The actual alternating value game accepts the correct claim and rejects the opposite one.
example (enc : LocalValueGame.Claim Address ↪ List Bool) (bit : Fin 3) :
    Wins (LocalValueGame.update (decoder 2 0 operand operand) enc)
        (LocalValueGame.position (decoder 2 0 operand operand) enc
          ⟨root 2 0 operand operand bit, true⟩) ∧
      ¬ Wins (LocalValueGame.update (decoder 2 0 operand operand) enc)
        (LocalValueGame.position (decoder 2 0 operand operand) enc
          ⟨root 2 0 operand operand bit, false⟩) := by
  rw [wins_root_iff 2 0 operand operand degree_operand degree_operand,
    wins_root_iff 2 0 operand operand degree_operand degree_operand, square_operand]
  fin_cases bit <;> norm_num [reducedCoeff, coeff_X_pow] <;> decide

end CslibFrontierTests.SignedValueGame
