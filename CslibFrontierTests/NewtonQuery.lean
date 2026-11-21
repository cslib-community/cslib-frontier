/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.NewtonQuery
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.NewtonCorrection

open Cslib.Circuits.Frontier.FastContraction
open NewtonQuery

-- The second round refers to the same earlier iterate at its two different multiplication ports.
example : step (7, false) = (2, 4) ∧ step (7, true) = (2, 6) ∧
    step (6, false) = (3, 5) ∧ step (5, true) = (2, 4) ∧ step (5, false) = (2, 0) := by
  decide

-- The one-bit seed calls the raw operand, and the input stage is terminal.
example : step (1, true) = (1, 0) ∧ step (0, false) = (0, 0) := by decide

-- Subtracting the scalar two from itself must yield zero at every precision and address.
example (m p : ℕ) (i : Fin (modulus m).length) (j : Fin p) :
    (Cslib.Circuits.Boolean.carryLookaheadAdd p).eval Cslib.Circuits.Boolean.interpretation
      (NewtonCorrection.pair i.val (representative m p 2)) j = false := by
  rw [NewtonCorrection.bit_sum, sub_self]
  simp [representative]

-- A high source digit never reaches the lifted one-bit Newton seed.
example (m : ℕ) (i : Fin (modulus m).length) :
    ((Cslib.GaloisRingArith.residueSeed (modulus m) [1]).getD i.val 0).testBit 7 = false := by
  rw [ResidueInverse.seed_bit _ _ _ _ (by simp)]
  rfl
