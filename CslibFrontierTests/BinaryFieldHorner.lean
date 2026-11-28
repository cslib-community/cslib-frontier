/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryFieldHorner
meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryFieldHorner

/-! Checked packed Horner workspace and evaluation at zero and two coefficient blocks. -/

set_option linter.privateModule false

open Turing Turing.BinaryField

/-- The native evaluator supplies linear workspace through an ordinary import. -/
example : MultiTapeTM.ComputableInSpace HornerInput.evaluate encHornerInput encCoefficients
    (fun p => (encHornerInput p).length) :=
  HornerInput.evaluate_inSpace

/-- The evaluator's public equation determines the result of a request with no blocks. -/
example : (Turing.BinaryField.HornerInput.mk [true, true, true] [true, false] 9 0).evaluate =
    [] := by
  rw [Turing.BinaryField.HornerInput.evaluate_eq]
  exact Cslib.BinaryField.hornerBits_eq_iterate 2
    (Cslib.BinaryField.fieldMulMod [true, true, true]) [true, false]
    (fun i => Cslib.BitString.lowBits 2 (9 >>> (2 * i))) 0

-- The packed blocks encode `1 + X·t`. At `t = X`, this reduces to `X` modulo `X² + X + 1`.
set_option linter.hashCommand false in
#guard (Turing.BinaryField.HornerInput.mk [true, true, true] [false, true] 9 2).evaluate ==
  [false, true]
