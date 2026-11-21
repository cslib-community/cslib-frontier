/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native binary-field scalar certificates)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryField

/-! Ordinary-import clients for supplied-modulus multiplication, including reduction and
padding. The resource certificate is composed with a caller that swaps its two operands. -/

set_option linter.privateModule false

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.BinaryField Cslib.BinaryField

-- X * X = X + 1 modulo X² + X + 1.
example : fieldMulMod [true, true, true] [false, true] [false, true] =
    [true, true] := by decide

-- Missing high coefficients are zero, and overlong inputs are truncated to the degree.
example : fieldMulMod [true, true, true] [true] [true, false, true] =
    [true, false] := by decide

example : fieldMulMod [] [true] [true] = [] := by decide

example : ComputableInSpace
    (fun p : MulInput => fieldMulMod p.modulus p.right p.left)
    encMulInput encCoefficients (fun p => (encMulInput p).length) := by
  have hid : ComputableInSpace (fun p : MulInput => p) encMulInput encMulInput
      (fun p => (encMulInput p).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  exact budget_comp_linear fieldMulMod_inSpace
    (encMulInput_mk_budget (encMulInput_modulus_budget hid)
      (encMulInput_right_budget hid) (encMulInput_left_budget hid))
