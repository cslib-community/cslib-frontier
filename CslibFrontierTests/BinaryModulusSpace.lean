/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryModulus
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-! Ordinary-import checks for the outer modulus search. -/

set_option linter.privateModule false

namespace CslibFrontierTests.BinaryModulusSpace

open Cslib Cslib.BinaryField Turing.BinaryField
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- A passing candidate zero is kept as a successful answer. -/
example : Cslib.findCode (fun _ => true) 0 3 = some 0 := rfl

/-- Degree three chooses the first passing code, 11, in little-endian order. -/
example : modulusBitsScan 3 = [true, true, false, true] := by
  rw [modulusBitsScan_eq_findCode]
  decide

/-- There is no irreducible code of degree zero, so the total search returns an empty word. -/
example : modulusBitsScan 0 = [] := by
  rw [modulusBitsScan_eq_findCode]
  decide

/-- Native modulus search can retain the degree in the same linear space bound. -/
example :
    ComputableInSpace (fun w => (w, modulusBitsScan w)) encNat (encPair encNat encBits)
      (fun w => w + 1) := by
  have hin : (fun w => (encNat w).length) ≼ fun w => w + 1 :=
    .of_le fun w => (length_encNat_le_self w).trans (Nat.le_succ w)
  exact budget_prod (budget_id hin) modulusBitsScan_inSpace

end CslibFrontierTests.BinaryModulusSpace
