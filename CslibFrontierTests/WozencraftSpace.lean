/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Wozencraft
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldArithmetic

/-! Ordinary-import checks for native selection of a Wozencraft coordinate. -/

set_option linter.privateModule false

namespace CslibFrontierTests.WozencraftSpace

open Cslib.Code Cslib.BinaryField
open Turing.Wozencraft Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- In the basis of the field modulo `1 + X + X²`, the constant coefficient of `X` is zero
while the constant coefficient of `X · X = 1 + X` is one. -/
example :
    wozencraftBitWith (fieldMulMod [true, true, true]) [false, true] [false, true] 0 0 = false ∧
    wozencraftBitWith (fieldMulMod [true, true, true]) [false, true] [false, true] 1 0 = true :=
  by decide

/-- An index far beyond either half returns the default. -/
example :
    wozencraftBitWith (fieldMulMod [true, true, true]) [false, true] [false, true] 0 (2 ^ 60) =
      false ∧
    wozencraftBitWith (fieldMulMod [true, true, true]) [false, true] [false, true] 1 (2 ^ 60) =
      false := by decide

private def chooseWord (context : Bool) (point evaluation : List Bool) : List Bool :=
  if context then point else evaluation

/-- The native caller can use a runtime context for its word operation. -/
example :
    ComputableInSpace
      (fun p : BitInput Bool => wozencraftBitWith (chooseWord p.context)
        p.point p.evaluation p.half p.bit)
      (encBitInput encBool) encBool (fun p => (encBitInput encBool p).length) := by
  let encWords := encPair (encList encBool) (encList encBool)
  have hw := snd encBool encWords
  have hchoose := budget_ite (fst encBool encWords) hw.fst' hw.snd'
  exact bitWith_inSpace (mul := chooseWord) (hchoose.of_enc_eq fun _ => rfl)

end CslibFrontierTests.WozencraftSpace
