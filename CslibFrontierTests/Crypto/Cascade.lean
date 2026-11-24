/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade

/-!
# Cascade evaluation tests

Use one-bit message blocks and a two-bit key to exercise the separate widths and the extension
identity.
-/

set_option linter.privateModule false

open Cslib.Crypto Turing.MultiTapeTM

private def toggle (key block : List Bool) : List Bool :=
  if block.headD false then key.map (!·) else key

example : cascadeFamily (fun _ => 1) toggle [true, false] [] = [true, false] :=
  cascadeFamily_nil _ _ _

example : cascadeFamily (fun _ => 1) toggle [true, false] [true, false] = [false, true] := by
  decide

example : cascadeFamily (fun _ => 1) toggle [true, false] ([true] ++ [true, false]) =
    cascadeFamily (fun _ => 1) toggle (cascadeFamily (fun _ => 1) toggle [true, false] [true])
      [true, false] :=
  cascadeFamily_append (fun key block _ => by
    unfold toggle
    split <;> simp) _ (by decide) (by decide) (by decide)

example : ComputableInPolyTime
    (fun p : List Bool × List Bool => cascadeFamily (fun _ => 1) (fun key _ => key) p.1 p.2)
    (encPair encBits encBits) encBits :=
  computableInPolyTime_cascadeFamily (ComputableInPolyTime.const 1) (fun _ _ _ => rfl)
    (ComputableInPolyTime.fst encBits encBits)
