/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

/-!
# Finite-state conversion from raw bits to framed Boolean lists

`bitsToBoolListT` changes only the representation of a Boolean list, inserting the standard
one-bit element frames after an outer frame has been added. Keeping the transducer here lets both
the asymptotic calculus and retained native compilers use the same concrete machine.

## Main definitions

* `Turing.MultiTapeTM.Internal.bitsToBoolListT`: convert one framed raw word to a Boolean list.
-/

public section

namespace Turing.MultiTapeTM.Internal

open Encodings

/-- Convert one framed raw word into a list of framed one-bit words. -/
def bitsToBoolListT : Transducer Bool Bool where
  q₀ := false
  step q b := if q then (false, [b, false]) else (b, if b then [true] else [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> decide
  length_final_le _ := by decide

/-- The framing transducer emits exactly the standard Boolean-list encoding. -/
theorem bitsToBoolListT_run (word : List Bool) :
    bitsToBoolListT.run bitsToBoolListT.q₀ (frame word) = encList encBool word := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    change bitsToBoolListT.run false (frame word) = encList encBool word at ih
    change true :: b :: false :: bitsToBoolListT.run false (frame word) = _
    rw [ih]
    rfl

end Turing.MultiTapeTM.Internal
