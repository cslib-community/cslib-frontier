/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (ordinary plain core regression client)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Ordinary core composition with distinct time/workspace budgets and order-sensitive outputs. -/

open Turing.MultiTapeTM

-- The copying machine has linear time and zero workspace; the resource bounds stay independent.
example : ComputableInPolyTime (fun w : List Bool => w) encBits encBits := by
  refine ⟨fun n => n + 1, fun _ => 0, ?_, ?_, ?_⟩
  · fun_prop
  · fun_prop
  · exact computableInTimeAndSpace_id (enc := encBits)

example : ComputableInPolyTime
    (fun p : List Bool × List Bool =>
      if p.1 == p.2 then (p.1, p.2) else (p.2, p.1))
    (encPair encBits encBits) (encPair encBits encBits) := by
  have hl := ComputableInPolyTime.fst encBits encBits
  have hr := ComputableInPolyTime.snd encBits encBits
  exact (hl.beq hr).ite' (hl.prod hr) (hr.prod hl)

-- A nonempty unequal pair takes the second branch, preserving the order of both words.
example : (if ([true, false] : List Bool) == [false] then
    ([true, false], [false]) else ([false], [true, false])) =
      ([false], [true, false]) := rfl

example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {left right : α → β} [DecidableEq β]
    (hl : ComputableInPolyTime left input output)
    (hr : ComputableInPolyTime right input output) :
    ComputableInPolyTime (fun a => decide (left a ≠ right a ∨ right a ≠ left a))
      input encBool := by
  exact ComputableInPolyTime.decide_or (hl.decide_ne hr) (hr.decide_ne hl)
