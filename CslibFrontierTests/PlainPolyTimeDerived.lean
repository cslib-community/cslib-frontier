/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (ordinary-import regression client)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Lean.Elab.Command

/-! Plain guards composed from computed operands, with no tidy transition in proof search.
The absence checks name exactly the three retired providers, rather than their plain replacements.
-/

open Turing.MultiTapeTM

run_cmd do
  let env ← Lean.getEnv
  for name in [`Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_or,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_ne,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_beq] do
    if env.contains name then throwError "retired tidy guard provider: {name}"

example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool} [DecidableEq β]
    {left right : α → β}
    (hl : ComputableInPolyTime left input output)
    (hr : ComputableInPolyTime right input output) :
    ComputableInPolyTime (fun a => decide (left a ≠ right a ∨ right a ≠ left a))
      input encBool := by
  exact ComputableInPolyTime.decide_or (hl.decide_ne hr) (hr.decide_ne hl)

example : ComputableInPolyTime (fun p : Bool × Bool => p.1 == p.2)
    (encPair encBool encBool) encBool := by
  exact (ComputableInPolyTime.fst encBool encBool).beq
    (ComputableInPolyTime.snd encBool encBool)

example {α : Type} {input : α ↪ List Bool} {left right : α → Prop}
    [∀ a, Decidable (left a)] [∀ a, Decidable (right a)]
    (hl : ComputableInPolyTime (fun a => decide (left a)) input encBool)
    (hr : ComputableInPolyTime (fun a => decide (right a)) input encBool) :
    ComputableInPolyTime (fun a => decide (left a ∨ right a)) input encBool := by
  fun_prop (config := { maxTransitionDepth := 0 })
