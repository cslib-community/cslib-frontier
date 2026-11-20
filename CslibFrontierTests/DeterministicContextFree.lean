/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Languages.DeterministicContextFree

/-! # Acceptance by a deterministic pushdown automaton -/

set_option linter.privateModule false

namespace Cslib

open Automata

/-- Reading `true` pushes a marker. The epsilon move pops it and enters the accepting state. -/
private def oneSymbol : DPDA Bool Bool Bool where
  start := false
  bottom := false
  accept := {true}
  transition
    | false, false, some true => some (false, [true, false])
    | false, true, none => some (true, [])
    | _, _, _ => none
  epsilon_exclusive q γ a := by cases q <;> cases γ <;> cases a <;> simp

example : [true] ∈ Acceptor.language oneSymbol := by
  rw [Acceptor.mem_language, DPDA.accepts_iff]
  refine ⟨true, rfl, [false], ?_⟩
  have readStep : oneSymbol.Step (oneSymbol.initial [true]) ⟨false, [], [true, false]⟩ :=
    DPDA.step_of_symbol (tail := []) (pushed := [true, false]) rfl
  have epsilonStep : oneSymbol.Step ⟨false, [], [true, false]⟩ ⟨true, [], [false]⟩ :=
    DPDA.step_of_epsilon (tail := [false]) (pushed := []) rfl
  exact (Relation.ReflTransGen.single readStep).tail epsilonStep

example : [] ∉ Acceptor.language oneSymbol := by
  rw [Acceptor.mem_language, DPDA.accepts_iff]
  rintro ⟨q, hq, stack, run⟩
  have stuck (c : DPDA.Config Bool Bool Bool) : ¬ oneSymbol.Step (oneSymbol.initial []) c :=
    nofun
  have equal := (Relation.reflTransGen_iff_eq stuck).mp run
  have state := congrArg DPDA.Config.state equal
  change q = false at state
  rw [state] at hq
  cases hq

example : Language.IsDeterministicContextFree (Acceptor.language oneSymbol) :=
  ⟨inferInstance, Bool, Bool, inferInstance, inferInstance, oneSymbol, rfl⟩

end Cslib
