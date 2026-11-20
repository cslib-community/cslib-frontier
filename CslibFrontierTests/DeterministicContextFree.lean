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
    | false, false, some true => some { state := false, replacement := [true, false] }
    | false, true, none => some { state := true, replacement := [] }
    | _, _, _ => none
  epsilon_exclusive q γ a := by cases q <;> cases γ <;> cases a <;> simp

private theorem run_to_final (rest : List Bool) :
    Relation.ReflTransGen oneSymbol.Step (oneSymbol.initial (true :: rest))
      ⟨true, rest, [false]⟩ :=
  (Relation.ReflTransGen.single
    (DPDA.step_of_epsilon (tail := [false]) (move := ⟨true, []⟩) rfl)).head
      (DPDA.step_of_symbol (tail := []) (move := ⟨false, [true, false]⟩) rfl)

example : [true] ∈ Acceptor.language oneSymbol := by
  rw [Acceptor.mem_language, DPDA.accepts_iff]
  exact ⟨true, rfl, [false], run_to_final []⟩

example : [true, false] ∉ Acceptor.language oneSymbol := by
  rw [Acceptor.mem_language, DPDA.accepts_iff]
  rintro ⟨q, hq, stack, run⟩
  have hq' : q = true := hq
  subst q
  have stuck (input stack : List Bool) (c : DPDA.Config Bool Bool Bool) :
      ¬oneSymbol.Step ⟨true, input, stack⟩ c := by
    cases stack with
    | nil => exact nofun
    | cons γ tail =>
      cases γ <;> cases input with
      | nil => exact nofun
      | cons a rest => cases a <;> exact nofun
  have unique : Relator.RightUnique oneSymbol.Step := by
    intro a b c hab hac
    exact DPDA.step_deterministic hab hac
  rcases Relation.ReflTransGen.total_of_right_unique unique (run_to_final [false]) run with h | h
  · have equal := (Relation.reflTransGen_iff_eq (stuck [false] [false])).mp h
    cases congrArg DPDA.Config.input equal
  · have equal := (Relation.reflTransGen_iff_eq (stuck [] stack)).mp h
    cases congrArg DPDA.Config.input equal

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
