/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.WellNested

/-! Clients of the public MPDA API under module encapsulation: a one-stack automaton that pushes
on `'a'` and pops on `'b'` accepts `ab` and rejects `b`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MPDA

open Cslib Cslib.Automata Cslib.Automata.MPDA

/-- One control state; `'a'` pushes `()` onto the only stack and `'b'` pops it. -/
private def pushPopAB : MPDA 1 Unit Char Unit where
  Tr _ μ _ := μ = ('a', .push 0 ()) ∨ μ = ('b', .pop 0 ())
  start := {()}
  accept := {()}

private theorem pushPopAB_run :
    pushPopAB.MTr () [('a', .push 0 ()), ('b', .pop 0 ())] () :=
  .stepL (s2 := ()) (Or.inl rfl) (.stepL (s2 := ()) (Or.inr rfl) .refl)

/-- The pair push/pop is well-nested, so Lemma 1 gives well-nested reachability. -/
example : pushPopAB.WellNestedReach () () :=
  wellNestedReach_iff.mpr ⟨_, .pushPop .nil .nil, pushPopAB_run⟩

/-- `ab` is accepted: its run is well-nested, so it lifts from the empty stacks to themselves. -/
example : Acceptor.Accepts pushPopAB ['a', 'b'] :=
  ⟨(), rfl, (), rfl, _, rfl,
    WellNested.configLTS_mTr (.pushPop .nil .nil) pushPopAB_run Stacks.empty⟩

/-- `b` is rejected: its only transition pops from an empty stack. -/
example : ¬Acceptor.Accepts pushPopAB ['b'] := by
  rintro ⟨_, -, _, -, μs, hμs, hrun⟩
  obtain ⟨μ, rfl⟩ : ∃ μ, μs = [μ] := by
    rcases μs with _ | ⟨μ, _ | ⟨_, _⟩⟩ <;> simp_all
  rw [LTS.MTr.singleton_iff, configLTS_tr] at hrun
  obtain ⟨htr, happ⟩ := hrun
  rcases htr with rfl | rfl
  · simp at hμs
  · have := congrFun (Op.apply_pop.mp happ) 0
    simp [Stacks.empty] at this

end CslibFrontierTests.MPDA
