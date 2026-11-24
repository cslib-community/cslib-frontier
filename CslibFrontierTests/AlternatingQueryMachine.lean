/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.AlternatingQueryMachine

/-! Tests for the acceptance of alternating query machines: the player of a state matters, an
infinite play never accepts, and a purely existential machine agrees with
`Turing.NondeterministicQueryMachine.Accepts`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.AlternatingQueryMachine

open Turing Turing.AlternatingQueryMachine

/-- From state `0`, the choice `true` leads to the accepting state `1` and the choice `false` to the
rejecting state `2`; the player of state `0` is `u`. -/
private def pick (u : Bool) : AlternatingQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.2.2 then 1 else 2
  halted q := q != 0
  accept q := q == 1
  universal _ := u

/-- The existential player picks the accepting choice. -/
example : (pick false).Accepts [] :=
  AcceptsFrom.existsChoice true rfl rfl (AcceptsFrom.halt rfl rfl)

/-- With no universal state, acceptance coincides with `NondeterministicQueryMachine.Accepts`. -/
example : (pick false).toNondeterministicQueryMachine.Accepts [] :=
  ((pick false).accepts_iff_of_universal_eq_false [] fun _ => rfl).mp
    (AcceptsFrom.existsChoice true rfl rfl (AcceptsFrom.halt rfl rfl))

/-- The universal player may pick the rejecting choice. -/
example : ¬ (pick true).Accepts [] := by
  intro h
  rw [Accepts, acceptsFrom_iff] at h
  simp only [show (pick true).halted (pick true).init = false from rfl,
    show (pick true).universal (pick true).init = true from rfl, Bool.false_eq_true,
    ↓reduceIte] at h
  have h2 := h false
  rw [show (pick true).step [] (pick true).init false = 2 from rfl, acceptsFrom_iff] at h2
  simp only [show (pick true).halted 2 = true from rfl, ↓reduceIte] at h2
  exact absurd h2 (by decide)

/-- A universal state that loops forever. -/
private def loop : AlternatingQueryMachine Unit where
  init := ()
  query _ := 0
  next _ := ()
  halted _ := false
  accept _ := true
  universal _ := true

/-- An infinite play never accepts: acceptance is a least fixed point. -/
example : ¬ loop.Accepts [] := by
  have h (s : Unit) (hs : loop.AcceptsFrom [] s) : False := by
    induction hs with
    | halt hh _ => exact absurd hh (by simp [loop])
    | existsChoice _ _ hu _ _ => exact absurd hu (by simp [loop])
    | forallChoice _ _ _ ih => exact ih true
  exact h _

end CslibFrontierTests.AlternatingQueryMachine
