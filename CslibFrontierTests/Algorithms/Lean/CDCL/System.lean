/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.System

/-!
# Abstract DPLL with learning

On the formula `a`, `¬a ∨ b` (variables `0` and `1`), two UnitPropagate steps lead from the
initial state to the trail `b, a`, which is a model. On `a`, `¬a`, a UnitPropagate step leads to a
false clause with no decision, from which Fail goes to `fail`; the invariant there says the formula
is unsatisfiable. With the empty clause in the database, Fail applies at once, and nothing follows
`fail`. A Decide step followed by Backjump and Learn illustrates the remaining Basic DPLL rule and
Learn, and Forget removes `a ∨ b` from `a, a ∨ b`, after which `b` no longer occurs in the database
and Decide cannot choose it. Forget cannot remove the tautology `b ∨ ¬b` from `a, b ∨ ¬b`: every
total assignment satisfies it, but the partial model `{a}` of `a` does not, so `a` does not entail
it in the sense of [NieuwenhuisOliverasTinelli2006, §2.1].
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.System

open Cslib.Logic.PL Cslib.Algorithms.Lean.CDCL

private abbrev chain : CNF ℕ := [[(0, true)], [(0, false), (1, true)]]

example : BasicStep (.run [] chain) (.run [⟨(0, true), false⟩] chain) :=
  .unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide)

example : BasicStep (.run [⟨(0, true), false⟩] chain)
    (.run [⟨(1, true), false⟩, ⟨(0, true), false⟩] chain) :=
  .unitPropagate (c := [(0, false), (1, true)]) (by decide) (by decide) (by decide) (by decide)

-- The final trail is a model.
example : chain.eval (Trail.assignment [⟨(1, true), false⟩, ⟨(0, true), false⟩]) = true := by
  decide

private abbrev contra : CNF ℕ := [[(0, true)], [(0, false)]]

-- Propagate `a`, then fail on `¬a`: the invariant of `fail` is unsatisfiability.
example : ¬ contra.Satisfiable := by
  have h₁ : Step (.run [] contra) (.run [⟨(0, true), false⟩] contra) :=
    .inl (.unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide))
  have h₂ : Step (.run [⟨(0, true), false⟩] contra) .fail :=
    .inl (.fail (c := [(0, false)]) (by decide) (by decide) (by decide))
  exact h₂.inv (h₁.inv (Inv.init (V := [0]) (by decide)))

-- With the empty clause in the database, Fail applies, and `fail` has no further step.
example : BasicStep (.run [] [[], [(0, true)]]) .fail :=
  .fail (c := []) (by decide) (by decide) (by decide)

example : ∀ S, ¬ Step .fail S := fun _ h => by
  rcases h with h | h | h <;> exact nomatch h

-- Decide `a` on `¬a`, backjump below it adding `¬a`, then learn `¬a`.
example : BasicStep (.run [] [[(0, false)]]) (.run [⟨(0, true), true⟩] [[(0, false)]]) :=
  .decide (l := (0, true)) (by decide) (by decide)

example : BasicStep (.run [⟨(0, true), true⟩] [[(0, false)]])
    (.run [⟨(0, false), false⟩] [[(0, false)]]) :=
  .backjump (N := []) (M₀ := []) (c := [(0, false)]) (C := [(0, false)]) (by decide)
    (by decide) (fun σ h => by simpa using h) (by decide) (by decide) (by decide) (.inl (by decide))

example : Learn (.run [⟨(0, false), false⟩] [[(0, false)]])
    (.run [⟨(0, false), false⟩] [[(0, false)], [(0, false)]]) :=
  .learn (fun σ h => by simpa using h) (by decide)

-- Forget `a ∨ b`, which `a` entails; then `b` no longer occurs in the database.
example : Forget (.run [] [[(0, true)], [(0, true), (1, true)]]) (.run [] [[(0, true)]]) :=
  .forget (F₁ := [[(0, true)]]) (F₂ := []) fun ρ h => by
    obtain ⟨l, hl, hρ⟩ := h [(0, true)] (by simp)
    simp only [List.mem_singleton] at hl
    subst hl
    exact ⟨(0, true), by simp, hρ⟩

example : 1 ∉ CNF.vars [[((0 : ℕ), true)]] := by decide

/-! ### Forget uses entailment by partial models -/

-- Every total assignment satisfies the tautology `b ∨ ¬b`, so `a` entails it in the total sense.
example (σ : ℕ → Bool) : Clause.eval σ [(1, true), (1, false)] = true := by
  cases h : σ 1 <;> simp [Clause.eval, h]

-- The partial model `{a}` of `a` does not satisfy `b ∨ ¬b`, so `a` does not entail it in the sense
-- of §2.1.
private theorem not_pentails_tautology : ¬ PEntails [[(0, true)]] [(1, true), (1, false)] :=
  fun h => by
    obtain ⟨l, hl, hρ⟩ := h (fun x => if x = 0 then some true else none)
      (by simp [PModels, PSat])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp at hρ

-- So Forget cannot remove `b ∨ ¬b` from `a, b ∨ ¬b`. If it could, the final trail `a` of the
-- remaining database `a` would not be a model of the input in the sense of §2.1: it has no literal
-- of `b ∨ ¬b`.
example : ¬ Forget (.run [] [[(0, true)], [(1, true), (1, false)]]) (.run [] [[(0, true)]]) := by
  intro h
  generalize hS : (State.run [] [[(0, true)], [(1, true), (1, false)]]) = S at h
  generalize hS' : (State.run [] [[(0, true)]]) = S' at h
  obtain ⟨hC⟩ := h
  rename_i F₁ F₂ C
  injection hS with _ hS
  injection hS' with _ hS'
  rcases F₁ with _ | ⟨c₁, _ | ⟨c₂, F₁⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at hS hS'
    obtain ⟨rfl, rfl⟩ := hS
    simp at hS'
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hS
    obtain ⟨rfl, rfl, rfl⟩ := hS
    exact not_pentails_tautology hC
  · simp at hS'

-- The final trail of `a, ¬a ∨ b` has a literal of every clause.
example : ∀ c ∈ chain, ∃ l ∈ c, l ∈ Trail.lits [⟨(1, true), false⟩, ⟨(0, true), false⟩] := by
  decide

end CslibFrontierTests.Algorithms.Lean.CDCL.System
