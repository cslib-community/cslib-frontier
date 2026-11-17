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
and Decide cannot choose it.
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
  .forget (F₁ := [[(0, true)]]) (F₂ := []) fun σ h => by
    simp only [List.append_nil, CNF.eval_cons, CNF.eval_nil, Bool.and_true, Clause.eval_cons,
      Clause.eval_nil, Bool.or_false, Literal.eval_mk, beq_iff_eq] at h
    simp [Clause.eval, h]

example : 1 ∉ CNF.vars [[((0 : ℕ), true)]] := by decide

end CslibFrontierTests.Algorithms.Lean.CDCL.System
