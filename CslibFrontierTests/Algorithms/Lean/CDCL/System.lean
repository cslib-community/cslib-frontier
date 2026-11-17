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
is unsatisfiable. With the empty clause in the database, Fail applies at once, and Decide no longer
applies after it, since `fail` has no steps. A Decide step followed by a Backjump and a Learn step
illustrates the remaining rules.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.System

open Cslib.Logic.PL Cslib.Algorithms.Lean.CDCL

private abbrev chain : CNF ℕ := [[(0, true)], [(0, false), (1, true)]]

private abbrev V : List ℕ := [0, 1]

example : BasicStep V (.run [] chain) (.run [⟨(0, true), false⟩] chain) :=
  .unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide) (by decide)

example : BasicStep V (.run [⟨(0, true), false⟩] chain)
    (.run [⟨(1, true), false⟩, ⟨(0, true), false⟩] chain) :=
  .unitPropagate (c := [(0, false), (1, true)]) (by decide) (by decide) (by decide) (by decide)
    (by decide)

-- The final trail is a model.
example : chain.eval (Trail.assignment [⟨(1, true), false⟩, ⟨(0, true), false⟩]) = true := by
  decide

private abbrev contra : CNF ℕ := [[(0, true)], [(0, false)]]

-- Propagate `a`, then fail on `¬a`: the invariant of `fail` is unsatisfiability.
example : ¬ contra.Satisfiable := by
  have h₁ : Step [0] (.run [] contra) (.run [⟨(0, true), false⟩] contra) :=
    .inl (.unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  have h₂ : Step [0] (.run [⟨(0, true), false⟩] contra) .fail :=
    .inl (.fail (c := [(0, false)]) (by decide) (by decide) (by decide))
  exact h₂.inv (h₁.inv (Inv.init (by decide)))

-- With the empty clause in the database, Fail applies, and `fail` has no further step: Decide
-- cannot follow it.
example : BasicStep [0] (.run [] [[], [(0, true)]]) .fail :=
  .fail (c := []) (by decide) (by decide) (by decide)

example : ∀ S, ¬ BasicStep [0] .fail S := fun _ h => nomatch h

-- Decide `a` on `¬a`, backjump below it adding `¬a`, then learn `¬a`.
example : BasicStep [0] (.run [⟨(0, true), true⟩] [[(0, false)]])
    (.run [⟨(0, false), false⟩] [[(0, false)]]) :=
  .backjump (N := []) (M₀ := []) (c := [(0, false)]) (C := [(0, false)]) (by decide)
    (by decide) (fun σ h => by simpa using h) (by decide) (by decide) (by decide) (by decide)

example : Learn [0] (.run [⟨(0, false), false⟩] [[(0, false)]])
    (.run [⟨(0, false), false⟩] [[(0, false)], [(0, false)]]) :=
  .learn (fun σ h => by simpa using h) (by decide)

end CslibFrontierTests.Algorithms.Lean.CDCL.System
