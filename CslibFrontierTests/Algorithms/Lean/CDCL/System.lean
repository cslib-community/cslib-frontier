/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Algorithms.Lean.CDCL.System

/-!
# The abstract CDCL transition system

On the formula `a`, `¬a ∨ b` (variables `0` and `1`), two UnitPropagate steps lead from the
initial state to the trail `b, a`, which is a model. On `a`, `¬a`, one UnitPropagate step leads to
a false clause with no decision, which shows that the formula is unsatisfiable. A Decide step
followed by a Backjump learning `¬a` illustrates the third rule.
-/

namespace CslibFrontierTests.Algorithms.Lean.CDCL.System

open Cslib.Logic.PL Cslib.Algorithms.Lean.CDCL

private abbrev chain : CNF ℕ := [[(0, true)], [(0, false), (1, true)]]

private abbrev V : List ℕ := [0, 1]

example : Step V ⟨[], chain⟩ ⟨[((0, true), false)], chain⟩ :=
  .unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide) (by decide)

example : Step V ⟨[((0, true), false)], chain⟩ ⟨[((1, true), false), ((0, true), false)], chain⟩ :=
  .unitPropagate (c := [(0, false), (1, true)]) (by decide) (by decide) (by decide) (by decide)
    (by decide)

-- The final trail is a model.
example : chain.eval (Trail.assignment [((1, true), false), ((0, true), false)]) = true := by
  decide

private abbrev contra : CNF ℕ := [[(0, true)], [(0, false)]]

example : Step [0] ⟨[], contra⟩ ⟨[((0, true), false)], contra⟩ :=
  .unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide) (by decide)

-- A false clause and no decision: the formula is unsatisfiable.
example : ¬ contra.Satisfiable := by
  have h : Inv contra [0] ⟨[((0, true), false)], contra⟩ :=
    (Step.unitPropagate (c := [(0, true)]) (by decide) (by decide) (by decide) (by decide)
      (by decide)).inv (Inv.init (by decide))
  exact h.not_satisfiable (c := [(0, false)]) (by decide) (by decide) fun l => by simp

-- Decide `a` on `¬a`, then backjump below it, learning `¬a`.
example : Step [0] ⟨[((0, true), true)], [[(0, false)]]⟩
    ⟨[((0, false), false)], [[(0, false)], [(0, false)]]⟩ :=
  .backjump (N := []) (M₀ := []) (c := [(0, false)]) (C := [(0, false)]) true (by decide)
    (by decide) (fun σ h => by simpa using h) (by decide) (by decide) (by decide) (by decide)

end CslibFrontierTests.Algorithms.Lean.CDCL.System
