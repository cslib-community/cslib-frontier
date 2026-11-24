/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.TFNP.Uncheckable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Checked clients of Goldreich, Exercise 2.1: for the empty set the guideline relation is in
`PC` (any polynomial-time decidable set would do; mere decidability does not suffice), so the
undecidability of `S` is what puts it outside; and the undecidable witness is solved by the
constant algorithm. -/

set_option linter.privateModule false

namespace CslibFrontierTests.UncheckableSearch

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- For the empty set the guideline relation is in `FNP`: its only solution is `[true]`. -/
example : membershipSearch (∅ : Set (List Bool)) ∈ FNP encBits :=
  mem_FNP.mpr ⟨⟨1, fun _ _ h => by simp [length_eq_one_of_membershipSearch h]⟩,
    fun x => decide (x.2 = [true]),
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _) (.const [true]),
    fun _ w => by simp [membershipSearch]⟩

/-- The self-halting witness has the solution `[true]` on every word, found by the solver. -/
example (x : List Bool) : membershipSearch selfHaltingProblem x [true] :=
  solvesSearch_membershipSearch.rel (a := x) rfl

end CslibFrontierTests.UncheckableSearch
