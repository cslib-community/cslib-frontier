/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.ThreeExactCover

/-! Checked clients of Goldreich's Proposition 2.25 (3-Exact Cover is NP-complete, draft `r1.pdf`
of 30 December 2006), `Cslib.Complexity.ThreeExactCover_npComplete`: a concrete yes-instance, the
rejection of a cover not drawn from the instance, the reduction on a formula with two variables of
identical occurrences (read back through the least of them), and the collapse `P = NP` that a
polynomial-time algorithm for 3XC would give. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichExactCover

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- `{0, …, 5}` is covered exactly by `{0, 1, 2}` and `{3, 4, 5}`; the set `{1, 2, 3}` is not
used. -/
example : [[0, 1, 2], [3, 4, 5], [1, 2, 3]] ∈ ThreeExactCover :=
  ⟨by decide, {[0, 1, 2], [3, 4, 5]}, by unfold IsExactCover; decide⟩

/-- An exact cover must be drawn from the instance: the foreign set `{0, 1, 2, 3}` covers the union
of `{0, 1, 2}` and `{0, 1, 3}` exactly once, but is not one of them. -/
example : ¬IsExactCover [[0, 1, 2], [0, 1, 3]] {[0, 1, 2, 3]} := by
  unfold IsExactCover
  decide

/-- Two clauses `x₀ + x₁ + x₂ = 1` and `x₀ + x₁ + x₃ = 1` in which the variables `0` and `1` occur
in exactly the same clauses. -/
def twins : CNF ℕ := [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (3, true)]]

/-- The reduced instance of `twins` is exactly covered by the set of variable `0` (or, identically,
`1`) padded by the dummy element `2`, and the window `{3, 4, 5}` of the remaining dummy elements. -/
theorem isExactCover_reduce_twins :
    IsExactCover (ThreeExactCover.reduce twins) {[0, 1, 2], [3, 4, 5]} := by
  unfold IsExactCover
  decide

/-- Reading the cover back sets only the least of the twin variables true; the reduction's
backward direction gives exact-one satisfiability of `twins`. -/
example : twins.OneSatisfiable := by
  have h : ThreeExactCover.reduce twins ∈ ThreeExactCover :=
    ⟨by decide, _, isExactCover_reduce_twins⟩
  exact ((PositiveOneInExactThreeSATThree.mem_iff_syntaxCheck twins).mp
    ((ThreeExactCover.reduce_mem_iff twins).mp h)).2

/-- A polynomial-time algorithm for 3XC would give `P = NP`. -/
example (h : ThreeExactCover ∈ P encNatSetList) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  ThreeExactCover_npComplete.P_eq_NP_of_mem_P h enc

end CslibFrontierTests.GoldreichExactCover
