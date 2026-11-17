/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.ThreeExactCover

/-! Checked clients of Goldreich's Proposition 2.25 (3-Exact Cover is NP-complete, draft `r1.pdf`
of 30 December 2006), `Cslib.Complexity.ThreeExactCover_npComplete`: a concrete yes-instance, and
the collapse `P = NP` that a polynomial-time algorithm for 3XC would give. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichExactCover

open Cslib.Complexity Turing.MultiTapeTM

/-- `{0, …, 5}` is covered exactly by `{0, 1, 2}` and `{3, 4, 5}`; the set `{1, 2, 3}` is not
used. -/
example : [[0, 1, 2], [3, 4, 5], [1, 2, 3]] ∈ ThreeExactCover :=
  ⟨by decide, {[0, 1, 2], [3, 4, 5]}, by decide, by unfold IsExactCover; decide⟩

/-- A polynomial-time algorithm for 3XC would give `P = NP`. -/
example (h : ThreeExactCover ∈ P encThreeExactCover) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  ThreeExactCover_npComplete.P_eq_NP_of_mem_P h enc

end CslibFrontierTests.GoldreichExactCover
