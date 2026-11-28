/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.LowerBound
meta import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Tournament

/-!
# Second-smallest comparison selection

An uneven bracket gives its champion either two or three direct opponents. The larger case
attains the comparison bound. The rank client counts duplicate minima in the sorted list.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.QuerySecondMin

open Cslib Cslib.Query

private def leOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

#guard (findSecondMin []).eval leOracle == none
#guard (findSecondMin [8]).eval leOracle == none
#guard (findSecondMin [8, 3]).eval leOracle == some 8
#guard (findSecondMin [4, 3, 2, 3, 2]).eval leOracle == some 2
#guard (findSecondMin [4, 3, 2, 1, 0]).eval leOracle == some 1
#guard (findSecondMin [0, 1, 2, 3, 4]).countQueries leOracle == 5
#guard (findSecondMin [4, 3, 2, 1, 0]).countQueries leOracle == 6

-- The oracle answering every comparison negatively also attains the cost bound.
#guard (findSecondMin [0, 1, 2, 3, 4]).countQueries (LEQuery.oracleOf fun _ _ => false) == 6

example (xs : List ℕ) (h : 2 ≤ xs.length) :
    (findSecondMin xs).eval leOracle = xs.mergeSort[1]? := by
  obtain ⟨m, hm, hrank⟩ := findSecondMin_correct (· ≤ ·) leOracle (fun _ _ => rfl) h
  exact hm.trans (List.isOrderStatistic_iff_mergeSort.mp hrank).symm

-- The universal lower bound rules out even an algorithm that hard-codes a possible answer.
example : ¬ IsSecondMinAlg (fun _ : List ℕ => pure (some 1)) := by
  intro h
  obtain ⟨_, _, hcount⟩ := h.exists_le_countQueries (xs := [0, 1]) (by decide) (by decide)
  simpa [FreeM.countQueries_pure, Nat.clog] using hcount

-- On any fixed list of five distinct keys a genuine linear order realizes the tournament bound.
example : ∃ f : ℕ → ℕ → Bool, IsLinearOrder ℕ (fun a b => f a b = true) ∧
    (findSecondMin [10, 20, 30, 40, 50]).countQueries (LEQuery.oracleOf f) = 6 := by
  exact exists_countQueries_findSecondMin_eq (by decide) (by decide)

end CslibFrontierTests.QuerySecondMin
