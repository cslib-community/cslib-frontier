/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Tournament
meta import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Tournament

/-!
# Second-smallest tournament tests

An uneven bracket gives its champion either two or three direct opponents. The larger case
attains the comparison bound. The rank client counts duplicate minima in the sorted list.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.QuerySecondMinTournament

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

end CslibFrontierTests.QuerySecondMinTournament
