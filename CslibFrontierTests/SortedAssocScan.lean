/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.List.SortedAssoc.Scan
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# Sorted association list scan examples

Checked examples for the comparator-polymorphic scans of `Cslib.SortedAssoc`: their pure
instances on a sorted list, a list that is not sorted, on which the early stop loses an entry,
and the instance in CSLib's query monad, where the comparisons are counted and a monad morphism
recovers the pure value.
-/

public section

namespace CslibFrontierTests.SortedAssocScan

open Cslib (FreeM)
open Cslib.SortedAssoc
open Cslib.Query (LEQuery)

/-- A sorted list with keys `1`, `3`, `5`. -/
def sample : List (ℕ × String) := [(1, "a"), (3, "c"), (5, "e")]

/-! ### Pure instances -/

example : Id.run (lookupM leI 3 sample) = some "c" := by decide
example : Id.run (lookupM leI 4 sample) = none := by decide
example : Id.run (rankM leI 4 sample) = 2 := by decide
example : Id.run (predM leI 3 sample) = some (1, "a") := by decide
example : Id.run (predM leI 1 sample) = none := by decide
example : Id.run (succM leI 3 sample) = some (5, "e") := by decide
example : Id.run (succM leI 5 sample) = none := by decide
example : Id.run (rangeM leI 2 5 sample) = [(3, "c"), (5, "e")] := by decide
example : Id.run (rangeM leI 6 9 sample) = [] := by decide

/-- On a sorted list the scans are the model functions. -/
example :
    Id.run (lookupM leI 3 sample) = List.lookup 3 sample ∧
      Id.run (rankM leI 4 sample) = rank 4 sample ∧
      Id.run (predM leI 4 sample) = pred? 4 sample ∧
      Id.run (rangeM leI 2 4 sample) = range 2 4 sample :=
  have h : sample.IsSortedAssoc := by decide
  ⟨idRun_lookupM h 3, idRun_rankM h 4, idRun_predM h 4, idRun_rangeM h 2 4⟩

/-- Sortedness is needed: the predecessor scan stops at the first key not below the query, so on
an unsorted list it misses a later entry that the model function finds. -/
example :
    Id.run (predM leI 4 [(5, "e"), (1, "a")]) = none ∧
      pred? 4 [(5, "e"), (1, "a")] = some (1, "a") := by
  decide

/-- The successor scan agrees with the model function on every list. -/
example :
    Id.run (succM leI 2 [(5, "e"), (1, "a"), (3, "c")]) =
      succ? 2 [(5, "e"), (1, "a"), (3, "c")] :=
  idRun_succM 2 _

/-! ### Counting comparisons -/

/-- The oracle of the order on `ℕ`. -/
def natOracle : {ι : Type} → LEQuery ℕ ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

/-- Looking up a present key asks once per entry passed and twice where it stops. -/
example : (lookupM LEQuery.ask 3 sample).countQueries natOracle = 3 := by
  simp [sample, natOracle, lookupM]

/-- The rank scan asks once per entry up to the first key not below the query. -/
example : (rankM LEQuery.ask 4 sample).countQueries natOracle = 3 := by
  simp [sample, natOracle, rankM]

/-- A range scan has two phases, and the first entry it keeps is compared in both. Here the lower
phase asks `2 ≤ 1` and `2 ≤ 3`, and the upper phase asks `3 ≤ 4` and `5 ≤ 4`: four comparisons,
with `3` compared against both bounds. -/
example : (rangeM LEQuery.ask 2 4 sample).countQueries natOracle = 4 := by
  simp [sample, natOracle, rangeM, takeUpToM]

/-- Evaluating the counted scan at the order's oracle gives the pure scan, by the transfer
lemma. -/
example (k : ℕ) (l : List (ℕ × String)) :
    (lookupM LEQuery.ask k l).eval natOracle = Id.run (lookupM leI k l) := by
  simpa [leI, natOracle] using
    Id.ext_iff.1 (map_lookupM (FreeM.isMonadHom_pure_eval natOracle) LEQuery.ask k l)

end CslibFrontierTests.SortedAssocScan
