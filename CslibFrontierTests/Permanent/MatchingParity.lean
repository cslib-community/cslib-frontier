/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of matching parity)

import CslibFrontier.Computability.Complexity.Problems.Permanent.MatchingParity

/-! Checked clients of the determinant-parity algorithm, including both sides of its promise. -/

set_option linter.privateModule false

namespace Cslib.Complexity

/-- The empty graph has one empty perfect matching. -/
example : [] ∈ uniqueBipartiteMatching.yes := by
  change BipartitePerfectMatchingCount [] = 1
  rw [bipartitePerfectMatchingCount_eq_zeroOnePermanent]
  simp [ZeroOnePermanent, Matrix.permanent]

/-- An isolated vertex on each side has no matching. -/
example : [[false]] ∈ uniqueBipartiteMatching.no := by
  change BipartitePerfectMatchingCount [[false]] = 0
  rw [bipartitePerfectMatchingCount_eq_zeroOnePermanent, zeroOnePermanent_eq_card]
  decide

/-- A ragged identity table still has a unique perfect matching. -/
example : [[true], [false, true]] ∈ uniqueBipartiteMatching.yes := by
  change BipartitePerfectMatchingCount _ = 1
  rw [bipartitePerfectMatchingCount_eq_zeroOnePermanent, zeroOnePermanent_eq_card]
  decide

/-- A table with a negative integer determinant is accepted. -/
example : bipartiteMatchingParity [[false, true], [true, false]] = true := by decide

/-- Two matchings are outside the promise and have even parity. -/
example : BipartitePerfectMatchingCount [[true, true], [true, true]] = 2 ∧
    bipartiteMatchingParity [[true, true], [true, true]] = false := by
  constructor
  · rw [bipartitePerfectMatchingCount_eq_zeroOnePermanent, zeroOnePermanent_eq_card]
    decide
  · decide

/-- Three matchings are also outside the promise, and have odd parity. -/
example :
    BipartitePerfectMatchingCount
      [[true, true, false], [true, true, true], [false, true, true]] = 3 ∧
    bipartiteMatchingParity
      [[true, true, false], [true, true, true], [false, true, true]] = true := by
  constructor
  · rw [bipartitePerfectMatchingCount_eq_zeroOnePermanent, zeroOnePermanent_eq_card]
    decide
  · decide

/-- The solver supplied by promise-P accepts a concrete unique-matching instance and rejects a
concrete no-matching instance; clients need no determinant or permanent representation work. -/
example : ∃ f : List (List Bool) → Bool,
    Turing.MultiTapeTM.ComputableInPolyTime f encBoolTable Turing.MultiTapeTM.encBool ∧
    f [[true], [false, true]] = true ∧ f [[false]] = false := by
  obtain ⟨f, hf, hy, hn⟩ := mem_PromiseP_iff.mp uniqueBipartiteMatching_mem_PromiseP
  refine ⟨f, hf, hy _ ?_, hn _ ?_⟩ <;>
    change BipartitePerfectMatchingCount _ = _ <;>
    rw [bipartitePerfectMatchingCount_eq_zeroOnePermanent, zeroOnePermanent_eq_card] <;> decide

end Cslib.Complexity
