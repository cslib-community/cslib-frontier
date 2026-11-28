/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.BinPacking.OnlineCompetitive

/-!
# Online bin packing in the competitive-analysis framework: examples

These kernel-checked examples (using no `native_decide`) exercise
`CslibFrontier.Algorithms.Lean.BinPacking.OnlineCompetitive`:

1. The steps. Putting an item into a bin with room and opening a new bin are valid; putting it
   into a bin without room is not.
2. A schedule of four items in capacity `10`, ending with two bins: its cost is `2`, and it ends
   in a packing.
3. The strategy of First Fit on the same items: its cost, computed by `decide`, is `2`, the number
   of bins of `OnlinePacker.run`, as `OnlinePacker.cost_toDetStrategy` states.
4. The theorems instantiated: a packing gives a schedule, every strategy has the cost of an online
   packer, and First Fit's strategy violates every ratio below `3/2` and is not
   `(1, b)`-competitive.
-/

public section

namespace CslibFrontierTests.BinPacking.OnlineCompetitive

open Cslib.Algorithms.Lean.BinPacking Cslib.DataStructure.Online

/-- The items `6, 5, 4, 5` as requests in capacity `10`. -/
abbrev reqs : List (problem 10).Req := [⟨6, by decide⟩, ⟨5, by decide⟩, ⟨4, by decide⟩,
  ⟨5, by decide⟩]

/-! ### 1. The steps -/

/-- A `4` joins a bin holding `6`. -/
example : (problem 10).ValidStep [[6], [5]] ⟨4, by decide⟩ [[6, 4], [5]] :=
  Or.inl ⟨0, by decide, by decide, rfl⟩

/-- A `5` may open a new bin even when a bin has room for it. -/
example : (problem 10).ValidStep [[5]] ⟨5, by decide⟩ [[5], [5]] := Or.inr rfl

/-- A `5` cannot join a bin holding `6`. -/
example : ¬ (problem 10).ValidStep [[6]] ⟨5, by decide⟩ [[6, 5]] := by
  rintro (⟨i, hi, hfit, -⟩ | h)
  · obtain rfl : i = 0 := by simpa using hi
    simp at hfit
  · simp at h

/-! ### 2. A schedule -/

/-- The schedule that opens a bin for `6`, a bin for `5`, and puts `4` and `5` into them. -/
abbrev schedule : List (problem 10).State :=
  [[[6]], [[6], [5]], [[6, 4], [5]], [[6, 4], [5, 5]]]

example : (problem 10).ValidSchedule [] reqs schedule :=
  ⟨Or.inr rfl, Or.inr rfl, Or.inl ⟨0, by decide, by decide, rfl⟩,
    Or.inl ⟨1, by decide, by decide, rfl⟩, trivial⟩

example : (problem 10).scheduleCost [] reqs schedule = 2 := by decide

example : IsPacking 10 [6, 5, 4, 5] ((problem 10).finalState [] schedule) :=
  isPacking_finalState (reqs := reqs)
    ⟨Or.inr rfl, Or.inr rfl, Or.inl ⟨0, by decide, by decide, rfl⟩,
      Or.inl ⟨1, by decide, by decide, rfl⟩, trivial⟩

/-! ### 3. The strategy of First Fit -/

example : (firstFitPacker 10).toDetStrategy.cost [] reqs = 2 := by decide

example : ((firstFitPacker 10).run [6, 5, 4, 5]).length = 2 := by decide

example : (firstFitPacker 10).toDetStrategy.cost [] reqs =
    ((firstFitPacker 10).run [6, 5, 4, 5]).length :=
  (firstFitPacker 10).cost_toDetStrategy reqs

/-! ### 4. The theorems instantiated -/

/-- The packing `[[6, 4], [5, 5]]` gives a schedule costing at most `2`. -/
example : ∃ ss, (problem 10).ValidSchedule [] reqs ss ∧
    (problem 10).scheduleCost [] reqs ss ≤ 2 :=
  exists_validSchedule_of_isPacking (Q := [[6, 4], [5, 5]])
    ⟨by decide, by decide⟩

example (S : DetStrategy (problem 10)) :
    ∃ A : OnlinePacker 10, ∀ reqs, S.cost [] reqs = (A.run (reqs.map Subtype.val)).length :=
  exists_onlinePacker_cost_eq S

/-- First Fit's strategy violates the ratio `7/5 < 3/2` with additive constant `100`. -/
example : ∃ reqs offStates, (problem 41).ValidSchedule [] reqs offStates ∧
    7 * (problem 41).scheduleCost [] reqs offStates + 100 <
      5 * (firstFitPacker 41).toDetStrategy.cost [] reqs :=
  yao_exists_validSchedule_ratio_violation _ (by decide) 100

/-- Every strategy of `problem 3263441` violates the ratio `1.54` with additive constant `100`. -/
example (S : DetStrategy (problem 3263441)) : ∃ reqs offStates,
    (problem 3263441).ValidSchedule [] reqs offStates ∧
      154 * (problem 3263441).scheduleCost [] reqs offStates + 100 < 100 * S.cost [] reqs :=
  brown_liang_exists_validSchedule_ratio_violation S (by decide) 100

example (b : ℕ) : ¬ (firstFitPacker 41).toDetStrategy.IsCompetitive 1 b :=
  not_isCompetitive_of_two_mul_lt _ (by decide) b

end CslibFrontierTests.BinPacking.OnlineCompetitive
