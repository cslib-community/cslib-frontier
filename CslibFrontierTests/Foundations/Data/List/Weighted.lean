/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Data.List.Weighted
import Mathlib.Algebra.Ring.Nat

/-! Tests of weighted lists, as a client: small lists over `ℕ` are evaluated, a sum over a
sequence is computed by `List.weightedSum_weightedBind`, and the outcomes of a walk that stays or
moves up in every step are bounded by `List.mem_weightedFoldl_induction`. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Data.List.Weighted

/-- `2 * 5 + 3 * 7 = 31`. -/
example : ([(2, true), (3, false)] : List (ℕ × Bool)).weightedSum (fun b => if b then 5 else 7) =
    31 := by decide

/-- A step that stays with weight `1` or moves up with weight `5`. -/
def walk (n : ℕ) : List (ℕ × ℕ) := [(1, n), (5, n + 1)]

/-- The weights multiply along a sequence. -/
example : ([(2, 0), (3, 1)] : List (ℕ × ℕ)).weightedBind walk =
    [(2, 0), (10, 1), (3, 1), (15, 2)] := by decide

/-- The total weight of a sequence, summed in two stages: `2 * 6 + 3 * 6`. -/
example : (([(2, 0), (3, 1)] : List (ℕ × ℕ)).weightedBind walk).weightedSum (fun _ => 1) = 30 := by
  rw [List.weightedSum_weightedBind]
  decide

/-- A fold of two steps of the walk has four outcomes. -/
example : [(), ()].weightedFoldl (fun _ => walk) 0 = [(1, 0), (5, 1), (5, 1), (25, 2)] := by
  decide

/-- A fold of steps with one outcome each is a fold of the list. -/
example : [3, 4, 5].weightedFoldl (fun x s => [((1 : ℕ), x + s)]) 0 = [(1, 12)] := by
  rw [List.weightedFoldl_singleton_one]
  rfl

/-- After `k` steps the walk is at most at `k`. -/
example (k : ℕ) : ∀ q ∈ (List.replicate k ()).weightedFoldl (fun _ => walk) 0, q.2 ≤ k := by
  intro q hq
  have := List.mem_weightedFoldl_induction (f := fun (_ : Unit) => walk) (Inv := fun m s => s ≤ m)
    (m := 0) (fun _ _ s m hm q hq => by
      simp only [walk, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp only <;> omega) le_rfl q hq
  simpa using this

end CslibFrontierTests.Foundations.Data.List.Weighted
