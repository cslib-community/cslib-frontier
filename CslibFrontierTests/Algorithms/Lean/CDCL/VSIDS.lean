/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.VSIDS

/-!
# VSIDS

The kernel checks the activities: a fresh state picks the first unassigned variable; a bumped
variable is picked first; a later bump outweighs an earlier one, because the increment grows;
assigned variables are never picked; and an activity past the limit scales every activity down.
It also runs the variable order: popping gives the most active unassigned variable, skipping
assigned variables and stale entries, and putting back an entry keyed above the activity with the
current activity.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.VSIDS

open Cslib.Algorithms.Lean.CDCL

/-- Fresh activities: the first unassigned variable. -/
example : (Activity.init 4).pick [] [0, 1, 2, 3] = some 0 := by decide

/-- A bumped variable is picked first. -/
example : ((Activity.init 4).bump [2]).pick [] [0, 1, 2, 3] = some 2 := by decide

/-- A variable met twice in one analysis is bumped once. -/
example : ((Activity.init 4).bump [2, 2]).get 2 = ((Activity.init 4).bump [2]).get 2 := by decide

/-- Decay: a later bump outweighs an earlier one. -/
example : (((Activity.init 4).bump [1]).bump [3]).pick [] [0, 1, 2, 3] = some 3 := by decide

/-- Two bumps outweigh one later bump. -/
example : ((((Activity.init 4).bump [1]).bump [1]).bump [3]).pick [] [0, 1, 2, 3] = some 1 := by
  decide

/-- An assigned variable is not picked, however active. -/
example : ((Activity.init 4).bump [2]).pick [⟨(2, false), true⟩] [0, 1, 2, 3] = some 0 := by
  decide

/-- Every variable assigned: no decision. -/
example : ((Activity.init 2).bump [1]).pick [⟨(0, true), true⟩, ⟨(1, true), false⟩] [0, 1] =
    none := by
  decide

/-- Past the limit, activities and the increment are scaled down by `2 ^ 100`. -/
example : (Activity.bumpVar ⟨#[2 ^ 200, 5], 1⟩ 0).score = #[2 ^ 100, 0] ∧
    (Activity.bumpVar ⟨#[2 ^ 200, 5], 1⟩ 0).inc = 0 := by
  decide +kernel

-- Bumping a variable beyond the activity array does nothing: its activity stays `0`.
example : ((Activity.init 0).bumpVar 0).get 0 = 0 := by decide

-- Bumping a variable within the array adds the increment.
example : ((Activity.init 1).bumpVar 0).get 0 = 2 ^ 100 := by decide

/-- Activities `0, 5, 3, 0` for the variables `0` to `3`. -/
private abbrev act : Activity := ⟨#[0, 5, 3, 0], 1⟩

/-- The order with every variable at its activity. -/
private abbrev order : VarOrder :=
  VarOrder.insertVars Batteries.BinaryHeap.emptyF act [0, 1, 2, 3]

/-- Popping gives the most active variable. -/
example : (VarOrder.pop act [] 10 order).1 = some 1 := by decide +kernel

/-- An assigned variable is skipped. -/
example : (VarOrder.pop act [⟨(1, true), true⟩] 10 order).1 = some 2 := by decide +kernel

/-- A stale entry, keyed below the variable's activity, is skipped: variable `3`, inserted at `0`,
now has activity `9`, and its fresh entry comes first. -/
example : (VarOrder.pop ⟨#[0, 5, 3, 9], 1⟩ [] 10 (order.insertVars ⟨#[0, 5, 3, 9], 1⟩ [3])).1 =
    some 3 := by
  decide +kernel

/-- An entry keyed above the variable's activity, as after a rescaling, is put back with the
current activity: variable `1`, at `5` in the order, now has activity `2`, below variable `2`.
Popping `2` leaves three entries, that of `1` among them. -/
example : (VarOrder.pop ⟨#[0, 2, 3, 0], 1⟩ [] 10 order).1 = some 2 ∧
    (VarOrder.pop ⟨#[0, 2, 3, 0], 1⟩ [] 10 order).2.size = 3 := by
  decide +kernel

/-- Every variable assigned: nothing to pop. -/
example : (VarOrder.pop act [⟨(0, true), true⟩, ⟨(1, true), true⟩, ⟨(2, true), true⟩,
    ⟨(3, true), true⟩] 10 order).1 = none := by
  decide +kernel

end CslibFrontierTests.Algorithms.Lean.CDCL.VSIDS
