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
It also runs the variable order, an indexed heap: inserting records each variable's position;
popping gives the most active unassigned variable, skipping assigned variables and variables no
longer occurring in the database, and breaks ties by variable; bumping moves a variable up, and
past the limit rebuilds the heap; and with every variable assigned, popping empties the heap.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.VSIDS

open Cslib.Algorithms.Lean.CDCL

/-- Fresh activities: the first unassigned variable. -/
example : (Activity.init 4).pick ⟨#[]⟩ [0, 1, 2, 3] = some 0 := by decide

/-- A bumped variable is picked first. -/
example : ((Activity.init 4).bump [2]).pick ⟨#[]⟩ [0, 1, 2, 3] = some 2 := by decide

/-- A variable met twice in one analysis is bumped once. -/
example : ((Activity.init 4).bump [2, 2]).get 2 = ((Activity.init 4).bump [2]).get 2 := by decide

/-- Decay: a later bump outweighs an earlier one. -/
example : (((Activity.init 4).bump [1]).bump [3]).pick ⟨#[]⟩ [0, 1, 2, 3] = some 3 := by decide

/-- Two bumps outweigh one later bump. -/
example :
    ((((Activity.init 4).bump [1]).bump [1]).bump [3]).pick ⟨#[]⟩ [0, 1, 2, 3] = some 1 := by
  decide

/-- An assigned variable is not picked, however active. -/
example :
    ((Activity.init 4).bump [2]).pick (Assign.ofTrail [⟨(2, false), true⟩]) [0, 1, 2, 3] =
      some 0 := by
  decide

/-- Every variable assigned: no decision. -/
example : ((Activity.init 2).bump [1]).pick
    (Assign.ofTrail [⟨(0, true), true⟩, ⟨(1, true), false⟩]) [0, 1] = none := by
  decide

/-- Past the limit, activities and the increment are scaled down by `2 ^ 20`. -/
example : (Activity.bumpVar ⟨#[2 ^ 60, 5], 1⟩ 0).score = #[2 ^ 40, 0] ∧
    (Activity.bumpVar ⟨#[2 ^ 60, 5], 1⟩ 0).inc = 0 := by
  decide +kernel

-- Bumping a variable beyond the activity array does nothing: its activity stays `0`.
example : ((Activity.init 0).bumpVar 0).get 0 = 0 := by decide

-- Bumping a variable within the array adds the increment.
example : ((Activity.init 1).bumpVar 0).get 0 = 2 ^ 40 := by decide

/-- Activities `0, 5, 3, 0` for the variables `0` to `3`. -/
private abbrev act : Activity := ⟨#[0, 5, 3, 0], 1⟩

/-- The order with every variable, with room for four. -/
private abbrev order : VarOrder := (VarOrder.empty 4).addAll act [0, 1, 2, 3]

/-- Inserting records the positions: the heap and the position of each variable, plus one. -/
example : order.heap = #[1, 3, 2, 0] ∧ order.pos = #[4, 1, 3, 2] := by decide +kernel

/-- A variable already in the heap, or without room, is not inserted again. -/
example : (order.addAll act [1, 7]).heap.size = 4 := by decide +kernel

/-- Every variable occurs in the database. -/
private abbrev every : ℕ → Bool := fun _ => true

/-- Popping gives the most active variable. -/
example : (VarOrder.pop act ⟨#[]⟩ every 10 order).var = some 1 := by decide +kernel

/-- An assigned variable is skipped, and removed from the heap. -/
example :
    (VarOrder.pop act (Assign.ofTrail [⟨(1, true), true⟩]) every 10 order).var = some 2 ∧
    (VarOrder.pop act (Assign.ofTrail [⟨(1, true), true⟩]) every 10 order).order.pos =
      #[2, 0, 0, 1] := by
  decide +kernel

/-- A variable that no longer occurs in the database is skipped. -/
example : (VarOrder.pop act ⟨#[]⟩ (fun v => v != 1) 10 order).var = some 2 := by
  decide +kernel

/-- Ties are broken by variable: with equal activities, the greatest variable comes first. -/
example : (VarOrder.pop ⟨#[0, 0, 0, 0], 1⟩ ⟨#[]⟩ every 10
    ((VarOrder.empty 4).addAll ⟨#[0, 0, 0, 0], 1⟩ [0, 1, 2, 3])).var = some 3 := by
  decide +kernel

/-- Bumping moves a variable up: variable `3`, at activity `0`, bumped by `9`, comes out first. -/
example : (VarOrder.pop (VarOrder.bump ⟨#[0, 5, 3, 0], 9⟩ order [3]).1 ⟨#[]⟩ every 10
    (VarOrder.bump ⟨#[0, 5, 3, 0], 9⟩ order [3]).2).var = some 3 := by
  decide +kernel

/-- Bumping past the limit scales the activities down and rebuilds the heap: variable `1`, bumped
to `2 ^ 60`, comes first, and every variable stays in the heap. -/
example : (VarOrder.bump ⟨#[0, 2 ^ 60 - 1, 3, 0], 1⟩ order [1]).1.score = #[0, 2 ^ 40, 0, 0] ∧
    (VarOrder.pop (VarOrder.bump ⟨#[0, 2 ^ 60 - 1, 3, 0], 1⟩ order [1]).1 ⟨#[]⟩ every 10
      (VarOrder.bump ⟨#[0, 2 ^ 60 - 1, 3, 0], 1⟩ order [1]).2).var = some 1 ∧
    (VarOrder.bump ⟨#[0, 2 ^ 60 - 1, 3, 0], 1⟩ order [1]).2.heap.size = 4 := by
  decide +kernel

/-- Putting back the variables `0` and `1` after popping `1` inserts `1` only. -/
example : ((VarOrder.pop act ⟨#[]⟩ every 10 order).order.addAll act [0, 1]).heap.size = 4 := by
  decide +kernel

/-- Every variable assigned: nothing to pop, and the heap is emptied. -/
example : (VarOrder.pop act (Assign.ofTrail [⟨(0, true), true⟩, ⟨(1, true), true⟩,
    ⟨(2, true), true⟩, ⟨(3, true), true⟩]) every 10 order).var = none ∧
    (VarOrder.pop act (Assign.ofTrail [⟨(0, true), true⟩, ⟨(1, true), true⟩,
    ⟨(2, true), true⟩, ⟨(3, true), true⟩]) every 10 order).order.heap.size = 0 := by
  decide +kernel

/-- Unassigning a variable past the end of the assignment array leaves the array as it is: no
slot is allocated for it. -/
example : (Assign.unassign ⟨#[]⟩ [1000000]).vals.size = 0 := by decide

/-- Unassigning a variable within the array clears it and keeps the size. -/
example : (Assign.unassign ⟨#[2, 1]⟩ [1]).vals = #[2, 0] := by decide

end CslibFrontierTests.Algorithms.Lean.CDCL.VSIDS
