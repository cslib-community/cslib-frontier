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

end CslibFrontierTests.Algorithms.Lean.CDCL.VSIDS
