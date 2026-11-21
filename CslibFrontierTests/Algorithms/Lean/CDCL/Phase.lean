/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Phase

/-!
# Phase saving

The kernel checks the saved phases: fresh variables are decided negative; a backjump saves the
values of the literals it undoes, the newest value of a variable winning over none; and variables
it does not undo keep their phases.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Phase

open Cslib.Algorithms.Lean.CDCL

/-- Fresh variables are decided negative. -/
example : (Phases.init 3).get 1 = false := by decide

/-- Undoing `x₁` (true) and the decision `¬x₂` saves both values; `x₀` keeps its phase. -/
example :
    let P := (Phases.init 3).save [⟨(1, true), false⟩, ⟨(2, false), true⟩]
    P.get 0 = false ∧ P.get 1 = true ∧ P.get 2 = false := by
  decide

/-- A later backjump overwrites a saved phase. -/
example :
    (((Phases.init 3).save [⟨(1, true), true⟩]).save [⟨(1, false), true⟩]).get 1 = false := by
  decide

/-- A phase saved once is kept until the variable is undone again. -/
example : (((Phases.init 3).save [⟨(1, true), true⟩]).save [⟨(2, true), true⟩]).get 1 = true := by
  decide

-- Saving a variable past the end of the array grows it: the single positive literal for
-- variable `1`, saved into the phases of one variable, reads back `true`.
example : ((Phases.init 1).save [⟨(1, true), false⟩]).get 1 = true := by decide

end CslibFrontierTests.Algorithms.Lean.CDCL.Phase
