/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set of `pm_exec`

The simp set used by `pm_exec` in `CslibFrontier.Computability.PointerMachine.SymbolicExec`,
declared in a file of its own because an attribute cannot be used in the file declaring it.

## Main definitions

* `pm_simps`: the effect of each data instruction, and reads of registers and records after
  assignments.
-/

public meta section

/-- The simp set `pm_simps` rewrites the effect of each data instruction to assignments, and
reads registers and records after assignments, for `pm_exec`. -/
register_simp_attr pm_simps

end
