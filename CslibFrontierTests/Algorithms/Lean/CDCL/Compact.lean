/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Watched
public meta import CslibFrontier.Algorithms.Lean.CDCL.Watched

/-!
# The CDCL solver on renamed variables

`solveCompact` renames the variables to `0, …, k - 1` before solving, so a formula over the
variable `10⁹` is solved with arrays of one slot. These checks run compiled code: the renaming
uses a hash map, which the kernel does not evaluate. The certificate it returns for
`[[], [(10⁹, true)]]` is accepted for the original formula, and on `x_{10⁹} ∧ (¬x_{10⁹} ∨ x₇)` the
model it returns satisfies the formula. A formula with no variables, `[]` or `[[]]`, gets activity
arrays of no slots; one whose greatest variable is `v` gets `v + 1`, checked on the arithmetic for
`10⁹` and on an actual array for `x₂`.
-/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Compact

open Cslib.Logic.PL Cslib.Algorithms.Lean.CDCL

private abbrev big : CNF ℕ := [[], [(1000000000, true)]]

#guard (CNF.denseRenaming big).size == 1
#guard match solveCompact big with
  | .unsat cert => big.checkLRAT cert
  | .sat _ => false

private abbrev chain : CNF ℕ := [[(1000000000, true)], [(1000000000, false), (7, true)]]

#guard match solveCompact chain with
  | .sat σ => chain.eval σ
  | .unsat _ => false

#guard (WExec.init ([] : CNF ℕ)).act.score.size == 0
#guard (WExec.init ([[]] : CNF ℕ)).act.score.size == 0
#guard varSlots big == 1000000001
#guard (WExec.init ([[(2, true)], [(0, false)]] : CNF ℕ)).act.score.size == 3

end CslibFrontierTests.Algorithms.Lean.CDCL.Compact
