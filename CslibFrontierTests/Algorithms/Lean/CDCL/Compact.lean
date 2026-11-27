/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Watched
import CslibFrontier.Logics.Propositional.Pigeonhole
public meta import CslibFrontier.Algorithms.Lean.CDCL.Watched
public meta import CslibFrontier.Logics.Propositional.Pigeonhole

/-!
# The CDCL solver on renamed variables

`solveCompact` renames the variables to `0, …, k - 1` before solving, so a formula over the
variable `10⁹` is solved with arrays of one slot. These checks run compiled code: the renaming
uses a hash map, which the kernel does not evaluate. The certificate it returns for
`[[], [(10⁹, true)]]` is accepted for the original formula, and on `x_{10⁹} ∧ (¬x_{10⁹} ∨ x₇)` the
model it returns satisfies the formula. A formula with no variables, `[]` or `[[]]`, gets activity
and phase arrays of no slots; one whose greatest variable is `v` gets `v + 1`, checked on the
arithmetic for `10⁹` and on actual arrays for `x₂`.
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

#guard (WExec.init ([] : CNF ℕ) {}).act.score.size == 0
#guard (WExec.init ([[]] : CNF ℕ) {}).act.score.size == 0
#guard varSlots big == 1000000001
#guard (WExec.init ([[(2, true)], [(0, false)]] : CNF ℕ) {}).act.score.size == 3
#guard (WExec.init ([] : CNF ℕ) {}).phase.saved.size == 0
#guard (WExec.init ([[]] : CNF ℕ) {}).phase.saved.size == 0
#guard (WExec.init ([[(2, true)], [(0, false)]] : CNF ℕ) {}).phase.saved.size == 3

/-- The minimization steps of a certificate: the RUP steps hinting at least three clauses, which
resolution steps, hinting two, cannot be. Each comes with whether its clause repeats no literal. -/
private def minimizationSteps (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) : List Bool :=
  cert.toList.filterMap fun
    | .addRup _ c hints => if 3 ≤ hints.size then some (decide c.toList.Nodup) else none
    | _ => none

/-- PHP(5, 4), with pigeon `i` in hole `j` as `4 * i + j`. -/
private def php54 : CNF ℕ := (CNF.pigeonhole 5 4).relabel fun x => 4 * x.1.val + x.2.val

-- On PHP(5, 4) minimization removes several literals at once, and its clauses repeat no literal:
-- the asserting literal is not kept in the tail as well as at the head.
#guard match (solveWith {} php54).1 with
  | .unsat cert => !(minimizationSteps cert).isEmpty && (minimizationSteps cert).all id
  | .sat _ => false

-- The mode is selected on PHP(5, 4): the two runs learn clauses of the same total width before
-- minimization and of different total widths after it. These totals do not show that the runs
-- learn the same clauses; `CslibFrontierTests.Algorithms.Lean.CDCL.Minimize` compares the two
-- modes on one fixed clause. All three modes' certificates are accepted.
#guard (solveWith { ccminMode := .basic } php54).2.maxLiterals ==
    (solveWith { ccminMode := .recursive } php54).2.maxLiterals &&
  (solveWith { ccminMode := .recursive } php54).2.literals <
    (solveWith { ccminMode := .basic } php54).2.literals
#guard [CcminMode.none, .basic, .recursive].all fun m =>
  match (solveWith { ccminMode := m } php54).1 with
  | .unsat cert => php54.checkLRAT cert
  | .sat _ => false

end CslibFrontierTests.Algorithms.Lean.CDCL.Compact
