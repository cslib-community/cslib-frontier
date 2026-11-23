/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Minimize

/-!
# Basic and recursive minimization on one learned clause

The variables are `p = 0`, `q = 1`, `a = 2`, `b = 3`, `c = 4`, `e = 5`, `d = 6`. At the root, `p`
holds and `p → q` implies `q`; the decision `a` implies `b` by `a → b`, `c` by `b → c` and `e` by
`a ∧ q → e`; then comes the decision `d`. The learned clause is `¬d ∨ ¬c ∨ ¬e ∨ ¬a`, asserting `¬d`,
numbered `6` after the five clauses of the formula.

Basic minimization (MiniSat's `ccmin_mode = 1`) follows only reasons of literals implied at the
root: it removes `¬e`, whose reason has `¬a` from the clause and `¬q` from the root, and keeps `¬c`,
whose reason has `¬b`, implied above the root. Recursive minimization (`ccmin_mode = 2`) also
follows `b`, and removes `¬c` as well. The kernel computes both, the hints of the RUP step,
including the root chain `1, 2`, and its check.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Minimize

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Algorithms.Lean.CDCL

/-- The five clauses of the formula, and the learned clause as the sixth. -/
private abbrev fx : CNF ℕ :=
  [[(0, true)], [(0, false), (1, true)], [(2, false), (3, true)], [(3, false), (4, true)],
    [(2, false), (1, false), (5, true)], [(6, false), (4, false), (5, false), (2, false)]]

/-- The array trail, oldest first (`0`, `1` at the root; decision `2`, implied `3`, `4`, `5`;
newest decision `6` at position `6`), with variable positions `vpos`. -/
private def tr : ATrail :=
  (((((((ATrail.empty.push (litKey (0, true)) 2).push (litKey (1, true)) 3).push
    (litKey (2, true)) 0).push (litKey (3, true)) 4).push (litKey (4, true)) 5).push
    (litKey (5, true)) 6).push (litKey (6, true)) 0)

private def vpos : Array ℕ := #[0, 1, 2, 3, 4, 5, 6]

/-- The learned clause `¬d ∨ ¬c ∨ ¬e ∨ ¬a`. -/
private abbrev C : Clause ℕ := [(6, false), (4, false), (5, false), (2, false)]

/-- The minimized clause and the hints of its RUP step, via `ATrail.reasonAt`, `redundant`, and
`ATrail.derivedHintsBelow` as `Learned.minimize` computes them at `p = 6`. -/
private def minimized (recursive : Bool) : Clause ℕ × List ℕ :=
  let inCArr := (⟨Array.replicate 7 0⟩ : Assign).markLits C
  let r0 := tr.firstDecGo 0 6
  let deep : ℕ → Bool :=
    if recursive then fun _ => true
    else fun v =>
      let i := vpos.getD v 0
      i < r0 && tr.lits.getD i 0 / 2 == v
  let r := redundant (LRATLog.init fx) (tr.reasonAt vpos 6) inCArr.assigned deep (tr.size + 1)
    (6, false) C ⟨Array.replicate 7 0⟩
  ((6, false) :: C.filter fun y => !Assign.litEq y (6, false) && !r.memo.holds (y.1, true),
    tr.derivedHintsBelow 6 r.memo ++ [6])

/-- Basic minimization removes `¬e` and keeps `¬c`; the hints replay the root chain and `e`. -/
example : minimized false = ([(6, false), (4, false), (2, false)], [1, 2, 5, 6]) := by
  decide +kernel

/-- Recursive minimization removes `¬c` and `¬e`, through `b`. -/
example : minimized true = ([(6, false), (2, false)], [1, 2, 3, 4, 5, 6]) := by decide +kernel

/-- Both RUP steps are accepted. -/
example : ∀ recursive : Bool, propagateHints fx.lratDB
    ((minimized recursive).1.map Std.Sat.Literal.negate) (minimized recursive).2 = true := by
  decide +kernel

end CslibFrontierTests.Algorithms.Lean.CDCL.Minimize
