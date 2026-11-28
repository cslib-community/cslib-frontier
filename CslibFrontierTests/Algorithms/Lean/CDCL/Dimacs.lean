/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Dimacs
public meta import CslibFrontier.Algorithms.Lean.CDCL.Dimacs

/-!
# The answers of `lake exe cdcl`

The answer the executable prints for DIMACS text (`answerDIMACS`, without the statistics), run
compiled. The empty formula `p cnf 0 0` is satisfiable with the model `v 0`. A formula over the
single DIMACS variable `10⁶` gets a model of one literal. The model of a formula over three
variables lists each once, in increasing order, whatever their order and repetitions in the file.
An unsatisfiable formula gets `s UNSATISFIABLE`, exit code `20` and a certificate the checker
accepts; text that is not DIMACS is an error. On the text printed for a formula built in Lean, the
answer concerns that formula (`answerDIMACS_toDIMACS`).
-/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Dimacs

open Cslib.Logic.PL Cslib.Algorithms.Lean.CDCL

private def out (text : String) : Option (String × UInt32) :=
  (answerDIMACS {} text).toOption.map fun a => (a.output, a.code)

#guard out "p cnf 0 0\n" == some ("s SATISFIABLE\nv 0\n", 10)
#guard out "p cnf 1000000 1\n1000000 0\n" == some ("s SATISFIABLE\nv 1000000 0\n", 10)
#guard out "p cnf 1000000 1\n-1000000 0\n" == some ("s SATISFIABLE\nv -1000000 0\n", 10)
/-- The DIMACS variables of the `v` lines of an answer, in the order printed, with the final `0`. -/
private def modelVars (output : String) : List ℕ :=
  ((output.splitOn "\n").filter (·.startsWith "v ")).flatMap fun line =>
    ((line.splitOn " ").drop 1).filterMap fun t => t.toInt?.map Int.natAbs

#guard (out "p cnf 5 3\n5 -2 0\n2 5 0\n-5 3 -2 0\n").map (modelVars ·.1) == some [2, 3, 5, 0]

#guard occurringVars [[(4, true), (1, false)], [(1, true), (4, false)], []] == [1, 4]

-- A long model is split into `v` lines of at most 80 characters, the last one ending with `0`.
#guard (modelLines (fun _ => true) (List.range 100)).splitOn "\n" |>.all (·.length ≤ 80)

#guard match answerDIMACS {} "p cnf 1 2\n1 0\n-1 0\n" with
  | .ok a => a.output == "s UNSATISFIABLE\n" && a.code == 20 &&
      a.cert.any (a.formula.checkLRAT ·)
  | .error _ => false

#guard (answerDIMACS {} "p cnf 1 1\n2 0\n").toOption.isNone

-- A formula built in Lean and printed: the answer is about the formula itself.
#guard (answerDIMACS {} (CNF.toDIMACS [[(0, true)], [(0, false)]])).toOption.map (·.code) ==
  some 20

example {a : DimacsAnswer} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : answerDIMACS {} (CNF.toDIMACS [[(0, true)], [(0, false)]]) = .ok a)
    (hc : a.cert = some cert) : ¬ CNF.Satisfiable [[(0, true)], [(0, false)]] :=
  CNF.not_satisfiable_of_checkLRAT (checkLRAT_of_answerDIMACS_toDIMACS h hc)

end CslibFrontierTests.Algorithms.Lean.CDCL.Dimacs
