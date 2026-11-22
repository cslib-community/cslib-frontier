/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.Resolution.FromLRAT
import CslibFrontier.Algorithms.Lean.CDCL.Watched
import CslibFrontier.Logics.Propositional.Pigeonhole
import CslibFrontierTests.Logics.Propositional.CNF.LRAT
public meta import CslibFrontier.Logics.Propositional.Resolution.FromLRAT
public meta import CslibFrontierTests.Logics.Propositional.CNF.LRAT

/-!
# Resolution refutations from LRAT certificates

The certificate of the LRAT checker's test for the four clauses over two variables,
`a ∨ b`, `a ∨ ¬b`, `¬a ∨ b`, `¬a ∨ ¬b`, translates to the refutation that resolves `a ∨ b` with
`a ∨ ¬b`, then `¬a ∨ b` with `¬a ∨ ¬b`, then the two results. The first RUP step adds the clause
`a`, but resolution, which has no weakening, derives `a ∨ a`: a line with a repeated literal.

The CDCL solver's certificate for PHP(3, 2) translates to a refutation of 19 lines, within the
bound of `Cslib.Logic.PL.CNF.isProof_lratToProof` (9 clauses, and the smaller of 12 hints and
2 steps times 6 variables). A Boolean resolution-proof checker written here, independent of the
translation, accepts it, by `decide +kernel`. At runtime it also accepts the 377-line
translation of CaDiCaL's certificate for PHP(5, 4).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.Resolution.FromLRAT

open Cslib.Logic.PL Cslib.Algorithms.Lean Std.Tactic.BVDecide

/-- A resolution-proof checker: every line, listed from last to first, is a clause of `φ` or the
resolvent of two lines below it on a variable occurring positively in the first and negatively in
the second. -/
private def checkProof (φ : CNF ℕ) : List (Clause ℕ) → Bool
  | [] => true
  | c :: ls => checkProof φ ls && (φ.contains c || ls.any fun c₁ => ls.any fun c₂ =>
      c₁.any fun l => l.2 && c₂.contains (l.1, false) && c == c₁.resolvent c₂ l.1)

/-- Every clause over two variables. -/
private abbrev φ : CNF ℕ :=
  [[(0, true), (1, true)], [(0, true), (1, false)], [(0, false), (1, true)],
    [(0, false), (1, false)]]

/-- The refutation: the unit clause `a`, then the empty clause. -/
private abbrev cert : Array LRAT.IntAction :=
  #[.addRup 5 #[1] #[1, 2], .addEmpty 6 #[5, 3, 4]]

example : φ.lratToProof cert = some
    [[], [(0, false), (0, false)], [(0, true), (0, true)], [(0, true), (1, true)],
      [(0, true), (1, false)], [(0, false), (1, true)], [(0, false), (1, false)]] := by
  decide +kernel

-- The bound: 4 clauses and the smaller of 5 hints and 2 steps times 2 variables.
example : φ.RefutableInSize 8 :=
  (CNF.refutableInSize_of_checkLRAT (φ := φ) (cert := cert) (by decide)).mono (by decide)

/-- PHP(3, 2), the library's pigeonhole formula with pigeon `i` in hole `j` as `2 * i + j`. -/
private abbrev php : CNF ℕ := (CNF.pigeonhole 3 2).relabel fun x => 2 * x.1.val + x.2.val

/-- The translation of the solver's certificate for PHP(3, 2) is a refutation of 19 lines. -/
example : (match CDCL.solve php with
    | .unsat c => match php.lratToProof c with
      | some ls => checkProof php ls && ls.contains [] && ls.length == 19 &&
          (php.length, CNF.lratHintCount c.toList, c.size) == (9, 12, 2)
      | none => false
    | .sat _ => false) = true := by
  decide +kernel

-- CaDiCaL's certificate for PHP(5, 4): 45 clauses, 380 hints and 55 steps.
/-- info: true -/
#guard_msgs in
#eval match CNF.LRAT.php.lratToProof CNF.LRAT.phpCert with
  | some ls => checkProof CNF.LRAT.php ls && ls.contains [] && ls.length == 377
  | none => false

end CslibFrontierTests.Logics.Propositional.Resolution.FromLRAT
