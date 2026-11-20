/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! The text front end of the VeriPB kernel-proof checker on proofs elaborated to the kernel format
by the VeriPB tool, version 3.0.2 (commit `f50be284`, run as `veripb --elaborate`):

* PHP(3, 2) as an OPB file, with the cutting-planes proof of
  `CslibFrontierTests.Logics.Propositional.VeriPB.proof`;
* PHP(4, 3) as a DIMACS file, with a proof logged by DPLL with unit propagation (each learned
  clause a `rup` step, children deleted after their parent is learned) and elaborated to hinted
  `rup` and `deld` steps; the logged proof itself is also accepted, its hintless `rup` steps read
  as `rupSearch` and `del id` as deletion;
* the test instance `redundance_explicit_subproof` of the VeriPB repository (MIT/Apache-2.0), a
  symmetry-breaking `red` step with `proofgoal` blocks whose other goals are autoproven;
* a small covering problem with an objective, its optimum `1` certified by `red`, `soli` and
  `conclusion BOUNDS 1 : 6 1`, with goal `#2` autoproven or proved explicitly; the proofs were
  also accepted by CakePB (CakeML commit `14856fcf`);
* unchecked deletion between logged solutions: the best logged value gives the lower bound, and
  only a solution of the input certifies the upper bound or `SAT`;

and rejections: wrong lower and upper bounds, a logged solution violating a constraint or leaving
an objective variable unassigned, a `red` step raising the objective, an upper bound or `SAT`
certified only by a solution logged after unchecked deletion that fails the input, a dropped
hint, a repeated deletion, deletion inside a subproof, malformed or mismatched DIMACS headers, a
wrong formula size, an unsupported rule, and a conclusion that is not a contradiction. Parsing is
tested on its own. The checks run by `#guard`; the soundness theorems apply to any accepted pair
of texts. -/

set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBText

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text

/-! ### Parsing -/

-- An equality is two constraints, `≥` then `≤`; negative coefficients move to the negated literal;
-- comments are skipped.
#guard (parseOPB "* comment\n+1 x1 -2 x2 = 1 ;\n3 ~x3 <= 2 ;\n").map (·.constraints) ==
  some [⟨[(1, (0, true)), (2, (1, false))], 3⟩, ⟨[(1, (0, false)), (2, (1, true))], 0⟩,
    ⟨[(3, (2, true))], 1⟩]

-- The objective line comes first; `-2 ~x2` is `2 x2 - 2`. Without it there is no objective.
#guard (parseOPB "* comment\nmin: +1 x1 -2 ~x2 ;\n+1 x1 >= 1 ;\n").map (·.objective) ==
  some (some ⟨[(0, 1), (1, 2)], -2⟩)
#guard (parseOPB "+1 x1 >= 1 ;\n").map (·.objective) == some none
-- An objective line after a constraint, or two of them, is rejected.
#guard (parseOPB "+1 x1 >= 1 ;\nmin: +1 x1 ;\n").isNone
#guard (parseOPB "min: +1 x1 ;\nmin: +1 x1 ;\n").isNone
-- A constraint needs a relation.
#guard (parseOPB "+1 x1 1 ;\n").isNone

-- DIMACS clauses may span lines; the variable `v + 1` is `v`.
#guard parseDIMACS "c comment\np cnf 2 2\n1 -2 0\n2\n0\n" ==
  some [[(0, true), (1, false)], [(1, true)]]

/-! ### PHP(3, 2), cutting planes -/

/-- PHP(3, 2) in OPB: pigeon `i` in hole `j` is `x(2i+j+1)`. -/
def php32 : String := "* #variable= 6 #constraint= 9
+1 x1 +1 x2 >= 1 ;
+1 x3 +1 x4 >= 1 ;
+1 x5 +1 x6 >= 1 ;
+1 ~x1 +1 ~x3 >= 1 ;
+1 ~x1 +1 ~x5 >= 1 ;
+1 ~x3 +1 ~x5 >= 1 ;
+1 ~x2 +1 ~x4 >= 1 ;
+1 ~x2 +1 ~x6 >= 1 ;
+1 ~x4 +1 ~x6 >= 1 ;
"

/-- The elaborated proof: division by `2` of the sums of the hole clauses, then the sum of
everything. -/
def php32Proof : String := "pseudo-Boolean proof version 3.0
f 9;
pol 4 5 + 6 + 2 d;
pol 7 8 + 9 + 2 d;
pol 1 2 + 3 + 10 + 11 +;
output NONE ;
conclusion UNSAT : 12;
end pseudo-Boolean proof;
"

#guard checkOPB php32 php32Proof == some (.unsat 12)

-- The conclusion must name the contradiction.
#guard (checkOPB php32 (php32Proof.replace "UNSAT : 12" "UNSAT : 11")).isNone

-- `f` must give the number of constraints.
#guard (checkOPB php32 (php32Proof.replace "f 9;" "f 8;")).isNone

-- The rounding variant of division, `c`, is not supported.
#guard (checkOPB php32 (php32Proof.replace "+ 2 d;" "+ 2 c;")).isNone

/-! ### PHP(4, 3), unit propagation -/

/-- PHP(4, 3) in DIMACS. -/
def php43 : String := "p cnf 12 22
1 2 3 0
4 5 6 0
7 8 9 0
10 11 12 0
-1 -4 0
-1 -7 0
-1 -10 0
-4 -7 0
-4 -10 0
-7 -10 0
-2 -5 0
-2 -8 0
-2 -11 0
-5 -8 0
-5 -11 0
-8 -11 0
-3 -6 0
-3 -9 0
-3 -12 0
-6 -9 0
-6 -12 0
-9 -12 0
"

/-- The proof logged by DPLL, before elaboration: hintless `rup` and `del id`. -/
def php43Logged : String := "pseudo-Boolean proof version 3.0
f 22 ;
rup 1 ~x1 1 ~x2 >= 1 ;
rup 1 ~x1 1 x2 1 ~x3 >= 1 ;
rup 1 ~x1 1 x2 1 x3 1 ~x5 >= 1 ;
rup 1 ~x1 1 x2 1 x3 1 x5 >= 1 ;
rup 1 ~x1 1 x2 1 x3 >= 1 ;
del id 25 ;
del id 26 ;
rup 1 ~x1 1 x2 >= 1 ;
del id 24 ;
del id 27 ;
rup 1 ~x1 >= 1 ;
del id 23 ;
del id 28 ;
rup 1 x1 1 ~x2 1 ~x3 >= 1 ;
rup 1 x1 1 ~x2 1 x3 1 ~x4 >= 1 ;
rup 1 x1 1 ~x2 1 x3 1 x4 >= 1 ;
rup 1 x1 1 ~x2 1 x3 >= 1 ;
del id 31 ;
del id 32 ;
rup 1 x1 1 ~x2 >= 1 ;
del id 30 ;
del id 33 ;
rup 1 x1 1 x2 1 ~x4 >= 1 ;
rup 1 x1 1 x2 1 x4 >= 1 ;
rup 1 x1 1 x2 >= 1 ;
del id 35 ;
del id 36 ;
rup 1 x1 >= 1 ;
del id 34 ;
del id 37 ;
rup  >= 1 ;
del id 29 ;
del id 38 ;
output NONE ;
conclusion UNSAT : 39 ;
end pseudo-Boolean proof ;
"

/-- The kernel proof elaborated by VeriPB from `php43Logged`. -/
def php43Kernel : String := "pseudo-Boolean proof version 3.0
f 22;
rup 1 ~x1 1 ~x2 >= 1 : ~ 5 6 11 12 2 3 20;
rup 1 ~x1 1 x2 1 ~x3 >= 1 : ~ 6 5 17 18 2 3 14;
rup 1 ~x1 1 x2 1 x3 1 ~x5 >= 1 : ~ 6 7 15 14 4 3 22;
rup 1 ~x1 1 x2 1 x3 1 x5 >= 1 : ~ 7 6 5 2 21 20 4 3 16;
rup 1 ~x1 1 x2 1 x3 >= 1 : ~ 26 25;
deld 25;
deld 26;
rup 1 ~x1 1 x2 >= 1 : ~ 27 24;
deld 24;
deld 27;
rup 1 ~x1 >= 1 : ~ 28 23;
deld 23;
deld 28;
rup 1 x1 1 ~x2 1 ~x3 >= 1 : ~ 13 11 19 17 4 2 9;
rup 1 x1 1 ~x2 1 x3 1 ~x4 >= 1 : ~ 12 13 8 9 3 4 22;
rup 1 x1 1 ~x2 1 x3 1 x4 >= 1 : ~ 13 12 11 2 20 21 3 4 10;
rup 1 x1 1 ~x2 1 x3 >= 1 : 29 ~ 32 31;
deld 31;
deld 32;
rup 1 x1 1 ~x2 >= 1 : 29 ~ 33 30;
deld 30;
deld 33;
rup 1 x1 1 x2 1 ~x4 >= 1 : 29 34 1 18 19 ~ 9 8 4 3 16;
rup 1 x1 1 x2 1 x4 >= 1 : 29 34 1 17 18 19 35 2 14 15 3 4 10;
rup 1 x1 1 x2 >= 1 : 29 34 1 17 18 19 35 2 14 15 3 4 10;
deld 35;
deld 36;
rup 1 x1 >= 1 : 29 34 37;
deld 34;
deld 37;
rup >= 1 : 29 38;
deld 29;
deld 38;
output NONE ;
conclusion UNSAT : 39;
end pseudo-Boolean proof;
"

#guard checkDIMACS php43 php43Kernel == some (.unsat 39)

#guard checkDIMACS php43 php43Logged == some (.unsat 39)

-- Dropping the last hint of the final `rup` leaves no conflict.
def php43DropHint : String := php43Kernel.replace "rup >= 1 : 29 38;" "rup >= 1 : 29;"

#guard php43DropHint != php43Kernel
#guard (checkDIMACS php43 php43DropHint).isNone

-- A constraint cannot be deleted twice.
def php43DeleteTwice : String := php43Kernel.replace "deld 38;" "deld 38 38;"

#guard php43DeleteTwice != php43Kernel
#guard (checkDIMACS php43 php43DeleteTwice).isNone

-- The DIMACS header must give the numbers of variables and clauses, and the clauses must match.
#guard (checkDIMACS ("p cnf\n" ++ (php43.drop 12).toString) php43Kernel).isNone
#guard parseDIMACS "p cnf\n0\n" == none
#guard parseDIMACS "p cnf 2 1\n1 -2 0\n2 0\n" == none
#guard parseDIMACS "p cnf 1 1\n1 -2 0\n" == none
#guard (php43.take 12).toString == "p cnf 12 22\n"

/-! ### Redundance-based strengthening -/

/-- The instance `redundance_explicit_subproof.opb` of the VeriPB test suite. -/
def rotation : String := "* #variable= 4 #constraint= 7
2 ~x1 1 ~x3 >= 1 ;
1 ~x3 1 ~x5 >= 1 ;
1 ~x1 1 ~x5 >= 1 ;
1 ~x2 1 ~x4 1 ~x6 >= 2 ;
+1 x1 +1 x2 >= 1 ;
+1 x3 +1 x4 >= 1 ;
+1 x5 +1 x6 >= 1 ;
"

/-- Its proof, elaborated by VeriPB: a `red` step with the rotation witness
`x1 → x3 → x5 → x1`, `x2 → x4 → x6 → x2`, proving goal `#1` and the goal of constraint `1`;
the goals of the other constraints are rotations of database constraints, or implied. -/
def rotationProof : String := "pseudo-Boolean proof version 3.0
f 7;
pol 1 s;
pol 8 2 + 3 +;
pol 9 2 d;
red 1 x1 >= 1 : x1 -> x3 x3 -> x5 x5 -> x1 x2 -> x4 x4 -> x6 x6 -> x2 : subproof
  proofgoal #1
    pol 12 11 + 5 + 6 +;
    pol 13 4 +;
    pol 14 x6 +;
  qed : 15;
  proofgoal 1
    pol 16 2 +;
  qed : 17;
qed;
rup >= 1 : 18 3 7 4 6 1;
output NONE ;
conclusion UNSAT : 19;
end pseudo-Boolean proof;
"

#guard checkOPB rotation rotationProof == some (.unsat 19)

/-- `rotationProof` without the `proofgoal 1` block, renumbered: `C` is now `16`. -/
def rotationNoGoal1 : String :=
  ((rotationProof.replace "  proofgoal 1\n    pol 16 2 +;\n  qed : 17;\n" "").replace
    "rup >= 1 : 18 3" "rup >= 1 : 16 3").replace "UNSAT : 19" "UNSAT : 17"

-- The goal of constraint `1`, `2 ~x3 + ~x5 >= 1`, is then not covered: it is not in the
-- database and not implied by `1` or by `~x1 >= 1`.
#guard rotationNoGoal1 != rotationProof
#guard (checkOPB rotation rotationNoGoal1).isNone

-- Deletion is accepted only at top level: not inside a `proofgoal` block.
def rotationNestedDel : String :=
  rotationProof.replace "    pol 16 2 +;\n" "    deld 9;\n    pol 16 2 +;\n"

#guard rotationNestedDel != rotationProof
#guard (parseProof 7 6 rotationNestedDel).isNone
#guard (parseProof 7 6 (rotationProof.replace "output NONE" "deld 9;\noutput NONE")).isSome

/-! ### Optimization -/

/-- Minimize `x1 + x2 + x3` subject to `x1 + x2 >= 1` and `x2 + x3 >= 1`; the optimum is `1`. -/
def cover : String := "* #variable= 3 #constraint= 2
min: 1 x1 1 x2 1 x3 ;
1 x1 1 x2 >= 1 ;
1 x2 1 x3 >= 1 ;
"

/-- The kernel proof elaborated by VeriPB of an optimality proof: `red` adds `~x1 >= 1`, with
`x1 -> 0 x2 -> 1` not raising the objective (goal `#2` is autoproven from `~C`); the solution
`x2` of value `1` is logged with `soli`, adding `x1 + x2 + x3 <= 0` as constraint `5`; RUP from
`5` and `1` refutes it, so `1` is a lower bound. CakePB (CakeML `14856fcf`) also accepts it. -/
def coverProof : String := "pseudo-Boolean proof version 3.0
f 2;
red 1 ~x1 >= 1 : x1 -> 0 x2 -> 1 : subproof
qed;
soli ~x1 x2 ~x3;
rup >= 1 : 5 1;
output NONE ;
conclusion BOUNDS 1 : 6 1;
end pseudo-Boolean proof;
"

#guard checkOPB cover coverProof == some (.bounds (some 1) 6 (some 1))

-- Goal `#2` may be proved explicitly: its negation `x1 + x2 <= 0` is `4`, and with `~C`, `3`,
-- it sums to a contradiction. VeriPB and CakePB accept this proof too.
def coverGoal2 : String :=
  ((coverProof.replace "qed;\nsoli"
    "  proofgoal #2\n    pol 4 3 +;\n  qed : 5;\nqed;\nsoli").replace "5 1;" "7 1;").replace
    "BOUNDS 1 : 6 1" "BOUNDS 1 : 8 1"

#guard coverGoal2 != coverProof
#guard checkOPB cover coverGoal2 == some (.bounds (some 1) 8 (some 1))

-- `INF` bounds claim nothing above, and a weaker lower bound may name any constraint implying
-- it; both are accepted by VeriPB and CakePB.
#guard checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 1 : 6 INF") ==
  some (.bounds (some 1) 6 none)
#guard checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 0 : 1 1") ==
  some (.bounds (some 0) 1 (some 1))

-- Rejected, as by VeriPB and CakePB: a lower bound above the logged value,
#guard (checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 2 : 6 1")).isNone
-- an upper bound below it,
#guard (checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 1 : 6 0")).isNone
-- a logged solution that violates constraint `1`,
#guard (checkOPB cover (coverProof.replace "soli ~x1 x2 ~x3" "soli ~x1 ~x2 ~x3")).isNone
-- and `UNSAT` for a feasible instance.
#guard (checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "UNSAT : 6")).isNone

-- Rejected, as by VeriPB (CakePB accepts both): an upper bound other than the logged value,
#guard (checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 1 : 6 2")).isNone
-- and a `soli` solution that leaves a variable of the objective unassigned.
#guard (checkOPB cover (coverProof.replace "soli ~x1 x2 ~x3" "soli ~x1 x2")).isNone

/-- A `red` step whose witness `x1 -> 1` raises the objective, followed by the logged solution
`x1 x3` of value `2` and a refutation of its improving constraint: the claim that the optimum is
`2` is false, and VeriPB and CakePB reject the `red` step because goal `#2` is not proved. -/
def coverBadRed : String := "pseudo-Boolean proof version 3.0
f 2;
red 1 x1 >= 1 : x1 -> 1 : subproof
qed;
soli x1 ~x2 x3;
rup >= 1 : 5 4 2;
output NONE ;
conclusion BOUNDS 2 : 6 2;
end pseudo-Boolean proof;
"

#guard (checkOPB cover coverBadRed).isNone

-- Without the objective, the same `red` step is accepted, and a logged solution proves `SAT`
-- (as for VeriPB and CakePB).
def coverDecision : String := "* #variable= 3 #constraint= 2
1 x1 1 x2 >= 1 ;
1 x2 1 x3 >= 1 ;
"

def coverDecisionSat : String :=
  ((coverBadRed.replace "soli" "sol").replace "rup >= 1 : 5 4 2;\n" "").replace
    "BOUNDS 2 : 6 2" "SAT"

#guard checkOPB coverDecision coverDecisionSat == some .sat
-- `soli` needs an objective, and `BOUNDS` too.
#guard (checkOPB coverDecision coverBadRed).isNone
#guard (checkOPB coverDecision (coverDecisionSat.replace "SAT" "BOUNDS 0 : 1 INF")).isNone

/-! ### Unchecked deletion and the witness -/

/-- Minimize `x1` subject to `x1 >= 1` and `x1 >= 0`; the optimum is `1`. -/
def delOpt : String := "* #variable= 1 #constraint= 2
min: 1 x1 ;
1 x1 >= 1 ;
1 x1 >= 0 ;
"

/-- `x1` is logged while both constraints are present, then constraint `1` is deleted without a
proof (`delc` without a subproof is unchecked deletion in VeriPB's kernel format), and `~x1`,
of value `0`, is logged against the weakened database. `~x1` gives the best logged value, so
the lower bound `0` is accepted. It does not solve the input, so `x1` stays the witness, of
value `1`, for the upper bound. VeriPB 3.0.2 and CakePB both accept this proof. -/
def delOptProof : String := "pseudo-Boolean proof version 3.0
f 2;
soli x1;
delc 1;
soli ~x1;
output NONE;
conclusion BOUNDS 0 : 2 1;
end pseudo-Boolean proof;
"

#guard checkOPB delOpt delOptProof == some (.bounds (some 0) 2 (some 1))
-- The invalid `~x1` does not certify the upper bound `0` (VeriPB and CakePB reject it too).
#guard (checkOPB delOpt (delOptProof.replace "BOUNDS 0 : 2 1" "BOUNDS 0 : 2 0")).isNone

/-- The decision version of `delOpt`. -/
def delDec : String := "* #variable= 1 #constraint= 2
1 x1 >= 1 ;
1 x1 >= 0 ;
"

/-- After an unchecked deletion, `~x1` (not a solution of the input) is logged, then `x1` (one
that is), with the same value. The later valid solution becomes the witness, so `SAT` is
accepted. VeriPB accepts this proof. CakePB rejects it: it ignores solutions logged after an
unchecked deletion, where this checker tests them against the input instead. -/
def delDecProof : String := "pseudo-Boolean proof version 3.0
f 2;
delc 1;
sol ~x1;
sol x1;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
"

#guard checkOPB delDec delDecProof == some .sat
-- With only the invalid solution logged, `SAT` is rejected (CakePB rejects it too).
#guard (checkOPB delDec (delDecProof.replace "sol x1;\n" "")).isNone

/-! ### Soundness -/

-- The accepted optimality proof: every solution of `cover` has value at least `1`, and one has
-- value `1`.
example (h : checkOPB cover coverProof = some (.bounds (some 1) 6 (some 1))) :
    ∃ I f, parseOPB cover = some I ∧ I.objective = some f ∧
    (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) →
      ∃ l, some 1 = some l ∧ l ≤ f.eval σ) ∧
    ∀ u, some 1 = some u →
      ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ = u :=
  bounds_of_checkOPB h

-- An accepted pair of texts is an unsatisfiable formula.
example (h : checkDIMACS php43 php43Kernel = some (.unsat 39)) :
    ∃ φ, parseDIMACS php43 = some φ ∧ ¬ φ.Satisfiable :=
  not_satisfiable_of_checkDIMACS h

end CslibFrontierTests.Logics.Propositional.VeriPBText
