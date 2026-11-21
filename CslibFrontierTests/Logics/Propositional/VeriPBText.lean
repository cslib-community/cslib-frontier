/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontierTests.Logics.Propositional.VeriPBOutputFixtures

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
* the core/derived split: a checked deletion followed by an upper bound certified by a solution
  that does not solve the input, `deld`, unchecked and checked `delc`, `core id`,
  strengthening-to-core mode, and the numbering of `red` and `delc` with and without subproofs,
  each compared with VeriPB 3.0.2 and CakePB;
* `obji`: a lower bound from an asserted value with no logged solution, alone and after `soli`;
* the conclusion section: `SAT : ρ` and `BOUNDS lb : q ub : ρ` with stated assignments, and
  `NONE`;
* `obju`: an objective update, autoproven or with explicit `proofgoal` blocks, before and after
  a logged solution;
* projected enumeration: `solx` over a `preserved:` set, with `ENUMERATION_PARTIAL` and
  `ENUMERATION_COMPLETE`;
* output sections: the test instances `decision_output` and
  `optimization_output_opposing_lits_objective` of the VeriPB repository, elaborated, with
  `EQUISATISFIABLE`, `DERIVABLE` and `EQUIOPTIMAL` outputs given as `FILE` or `IMPLICIT`, and an
  `EQUIENUMERABLE` output after a witness on an unpreserved variable, each compared with VeriPB
  and CakePB;

and rejections: wrong lower and upper bounds, a logged solution violating a constraint or leaving
an objective variable unassigned, a `red` step raising the objective, an upper bound or `SAT`
certified only by a solution logged after unchecked deletion that fails the input, a typed
deletion of the wrong kind, a checked deletion with a failing witness, a witness or an unchecked
deletion that strengthening-to-core mode forbids, an upper bound, a lower bound above the asserted
value or `UNSAT` resting on `obji` alone, stated assignments that fail the input, have the wrong
value or leave an objective variable unassigned, an objective update that is not an equality on
the core set or rests on derived constraints, an enumeration that overcounts, repeats a solution,
claims completeness without a contradiction, leaves a preserved variable unassigned, follows an
unchecked deletion, or uses a witness that moves a preserved variable, a dropped
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

#guard checkOPB cover coverProof == some (.bounds (some 1) 6 (some 1) none)

-- Goal `#2` may be proved explicitly: its negation `x1 + x2 <= 0` is `4`, and with `~C`, `3`,
-- it sums to a contradiction. VeriPB and CakePB accept this proof too.
def coverGoal2 : String :=
  ((coverProof.replace "qed;\nsoli"
    "  proofgoal #2\n    pol 4 3 +;\n  qed : 5;\nqed;\nsoli").replace "5 1;" "7 1;").replace
    "BOUNDS 1 : 6 1" "BOUNDS 1 : 8 1"

#guard coverGoal2 != coverProof
#guard checkOPB cover coverGoal2 == some (.bounds (some 1) 8 (some 1) none)

-- `INF` bounds claim nothing above, and a weaker lower bound may name any constraint implying
-- it; both are accepted by VeriPB and CakePB.
#guard checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 1 : 6 INF") ==
  some (.bounds (some 1) 6 none none)
#guard checkOPB cover (coverProof.replace "BOUNDS 1 : 6 1" "BOUNDS 0 : 1 1") ==
  some (.bounds (some 0) 1 (some 1) none)

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

#guard checkOPB coverDecision coverDecisionSat == some (.sat none)
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

#guard checkOPB delOpt delOptProof == some (.bounds (some 0) 2 (some 1) none)
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

#guard checkOPB delDec delDecProof == some (.sat none)
-- With only the invalid solution logged, `SAT` is rejected (CakePB rejects it too).
#guard (checkOPB delDec (delDecProof.replace "sol x1;\n" "")).isNone

/-! ### Core and derived constraints

The fixtures below were also run through VeriPB 3.0.2 and CakePB; their verdicts are noted. CakePB
parses `red` and checked `delc` only with a subproof, so the subproof forms are the ones compared
with it. -/

/-- Minimize `x2` subject to `x1 >= 1`; the optimum is `0`. -/
def ck : String := "* #variable= 2 #constraint= 1
min: 1 x2 ;
1 x1 >= 1 ;
"

/-- The checked deletion of constraint `1` with the witness `x1 ↦ 1`, whose goals are trivial.
Then `~x1 ~x2`, of value `0`, is logged. It does not solve the input, but no unchecked deletion
has happened, so it certifies the upper bound: the witness maps it to the input solution
`x1 ~x2`. The subproof gives `¬C` the number `2`, so the improving constraint is `3`. VeriPB and
CakePB accept this proof. -/
def ckProof : String := "pseudo-Boolean proof version 3.0
f 1;
delc 1 : x1 -> 1 : subproof
qed delc;
soli ~x1 ~x2;
output NONE;
conclusion BOUNDS 0 : 3 0;
end pseudo-Boolean proof;
"

#guard checkOPB ck ckProof == some (.bounds (some 0) 3 (some 0) none)
-- Without a subproof, `¬C` takes no number and the improving constraint is `2` (VeriPB accepts).
#guard checkOPB ck ((ckProof.replace " : subproof\nqed delc;" " ;").replace ": 3 0" ": 2 0") ==
  some (.bounds (some 0) 2 (some 0) none)
-- After an unchecked deletion the same solution certifies nothing (VeriPB and CakePB reject).
#guard (checkOPB ck (ckProof.replace "delc 1 : x1 -> 1 : subproof\nqed delc;" "delc 1;")).isNone
-- The witness `x1 ↦ 0` falsifies goal `#1` (VeriPB and CakePB reject).
#guard (checkOPB ck (ckProof.replace "x1 -> 1" "x1 -> 0")).isNone
-- `deld` of a core constraint is an error (VeriPB and CakePB reject).
#guard (checkOPB ck (ckProof.replace "delc 1 : x1 -> 1 : subproof\nqed delc;" "deld 1;")).isNone

/-- `x1 >= 1`. -/
def one : String := "* #variable= 2 #constraint= 1
1 x1 >= 1 ;
"

/-- Constraint `2`, `x1 + x2 >= 1`, is derived and moved to the core; it is then deleted by a
checked deletion whose subproof refutes its negation `3` with constraint `1`. VeriPB and CakePB
accept this proof. -/
def coreProof : String := "pseudo-Boolean proof version 3.0
f 1;
pol 1 x2 + ;
core id 2;
delc 2 : : subproof
rup >= 1 : 3 1;
qed delc : 4;
sol x1;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
"

#guard checkOPB one coreProof == some (.sat none)
-- Promoting a core constraint again is a no-op (VeriPB and CakePB accept).
#guard checkOPB one (coreProof.replace "core id 2;" "core id 2 2;\ncore id 1 2;") ==
  some (.sat none)
-- `core id` needs at least one ID (§5.1; VeriPB 3.0.2 and CakePB accept the empty list).
#guard (checkOPB one (coreProof.replace "core id 2;" "core id 2;\ncore id ;")).isNone
-- `~x1` is not a solution of the database (VeriPB and CakePB reject).
#guard (checkOPB one (coreProof.replace "sol x1;" "sol ~x1;")).isNone
-- Without `core id`, constraint `2` is derived and `delc` cannot delete it (VeriPB rejects; CakePB
-- deletes it unchecked, then rejects `SAT`).
#guard (checkOPB one ((coreProof.replace "core id 2;\n" "").replace
  "delc 2 : : subproof\nrup >= 1 : 3 1;\nqed delc : 4;" "delc 2;")).isNone
/-- `deld` deletes it instead (VeriPB and CakePB accept). -/
def deldProof : String := (coreProof.replace "core id 2;\n" "").replace
  "delc 2 : : subproof\nrup >= 1 : 3 1;\nqed delc : 4;" "deld 2;"

#guard (deldProof.splitOn "deld 2;").length == 2 && (deldProof.splitOn "core").length == 1
#guard checkOPB one deldProof == some (.sat none)

/-- Unchecked deletion of the core constraint `2`: `sol x1` solves the input, so `SAT` stands
(VeriPB accepts; CakePB ignores solutions logged after unchecked deletion and rejects). -/
def uncheckedProof : String := coreProof.replace
  "delc 2 : : subproof\nrup >= 1 : 3 1;\nqed delc : 4;" "delc 2;"

#guard uncheckedProof != coreProof
#guard checkOPB one uncheckedProof == some (.sat none)

/-- `red` without a subproof: `¬C` takes no number, so `C`, `x2 >= 1`, is constraint `2`, which
the next step uses. VeriPB accepts this proof. -/
def redNumProof : String := "pseudo-Boolean proof version 3.0
f 1;
red 1 x2 >= 1 : x2 -> 1 ;
pol 2 1 + ;
sol x1 x2;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
"

#guard checkOPB one redNumProof == some (.sat none)
/-- With a subproof, `¬C` is `2` and `C` is `3` (VeriPB and CakePB accept). -/
def redNumSubProof : String :=
  (redNumProof.replace "x2 -> 1 ;" "x2 -> 1 : subproof\nqed;").replace "pol 2 1" "pol 3 1"

#guard (redNumSubProof.splitOn "subproof").length == 2
#guard (redNumSubProof.splitOn "pol 3").length == 2
#guard checkOPB one redNumSubProof == some (.sat none)
-- The old numbering fails without a subproof: constraint `3` does not exist.
#guard (checkOPB one (redNumProof.replace "pol 2 1" "pol 3 1")).isNone

/-- Strengthening-to-core mode: `red` adds a core constraint. VeriPB and CakePB accept this
proof. -/
def tcbProof : String := "pseudo-Boolean proof version 3.0
f 1;
strengthening_to_core on;
red 1 x2 >= 1 : x2 -> 1 : subproof
qed;
sol x1 x2;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
"

#guard checkOPB one tcbProof == some (.sat none)
#guard (tcbProof.replace "core on" "core off") != tcbProof
#guard checkOPB one (tcbProof.replace "core on" "core off") == some (.sat none)
-- In the mode, a checked deletion takes no witness (VeriPB and CakePB reject).
#guard (checkOPB one (tcbProof.replace "red 1 x2 >= 1 : x2 -> 1 : subproof\nqed;\nsol x1 x2;"
  "delc 1 : x1 -> 1 : subproof\nqed delc;\nsol ~x1;")).isNone
/-- In the mode, a checked deletion is a proof by contradiction: its subproof must close with a
contradiction `qed : n` (§5.7.4; CakePB's `check_tcb_idopt`). VeriPB and CakePB accept this proof;
without `: 4`, CakePB rejects it and VeriPB accepts it. -/
def tcbCheckedProof : String := tcbProof.replace
  "red 1 x2 >= 1 : x2 -> 1 : subproof\nqed;\nsol x1 x2;"
  "pol 1 x2 + ;\ncore id 2;\ndelc 2 : : subproof\nrup >= 1 : 3 1;\nqed delc : 4;\nsol x1;"

#guard checkOPB one tcbCheckedProof == some (.sat none)
#guard (checkOPB one (tcbCheckedProof.replace "qed delc : 4;" "qed delc;")).isNone
-- In the mode, an unchecked core deletion needs an empty derived set (VeriPB and CakePB reject).
#guard (checkOPB one (tcbProof.replace "red 1 x2 >= 1 : x2 -> 1 : subproof\nqed;\nsol x1 x2;"
  "pol 1 x2 + ;\ndelc 1;\nsol x1;")).isNone

/-- With the derived set emptied first it is allowed (§5.7.4), and `sol x1` solves the input.
CakePB allows the deletion and then rejects `SAT`, as it ignores the later solution. VeriPB
rejects the deletion: it checks a core deletion in this mode by RUP. -/
def tcbDeleteProof : String := tcbProof.replace
  "red 1 x2 >= 1 : x2 -> 1 : subproof\nqed;\nsol x1 x2;" "pol 1 x2 + ;\ndeld 2;\ndelc 1;\nsol x1;"

#guard (tcbDeleteProof.splitOn "delc 1;").length == 2
#guard checkOPB one tcbDeleteProof == some (.sat none)

/-! ### Bounds without a solution

`obji v` adds the improving constraint `f ≤ v - 1` without logging a solution (§5.8.2). It
lowers the value that the lower bounds are checked against to `v`, but certifies no upper bound,
and rules out `UNSAT`. VeriPB 3.0.2 and CakePB give the same verdicts as this checker on every
fixture below. -/

/-- On `cover`, `obji 1` asserts `f ≤ 0`, constraint `3`, which contradicts constraint `1` by
RUP. So every solution has value at least `1`, with no solution logged. -/
def objiProof : String := "pseudo-Boolean proof version 3.0
f 2;
obji 1;
rup >= 1 : 3 1;
output NONE;
conclusion BOUNDS 1 : 4 INF;
end pseudo-Boolean proof;
"

#guard checkOPB cover objiProof == some (.bounds (some 1) 4 none none)
-- `obji` certifies no upper bound.
#guard (checkOPB cover (objiProof.replace "4 INF" "4 1")).isNone
-- The lower bound may not exceed the asserted value.
#guard (checkOPB cover (objiProof.replace "BOUNDS 1" "BOUNDS 2")).isNone
-- After `obji`, a contradiction proves no unsatisfiability: the formula has solutions of value
-- at least `1`.
#guard (checkOPB cover
  (objiProof.replace "conclusion BOUNDS 1 : 4 INF;" "conclusion UNSAT : 4;")).isNone
-- With a logged solution of value `1` first, its improving constraint and that of `obji` are
-- constraints `3` and `4`, and the optimum `1` is certified.
#guard checkOPB cover ((objiProof.replace "obji 1;" "soli ~x1 x2 ~x3;\nobji 1;").replace
  "rup >= 1 : 3 1;\noutput NONE;\nconclusion BOUNDS 1 : 4 INF;"
  "rup >= 1 : 4 1;\noutput NONE;\nconclusion BOUNDS 1 : 5 1;") ==
  some (.bounds (some 1) 5 (some 1) none)
/-- `obji` needs an objective: on the decision problem `coverDecision`, this proof is rejected,
while it is accepted without `obji 1` (VeriPB and CakePB agree). -/
def objiDecision : String := "pseudo-Boolean proof version 3.0
f 2;
obji 1;
sol x2;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
"

#guard checkOPB coverDecision (objiDecision.replace "obji 1;\n" "") == some (.sat none)
#guard (checkOPB coverDecision objiDecision).isNone

/-! ### Stated assignments and `NONE`

A conclusion may state its solution (§4.3): `SAT : ρ` is accepted when `ρ` solves the input,
whatever was logged, and `BOUNDS lb : q ub : ρ` when `ρ` solves the input, assigns every
objective variable and has value `ub`. `NONE` claims nothing. VeriPB 3.0.2 and CakePB give the
same verdicts as this checker, except where noted. -/

/-- `objiProof` with its conclusion replaced. -/
def objiConcl (c : String) : String := objiProof.replace "BOUNDS 1 : 4 INF" c

-- The optimal solution `~x1 x2 ~x3`, stated, certifies the upper bound with nothing logged.
#guard checkOPB cover (objiConcl "BOUNDS 1 : 4 1 : ~x1 x2 ~x3") ==
  some (.bounds (some 1) 4 (some 1) (some [(0, false), (1, true), (2, false)]))
-- `x1 x2 ~x3` solves the input but has value `2`.
#guard (checkOPB cover (objiConcl "BOUNDS 1 : 4 1 : x1 x2 ~x3")).isNone
-- `x1 ~x2 ~x3` violates `x2 + x3 >= 1`.
#guard (checkOPB cover (objiConcl "BOUNDS 1 : 4 1 : x1 ~x2 ~x3")).isNone
-- `x2` leaves `x1` and `x3` unassigned (VeriPB rejects; CakePB sets them false and accepts).
#guard (checkOPB cover (objiConcl "BOUNDS 1 : 4 1 : x2")).isNone
-- After `INF` the assignment is not checked: `~x1 ~x2 ~x3` violates the input, yet the
-- conclusion is accepted with no finite upper bound (VeriPB and CakePB accept).
#guard checkOPB cover (objiConcl "BOUNDS 1 : 4 INF : ~x1 ~x2 ~x3") ==
  some (.bounds (some 1) 4 none (some [(0, false), (1, false), (2, false)]))
-- `NONE` claims nothing.
#guard checkOPB cover "pseudo-Boolean proof version 3.0
f 2;
obji 1;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
" == some .noClaim

/-- `SAT : ρ` for `x1 >= 1` with no step at all. -/
def satAsgProof : String := "pseudo-Boolean proof version 3.0
f 1;
output NONE;
conclusion SAT : x1;
end pseudo-Boolean proof;
"

#guard checkOPB one satAsgProof == some (.sat (some [(0, true)]))
-- A logged solution does not rescue a wrong stated one.
#guard (checkOPB one ((satAsgProof.replace "output" "sol x1;\noutput").replace
  "SAT : x1" "SAT : ~x1")).isNone
-- `x2` does not satisfy `x1 >= 1`.
#guard (checkOPB one (satAsgProof.replace "SAT : x1" "SAT : x2")).isNone
#guard checkOPB one (satAsgProof.replace "SAT : x1" "NONE") == some .noClaim
-- A step that fails is rejected even under `NONE`.
#guard (checkOPB one ((satAsgProof.replace "SAT : x1" "NONE").replace "output"
  "rup >= 1 : 1;\noutput")).isNone

/-! ### Objective updates

`obju new g` or `obju diff g` replaces the objective `f` by `g` or `f + g` (§5.9). Its goals
`#1`, the new objective at least the old, and `#2`, the old at least the new, must follow from the
core set alone. VeriPB 3.0.2 gives the same verdicts as this checker, except where noted; CakePB
parses `obju` only with a subproof. -/

/-- Minimize `x1 + x2 + x3` subject to `x1 = x2` and `x1 + x3 >= 1`; the optimum is `1`. -/
def eqOpt : String := "* #variable= 3 #constraint= 3
min: 1 x1 1 x2 1 x3 ;
1 x1 1 ~x2 >= 1 ;
1 ~x1 1 x2 >= 1 ;
1 x1 1 x3 >= 1 ;
"

/-- As `x1 = x2` in the core, the objective becomes `2 x1 + x3`; both goals are constraints of
the core, so they need no subproof. Then `~x1 ~x2 x3` of value `1` is logged, and its improving
constraint `4` contradicts constraint `3`. -/
def objuProof : String := "pseudo-Boolean proof version 3.0
f 3;
obju new 2 x1 1 x3 ;
soli ~x1 ~x2 x3;
rup >= 1 : 4 3;
output NONE;
conclusion BOUNDS 1 : 5 1;
end pseudo-Boolean proof;
"

#guard checkOPB eqOpt objuProof == some (.bounds (some 1) 5 (some 1) none)
-- The same update as a difference.
#guard checkOPB eqOpt (objuProof.replace "obju new 2 x1 1 x3" "obju diff 1 x1 -1 x2") ==
  some (.bounds (some 1) 5 (some 1) none)
-- With explicit `proofgoal` blocks: each negated goal takes a number (`4`, then `6`), and the
-- improving constraint is `8` (VeriPB and CakePB accept).
#guard checkOPB eqOpt (objuProof.replace "obju new 2 x1 1 x3 ;\nsoli ~x1 ~x2 x3;\nrup >= 1 : 4 3;"
  "obju new 2 x1 1 x3 : subproof\nproofgoal #1\npol 4 1 + ;\nqed : 5;\nproofgoal #2\n\
  pol 6 2 + ;\nqed : 7;\nqed obju;\nsoli ~x1 ~x2 x3;\nrup >= 1 : 8 3;" |>.replace
  "BOUNDS 1 : 5 1" "BOUNDS 1 : 9 1") == some (.bounds (some 1) 9 (some 1) none)
-- A solution logged before the update keeps the value it had then (VeriPB accepts); here the
-- value `1` is the same under both objectives, which `objuLoggedProof` below separates.
#guard checkOPB eqOpt (objuProof.replace "obju new 2 x1 1 x3 ;\nsoli ~x1 ~x2 x3;"
  "soli ~x1 ~x2 x3;\nobju new 2 x1 1 x3 ;") == some (.bounds (some 1) 5 (some 1) none)

/-- The solution `x1 x2 ~x3` of value `2` is logged; its improving constraint `4`,
`x1 + x2 + x3 <= 1`, joins the core, where `x1 = x2` then forces `x1 = x2 = 0` and `x3 = 1`. So the
objective becomes the constant `1`. The logged solution keeps its value `2`, which it no longer
has under the new objective. Constraint `9`, `2 >= 1` from constraint `3` and literal axioms, is
trivially true, hence weakly implies `f ≥ 1` for the constant objective `f = 1`. VeriPB and CakePB
accept this proof. -/
def objuLoggedProof : String := "pseudo-Boolean proof version 3.0
f 3;
soli x1 x2 ~x3;
obju new 1 : subproof
proofgoal #1
pol 5 4 + ;
qed : 6;
proofgoal #2
pol 7 3 + ;
qed : 8;
qed obju;
pol 3 ~x1 + ~x3 + ;
output NONE;
conclusion BOUNDS 1 : 9 2;
end pseudo-Boolean proof;
"

#guard checkOPB eqOpt objuLoggedProof == some (.bounds (some 1) 9 (some 2) none)
-- The upper bound is the value at logging, `2`, not `1` (VeriPB and CakePB reject).
#guard (checkOPB eqOpt (objuLoggedProof.replace "1 : 9 2" "1 : 9 1")).isNone
-- A stated assignment is valued under the input objective: `x1 x2 ~x3` has value `2` there,
-- though `1` under the final objective (VeriPB and CakePB agree).
#guard checkOPB eqOpt (objuLoggedProof.replace "1 : 9 2" "1 : 9 2 : x1 x2 ~x3") ==
  some (.bounds (some 1) 9 (some 2) (some [(0, true), (1, true), (2, false)]))
#guard (checkOPB eqOpt (objuLoggedProof.replace "1 : 9 2" "1 : 9 1 : x1 x2 ~x3")).isNone
-- `x1 + x3` is not the objective on the core: it drops `x2` (VeriPB rejects).
#guard (checkOPB eqOpt (objuProof.replace "2 x1 1 x3" "1 x1 1 x3")).isNone

/-- Minimize `x1` subject to `x1 >= 1` and `x2 >= 1`. -/
def twoOpt : String := "* #variable= 2 #constraint= 2
min: 1 x1 ;
1 x1 >= 1 ;
1 x2 >= 1 ;
"

/-- The goals of `obju new 1 x2`, `x2 + ~x1 >= 1` and `x1 + ~x2 >= 1`, are derived as `3` and
`4` and moved to the core, so they are constraints of the core. -/
def objuCoreProof : String := "pseudo-Boolean proof version 3.0
f 2;
pol 2 ~x1 + ;
pol 1 ~x2 + ;
core id 3 4;
obju new 1 x2 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkOPB twoOpt objuCoreProof == some .noClaim
-- Without `core id` the goals rest on derived constraints, which §5.9 forbids. VeriPB accepts
-- this proof: its autoproving checks the goals against the whole database.
#guard (checkOPB twoOpt (objuCoreProof.replace "core id 3 4;\n" "")).isNone
-- `obju` needs an objective.
#guard (checkOPB "* #variable= 2 #constraint= 2\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n"
  objuCoreProof).isNone
#guard (checkOPB "* #variable= 2 #constraint= 2\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n"
  (objuCoreProof.replace "obju new 1 x2 ;\n" "")).isSome

/-- An objective ends in an optional constant (§5.9, reusing the OPB syntax): as `x1 = 1` on the
core, `obju diff -1 x1 1` makes the objective the constant `1`. The improving constraint of the
solution `x1 x2` is then `0 >= 1`, constraint `3`. VeriPB accepts this proof. -/
def objuConstProof : String := "pseudo-Boolean proof version 3.0
f 2;
obju diff -1 x1 1 ;
soli x1 x2;
output NONE;
conclusion BOUNDS 1 : 3 1;
end pseudo-Boolean proof;
"

#guard checkOPB twoOpt objuConstProof == some (.bounds (some 1) 3 (some 1) none)
#guard checkOPB twoOpt (objuConstProof.replace "obju diff -1 x1 1" "obju new 1") ==
  some (.bounds (some 1) 3 (some 1) none)
-- Without the constant, the objective `0` is not `x1` on the core (VeriPB rejects).
#guard (checkOPB twoOpt (objuConstProof.replace "-1 x1 1 ;" "-1 x1 ;")).isNone
-- A constraint still needs its relation: a constant is no constraint (VeriPB and CakePB reject
-- the instance).
#guard (parseOPB "* #variable= 2 #constraint= 2\nmin: 1 x1 ;\n1 x1 1 ;\n1 x2 >= 1 ;\n").isNone
#guard (parseOPB "* #variable= 2 #constraint= 2\nmin: 1 x1 ;\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n").isSome
-- `min:` ends in an optional constant: `x1 + 5`, and `~x1 + 3`, that is `-x1 + 4`.
#guard (parseOPB "min: 1 x1 5 ;\n1 x1 >= 1 ;\n").map (·.objective) == some (some ⟨[(0, 1)], 5⟩)
#guard (parseOPB "min: 1 ~x1 3 ;\n1 x1 >= 1 ;\n").map (·.objective) == some (some ⟨[(0, -1)], 4⟩)
-- The constant shifts the optimum: minimizing `x1 + 5` under `x1 >= 1` gives `6` (VeriPB and
-- CakePB accept).
#guard checkOPB "* #variable= 2 #constraint= 2\nmin: 1 x1 5 ;\n1 x1 >= 1 ;\n1 x2 >= 1 ;\n"
  "pseudo-Boolean proof version 3.0
f 2;
soli x1 x2;
rup >= 1 : 3 1;
output NONE;
conclusion BOUNDS 6 : 4 6;
end pseudo-Boolean proof;
" == some (.bounds (some 6) 4 (some 6) none)

/-- Minimize `x1 + x2` subject to `x1 + x2 >= 1` and `~x2 >= 1`. -/
def cancelOpt : String := "* #variable= 2 #constraint= 2
min: 1 x1 1 x2 ;
1 x1 1 x2 >= 1 ;
1 ~x2 >= 1 ;
"

/-- `obju diff -1 x2` cancels `x2` from the objective, leaving `x1`. Once constraint `2` is
deleted, `soli x1` leaves `x2` unassigned, which only the old objective mentions. VeriPB accepts
this proof. -/
def cancelProof : String := "pseudo-Boolean proof version 3.0
f 2;
obju diff -1 x2 ;
delc 2;
soli x1;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkOPB cancelOpt cancelProof == some .noClaim
-- Under the old objective, `soli x1` leaves `x2` unassigned (VeriPB rejects).
#guard (checkOPB cancelOpt (cancelProof.replace "obju diff -1 x2 ;\n" "")).isNone

/-! ### Projected enumeration

`solx ρ` logs `ρ` and excludes every assignment that agrees with it on the preserved set
(§5.8.3); `ENUMERATION_PARTIAL n` and `ENUMERATION_COMPLETE n : q` claim at least, or exactly,
`n` distinct projections of solutions (§4.3). VeriPB 3.0.2 and CakePB give the same verdicts as
this checker, except where noted. -/

/-- `x1 + x2 >= 1`, preserving both variables: three solutions. -/
def enum3 : String := "* #variable= 2 #constraint= 1
preserved: x1 x2 ;
1 x1 1 x2 >= 1 ;
"

#guard (parseOPB enum3).map (·.preserved) == some (some [0, 1])

/-- The three solutions, then a contradiction from the three exclusions and the input: `5` is
`~x1`, `6` is `x1`. -/
def enumProof : String := "pseudo-Boolean proof version 3.0
f 1;
solx x1 x2;
solx x1 ~x2;
solx ~x1 x2;
pol 2 3 + 2 d ;
pol 1 4 + 2 d ;
pol 5 6 + ;
output NONE;
conclusion ENUMERATION_COMPLETE 3 : 7;
end pseudo-Boolean proof;
"

#guard checkOPB enum3 enumProof == some (.enumComplete 3 7)
-- Two of them, as a partial enumeration.
def enumPartialProof : String := "pseudo-Boolean proof version 3.0
f 1;
solx x1 x2;
solx ~x1 x2;
output NONE;
conclusion ENUMERATION_PARTIAL 2;
end pseudo-Boolean proof;
"

#guard checkOPB enum3 enumPartialProof == some (.enumPartial 2)
-- The count must match.
#guard (checkOPB enum3 (enumPartialProof.replace "PARTIAL 2" "PARTIAL 3")).isNone
-- Completeness needs a contradiction.
#guard (checkOPB enum3 (enumPartialProof.replace "ENUMERATION_PARTIAL 2"
  "ENUMERATION_COMPLETE 2 : 1")).isNone
-- A solution cannot be logged twice: its exclusion rules it out.
#guard (checkOPB enum3 (enumPartialProof.replace "solx ~x1 x2;" "solx x1 x2;")).isNone
-- Every preserved variable must be assigned (CakePB sets `x2` false and accepts).
#guard (checkOPB enum3 ((enumPartialProof.replace "solx ~x1 x2;\n" "").replace "solx x1 x2;"
  "solx x1;" |>.replace "PARTIAL 2" "PARTIAL 1")).isNone
-- Not after an unchecked deletion.
#guard (checkOPB enum3 ((enumPartialProof.replace "solx x1 x2;" "delc 1;").replace "PARTIAL 2"
  "PARTIAL 1")).isNone
-- A witness may not move a preserved variable.
#guard (checkOPB enum3 ((enumPartialProof.replace "solx x1 x2;"
  "red 1 ~x1 >= 1 : x1 -> 0 : subproof\nqed;").replace "PARTIAL 2" "PARTIAL 1")).isNone
-- Without a preserved set there is nothing to enumerate.
#guard (checkOPB "* #variable= 2 #constraint= 1\n1 x1 1 x2 >= 1 ;\n" enumPartialProof).isNone
-- A variable listed twice is preserved once: the exclusions stay normalized and the proof
-- still checks (VeriPB and CakePB accept).
#guard checkOPB (enum3.replace "preserved: x1 x2" "preserved: x1 x1 x2") enumProof ==
  some (.enumComplete 3 7)
-- An empty preserved set has one projection; the exclusion of `solx x1` is `0 >= 1`
-- (VeriPB and CakePB accept).
#guard checkOPB (enum3.replace "preserved: x1 x2" "preserved:") "pseudo-Boolean proof version 3.0
f 1;
solx x1;
output NONE;
conclusion ENUMERATION_COMPLETE 1 : 2;
end pseudo-Boolean proof;
" == some (.enumComplete 1 2)
#guard (parseOPB (enum3.replace "preserved: x1 x2" "preserved:")).map (·.preserved) ==
  some (some [])
/-- `solx x1 x2` with no conclusion. -/
def solxNone : String := "pseudo-Boolean proof version 3.0
f 1;
solx x1 x2;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkOPB enum3 solxNone == some .noClaim
-- `solx` is not allowed under an objective (VeriPB and CakePB reject).
#guard (checkOPB (enum3.replace "preserved:" "min: 1 x1 ;\npreserved:") solxNone).isNone
/-- A checked deletion whose witness moves a preserved variable. -/
def delcPresProof : String := "pseudo-Boolean proof version 3.0
f 1;
delc 1 : x1 -> 1 : subproof
qed delc;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

-- VeriPB and CakePB reject it with `x1` preserved, and accept it without a preserved set.
#guard (checkOPB enum3 delcPresProof).isNone
#guard checkOPB "* #variable= 2 #constraint= 1\n1 x1 1 x2 >= 1 ;\n" delcPresProof == some .noClaim

/-- `x4` is preserved but appears neither in the constraints nor in the proof. -/
def presOnly : String := "* #variable= 4 #constraint= 1
preserved: x1 x4 ;
1 x1 >= 1 ;
"

/-- A `red` step on the proof's own name `aux`. -/
def presOnlyProof : String := "pseudo-Boolean proof version 3.0
f 1;
red 1 aux >= 1 : aux -> 1 : subproof
qed;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

/-- The variable of the witness of a proof consisting of one `red` step. -/
def redVar : Option RedProof → Option ℕ
  | some ⟨[.red _ [(v, _)] _ _], _⟩ => some v
  | _ => none

-- The proof's names other than `xN` are numbered in order from the base, each at its last
-- occurrence: `version`, `red`, `aux`, …, as `pseudo-Boolean` and `proof` recur at the end. So
-- numbered after the constraints alone (base `1`), `aux` is variable `3`, that is the preserved
-- `x4`; numbered after the preserved set too (base `4`), it is `6`.
#guard redVar (parseProof 1 1 presOnlyProof) == some 3
#guard redVar (parseProof 1 4 presOnlyProof) == some 6
-- So the witness `aux -> 1` leaves the preserved set alone (VeriPB and CakePB accept).
#guard checkOPB presOnly presOnlyProof == some .noClaim

/-- `x1 + x2 + x3 >= 1`, preserving `x1` and `x2`. A witness that moves only the unpreserved `x3`
is allowed (VeriPB and CakePB accept). -/
def enum2 : String := "* #variable= 3 #constraint= 1
preserved: x1 x2 ;
1 x1 1 x2 1 x3 >= 1 ;
"

#guard checkOPB enum2 "pseudo-Boolean proof version 3.0
f 1;
red 1 x3 >= 1 : x3 -> 1 : subproof
qed;
solx ~x1 ~x2 x3;
output NONE;
conclusion ENUMERATION_PARTIAL 1;
end pseudo-Boolean proof;
" == some (.enumPartial 1)

/-! ### Output sections

`output g FILE;` checks the output formula, a separate OPB text, against the core set at the end
of the proof, and `output g IMPLICIT;` takes the core set itself (§4.2). The verdicts are
compared with VeriPB 3.0.2 and CakePB (CakeML commit `14856fcf`), run on the same texts; CakePB
supports only `FILE`, and this checker follows its `check_output` where the two tools differ. -/

-- All three tools accept, also with the terms of a constraint reordered.
#guard (checkOPBOutput amo3 amo3Proof amo3Out).map (·.2.map (·.guarantee)) ==
  some (some .equisatisfiable)
#guard (checkOPBOutput amo3 amo3Proof
  (amo3Out.replace "1 ~x1 1 ~x2 >= 1 ;" "1 ~x2 1 ~x1 >= 1 ;")).isSome
-- A missing or an extra constraint (the derived `6`), or no output text: all three reject.
#guard (checkOPBOutput amo3 amo3Proof (amo3Out.replace "1 ~x1 1 ~x2 1 ~x3 1 ~y1 >= 3 ;\n" ""))
  |>.isNone
#guard (checkOPBOutput amo3 amo3Proof (amo3Out ++ "1 ~x1 1 ~x2 1 ~x3 3 ~y1 >= 3 ;\n")).isNone
#guard (checkOPBOutput amo3 amo3Proof).isNone
-- `checkOPB` takes no output text.
#guard (checkOPB amo3 amo3Proof).isNone
-- `DERIVABLE` needs only the output in the core set (CakePB accepts; VeriPB asks for every core
-- constraint), not the converse.
#guard (checkOPBOutput amo3 (amo3Proof.replace "EQUISATISFIABLE" "DERIVABLE")
  (amo3Out.replace "1 ~x1 1 ~x2 1 ~x3 1 ~y1 >= 3 ;\n" "")).isSome
#guard (checkOPBOutput amo3 (amo3Proof.replace "EQUISATISFIABLE" "DERIVABLE")
  (amo3Out ++ "1 ~x1 1 ~x2 1 ~x3 3 ~y1 >= 3 ;\n")).isNone
-- `IMPLICIT` outputs the core set (VeriPB accepts; CakePB does not parse it); it takes no output
-- text (VeriPB ignores one).
#guard (checkOPBOutput amo3 (amo3Proof.replace "FILE" "IMPLICIT")).map
  (·.2.map (·.formula.constraints.length)) == some (some 6)
#guard (checkOPB amo3 (amo3Proof.replace "FILE" "IMPLICIT")) == some .noClaim
#guard (checkOPBOutput amo3 (amo3Proof.replace "FILE" "IMPLICIT") amo3Out).isNone
-- `EQUIOPTIMAL` needs an objective (all three reject), and `EQUIENUMERABLE` a preserved set
-- (CakePB rejects; VeriPB rejects as well, but for another reason: without `preserved:` it treats
-- every variable as preserved, and the `red` witnesses on `y1` move one).
#guard (checkOPBOutput amo3 (amo3Proof.replace "EQUISATISFIABLE" "EQUIOPTIMAL") amo3Out).isNone
#guard (checkOPBOutput amo3 (amo3Proof.replace "EQUISATISFIABLE" "EQUIENUMERABLE") amo3Out)
  |>.isNone
-- After the unchecked deletion of `1`, `EQUISATISFIABLE` is rejected and `DERIVABLE` accepted
-- (as by CakePB; VeriPB accepts both, reading `delc 1;` as a checked deletion it autoproves).
#guard (checkOPBOutput amo3 (amo3Proof.replace "output" "delc 1;\noutput")
  (amo3Out.replace "1 ~x1 1 ~x2 >= 1 ;\n" "")).isNone
#guard (checkOPBOutput amo3
  ((amo3Proof.replace "output" "delc 1;\noutput").replace "EQUISATISFIABLE" "DERIVABLE")
  (amo3Out.replace "1 ~x1 1 ~x2 >= 1 ;\n" "")).isSome
-- After a logged solution, neither (CakePB rejects; VeriPB accepts both).
#guard (checkOPBOutput amo3 (amo3Proof.replace "output" "sol ~x1 ~x2 ~x3 y1;\noutput") amo3Out)
  |>.isNone
#guard (checkOPBOutput amo3 ((amo3Proof.replace "output" "sol ~x1 ~x2 ~x3 y1;\noutput").replace
  "EQUISATISFIABLE" "DERIVABLE") amo3Out).isNone

-- All three tools accept, for values below the bound `2`, also with the objective written
-- `y1 + 2`, and the conclusion is checked as well.
#guard (checkOPBOutput amo3Opt amo3OptProof amo3OptOut).map
  (fun r => (r.1, r.2.map (·.bound))) == some (.bounds (some 2) 14 (some 2) none, some (some 2))
#guard (checkOPBOutput amo3Opt amo3OptProof
  (amo3OptOut.replace "1 y1 2 x1 2 ~x1" "1 y1 2")).isSome
-- Another objective constant, or an extra term: all three reject.
#guard (checkOPBOutput amo3Opt amo3OptProof
  (amo3OptOut.replace "1 y1 2 x1 2 ~x1" "1 y1 1")).isNone
#guard (checkOPBOutput amo3Opt amo3OptProof
  (amo3OptOut.replace "1 y1 2 x1 2 ~x1" "1 y1 2 x1")).isNone
-- `EQUISATISFIABLE` after a logged solution, or `EQUIENUMERABLE` without a preserved set: all
-- three reject (VeriPB rejects `EQUIENUMERABLE` after any logged solution).
#guard (checkOPBOutput amo3Opt (amo3OptProof.replace "EQUIOPTIMAL" "EQUISATISFIABLE")
  amo3OptOut).isNone
#guard (checkOPBOutput amo3Opt (amo3OptProof.replace "EQUIOPTIMAL" "EQUIENUMERABLE")
  amo3OptOut).isNone
-- Without the solution: `EQUIOPTIMAL` for every value (all three accept), and `EQUISATISFIABLE`
-- under an objective (CakePB accepts; VeriPB asks for a decision problem).
#guard (checkOPBOutput amo3Opt
  ((amo3OptProof.replace "soli x1 ~x2 ~x3 ~y1;\n" "").replace "BOUNDS 2 : 14 2" "NONE")
  (amo3OptOut.replace "1 ~y1 >= 2 ;\n" "")).map (·.2.map (·.bound)) == some (some none)
#guard (checkOPBOutput amo3Opt
  (((amo3OptProof.replace "soli x1 ~x2 ~x3 ~y1;\n" "").replace "BOUNDS 2 : 14 2" "NONE").replace
    "EQUIOPTIMAL" "EQUISATISFIABLE") (amo3OptOut.replace "1 ~y1 >= 2 ;\n" "")).isSome

/-- `amo3OptProof` with the output formula given by `IMPLICIT`, and no conclusion. -/
def amo3OptImplicit : String :=
  (amo3OptProof.replace "FILE" "IMPLICIT").replace "BOUNDS 2 : 14 2" "NONE"

#guard (checkOPBOutput amo3Opt amo3OptImplicit).map (·.2.map (·.bound)) == some (some (some 2))
-- `EQUIOPTIMAL` needs `bound` at most `dbound`. An `obji` below the logged value, or in place of
-- the logged solution, breaks it (CakePB rejects both, with the output formula given as a file;
-- VeriPB accepts both).
#guard (checkOPBOutput amo3Opt (amo3OptImplicit.replace "soli x1 ~x2 ~x3 ~y1;"
  "soli x1 ~x2 ~x3 ~y1;\nobji 1;")).isNone
#guard (checkOPBOutput amo3Opt (amo3OptImplicit.replace "soli x1 ~x2 ~x3 ~y1;" "obji 2;")).isNone

/-- `amo3Opt` preserving `x1`, `x2` and `x3`. -/
def amo3OptPres : String := amo3Opt.replace "min: 1 ~x1 1 ~x2 1 ~x3 ;"
  "min: 1 ~x1 1 ~x2 1 ~x3 ;\npreserved: x1 x2 x3 ;"

/-- `amo3OptImplicit` with an `EQUIENUMERABLE` output section. -/
def amo3OptEnum : String := amo3OptImplicit.replace "EQUIOPTIMAL" "EQUIENUMERABLE"

-- With the preserved set, `EQUIENUMERABLE` is accepted below the bound `2` (CakePB accepts with
-- the output formula as a file; VeriPB rejects after a logged solution), and the same proof with
-- only an `obji` below the logged value added is rejected, as then `bound` exceeds `dbound`
-- (CakePB rejects).
#guard (checkOPBOutput amo3OptPres amo3OptEnum).map (·.2.map (·.bound)) ==
  some (some (some 2))
#guard (checkOPBOutput amo3OptPres
  (amo3OptEnum.replace "soli x1 ~x2 ~x3 ~y1;" "soli x1 ~x2 ~x3 ~y1;\nobji 1;")).isNone

/-- `x1 + x2 + x3 >= 1`, preserving `x1` and `x2`. -/
def enumOut : String := "* #variable= 3 #constraint= 1
preserved: x1 x2 ;
1 x1 1 x2 1 x3 >= 1 ;
"

/-- `x3 >= 1` is added by `red` with a witness on the unpreserved `x3`, and the input constraint
is deleted by a checked deletion, so the output `x3 >= 1` has the same projections. -/
def enumOutProof : String := "pseudo-Boolean proof version 3.0
f 1;
red 1 x3 >= 1 : x3 -> 1 : subproof
qed;
core id 3;
delc 1 : : subproof
rup >= 1 : 4 3;
qed delc : 5;
output EQUIENUMERABLE FILE;
conclusion NONE;
end pseudo-Boolean proof;
"

-- All three tools accept, also with the preserved variables in another order.
#guard (checkOPBOutput enumOut enumOutProof "preserved: x1 x2 ;\n1 x3 >= 1 ;\n").isSome
#guard (checkOPBOutput enumOut enumOutProof "preserved: x2 x1 ;\n1 x3 >= 1 ;\n").isSome
#guard (checkOPBOutput enumOut (enumOutProof.replace "FILE" "IMPLICIT")).isSome
-- Another preserved set, or none: all three reject.
#guard (checkOPBOutput enumOut enumOutProof "preserved: x1 ;\n1 x3 >= 1 ;\n").isNone
#guard (checkOPBOutput enumOut enumOutProof "1 x3 >= 1 ;\n").isNone
-- The preserved variable `x12` appears only in `preserved:`, and the output formula preserves the
-- fresh `y1` instead: the names of the proof and the output are numbered after `x12`, so `y1` is
-- not `x12`, and all three reject. The same output with `x12` is accepted (VeriPB and CakePB
-- accept).
#guard (checkOPBOutput "preserved: x1 x12 ;\n1 x1 >= 1 ;\n" "pseudo-Boolean proof version 3.0
f 1;
output EQUIENUMERABLE FILE;
conclusion NONE;
end pseudo-Boolean proof;
" "preserved: x1 y1 ;\n1 x1 >= 1 ;\n").isNone
#guard (checkOPBOutput "preserved: x1 x12 ;\n1 x1 >= 1 ;\n" "pseudo-Boolean proof version 3.0
f 1;
output EQUIENUMERABLE FILE;
conclusion NONE;
end pseudo-Boolean proof;
" "preserved: x1 x12 ;\n1 x1 >= 1 ;\n").isSome
-- After `solx` the bound is `0`, and the guarantee is vacuous: CakePB accepts, VeriPB rejects.
#guard (checkOPBOutput enumOut (enumOutProof.replace "output" "solx x1 x2 x3;\noutput")
  "preserved: x1 x2 ;\n1 x3 >= 1 ;\n1 ~x1 1 ~x2 >= 1 ;\n").map (·.2.map (·.bound)) ==
  some (some (some 0))

/-! ### Soundness -/

-- The accepted optimality proof: every solution of `cover` has value at least `1`, and one has
-- value at most `1`, so the optimum is `1`.
example (h : checkOPB cover coverProof = some (.bounds (some 1) 6 (some 1) none)) :
    ∃ I f, parseOPB cover = some I ∧ I.objective = some f ∧
    (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) →
      ∃ l, some 1 = some l ∧ l ≤ f.eval σ) ∧
    ∀ u, some 1 = some u →
      ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ u :=
  bounds_of_checkOPB h

-- An accepted complete enumeration counts the projections of the solutions to the preserved set.
example (h : checkOPB enum3 enumProof = some (.enumComplete 3 7)) :
    ∃ I P, parseOPB enum3 = some I ∧ I.preserved = some P ∧
      (projections I.constraints P).encard = 3 :=
  encard_eq_of_checkOPB_enumComplete h

-- An accepted partial enumeration bounds that count from below.
example (h : checkOPB enum3 enumPartialProof = some (.enumPartial 2)) :
    ∃ I P, parseOPB enum3 = some I ∧ I.preserved = some P ∧
      (2 : ℕ∞) ≤ (projections I.constraints P).encard :=
  le_encard_of_checkOPB_enumPartial h

-- The output and `FILE` conclusion clients, with their acceptance decided in the kernel, are in
-- `CslibFrontierTests.Logics.Propositional.VeriPBTextDecide`.

-- An accepted pair of texts is an unsatisfiable formula.
example (h : checkDIMACS php43 php43Kernel = some (.unsat 39)) :
    ∃ φ, parseDIMACS php43 = some φ ∧ ¬ φ.Satisfiable :=
  not_satisfiable_of_checkDIMACS h

end CslibFrontierTests.Logics.Propositional.VeriPBText
