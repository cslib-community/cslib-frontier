/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Init

/-! Output-section fixtures from the VeriPB repository (MIT/Apache-2.0), shared by the `#guard`
tests of `CslibFrontierTests.Logics.Propositional.VeriPBText` and the decided clients of
`CslibFrontierTests.Logics.Propositional.VeriPBTextDecide`. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBText

/-- The test instance `decision_output` of the VeriPB repository (MIT/Apache-2.0): three
pairwise at-most-one clauses. -/
def amo3 : String := "* #variable= 3 #constraint= 3
1 ~x1 1 ~x2 >= 1 ;
1 ~x1 1 ~x3 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
"

/-- Its proof, elaborated by VeriPB: the cardinality constraint `4`, a fresh variable `y1` defined
by the `red` steps `6` and `8`, and the constraint `9`; the core set is `1`–`4`, `8` and `9`. -/
def amo3Proof : String := "pseudo-Boolean proof version 3.0
f 3;
pol 1 2 + 3 + 2 d;
core id 4;
red 1 ~x1 1 ~x2 1 ~x3 3 ~y1 >= 3 : y1 -> 0 : subproof
qed;
red 1 x1 1 x2 1 x3 1 y1 >= 1 : y1 -> 1 : subproof
qed;
core id 8;
pol 4 2 * 6 + 3 d;
core id 9;
output EQUISATISFIABLE FILE;
conclusion NONE;
end pseudo-Boolean proof;
"

/-- The output formula of `decision_output`: the core set, in another order. -/
def amo3Out : String := "* #variable= 4 #constraint= 7
1 ~x1 1 ~x2 >= 1 ;
1 ~x1 1 ~x3 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
1 ~x1 1 ~x2 1 ~x3 >= 2 ;
1 x1 1 x2 1 x3 1 y1 >= 1 ;
1 ~x1 1 ~x2 1 ~x3 1 ~y1 >= 3 ;
"

/-- The test instance `optimization_output_opposing_lits_objective` of the VeriPB repository:
`amo3`, maximizing the number of true variables. -/
def amo3Opt : String := "* #variable= 3 #constraint= 3
min: 1 ~x1 1 ~x2 1 ~x3 ;
1 ~x1 1 ~x2 >= 1 ;
1 ~x1 1 ~x3 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
"

/-- Its proof, elaborated by VeriPB: the objective becomes `y1 + 2` (`obju`), and the optimal
solution, of value `2`, is logged; the improving constraint `14` is `~y1 >= 2`. -/
def amo3OptProof : String := "pseudo-Boolean proof version 3.0
f 3;
pol 1 2 + 3 + 2 d;
core id 4;
red 1 ~x1 1 ~x2 1 ~x3 3 ~y1 >= 3 : y1 -> 0 : subproof
qed;
red 1 x1 1 x2 1 x3 1 y1 >= 1 : y1 -> 1 : subproof
qed;
core id 8;
pol 4 2 * 6 + 3 d;
core id 9;
obju new 1 y1 2 : subproof
  proofgoal #1
    pol 10 8 + ;
  qed : 11;
  proofgoal #2
    pol 12 9 + ;
  qed : 13;
qed;
soli x1 ~x2 ~x3 ~y1;
output EQUIOPTIMAL FILE;
conclusion BOUNDS 2 : 14 2;
end pseudo-Boolean proof;
"

/-- The output formula, with the objective `y1 + 2x1 + 2~x1`, that is `y1 + 2`. -/
def amo3OptOut : String := "* #variable= 4 #constraint= 8
min: 1 y1 2 x1 2 ~x1 ;
1 ~x1 1 ~x2 >= 1 ;
1 ~x1 1 ~x3 >= 1 ;
1 ~x2 1 ~x3 >= 1 ;
1 ~x1 1 ~x2 1 ~x3 >= 2 ;
1 x1 1 x2 1 x3 1 y1 >= 1 ;
1 ~x1 1 ~x2 1 ~x3 1 ~y1 >= 3 ;
1 ~y1 >= 2 ;
"

end CslibFrontierTests.Logics.Propositional.VeriPBText

end
