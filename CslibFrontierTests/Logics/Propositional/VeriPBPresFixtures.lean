/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Init

/-! Fixtures for changing the preserved set (§5.10 of the VeriPB/CakePB documentation, 22 June
2026 edition) in the VeriPB checker, adapted from the test instances `add_preserved_var_subproof`
and `remove_preserved_var_subproof` of the VeriPB repository (VeriPB 3.0.2, commit `f50be284`,
MIT/Apache-2.0). They are shared by the `#guard` tests of
`CslibFrontierTests.Logics.Propositional.VeriPBText` and the decided client of
`CslibFrontierTests.Logics.Propositional.VeriPBTextDecide`. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBText

/-- Four constraints over `x1` … `x4`, preserving `x1` and `x3`. -/
def pres4 : String := "* #variable= 5 #constraint= 4
preserved: x1 x3 ;
1 x1 +1 x2 >= 1 ;
1 x2 +1 x3 >= 1 ;
1 x1 +1 x3 +1 x4 >= 1 ;
1 x1 +1 x3 -1 x4 >= 0 ;
"

/-- The same constraints with `x5 ⇔ x1` (`5`, `6`), preserving `x1`, `x3` and `x5`. -/
def pres4Rm : String := "* #variable= 5 #constraint= 6
preserved: x1 x3 x5 ;
1 x1 +1 x2 >= 1 ;
1 x2 +1 x3 >= 1 ;
1 x1 +1 x3 +1 x4 >= 1 ;
1 x1 +1 x3 -1 x4 >= 0 ;
1 ~x5 1 x1 >= 1 ;
1 x5 1 ~x1 >= 1 ;
"

/-- A proof for a formula of `m` constraints taking the steps `steps`, with no conclusion. -/
def presProof (m : ℕ) (steps : String) : String :=
  "pseudo-Boolean proof version 3.0\nf " ++ toString m ++ ";\n" ++ steps ++
    "output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n"

/-- For `pres4`: define `x5 ⇔ x1` by two `red` steps on `x5`, moved to the core set as `6` and
`8`. -/
def defX5 : String := "red 1 x1 1 ~x5 >= 1 : x5 -> 0 : subproof
qed;
core id 6;
red 1 ~x1 1 x5 >= 1 : x5 -> 1 : subproof
qed;
core id 8;
"

/-- `preserved_add x5 : x1 >= 1` after `defX5`: goal `#1`, `x5 ⇒ x1`, negated as `9`, and goal
`#2`, `x5 ⇐ x1`, negated as `11`, refuted with the core constraints `6` and `8`. -/
def addX5 : String := "preserved_add x5 : 1 x1 >= 1 : subproof
proofgoal #1
pol 9 6 +;
qed : 10;
proofgoal #2
pol 11 8 +;
qed : 12;
qed;
"

/-- For `pres4Rm`: `preserved_rm x5 : x1 >= 1`, goal `#1`, `x5 ⇒ x1`, negated as `7`, and goal
`#2`, `x5 ⇐ x1`, negated as `9`, refuted with the input constraints `5` and `6`. -/
def rmX5 : String := "preserved_rm x5 : 1 x1 >= 1 : subproof
proofgoal #1
pol 7 5 +;
qed : 8;
proofgoal #2
pol 9 6 +;
qed : 10;
qed;
"

/-- `red x5 + ~x1 >= 1 : x5 -> x1`, whose witness moves `x5`: it maps the constraint and both
definitions of `x5 ⇔ x1` to trivially true ones, so it is accepted exactly when `x5` is not
preserved. -/
def moveX5 : String := "red 1 x5 1 ~x1 >= 1 : x5 -> x1 : subproof
qed;
"

/-- For `pres4Rm`: log the solution `x1 ~x2 x3 x4 x5`, excluding its projection by `7`, then
remove `x5` by `preserved_rm x5 : x1 >= 1`, whose goals are refuted with `5` and `6`; the one
logged projection gives `ENUMERATION_PARTIAL 1`. VeriPB and CakePB accept. -/
def enumAfterRm : String := "pseudo-Boolean proof version 3.0
f 6;
solx x1 ~x2 x3 x4 x5;
preserved_rm x5 : 1 x1 >= 1 : subproof
proofgoal #1
pol 8 5 +;
qed : 9;
proofgoal #2
pol 10 6 +;
qed : 11;
qed;
output NONE;
conclusion ENUMERATION_PARTIAL 1;
end pseudo-Boolean proof;
"

/-- An `EQUIENUMERABLE` output of `pres4Rm` itself, after the steps `steps`. -/
def presEnumOut (steps : String) : String :=
  "pseudo-Boolean proof version 3.0\nf 6;\n" ++ steps ++
    "output EQUIENUMERABLE FILE;\nconclusion NONE;\nend pseudo-Boolean proof;\n"

/-- For `pres4Rm`, after `rmX5`: `preserved_add x5 : x1 >= 1` adds `x5` back, its goals negated
as `11` and `13` and refuted with `5` and `6`. -/
def readdX5 : String := "preserved_add x5 : 1 x1 >= 1 : subproof
proofgoal #1
pol 11 5 +;
qed : 12;
proofgoal #2
pol 13 6 +;
qed : 14;
qed;
"

/-- For `pres4Rm`, after `rmX5`: delete the definition `5`, `6` of `x5` by checked deletions with
witnesses on `x5`, which is no longer preserved, numbered `11` and `12`. -/
def freeX5 : String := "delc 5 : x5 -> x1 : subproof
qed delc;
delc 6 : x5 -> 1 : subproof
qed delc;
"

/-- The core set after `rmX5` and `freeX5`: the first four constraints, preserving `x1` and
`x3`. -/
def pres4Free : String := "* #variable= 5 #constraint= 4
preserved: x1 x3 ;
1 x1 +1 x2 >= 1 ;
1 x2 +1 x3 >= 1 ;
1 x1 +1 x3 +1 x4 >= 1 ;
1 x1 +1 x3 -1 x4 >= 0 ;
"

/-- `pres4Free` still preserving `x5`, which no constraint mentions any more. -/
def pres4FreeX5 : String := "* #variable= 5 #constraint= 4
preserved: x1 x3 x5 ;
1 x1 +1 x2 >= 1 ;
1 x2 +1 x3 >= 1 ;
1 x1 +1 x3 +1 x4 >= 1 ;
1 x1 +1 x3 -1 x4 >= 0 ;
"

/-- For `pres4Rm`, after `rmX5`: `freeX5`, then define `x5 ⇔ ~x1` by two `red` steps on `x5`,
moved to the core set as `14` and `16` (the goal of `14` under the second witness follows from the
negated constraint `15`), and add `x5` back by `preserved_add x5 : ~x1 >= 1`, its goals negated as
`17` and `19` and refuted with `14` and `16`. -/
def flipX5 : String := freeX5 ++ "red 1 ~x5 1 ~x1 >= 1 : x5 -> 0 : subproof
qed;
core id 14;
red 1 x5 1 x1 >= 1 : x5 -> 1 : subproof
qed;
core id 16;
preserved_add x5 : 1 ~x1 >= 1 : subproof
proofgoal #1
pol 17 14 +;
qed : 18;
proofgoal #2
pol 19 16 +;
qed : 20;
qed;
epreserved x1 x3 x5;
"

/-- The core set after `rmX5` and `flipX5`: the first four constraints and `x5 ⇔ ~x1`,
preserving `x1`, `x3` and `x5`. -/
def pres4Flip : String := "* #variable= 5 #constraint= 6
preserved: x1 x3 x5 ;
1 x1 +1 x2 >= 1 ;
1 x2 +1 x3 >= 1 ;
1 x1 +1 x3 +1 x4 >= 1 ;
1 x1 +1 x3 -1 x4 >= 0 ;
1 ~x5 1 ~x1 >= 1 ;
1 x5 1 x1 >= 1 ;
"

end CslibFrontierTests.Logics.Propositional.VeriPBText
