/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate
-- `import all`: the kernel evaluates the parsers and checkers of `Text` and the step `stepTop` of
-- `Redundance`, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text
-- `#guard` runs the elaborator and the kernel checker at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate

/-! Constraint labels `@l` (§5 of the VeriPB/CakePB documentation, 22 June 2026 edition), in
instances and in augmented proofs. Each verdict is that of VeriPB 3.0.2 (commit `f50be284`) on the
same texts; where an augmented proof is accepted, CakePB (CakeML `14856fcf`) accepts VeriPB's
elaboration of it.

* **Instances**, checked by the kernel. A constraint line carries no label or one label for each
  constraint it stands for, an equality two (`label_equality` and `input_equality_with_label` of
  VeriPB's tests, without their implications). The labels come with the numbers of their
  constraints, and they do not change the instance. One label on an equality, two on an
  inequality (`label_equality_too_few` and `label_inequality_too_many`), a label before `min:`
  and a bare `@` are rejected, as by VeriPB. CakePB accepts the first two, ignoring the labels.
* **Kernel proofs** for labelled instances are accepted, and a proof referring to a label is
  rejected by the kernel text front end, as by CakePB.
* **Augmented proofs**, elaborated by `Cslib.Logic.PL.VeriPB.Elab.checkAugmented` and run by
  `#guard`: references to the labels of the instance; a later label of the same name, in the
  instance or in the proof, takes precedence; VeriPB's test `def_order_labels`, where a label
  inside the transitivity proof of an order is local to it; and a label on a `red` step of a
  specification, used by a `proofgoal` of the next step, but not visible in the transitivity
  proof. The goal of a `proofgoal` is resolved before its subproof. After a step of the
  specification without a subproof, references to earlier steps, by number or by label, and to
  the constraints of the current step reach the right constraints.
-/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBLabels

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text Cslib.Logic.PL.VeriPB.Elab

/-! ### Instances -/

/-- `x1 + x2 = 1`, labelled `@both_lo` (`≥`) and `@both_hi` (`≤`), `x1 >= 1` and `x2 >= 1`:
unsatisfiable. -/
def eqOPB : String := "* #variable= 2 #constraint= 4
@both_lo @both_hi 1 x1 1 x2 = 1 ;
@one 1 x1 >= 1 ;
@two 1 x2 >= 1 ;
"

/-- `eqOPB` without its labels. -/
def eqPlain : String := "* #variable= 2 #constraint= 4
1 x1 1 x2 = 1 ;
1 x1 >= 1 ;
1 x2 >= 1 ;
"

-- The labels name the constraints `1` to `4`, an equality giving `≥` before `≤`.
example : (parseOPBLabelled (opbNames eqOPB) eqOPB).map (·.2) =
    some [("@both_lo", 1), ("@both_hi", 2), ("@one", 3), ("@two", 4)] := by
  decide +kernel

-- The labels do not change the instance.
example : parseOPB eqOPB = parseOPB eqPlain ∧ (parseOPB eqOPB).isSome := by decide +kernel

/-- VeriPB's test `input_equality_with_label`: labels with all the characters of a name. -/
def charsOPB : String := "* #variable= 3 #constraint= 4
@first^_-{[1]} 2 x1 +1 x2 +1 x3 >= 2 ;
@second^_-{[2]} -2 x1 -1 x2 -1 x3 >= -2 ;
@third^_-{[3]} -2 x1 -1 x2 -1 x3 >= -1 ;
@fourth^_-{[4]} 2 x1 1 x2 1 x3 >= 1 ;
"

example : (parseOPBLabelled (opbNames charsOPB) charsOPB).map (·.2) = some [("@first^_-{[1]}", 1),
    ("@second^_-{[2]}", 2), ("@third^_-{[3]}", 3), ("@fourth^_-{[4]}", 4)] := by
  decide +kernel

-- One label for the two constraints of an equality, two for one inequality, a label before
-- `min:` and a bare `@` are rejected.
example : parseOPB "@only_one 1 x1 1 x2 = 1 ;\n" = none := by decide +kernel
example : parseOPB "@one @two 1 x1 >= 1 ;\n" = none := by decide +kernel
example : parseOPB "@l min: 1 x1 ;\n1 x1 >= 0 ;\n" = none := by decide +kernel
example : parseOPB "@ 1 x1 >= 0 ;\n" = none := by decide +kernel

/-! ### Kernel proofs -/

/-- The kernel refutation of `eqOPB`: `~x1 + ~x2 >= 1` plus `x1 >= 1` plus `x2 >= 1`. -/
def eqKernel : String := "pseudo-Boolean proof version 3.0
f 4;
pol 2 3 + 4 + ;
output NONE;
conclusion UNSAT : 5;
end pseudo-Boolean proof;
"

theorem eqKernel_accepted : checkOPB eqOPB eqKernel = some (.unsat 5) := by decide +kernel

-- So the labelled instance `eqOPB` has no solution.
example : ∃ I, parseOPB eqOPB = some I ∧ ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ :=
  not_satisfiable_of_checkOPB eqKernel_accepted

/-- `eqKernel` with the label `@both_hi` for the constraint `2`. -/
def eqKernelLabel : String := "pseudo-Boolean proof version 3.0
f 4;
pol @both_hi 3 + 4 + ;
output NONE;
conclusion UNSAT : 5;
end pseudo-Boolean proof;
"

-- A label in a kernel proof is rejected, as by CakePB (VeriPB accepts it).
example : checkOPB eqOPB eqKernelLabel = none := by decide +kernel

/-! ### Augmented proofs -/

/-- The refutation of `eqOPB` through its labels, with a label of the proof for the
contradiction. -/
def eqAugmented : String := "pseudo-Boolean proof version 3.0
f 4;
@c pol @both_hi @one + @two + ;
output NONE;
conclusion UNSAT : @c;
end pseudo-Boolean proof;
"

#guard checkAugmented eqOPB eqAugmented == some (.unsat 5)
-- `@both_lo` is `x1 + x2 >= 1`, which does not refute.
#guard checkAugmented eqOPB (eqAugmented.replace "@both_hi" "@both_lo") == none
-- Without the labels of the instance, the proof is rejected.
#guard checkAugmented eqPlain eqAugmented == none

/-- VeriPB's test `input_equality_with_label`: each labelled constraint checked by `e`. -/
def charsProof : String := "pseudo-Boolean proof version 3.0
f 4;
e -2 x1 -1 x2 -1 x3 >= -2 : @second^_-{[2]};
e  2 x1 +1 x2 +1 x3 >= 2 : @first^_-{[1]};
e  2 x1  1 x2  1 x3 >= 1 : @fourth^_-{[4]};
e -2 x1 -1 x2 -1 x3 >= -1 : @third^_-{[3]};
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkAugmented charsOPB charsProof == some .noClaim
#guard checkAugmented charsOPB (charsProof.replace ": @second" ": @first") == none

/-- Two constraints with the same label `@a`. -/
def dupOPB : String := "* #variable= 2 #constraint= 2
@a 1 x1 >= 0 ;
@a 1 x2 >= 0 ;
"

/-- A proof with the steps `steps` and no conclusion, for an instance of `m` constraints. -/
def noClaim (m : ℕ) (steps : String) : String :=
  "pseudo-Boolean proof version 3.0\nf " ++ toString m ++ ";\n" ++ steps ++
    "output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n"

-- The later label of the instance takes precedence, and a label of the proof over both.
#guard checkAugmented dupOPB (noClaim 2 "e 1 x2 >= 0 : @a ;\n") == some .noClaim
#guard checkAugmented dupOPB (noClaim 2 "e 1 x1 >= 0 : @a ;\n") == none
#guard checkAugmented dupOPB (noClaim 2 "@a pol 1 ;\ne 1 x1 >= 0 : @a ;\n") == some .noClaim

/-! #### Labels inside `def_order` -/

/-- VeriPB's test `def_order_labels`, without its comments: the label `@x` of the transitivity
proof is local to it, so after the order `@x` names the last constraint labelled at top level,
`x9 >= 0`. -/
def defOrderLabels : String := "pseudo-Boolean proof version 3.0
f 0;
@x pol x1;
@x pol x2;
@x pol x3;
@x pol x4;
@x pol x5;
@x pol x6;
@x pol x7;
@x pol x8;
@x pol x9;
def_order lex3
    vars
        left u1 u2 u3;
        right v1 v2 v3;
        aux;
    end vars;

    def
        -1 u1 +1 v1 -2 u2 +2 v2 -4 u3 +4 v3 >= 0;
    end def;

    transitivity
        vars
            fresh_right w1 w2 w3;
        end vars;

        proof
            proofgoal #1
                @x pol 1 2 + 3 +;
            qed #1 : @x;
        qed proof;
    end transitivity;
end def_order;
e +1 x9 >= 0 : @x;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkAugmented "" defOrderLabels == some .noClaim
#guard checkAugmented "" (defOrderLabels.replace "e +1 x9" "e +1 x8") == none

/-- The order `u1 ≤ v1` through `$a1` of
`CslibFrontierTests.Logics.Propositional.VeriPBText.notAux`, the first step of its specification
labelled `@s1`, and the goal of `@s1` under the second step's witness, given as `goal`, proved
explicitly; the transitivity proof labels its contradiction `@x`, and the proof refers to its own
`@x` after the order. -/
def specLabels (goal : String) : String := "pseudo-Boolean proof version 3.0
f 1;
@x pol 1;
def_order notaux
vars
left u1;
right v1;
aux $a1;
end;
spec
@s1 red 1 $a1 1 u1 >= 1 : $a1 -> 1 : subproof
qed;
red 1 ~$a1 1 ~u1 >= 1 : $a1 -> 0 : subproof
proofgoal " ++ goal ++ "
rup >= 1 : -1 -2 ;
qed : -1;
qed;
end;
def
1 $a1 1 v1 >= 1;
end;
transitivity
vars
fresh_right w1;
fresh_aux_1 $b1;
fresh_aux_2 $c1;
end;
proof
proofgoal #1
@x pol 9 5 + 2 + 7 + 4 + 8 +;
qed : @x;
qed;
end;
reflexivity
proof
proofgoal #1
pol 11 13 +;
qed : 14;
qed;
end;
end;
e 1 x1 >= 0 : @x;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

/-- `x1 >= 0`. -/
def trivOPB : String := "* #variable= 1 #constraint= 1\n1 x1 >= 0 ;\n"

#guard checkAugmented trivOPB (specLabels "@s1") == some .noClaim
-- `@s1` is not a label of the transitivity proof.
#guard checkAugmented trivOPB ((specLabels "@s1").replace "qed : @x;\nqed;\nend;\nreflexivity"
  "qed : @s1;\nqed;\nend;\nreflexivity") == none

/-- `specLabels goal` with the subproof `body` of its `proofgoal`, closed by the label `@y`. -/
def specGoal (goal body : String) : String :=
  (specLabels goal).replace "rup >= 1 : -1 -2 ;\nqed : -1;" (body ++ "\nqed : @y;")

-- The goal of a `proofgoal` is resolved before its subproof, so a label `@s1` given again inside
-- the subproof does not change it, and a label first given there does not name it.
#guard checkAugmented trivOPB (specGoal "@s1" "@y rup >= 1 : -1 -2 ;") == some .noClaim
#guard checkAugmented trivOPB ((specGoal "@s1" "@s1 rup >= 1 : -1 -2 ;").replace "@y" "@s1") ==
  some .noClaim
#guard checkAugmented trivOPB ((specGoal "@u" "@u rup >= 1 : -1 -2 ;").replace "@y" "@u") == none

/-- `specGoal goal body` with a first step `@s1` of the specification without a subproof: its
negation takes a kernel number but no augmented one, so the augmented references of the
specification are sent to kernel numbers. -/
def specNoSub (goal body : String) : String :=
  (specGoal goal body).replace "1 u1 >= 1 : $a1 -> 1 : subproof\nqed;" "1 u1 >= 1 : $a1 -> 1 ;"

-- A labelled step referring to the first step by number or by label, and a `proofgoal` naming
-- the first step by number or by label; `1 -1 +` is not a contradiction.
#guard checkAugmented trivOPB (specNoSub "1" "@y pol 1 -2 + -1 2 * + ;") == some .noClaim
#guard checkAugmented trivOPB (specNoSub "@s1" "@y pol @s1 -2 + -1 2 * + ;") == some .noClaim
#guard checkAugmented trivOPB (specNoSub "1" "@y pol -2 -1 + ;") == some .noClaim
#guard checkAugmented trivOPB (specNoSub "@s1" "@y pol -2 -1 + ;") == some .noClaim
#guard checkAugmented trivOPB (specNoSub "1" "@y pol 1 -1 + ;") == none
-- Absolute references to the negation `2` of the second step and to the negated goal `3`.
#guard checkAugmented trivOPB (specNoSub "1" "@y rup >= 1 : 3 2 ;") == some .noClaim
#guard checkAugmented trivOPB (specNoSub "@s1" "@y pol 3 2 + ;") == some .noClaim
#guard checkAugmented trivOPB (specNoSub "1" "@y rup >= 1 : 3 ;") == none

end CslibFrontierTests.Logics.Propositional.VeriPBLabels
