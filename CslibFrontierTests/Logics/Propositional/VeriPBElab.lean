/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate
-- `#guard` runs the elaborator and the kernel checker at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate

/-! The elaborator from the augmented to the kernel VeriPB format
(`Cslib.Logic.PL.VeriPB.Elab.checkAugmented`) on small proofs, each also accepted by VeriPB 3.0.2
(commit `f50be284`), with the elaborated proof accepted by CakePB (CakeML commit `14856fcf`):

* PHP(3, 2) with hintless `rup`, a label, relative references, `ia`, `e`, `del spec`, levels
  (`setlvl`, `wiplvl`) and `conclusion UNSAT` without a constraint;
* the `pol` operations `n`, `c`, `m` and `-`, the cuts checked by `e`;
* a `red` step whose goal is autoproven by RUP, and `pbc` without a subproof;
* `red` steps whose goals are autoproven by syntactic implication: by `¬C`, by `D` for the goal
  `D|ω`, by another constraint, and, with the propagated assignment substituted, VeriPB's
  `autoproving` instance and a checked deletion whose goal `¬C` implies;
* `core range` and `del range`;
* a DIMACS formula with a hintless proof;
* the names of an instance, `x01` apart from `x1`, and the standard name `x1099511627777` next to
  an auxiliary name.

And rejections: a step that is not RUP, a wrong `e` check, a reference to a deleted constraint,
a premise that does not imply the `ia` constraint, goals that no constraint implies, and an
`ENUMERATION` count that is not a number. The checks run by `#guard`; the soundness
theorems (`Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_checkAugmented`, …) apply to any
accepted pair of texts. -/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBElab

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Elab

/-- PHP(3, 2): three pigeons `xᵢ` in two holes. -/
def php32 : String := "* #variable= 6 #constraint= 5
1 x1 1 x2 >= 1 ;
1 x3 1 x4 >= 1 ;
1 x5 1 x6 >= 1 ;
1 ~x1 1 ~x3 1 ~x5 >= 2 ;
1 ~x2 1 ~x4 1 ~x6 >= 2 ;
"

/-- An augmented proof of PHP(3, 2). The constraints derived at level `1` are wiped before the
final sum, which needs none of them. -/
def php32Proof : String := "pseudo-Boolean proof version 3.0
f 5;
setlvl 1;
rup 1 ~x1 1 ~x3 >= 1 ;
@a rup 1 x2 1 x4 >= 1 ;
ia 1 x2 1 x4 1 x6 >= 1 : @a ;
e 1 x2 1 x4 1 x6 >= 1 : -1 ;
del spec 1 x2 1 x4 1 x6 >= 1 ;
pol -2 -3 + ;
wiplvl 1;
pol 1 2 + 3 + 4 + 5 + ;
output NONE;
conclusion UNSAT;
end pseudo-Boolean proof;
"

-- The kernel proof is trimmed to the final sum, the constraint `6`.
#guard checkAugmented php32 php32Proof == some (.unsat 6)

-- A derived constraint that nothing uses is trimmed.
#guard (elaborate [] none none "pseudo-Boolean proof version 3.0\nrup >= 0 ;\noutput NONE;
conclusion NONE;\nend pseudo-Boolean proof;").toOption.map (·.proof.steps.length) == some 0

-- A step that is not RUP is rejected.
#guard (checkAugmented php32
  (php32Proof.replace "rup 1 ~x1 1 ~x3 >= 1" "rup 1 x1 1 x2 >= 2")).isNone
-- So is a wrong `e` check, and a premise that does not imply the `ia` constraint.
#guard (checkAugmented php32 (php32Proof.replace "1 x6 >= 1 : -1" "1 x6 >= 2 : -1")).isNone
#guard (checkAugmented php32 (php32Proof.replace "1 x6 >= 1 : @a" "1 x6 >= 1 : 1")).isNone
-- After `wiplvl 1`, the constraints of level `1` are gone.
#guard (checkAugmented php32 (php32Proof.replace "pol 1 2 + 3 + 4 + 5 +" "pol -1 1 +")).isNone

-- The count of an `ENUMERATION` conclusion must be a number.
#guard match elaborate [] none none "pseudo-Boolean proof version 3.0\noutput NONE;
conclusion ENUMERATION_PARTIAL x1 ;\nend pseudo-Boolean proof;" with
  | .ok _ => false
  | .error e => (e.splitOn "expected a number, found `x1`").length == 2

/-- A formula for the `pol` operations of the augmented format. -/
def cuts : String := "* #variable= 4 #constraint= 3
3 x1 2 x2 2 x3 1 x4 >= 4 ;
1 ~x1 1 ~x2 >= 1 ;
3 ~x1 2 x2 >= 3 ;
"

/-- Mixed-integer-rounding cuts `n` and `m`, division in variable form `c`, and `-`. -/
def cutsProof : String := "pseudo-Boolean proof version 3.0
f 3;
pol 1 3 n 2 + ;
e 1 x3 1 x4 >= 1 : -1 ;
pol 3 2 c ;
e 1 ~x1 1 x2 >= 1 : -1 ;
pol 3 2 d ;
e 2 ~x1 1 x2 >= 2 : -1 ;
pol 1 x4 w 1 - ;
e 3 x1 2 x2 2 x3 >= 2 : -1 ;
pol 1 3 m ;
e 1 x1 1 x2 1 x3 1 x4 >= 2 : -1 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkAugmented cuts cutsProof == some .noClaim
#guard (checkAugmented cuts (cutsProof.replace "1 x3 1 x4 >= 1 : -1" "1 x3 1 x4 >= 2 : -1")).isNone

/-- `red` with its goal autoproven by RUP, `pbc` without a subproof, `core range` and
`del range`. -/
def redProof : String := "pseudo-Boolean proof version 3.0
f 5;
red 1 ~x1 1 ~x2 >= 1 : x1 -> 0 ;
pbc 1 ~x1 1 ~x2 >= 1 ;
core range 6 8 ;
del range 6 8 ;
pol 1 2 + 3 + 4 + 5 + ;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
"

#guard checkAugmented php32 redProof == some (.unsat 11)

/-! Goals autoproven by syntactic implication (§5.5.2), as VeriPB 3.0.2 autoproves them
(`Proofgoal::autoprove`): by the additional premise `¬C`, by `D` for the goal `D|ω`, by another
constraint of the database, and by a constraint of the database once the assignment propagated at
the root is substituted. None of these goals follows by RUP, and the kernel format autoproves
none of them. Each rejected variant is rejected by VeriPB too. -/

/-- A red step without a subproof. -/
def redOnly (f : ℕ) (red : String) : String := s!"pseudo-Boolean proof version 3.0
f {f};
{red}
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

/-- The goal `D|ω` of the first constraint is `y₁ + ⋯ + y₅ ≥ 2`, which the second implies. -/
def implOther : String := "* #variable= 6 #constraint= 2
1 x1 1 y1 1 y2 1 y3 1 y4 1 y5 >= 2 ;
1 y1 1 y2 1 y3 1 y4 >= 2 ;
"

#guard checkAugmented implOther (redOnly 2 "red 1 ~x1 >= 1 : x1 -> 0 ;") == some .noClaim
-- With `y₆` in the second constraint, nothing implies the goal.
#guard checkAugmented (implOther.replace "1 y4 >= 2" "1 y4 1 y6 >= 2")
  (redOnly 2 "red 1 ~x1 >= 1 : x1 -> 0 ;") == none

/-- The goal `D|ω` is `2 y₁ + y₂ + ⋯ + y₅ ≥ 2`, which `¬C` implies by saturation, but not
weakly. -/
def implPremise : String := "* #variable= 7 #constraint= 1
1 x2 2 y1 1 y2 1 y3 1 y4 1 y5 >= 2 ;
"

#guard checkAugmented implPremise
  (redOnly 1 "red 5 ~y1 1 ~y2 1 ~y3 1 ~y5 7 ~x1 7 ~x2 >= 7 : x2 -> 0 ;") == some .noClaim
#guard checkAugmented implPremise
  (redOnly 1 "red 3 ~y1 1 ~y2 1 ~y3 1 ~y5 7 ~x1 7 ~x2 >= 7 : x2 -> 0 ;") == none

/-- With `x₁ ↦ ¬y₁`, the goal `D|ω` is `3 y₁ + y₂ + y₃ + y₅ ≥ 2`, which `D` implies by saturation,
but not weakly. -/
def implSelf : String := "* #variable= 7 #constraint= 1
2 x1 5 y1 1 y2 1 y3 1 y5 >= 4 ;
"

#guard checkAugmented implSelf (redOnly 1 "red 1 z1 >= 1 : z1 -> 1 x1 -> ~y1 ;") == some .noClaim
-- With `x₁ ↦ y₂`, the goal `5 y₁ + 3 y₂ + y₃ + y₅ ≥ 4` is not implied.
#guard checkAugmented implSelf (redOnly 1 "red 1 z1 >= 1 : z1 -> 1 x1 -> y2 ;") == none

/-- VeriPB's instance `tests/instances/correct/version3/autoproving.opb`: `¬C` propagates
`a₃ = a₄ = 0`, and with these values substituted the first constraint implies its goal
`a₁ + a₂ + x₁ + ⋯ + x₄ ≥ 3`. -/
def implSubst : String := "* #variable= 2 #constraint= 10
1 a1 1 a2 1 a3 1 x1 1 x2 1 x3 1 x4 >= 3 ;
1 a1 1 z1 1 z2 >= 1 ;
1 z1 1 z2 1 z3 >= 1 ;
1 z1 1 z2 1 ~z3 >= 1 ;
1 a1 1 y1 1 y2 1 y3 1 y4 1 y5 >= 3 ;
1 a2 1 y1 1 y2 1 y3 1 y4 1 y5 >= 3 ;
"

/-- VeriPB's proof `autoproving.pbp`. -/
def implSubstProof : String := "pseudo-Boolean proof version 3.0
red 1 a3 1 a4 >= 1 : a1 a2 a2 a1 a3 0 a4 1;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard checkAugmented implSubst implSubstProof == some .noClaim
-- The unit `¬a₃`, the propagated value on the variables of the constraint and the goal, is
-- derived by a hinted `rup` before the implication.
#guard match elaborate (((Text.parseOPB implSubst).map (·.constraints)).getD []) none none
    implSubstProof (Text.opbNames implSubst) with
  | .ok ⟨⟨[.red _ _ (some items) _], _⟩, _, N⟩ =>
    items.any fun
      | .goal _ (.rup c _ :: _) _ => c.degree == 1 &&
        c.terms.map (fun t => (N.name (PBConstr.termVar t), PBConstr.termPos t)) == [("a3", false)]
      | _ => false
  | _ => false
-- With `¬a₄` in place of `a₃`, the substituted constraint `a₁ + a₂ + x₁ + ⋯ + x₄ ≥ 2` is too
-- weak.
#guard checkAugmented (implSubst.replace "1 a2 1 a3 1 x1" "1 a2 1 ~a4 1 x1") implSubstProof ==
  none

/-- The goal `C₃|ω` of a checked deletion of the first constraint with `x₁ ↦ 1` is
`y₁ + ⋯ + y₄ ≥ 2`. `C₂` and `¬C₁` propagate `a₁ = x₁ = 0`, and with these values substituted
`¬C₁` becomes `y₁ + y₂ + y₃ ≥ 2`, which implies the goal. -/
def implCore : String := "* #variable= 6 #constraint= 3
3 x1 1 ~a1 1 ~y1 1 ~y2 1 ~y3 >= 3 ;
1 ~a1 >= 1 ;
1 ~x1 1 y1 1 y2 1 y3 1 y4 >= 2 ;
"

/-- A checked deletion of the first constraint with `x₁ ↦ 1`, ending with `e`. -/
def delcX1 (e : String) : String := s!"pseudo-Boolean proof version 3.0
f 3;
delc 1 : x1 -> 1 {e}
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

-- In a core-only subproof, `¬C₁` is a core constraint (VeriPB 3.0.2, `checker.rs`), so it is a
-- candidate.
#guard checkAugmented implCore (delcX1 ": subproof qed;") == some .noClaim
-- Without a subproof, `¬C₁` is not in VeriPB's database and is no candidate (VeriPB 3.0.2
-- rejects it with `--force-checked-deletion`, and otherwise falls back to unchecked deletion).
#guard checkAugmented implCore (delcX1 ";") == none

/-- A DIMACS formula, PHP(3, 2) as clauses, with a hintless proof that deletes by
specification. -/
def php32cnf : String := "p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
"

/-- A resolution-style proof of PHP(3, 2), as a CDCL solver would log it. -/
def php32cnfProof : String := "pseudo-Boolean proof version 3.0
f 9;
rup 1 ~x1 >= 1 ;
rup 1 ~x3 >= 1 ;
del spec 1 ~x1 1 ~x3 >= 1 ;
rup >= 1 ;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
"

#guard checkAugmentedDIMACS php32cnf php32cnfProof == some (.unsat 12)

/-! Names are read with the names of the instance (`Cslib.Logic.PL.VeriPB.Text.opbNames`). A
standard name from the base of the instance on, here `x1099511627777` for an instance without
variables, is a name of the proof like `$a`: both are new variables, numbered in order of first
appearance, and each prints as its own name. -/

/-- A proof with the standard name `x1099511627777` and the auxiliary name `$a`. -/
def bigNameProof : String := "pseudo-Boolean proof version 3.0
red 1 x1099511627777 1 $a >= 1 : $a -> 1 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

#guard match elaborate [] none none bigNameProof with
  | .ok r =>
    r.names == ⟨["x1099511627777", "$a"], 0⟩ &&
      (match r.proof.steps with
        | [.red c _ _ _] => c.terms.map fun t => r.names.name (PBConstr.termVar t)
        | _ => []) == ["x1099511627777", "$a"]
  | .error _ => false

/-- An instance with names of its own. -/
def named : String := "* #variable= 2 #constraint= 1
1 ab 1 cd >= 1 ;
"

-- The names of the proof are those of the instance.
#guard checkAugmented named "pseudo-Boolean proof version 3.0
f 1;
rup 1 cd 1 ab >= 1 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
" == some .noClaim

/-- An instance over the variable `x1`. -/
def x1Only : String := "* #variable= 1 #constraint= 1
1 x1 >= 1 ;
"

-- `x01` is not `x1`, as in VeriPB: it is a new variable, so `rup 1 x01 >= 1` is not RUP.
#guard checkAugmented x1Only "pseudo-Boolean proof version 3.0
f 1;
rup 1 x01 >= 1 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
" == none

#guard checkAugmented x1Only "pseudo-Boolean proof version 3.0
f 1;
rup 1 x1 >= 1 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
" == some .noClaim

/-- An instance over the variable `2 ^ 40`, which it sets to `1`. -/
def bigName : String := "* #variable= 1 #constraint= 1
1 x1099511627777 >= 1 ;
"

-- Setting `$a` to `0` by redundance is sound only if `$a` is not the variable of the instance.
#guard checkAugmented bigName "pseudo-Boolean proof version 3.0
f 1;
red 1 ~$a >= 1 : $a -> 0 ;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
" == some .noClaim

end CslibFrontierTests.Logics.Propositional.VeriPBElab
