/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate
import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Spec
-- `#guard` runs the elaborator and the kernel checker at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate

/-! The declarative semantics of the clausal and `pol` fragment of the augmented VeriPB format
(`Cslib.Logic.PL.VeriPB.Elab.AugValid`) and the elaborator's `ea` rule.

* A hintless `rup` of the empty clause from `x₁` and `¬x₁`, concluding `UNSAT`, is valid; a proof
  of `UNSAT` without rules for the satisfiable formula `x₁` is not, by the soundness of the spec
  (`Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_augValid`).
* The elaborator accepts `ea C : j` when the constraint `j` is `C`, and rejects it otherwise.
* A proof whose text ends inside a rule without effect (`start_time` with no `;`) is rejected; the
  parser used to loop forever on it. -/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBAugValid

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Elab

/-- The unsatisfiable formula `x₁`, `¬x₁`. -/
def contra : List PBConstr := [⟨[(1, (0, true))], 1⟩, ⟨[(1, (0, false))], 1⟩]

/-- `f 2; rup >= 1; output NONE; conclusion UNSAT;`. -/
def contraProof : AProof := ⟨some 2, [.rup ⟨[], 1⟩ none], none, .unsat none⟩

/-- The proof is valid: propagating `x₁` and then `¬x₁` meets a conflict. -/
example : AugValid contra none none contraProof .unsat :=
  ⟨rfl, rfl, _,
    .cons (.rup [.id 1, .id 2] trivial (fun h _ => by cases h <;> trivial) (by decide)) .nil,
    .unsat (j := 3) trivial (by decide)⟩

/-- A proof of `UNSAT` without rules is not valid for the satisfiable formula `x₁`. -/
example : ¬ AugValid [⟨[(1, (0, true))], 1⟩] none none ⟨none, [], none, .unsat none⟩ .unsat :=
  fun h => not_satisfiable_of_augValid h (fun _ => true) (by decide)

/-- `x1`, `-x1` in DIMACS. -/
def contraCNF : String := "p cnf 1 2
1 0
-1 0
"

#guard (checkAugmentedDIMACS contraCNF "pseudo-Boolean proof version 3.0
f 2;
ea 1 x1 >= 1 : 1;
pol 3 2 +;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
").any (· matches .unsat _)

#guard (checkAugmentedDIMACS contraCNF "pseudo-Boolean proof version 3.0
f 2;
ea 1 ~x1 >= 1 : 1;
pol 3 2 +;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
").isNone

#guard (checkAugmentedDIMACS contraCNF "pseudo-Boolean proof version 3.0
f 2;
start_time").isNone

end CslibFrontierTests.Logics.Propositional.VeriPBAugValid
