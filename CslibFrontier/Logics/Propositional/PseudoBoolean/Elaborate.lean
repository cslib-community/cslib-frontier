/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Core
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-!
# Checking augmented VeriPB proofs by elaboration

The end-to-end checker for proofs in the augmented format of VeriPB [Bogaerts, Gocht, McCreesh
and Nordström][BogaertsGochtMcCreeshNordstrom2023], version 3.0: parse the instance with the
text front end (`Cslib.Logic.PL.VeriPB.Text.parseOPB`, `Cslib.Logic.PL.VeriPB.Text.parseDIMACS`),
elaborate the proof into a kernel proof (`Cslib.Logic.PL.VeriPB.Elab.elaborate`), and check the
kernel proof (`Cslib.Logic.PL.VeriPB.checkRed`). This is how CakePB is meant to be used, with the
elaborator of the VeriPB tool in front of it (§5 and §6.1 of the VeriPB/CakePB documentation,
22 June 2026 edition).

**What the guarantee rests on.** The elaborator and its proof parser are untrusted and unverified:
they appear in the soundness theorems only under an existential, as the producer of *some* kernel
proof (`Cslib.Logic.PL.VeriPB.Elab.exists_checkRed_of_checkAugmented`). So an accepted proof
gives exactly what the kernel checker gives for the parsed instance: `UNSAT` means the instance
has no 0/1 solution (`Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_checkAugmented`), and the
other conclusions follow from the kernel checker's theorems
(`Cslib.Logic.PL.VeriPB.exists_satisfies_of_checkRed`,
`Cslib.Logic.PL.VeriPB.le_eval_of_checkRed`, `Cslib.Logic.PL.VeriPB.exists_eval_le_of_checkRed`,
…). The trusted parts are the instance parser and the kernel checker, as for
`Cslib.Logic.PL.VeriPB.Text.checkOPB`.

**Completeness** is not proved: the elaborator may fail on a valid proof (its limitations are
listed in `Cslib.Logic.PL.VeriPB.Elab`), and then the checker rejects. Output sections are
accepted with `NONE` and `IMPLICIT`, as for `Cslib.Logic.PL.VeriPB.Text.checkOPB`.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Elab.checkAugmented`,
  `Cslib.Logic.PL.VeriPB.Elab.checkAugmentedDIMACS`: the checkers, for OPB and DIMACS instances.

## Main results

* `Cslib.Logic.PL.VeriPB.Elab.exists_checkRed_of_checkAugmented`,
  `Cslib.Logic.PL.VeriPB.Elab.exists_checkRed_of_checkAugmentedDIMACS`: an accepted proof has a
  kernel proof with the same conclusion, accepted by the kernel checker on the parsed instance.
* `Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_checkAugmented`,
  `Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_checkAugmentedDIMACS`: soundness of `UNSAT`.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Elab

open Text

/-- Check the kernel proof of an elaboration for the formula `F`, the objective `obj` and the
preserved set `pres`: its conclusion if accepted, with the output section `NONE` or `IMPLICIT`. -/
def checkResult (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) :
    Except String Result → Option Conclusion
  | .ok ⟨P, none, _⟩ => if checkRed F obj P pres then some P.conclusion else none
  | .ok ⟨P, some (g, false), _⟩ =>
    (checkRedOutput F obj P pres ⟨g, none⟩).map fun _ => P.conclusion
  | _ => none

/-- **Check an augmented proof for an OPB instance**: parse the instance, elaborate the proof and
check the kernel proof; the conclusion, if accepted. The proof may refer to the constraints of
the instance by their labels (`Cslib.Logic.PL.VeriPB.Text.parseOPBLabelled`). -/
def checkAugmented (opb pbp : String) : Option Conclusion :=
  let N := opbNames opb
  (parseOPBLabelled N opb).bind fun (I, L) =>
    checkResult I.constraints I.objective I.preserved
      (elaborate I.constraints I.objective I.preserved pbp N L)

/-- **Check an augmented proof for a DIMACS CNF formula**, its clause `1 -2 3 0` read as the
constraint `x1 + ~x2 + x3 >= 1`. -/
def checkAugmentedDIMACS (cnf pbp : String) : Option Conclusion :=
  (parseDIMACS cnf).bind fun φ =>
    checkResult (φ.map Clause.toPB) none none (elaborate (φ.map Clause.toPB) none none pbp)

/-- An accepted elaboration has a kernel proof with its conclusion, accepted by the kernel
checker. -/
theorem exists_checkRed_of_checkResult {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {r : Except String Result} {c : Conclusion}
    (h : checkResult F obj pres r = some c) :
    ∃ P, checkRed F obj P pres = true ∧ P.conclusion = c := by
  unfold checkResult at h
  split at h
  · split at h
    · exact ⟨_, ‹_›, Option.some.inj h⟩
    · cases h
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, checkRed_of_checkRedOutput ho, rfl⟩
  · cases h

/-- **An accepted augmented proof gives an accepted kernel proof**: if
`Cslib.Logic.PL.VeriPB.Elab.checkAugmented` accepts with the conclusion `c`, the instance parses,
and some kernel proof with the conclusion `c` is accepted by the kernel checker
`Cslib.Logic.PL.VeriPB.checkRed` on it. The guarantee depends only on the instance parser and
the kernel checker: the elaborator only supplies the kernel proof. -/
theorem exists_checkRed_of_checkAugmented {opb pbp : String} {c : Conclusion}
    (h : checkAugmented opb pbp = some c) :
    ∃ I P, parseOPB opb = some I ∧ checkRed I.constraints I.objective P I.preserved = true ∧
      P.conclusion = c := by
  obtain ⟨⟨I, L⟩, hI, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨P, hP, hc⟩ := exists_checkRed_of_checkResult h
  exact ⟨I, P, parseOPB_eq_some_of_parseOPBLabelled hI, hP, hc⟩

/-- **An accepted augmented proof for a DIMACS formula gives an accepted kernel proof** for its
clauses read as constraints. -/
theorem exists_checkRed_of_checkAugmentedDIMACS {cnf pbp : String} {c : Conclusion}
    (h : checkAugmentedDIMACS cnf pbp = some c) :
    ∃ φ P, parseDIMACS cnf = some φ ∧ checkRed (φ.map Clause.toPB) none P = true ∧
      P.conclusion = c := by
  obtain ⟨φ, hφ, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨P, hP, hc⟩ := exists_checkRed_of_checkResult h
  exact ⟨φ, P, hφ, hP, hc⟩

/-- **Soundness of `UNSAT` for augmented proofs of OPB instances**: an accepted proof of `UNSAT`
means the instance parses and its constraints have no 0/1 solution. -/
theorem not_satisfiable_of_checkAugmented {opb pbp : String} {q : ℕ}
    (h : checkAugmented opb pbp = some (.unsat q)) :
    ∃ I, parseOPB opb = some I ∧ ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ := by
  obtain ⟨I, P, hI, hP, hc⟩ := exists_checkRed_of_checkAugmented h
  exact ⟨I, hI, not_satisfiable_of_checkRed hP hc⟩

/-- **Soundness of `UNSAT` for augmented proofs of DIMACS formulas**: an accepted proof of
`UNSAT` means the CNF parses and is unsatisfiable. -/
theorem not_satisfiable_of_checkAugmentedDIMACS {cnf pbp : String} {q : ℕ}
    (h : checkAugmentedDIMACS cnf pbp = some (.unsat q)) :
    ∃ φ, parseDIMACS cnf = some φ ∧ ¬ φ.Satisfiable := by
  obtain ⟨φ, P, hφ, hP, hc⟩ := exists_checkRed_of_checkAugmentedDIMACS h
  exact ⟨φ, hφ, not_satisfiable_cnf_of_checkRed hP hc⟩

end Cslib.Logic.PL.VeriPB.Elab

end
