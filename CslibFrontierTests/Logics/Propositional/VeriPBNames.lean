/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
-- `import all`: the kernel evaluates the printer and its private word builders in `Print`, the
-- parsers and checkers of `Text` and the step `stepTop` of `Redundance`, whose bodies are not
-- exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Variable names other than `xN` in OPB instances and VeriPB proofs, checked by the kernel.

* A named instance is read with its names numbered in order of first appearance, and a proof
  with a `red` step on a fresh name `zz`, a `sol` line and `conclusion SAT : ρ` is accepted; the
  conclusion then holds for every assignment of the names (`Instance.valuesVia_eq`). A `red`
  step whose witness moves an input variable without a subproof is rejected. VeriPB 3.0.2
  agrees on both; it rejects the one-letter name `z`, as the parser does.
* `x01` is not `x1`: VeriPB reads them as distinct variables, and so does the parser, so the
  instance `x1 >= 1`, `~x01 >= 1` is satisfiable and its "refutation" is rejected (VeriPB 3.0.2
  agrees).
* The name `$a` of an auxiliary variable is a name of a proof but not of an instance: the
  instance `$a >= 1` is rejected, as an output formula too, and names that give a variable of an
  instance the name `$a` do not cover it for printing, while a proof introducing `$a` by `red` is
  accepted (VeriPB 3.0.2 agrees on both texts). Names with an unused `$a` still cover it.
* Instances built in Lean with names are printed and read back, renumbered when their names are
  not in order of first appearance; the soundness theorems end to end apply to them.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBNames

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text

/-! ### Named text -/

/-- `a1 + b_2 >= 1` and `~a1 + c[3] >= 1`. -/
def namedOPB : String := "* #variable= 3 #constraint= 2
1 a1 1 b_2 >= 1 ;
1 ~a1 1 c[3] >= 1 ;
"

-- The names are numbered in order of first appearance.
example : opbNames namedOPB = ⟨["a1", "b_2", "c[3]"], 0⟩ := by decide +kernel
example : parseOPB namedOPB = some ⟨[⟨[(1, (0, true)), (1, (1, true))], 1⟩,
    ⟨[(1, (0, false)), (1, (2, true))], 1⟩], none, none⟩ := by
  decide +kernel

/-- A `red` step introducing the fresh name `zz`, then a logged solution and its assignment. -/
def namedProof : String := "pseudo-Boolean proof version 3.0
f 2;
red 1 ~zz 1 a1 >= 1 : zz -> 0;
sol a1 ~b_2 c[3] ~zz;
output NONE;
conclusion SAT : a1 ~b_2 c[3];
end pseudo-Boolean proof;
"

/-- The proof is accepted, its assignment read with the names of the instance: `a1` is `0`. -/
theorem named_accepted :
    checkOPB namedOPB namedProof = some (.sat (some [(0, true), (1, false), (2, true)])) := by
  decide +kernel

-- The proof's own names are the next variables, in order of first appearance; the keywords
-- `pseudo-Boolean`, `proof`, `version` and `red` are names too, so `zz` is the variable `7`.
example : (proofNames namedOPB namedProof).var? "zz" = some 7 := by decide +kernel

/-- The same proof with the one-letter name `z`, which is not a name. -/
def namedProofZ : String := "pseudo-Boolean proof version 3.0
f 2;
red 1 ~z 1 a1 >= 1 : z -> 0;
sol a1 ~b_2 c[3] ~z;
output NONE;
conclusion SAT : a1 ~b_2 c[3];
end pseudo-Boolean proof;
"

example : checkOPB namedOPB namedProofZ = none := by decide +kernel

/-- A `red` step whose witness moves the input variable `a1` without a subproof. -/
def namedBad : String := "pseudo-Boolean proof version 3.0
f 2;
sol a1 ~b_2 c[3];
red 1 ~a1 >= 1 : a1 -> 0;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

example : checkOPB namedOPB namedBad = none := by decide +kernel

/-- **The named instance is satisfiable under an assignment of its names**: the conclusion holds
for the instance read through the names of its text. -/
example : ∃ I, parseOPB namedOPB = some I ∧
    ∃ τ : String → Bool, ∀ c ∈ I.constraints, c.Holds (τ ∘ (opbNames namedOPB).name) := by
  obtain ⟨I, hI, hσ⟩ := exists_satisfies_of_checkOPB (out := none)
    (show (checkOPBOutput namedOPB namedProof).map (·.1) = _ from named_accepted)
  refine ⟨I, hI, ?_⟩
  have hne : (I.values []).Nonempty := (Instance.satisfiable_iff I).1 hσ
  rw [← Instance.valuesVia_eq (e := (opbNames namedOPB).name)
    (Names.name_injective (opbNames_wf _)).injOn] at hne
  obtain ⟨_, τ, hτ, -⟩ := hne
  exact ⟨τ, hτ⟩

/-! ### Standard names without leading zeros -/

/-- `x1 >= 1` and `~x01 >= 1`, over two variables. -/
def leadOPB : String := "* #variable= 2 #constraint= 2
1 x1 >= 1 ;
1 ~x01 >= 1 ;
"

example : opbNames leadOPB = ⟨["x01"], 1⟩ := by decide +kernel

/-- The sum of the two constraints is not a contradiction. -/
def leadUnsat : String := "pseudo-Boolean proof version 3.0
f 2;
pol 1 2 +;
output NONE;
conclusion UNSAT : 3;
end pseudo-Boolean proof;
"

/-- `x1 = 1`, `x01 = 0` is a solution. -/
def leadSat : String := "pseudo-Boolean proof version 3.0
f 2;
sol x1 ~x01;
output NONE;
conclusion SAT;
end pseudo-Boolean proof;
"

example : checkOPB leadOPB leadUnsat = none := by decide +kernel
example : checkOPB leadOPB leadSat = some (.sat none) := by decide +kernel

/-! ### Auxiliary names in instances and proofs -/

/-- `$a >= 1`. The name `$a` of an auxiliary variable is not an OPB name, so VeriPB 3.0.2 rejects
the instance ("Expected literal!"; CakePB accepts it). -/
def auxOPB : String := "* #variable= 1 #constraint= 1
1 $a >= 1 ;
"

example : opbNames auxOPB = ⟨[], 0⟩ := by decide +kernel
example : parseOPB auxOPB = none := by decide +kernel

/-- `x1 >= 1`. -/
def x1OPB : String := "* #variable= 1 #constraint= 1
1 x1 >= 1 ;
"

/-- A proof that introduces the auxiliary variable `$a` by `red`, then derives `$a + x1 >= 2`. -/
def auxProof : String := "pseudo-Boolean proof version 3.0
f 1;
red 1 $a >= 1 : $a -> 1;
rup 1 $a 1 x1 >= 2;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"

-- A proof may name `$a`, a fresh variable after the keywords (VeriPB 3.0.2 accepts the proof).
example : (proofNames x1OPB auxProof).var? "$a" = some 5 := by decide +kernel
example : checkOPB x1OPB auxProof = some .noClaim := by decide +kernel
-- An output formula may not, even read with the names of that proof.
example : parseOPBWith (proofNames x1OPB auxProof) auxOPB = none := by decide +kernel
/-- `x₀ >= 1`, printed `1 x1 >= 1 ;` with the standard names. -/
def x1I : Instance := ⟨[⟨[(1, (0, true))], 1⟩], none, none⟩

-- `Covers` guarantees that `printOPB` writes an OPB name for every variable of the instance;
-- `printOPB` itself takes any names. Well-formed names that give `x₀` the name `$a` do not
-- cover `x1I`: with them `printOPB` writes `1 $a >= 1 ;`, which the parser rejects.
example : (⟨["$a"], 0⟩ : Names).WF := by decide
example : ¬ (⟨["$a"], 0⟩ : Names).Covers x1I := by decide
example : printOPB x1I ⟨["$a"], 0⟩ = "* #variable= 1 #constraint= 1 \n1 $a >= 1 ; \n" := by
  decide +kernel
example : parseOPB (printOPB x1I ⟨["$a"], 0⟩) = none := by decide +kernel

/-- Names with `$a` for the variable `1`, which `x1I` does not use: `x₀` keeps `x1`. -/
def auxN : Names := ⟨["$a"], 1⟩

-- They cover `x1I`, so the round trip and the soundness theorems end to end apply.
example : auxN.Covers x1I := by decide
example : printOPB x1I auxN = "* #variable= 1 #constraint= 1 \n1 x1 >= 1 ; \n" := by
  decide +kernel
example : parseOPB (printOPB x1I auxN) = some x1I := by
  rw [parseOPB_printOPB_of_var? (by decide) (by decide +kernel), reread_eq (by decide)]

/-- A solution of `x1I`. -/
def x1Proof : String := "pseudo-Boolean proof version 3.0
f 1;
sol x1;
output NONE;
conclusion SAT : x1;
end pseudo-Boolean proof;
"

theorem x1_accepted : checkOPB (printOPB x1I auxN) x1Proof = some (.sat (some [(0, true)])) := by
  decide +kernel

/-- **`x1I` has a solution**, from the proof checked against its text printed with `auxN`. -/
example : ∃ σ : ℕ → Bool, ∀ c ∈ x1I.constraints, c.Holds σ :=
  exists_satisfies_of_checkOPB_printOPB (N := auxN) (by decide) (out := none)
    (show (checkOPBOutput (printOPB x1I auxN) x1Proof).map (·.1) = _ from x1_accepted)

/-! ### Printing with names -/

/-- Minimize `3 x₀ - x₁` subject to `x₀ + x₁ >= 1` and `2 ¬x₁ + x₂ >= 2`, preserving `x₂`. -/
def grid : Instance :=
  ⟨[⟨[(1, (0, true)), (1, (1, true))], 1⟩, ⟨[(2, (1, false)), (1, (2, true))], 2⟩],
    some ⟨[(0, 3), (1, -1)], 0⟩, some [2]⟩

/-- Names in the order in which the printed text first mentions the variables. -/
def gridN : Names := ⟨["e_0_1", "e_1_2", "sel[0]"], 0⟩

example : gridN.Covers grid := by decide
example : printOPB grid gridN = "* #variable= 3 #constraint= 2 \nmin: 3 e_0_1 -1 e_1_2 ; \n\
    preserved: sel[0] ; \n1 e_0_1 1 e_1_2 >= 1 ; \n2 ~e_1_2 1 sel[0] >= 2 ; \n" := by
  decide +kernel

-- The names read each variable as itself, so `grid` is read back as printed.
theorem gridN_canonical : ∀ v ∈ grid.varList,
    (opbNames (printOPB grid gridN)).var? (gridN.name v) = some v := by
  decide +kernel

example : parseOPB (printOPB grid gridN) = some grid := by
  rw [parseOPB_printOPB_of_var? (by decide) gridN_canonical, reread_eq (by decide)]

/-- `grid` with the terms of its objective swapped, so that its text mentions `x₁` first. -/
def gridR : Instance :=
  ⟨[⟨[(1, (0, true)), (1, (1, true))], 1⟩, ⟨[(2, (1, false)), (1, (2, true))], 2⟩],
    some ⟨[(1, -1), (0, 3)], 0⟩, some [2]⟩

-- So `x₁`, named `e_1_2`, is read back as `0` and `x₀` as `1`: the instance is renumbered, with
-- the same names (`exists_parseOPB_printOPB`).
example : opbNames (printOPB gridR gridN) = ⟨["e_1_2", "e_0_1", "sel[0]"], 0⟩ := by
  decide +kernel
example : parseOPB (printOPB gridR gridN) = some ⟨[⟨[(1, (1, true)), (1, (0, true))], 1⟩,
    ⟨[(2, (0, false)), (1, (2, true))], 2⟩], some ⟨[(0, -1), (1, 3)], 0⟩, some [2]⟩ := by
  decide +kernel

/-- `ab >= 1`, `~cd >= 1` and `cd + ~ab >= 1`, with the names `ab` and `cd`. -/
def abI : Instance :=
  ⟨[⟨[(1, (0, true))], 1⟩, ⟨[(1, (1, false))], 1⟩, ⟨[(1, (1, true)), (1, (0, false))], 1⟩],
    none, none⟩

/-- The names of `abI`. -/
def abN : Names := ⟨["ab", "cd"], 0⟩

/-- Their sum is a contradiction. -/
def abProof : String := "pseudo-Boolean proof version 3.0
f 3;
pol 1 3 + 2 +;
output NONE;
conclusion UNSAT : 4;
end pseudo-Boolean proof;
"

theorem ab_accepted : checkOPB (printOPB abI abN) abProof = some (.unsat 4) := by
  decide +kernel

/-- **`abI` has no solution**, from the refutation of its text printed with names. -/
example : ∀ σ : ℕ → Bool, ¬ ∀ c ∈ abI.constraints, c.Holds σ :=
  not_satisfiable_of_checkOPB_printOPB (by decide) (out := none)
    (show (checkOPBOutput (printOPB abI abN) abProof).map (·.1) = _ from ab_accepted)

/-- `ab + cd >= 1`, named in the order `cd`, `ab`: the printed text mentions `cd` first. -/
def orI : Instance := ⟨[⟨[(1, (1, true)), (1, (0, true))], 1⟩], none, none⟩

/-- A solution with `cd` false and `ab` true. -/
def orProof : String := "pseudo-Boolean proof version 3.0
f 1;
sol ~cd ab;
output NONE;
conclusion SAT : ~cd ab;
end pseudo-Boolean proof;
"

theorem or_accepted :
    checkOPB (printOPB orI abN) orProof = some (.sat (some [(0, false), (1, true)])) := by
  decide +kernel

/-- **The assignment of `SAT : ρ` solves `orI`, translated by names**: in the text the variable
`1` of `orI`, named `cd`, is read as `0`, so `ρ` makes `0` false and `1` true; through the names,
`ab` (the variable `0` of `orI`) is true. -/
example : ∀ c ∈ orI.constraints, c.Holds fun v =>
    ([("cd", false), ("ab", true)] : List (String × Bool)).contains (abN.name v, true) := by
  have h := holds_of_checkOPB_printOPB_sat (by decide) (out := none)
    (show (checkOPBOutput (printOPB orI abN) orProof).map (·.1) = _ from or_accepted)
  have hρ : ([(0, false), (1, true)] : List (Literal ℕ)).map
      (fun l => ((proofNames (printOPB orI abN) orProof none).name l.1, l.2)) =
      [("cd", false), ("ab", true)] := by
    decide +kernel
  rwa [hρ] at h

end CslibFrontierTests.Logics.Propositional.VeriPBNames
