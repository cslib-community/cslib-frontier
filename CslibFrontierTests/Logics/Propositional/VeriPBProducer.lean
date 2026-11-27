/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontierTests.Logics.Propositional.VeriPBProofText
-- `#guard` runs the producers and the checkers at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! The producers of complete VeriPB certificates
(`CslibFrontier.Logics.Propositional.PseudoBoolean.Completeness`) on random small instances:

* `#guard` runs of the checker on the produced proofs: `refute` or `solve` answers every
  instance, `optimize` and `enumerate` are always accepted, and their conclusions agree with a
  brute force over all assignments;
* the instances printed as OPB by the library's printer `Cslib.Logic.PL.VeriPB.Text.printOPB`
  and the proofs by the test-only printer
  `CslibFrontierTests.Logics.Propositional.VeriPBProofText.pbpText`, whose output the text front
  end parses and accepts with the same conclusion. `writeCases` writes the texts out for VeriPB
  and CakePB.

The kernel-checked clients are in `CslibFrontierTests.Logics.Propositional.VeriPBCompleteness`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBProducer

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB
open CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! ### Random instances -/

/-- A step of a linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `k` pseudo-random numbers below `b` from the seed `s`, and the next seed. -/
def rands (s b : ℕ) : ℕ → List ℕ × ℕ
  | 0 => ([], s)
  | k + 1 =>
    let s' := lcg s
    let (l, s'') := rands s' b k
    ((s' / 65536) % b :: l, s'')

/-- A random constraint on the variables `0, …, n - 1`: up to three terms with coefficients `1` to
`3`, and a degree from `1` to `3`. -/
def randConstr (s n : ℕ) : PBConstr × ℕ :=
  let (l, s') := rands s 12 7
  match l with
  | [k, a₁, a₂, a₃, v₁, v₂, d] =>
    let ts := [(a₁ % 3 + 1, (v₁ % n, decide (a₁ % 2 = 0))),
      (a₂ % 3 + 1, (v₂ % n, decide (a₂ % 2 = 1))),
      (a₃ % 3 + 1, ((v₁ + v₂ + 1) % n, decide (a₃ % 4 < 2)))]
    (⟨ts.take (k % 3 + 1), d % 3 + 1⟩, s')
  | _ => (⟨[], 0⟩, s')

/-- `m` random constraints. -/
def randConstrs (s n : ℕ) : ℕ → List PBConstr × ℕ
  | 0 => ([], s)
  | m + 1 =>
    let (c, s') := randConstr s n
    let (cs, s'') := randConstrs s' n m
    (c :: cs, s'')

/-- A random instance of seed `s`: up to four variables and five constraints, an objective with
weights from `-3` to `3`, and the first two variables preserved. -/
structure Case where
  /-- The number of variables. -/
  n : ℕ
  /-- The constraints. -/
  formula : List PBConstr
  /-- The objective. -/
  obj : Objective

/-- The random instance of seed `s`. -/
def randCase (s : ℕ) : Case :=
  let (l, s') := rands s 5 2
  let n := (l.headD 0) % 3 + 2
  let m := (l.getD 1 0) + 1
  let (F, s'') := randConstrs s' n m
  let (w, _) := rands s'' 7 n
  ⟨n, F, ⟨(List.range n).zip (w.map fun x => (x : ℤ) - 3), 0⟩⟩

/-- The cases. -/
def cases : List Case := (List.range 30).map fun s => randCase (s + 1)

/-! ### The brute force -/

/-- The assignments of the variables `0, …, n - 1` that satisfy the formula. -/
def Case.sols (c : Case) : List (ℕ → Bool) :=
  (assignments (List.range c.n)).filter fun σ => c.formula.all fun d => decide (d.Holds σ)

/-- The preserved set: the first two variables. -/
def pres : List ℕ := [0, 1]

/-- The number of distinct projections of the solutions to `pres`. -/
def Case.numProj (c : Case) : ℕ := (c.sols.map (proj pres)).dedup.length

/-- The optimum, if any. -/
def Case.opt (c : Case) : Option ℤ := (c.sols.map c.obj.eval).min?

/-! ### The proofs -/

/-- The decision proof: `SAT : ρ` or `UNSAT : q`. -/
def Case.decision (c : Case) : RedProof := ((solve c.formula).orElse fun _ => refute c.formula).getD
  ⟨[], .noClaim⟩

/-- The checker accepts every produced proof, and the conclusions agree with the brute force. -/
def Case.agrees (c : Case) : Bool :=
  let P := c.decision
  let B := optimize c.formula c.obj
  let E := enumerate c.formula pres
  checkRed c.formula none P &&
    (match P.conclusion with
      | .sat _ => !c.sols.isEmpty
      | .unsat _ => c.sols.isEmpty
      | _ => false) &&
    checkRed c.formula (some c.obj) B &&
    (match B.conclusion with
      | .bounds lb _ ub none => lb == c.opt && ub == c.opt
      | _ => false) &&
    checkRed c.formula none E (some pres) &&
    (match E.conclusion with
      | .enumComplete k _ => k == c.numProj
      | _ => false)

#guard cases.all Case.agrees

-- Both satisfiable and unsatisfiable instances occur.
#guard cases.any (·.sols.isEmpty) && cases.any (!·.sols.isEmpty)

/-! ### Kernel text -/

/-- The instance with the objective, or the preserved set, as OPB text, by the library's
printer. -/
def Case.opbText (c : Case) (obj : Option Objective) (P : Option (List ℕ)) : String :=
  Text.printOPB ⟨c.formula, obj, P⟩

/-- The three texts of a case: the instance, the proof and its conclusion, for the decision, the
optimization and the enumeration. -/
def Case.texts (c : Case) : List (String × String × Conclusion) :=
  let P := c.decision
  let B := optimize c.formula c.obj
  let E := enumerate c.formula pres
  [(c.opbText none none, pbpText c.formula.length P, P.conclusion),
    (c.opbText (some c.obj) none, pbpText c.formula.length B, B.conclusion),
    (c.opbText none (some pres), pbpText c.formula.length E, E.conclusion)]

/-- The text front end accepts the printed proofs against the printed instances, with the same
conclusions. -/
def Case.textAgrees (c : Case) : Bool :=
  c.texts.all fun (opb, pbp, concl) => Text.checkOPB opb pbp == some concl

#guard cases.all Case.textAgrees

/-- Write the texts of the cases to `dir`, for the external checkers: `c{k}-{dec,opt,enum}.opb` and
`.pbp`. -/
def writeCases (dir : System.FilePath) : IO Unit := do
  for (c, k) in cases.zipIdx do
    for ((opb, pbp, _), tag) in c.texts.zip ["dec", "opt", "enum"] do
      IO.FS.writeFile (dir / s!"c{k}-{tag}.opb") opb
      IO.FS.writeFile (dir / s!"c{k}-{tag}.pbp") pbp

end CslibFrontierTests.Logics.Propositional.VeriPBProducer
