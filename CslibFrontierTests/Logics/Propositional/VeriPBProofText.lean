/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-! A test-only printer of kernel proofs as VeriPB text, for the fragment that the certified
dynamic programs and the producers of complete certificates write (`pol`, hinted `rup`, `red` with
an empty subproof, `soli`, `solx`, `deld`, and the conclusions `UNSAT`, `SAT : ρ`, `BOUNDS` and
`ENUMERATION_COMPLETE`). The tests of the certified dynamic programs parse its output with the
repository's text front end, and write it out for VeriPB and CakePB. -/

public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBProofText

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-- The name of a literal. -/
def litText (l : Literal ℕ) : String := (if l.2 then "x" else "~x") ++ toString (l.1 + 1)

/-- A constraint `a₁ ℓ₁ … >= d`. -/
def constrText (c : PBConstr) : String :=
  String.join (c.terms.map fun t => s!"{t.1} {litText t.2} ") ++ s!">= {c.degree}"

/-- A witness `x -> 0 …`. -/
def witnessText (ω : Witness) : String :=
  " ".intercalate (ω.map fun e => s!"x{e.1 + 1} -> " ++ match e.2 with
    | .zero => "0"
    | .one => "1"
    | .lit l => litText l)

/-- The operations of a `pol` step. -/
def opText : PolOp → String
  | .id k => toString k
  | .lit l => litText l
  | .add => "+"
  | .mul k => s!"{k} *"
  | .div k => s!"{k} d"
  | .sat => "s"
  | .weaken v => s!"x{v + 1} w"

/-- A top-level step, in the fragment the dynamic program writes. -/
def stepText : TopStep → String
  | .step (.pol ops) => s!"pol {" ".intercalate (ops.map opText)} ;\n"
  | .step (.rup c hs) =>
    s!"rup {constrText c} : " ++
      " ".intercalate (hs.map fun | .neg => "~" | .id k => toString k) ++ " ;\n"
  | .red c ω (some []) none => s!"red {constrText c} : {witnessText ω} : subproof\nqed ;\n"
  | .soli ρ => s!"soli {" ".intercalate (ρ.map litText)} ;\n"
  | .solx ρ => s!"solx {" ".intercalate (ρ.map litText)} ;\n"
  | .deld ids => s!"deld {" ".intercalate (ids.map toString)} ;\n"
  | _ => "unsupported ;\n"

/-- An optional bound, `INF` for none. -/
def boundText : Option ℤ → String
  | some b => toString b
  | none => "INF"

/-- A proof for a formula of `m` constraints, in the kernel format. -/
def pbpText (m : ℕ) (P : RedProof) : String :=
  s!"pseudo-Boolean proof version 3.0\nf {m} ;\n" ++ String.join (P.steps.map stepText) ++
    "output NONE ;\n" ++
    (match P.conclusion with
      | .bounds lb q ub none => s!"conclusion BOUNDS {boundText lb} : {q} {boundText ub} ;\n"
      | .unsat q => s!"conclusion UNSAT : {q} ;\n"
      | .sat (some ρ) => s!"conclusion SAT : {" ".intercalate (ρ.map litText)} ;\n"
      | .enumComplete n q => s!"conclusion ENUMERATION_COMPLETE {n} : {q} ;\n"
      | _ => "conclusion NONE ;\n") ++
    "end pseudo-Boolean proof ;\n"

end CslibFrontierTests.Logics.Propositional.VeriPBProofText

end
