/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance

/-! A test-only printer of kernel proofs as VeriPB text, for the fragment that the certified
dynamic programs write (`pol`, hinted `rup`, `red` with an empty subproof, `soli`, `deld` and a
`BOUNDS` conclusion), and the symmetry-breaking prefix of
`Cslib.Logic.PL.VeriPB.symmetryBreaking` (`def_order` without auxiliary variables or
specification, `load_order`, and `dom` with `proofgoal` blocks of `pol` steps), with an `UNSAT`
conclusion. The tests of the certified dynamic programs parse its output with the
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

/-- A variable of an order, by its position: `u`, `v` or a fresh right variable `w`, numbered
from `1`. -/
def orderVarText (O : Order) (w : TransVars) (v : ℕ) : String :=
  match O.left.idxOf? v, O.right.idxOf? v, w.right.idxOf? v with
  | some i, _, _ => s!"u{i + 1}"
  | none, some i, _ => s!"v{i + 1}"
  | none, none, some i => s!"w{i + 1}"
  | none, none, none => s!"x{v + 1}"

/-- A constraint of an order, over its variable names. -/
def orderConstrText (O : Order) (w : TransVars) (c : PBConstr) : String :=
  String.join (c.terms.map fun t =>
    s!"{t.1} " ++ (if t.2.2 then "" else "~") ++ orderVarText O w t.2.1 ++ " ") ++
    s!">= {c.degree}"

/-- `proofgoal` blocks of `pol` steps, as the order proofs and the lex-leader steps use. -/
def itemText : RedItem → String
  | .goal (.hash k) sub q =>
    s!"proofgoal #{k}\n" ++ String.join (sub.map fun
      | .pol ops => s!"pol {" ".intercalate (ops.map opText)};\n"
      | _ => "unsupported;\n") ++ s!"qed : {q};\n"
  | _ => "unsupported;\n"

/-- A top-level step, in the fragment the dynamic program and the symmetry breaking write. -/
def stepText : TopStep → String
  | .step (.pol ops) => s!"pol {" ".intercalate (ops.map opText)} ;\n"
  | .step (.rup c hs) =>
    s!"rup {constrText c} : " ++
      " ".intercalate (hs.map fun | .neg => "~" | .id k => toString k) ++ " ;\n"
  | .red c ω (some []) none => s!"red {constrText c} : {witnessText ω} : subproof\nqed ;\n"
  | .soli ρ => s!"soli {" ".intercalate (ρ.map litText)} ;\n"
  | .deld ids => s!"deld {" ".intercalate (ids.map toString)} ;\n"
  | .defOrder name O [] w tp rp =>
    s!"def_order {name}\nvars\nleft {" ".intercalate (O.left.map (orderVarText O w))};\n" ++
      s!"right {" ".intercalate (O.right.map (orderVarText O w))};\naux;\nend;\ndef\n" ++
      String.join (O.defn.map fun c => orderConstrText O w c ++ ";\n") ++
      s!"end;\ntransitivity\nvars\nfresh_right " ++
      s!"{" ".intercalate (w.right.map (orderVarText O w))};\nend;\nproof\n" ++
      String.join (tp.items.map itemText) ++ "qed;\nend;\nreflexivity\nproof\n" ++
      String.join (rp.items.map itemText) ++ "qed;\nend;\nend;\n"
  | .loadOrder name z => s!"load_order {name} {" ".intercalate (z.map litText)};\n"
  | .dom c ω (some items) none =>
    s!"dom {constrText c} : {witnessText ω} : subproof\n" ++ String.join (items.map itemText) ++
      "qed;\n"
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
      | _ => "conclusion NONE ;\n") ++
    "end pseudo-Boolean proof ;\n"

end CslibFrontierTests.Logics.Propositional.VeriPBProofText

end
