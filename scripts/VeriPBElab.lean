/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate

/-!
# The VeriPB elaborator on files

`lake exe veripb_elab [--cnf] [--emit OUT.pbp] [--no-check] FORMULA PROOF` reads an OPB instance
(a DIMACS formula with `--cnf`) and a proof in the augmented VeriPB format, elaborates the proof
into a kernel proof (`Cslib.Logic.PL.VeriPB.Elab.elaborate`) and checks the kernel proof with
`Cslib.Logic.PL.VeriPB.checkRed`, as `Cslib.Logic.PL.VeriPB.Elab.checkAugmented` does. It prints
`s VERIFIED <conclusion>` or `s REJECTED <reason>` and the time of each phase on `c` lines, and
exits with `0` on acceptance and `1` otherwise. With `--emit`, it writes the kernel proof in the
text format, for an external kernel checker such as CakePB; the printer is not verified.
With `--no-check`, it only elaborates. With `--kernel`, it does not elaborate: it checks a proof
in the kernel format with the text front end (`Cslib.Logic.PL.VeriPB.Text.checkOPB`,
`Cslib.Logic.PL.VeriPB.Text.checkDIMACS`), for comparison with other elaborators.
-/

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

namespace VeriPBElab

/-- The variable names of a result, as an array for constant-time lookup. -/
structure NameTable where
  /-- `Cslib.Logic.PL.VeriPB.Text.Names.base`. -/
  base : ℕ := 0
  /-- `Cslib.Logic.PL.VeriPB.Text.Names.others`. -/
  others : Array String := #[]
  deriving Inhabited

def NameTable.ofNames (N : Text.Names) : NameTable := ⟨N.base, N.others.toArray⟩

/-- The name of a variable, as `Cslib.Logic.PL.VeriPB.Text.Names.name` gives it below
`Cslib.Logic.PL.VeriPB.Text.Names.next` (the elaborator names every variable it uses). -/
def varName (N : NameTable) (v : ℕ) : String :=
  if v < N.base then s!"x{v + 1}" else (N.others[v - N.base]?).getD s!"x{v + 1}"

def litStr (N : NameTable) (l : Literal ℕ) : String :=
  (if l.2 then "" else "~") ++ varName N l.1

def constrStr (N : NameTable) (c : PBConstr) : String :=
  String.join (c.terms.map fun t => s!"+{t.1} {litStr N t.2} ") ++ s!">= {c.degree}"

def objStr (N : NameTable) (f : Objective) : String :=
  String.join (f.lin.map fun e => s!"{if e.2 ≥ 0 then "+" else ""}{e.2} {varName N e.1} ") ++
    s!"{if f.const ≥ 0 then "+" else ""}{f.const}"

def hintStr : Hint → String
  | .neg => "~"
  | .id n => toString n

def polStr (N : NameTable) : PolOp → String
  | .id n => toString n
  | .lit l => litStr N l
  | .add => "+"
  | .mul k => s!"{k} *"
  | .div k => s!"{k} d"
  | .sat => "s"
  | .weaken v => s!"{varName N v} w"

def witStr (N : NameTable) (ω : Witness) : String :=
  " ".intercalate (ω.map fun (x, w) => s!"{varName N x} -> " ++ match w with
    | .zero => "0" | .one => "1" | .lit l => litStr N l)

def goalStr : GoalId → String
  | .hash k => s!"#{k}"
  | .db n => toString n

mutual

partial def stepStr (N : NameTable) : Step → String
  | .pol ops => s!"pol {" ".intercalate (ops.map (polStr N))};\n"
  | .rup c hs => s!"rup {constrStr N c} : {" ".intercalate (hs.map hintStr)};\n"
  | .rupSearch c => s!"rup {constrStr N c};\n"
  | .pbc c sub q => s!"pbc {constrStr N c} : subproof\n" ++
      String.join (sub.map (stepStr N)) ++ s!"qed : {q};\n"
  | .del ids => s!"del id {" ".intercalate (ids.map toString)};\n"

partial def itemStr (N : NameTable) : RedItem → String
  | .step s => stepStr N s
  | .goal g sub q => s!"proofgoal {goalStr g}\n" ++ String.join (sub.map (stepStr N)) ++
      s!"qed : {q};\n"
  | .scope b items => s!"scope {if b then "geq" else "leq"}\n" ++
      String.join (items.map (itemStr N)) ++ "end scope;\n"

end

def subStr (N : NameTable) (kw : String) (sub : Option (List RedItem)) (q : Option ℕ) :
    String :=
  match sub with
  | none => ";\n"
  | some items => " : subproof\n" ++ String.join (items.map (itemStr N)) ++
      s!"qed {kw}" ++ (match q with | some q => s!" : {q}" | none => "") ++ ";\n"

def orderProofStr (N : NameTable) (p : OrderProof) : String :=
  "proof\n" ++ String.join (p.items.map (itemStr N)) ++
    "qed" ++ (match p.qed with | some q => s!" : {q}" | none => "") ++ ";\n"

def varsStr (N : NameTable) (vs : List ℕ) : String := " ".intercalate (vs.map (varName N))

def topStr (N : NameTable) : TopStep → String
  | .step s => stepStr N s
  | .red c ω sub q => s!"red {constrStr N c} : {witStr N ω}" ++ subStr N "red" sub q
  | .dom c ω sub q => s!"dom {constrStr N c} : {witStr N ω}" ++ subStr N "dom" sub q
  | .sol ρ => s!"sol {" ".intercalate (ρ.map (litStr N))};\n"
  | .soli ρ => s!"soli {" ".intercalate (ρ.map (litStr N))};\n"
  | .solx ρ => s!"solx {" ".intercalate (ρ.map (litStr N))};\n"
  | .deld ids => s!"deld {" ".intercalate (ids.map toString)};\n"
  | .delc ids => s!"delc {" ".intercalate (ids.map toString)};\n"
  | .delcChecked i ω sub q => s!"delc {i} : {witStr N ω}" ++ subStr N "delc" sub q
  | .core ids => s!"core id {" ".intercalate (ids.map toString)};\n"
  | .strengthenToCore b => s!"strengthening_to_core {if b then "on" else "off"};\n"
  | .obji v => s!"obji {v};\n"
  | .obju diff g sub =>
    s!"obju {if diff then "diff" else "new"} {objStr N g}" ++ subStr N "obju" sub none
  | .defOrder name O sp w tp rp =>
    s!"def_order {name}\nvars\nleft {varsStr N O.left};\nright {varsStr N O.right};\n" ++
      s!"aux {varsStr N O.aux};\nend vars;\n" ++
      (if O.spec.isEmpty then "" else "spec\n" ++ String.join ((O.spec.zip sp).map fun (c, p) =>
        s!"red {constrStr N c} : {witStr N p.witness}" ++ subStr N "red" p.sub p.qed) ++
        "end spec;\n") ++
      "def\n" ++ String.join (O.defn.map fun c => constrStr N c ++ ";\n") ++ "end def;\n" ++
      s!"transitivity\nvars\nfresh_right {varsStr N w.right};\n" ++
      (if O.aux.isEmpty then "" else
        s!"fresh_aux_1 {varsStr N w.aux₁};\nfresh_aux_2 {varsStr N w.aux₂};\n") ++
      "end vars;\n" ++ orderProofStr N tp ++ "end transitivity;\n" ++
      "reflexivity\n" ++ orderProofStr N rp ++ "end reflexivity;\nend def_order;\n"
  | .loadOrder name z => s!"load_order {name} {" ".intercalate (z.map (litStr N))};\n"
  | .unloadOrder => "load_order;\n"
  | .eordDef name O =>
    s!"eord_def {name}\nvars\nleft {varsStr N O.left};\nright {varsStr N O.right};\n" ++
      s!"aux {varsStr N O.aux};\nend vars;\n" ++
      (if O.spec.isEmpty then "" else
        "spec\n" ++ String.join (O.spec.map fun c => constrStr N c ++ ";\n") ++ "end spec;\n") ++
      "def\n" ++ String.join (O.defn.map fun c => constrStr N c ++ ";\n") ++ "end def;\n" ++
      "end eord_def;\n"
  | .eordLoaded name z => s!"eord_loaded {name} {" ".intercalate (z.map (litStr N))};\n"
  | .presChange add x c sub =>
    s!"{if add then "preserved_add" else "preserved_rm"} {varName N x} : {constrStr N c}" ++
      subStr N (if add then "preserved_add" else "preserved_rm") sub none
  | .epreserved vs => s!"epreserved {varsStr N vs};\n"

def boundStr : Option ℤ → String
  | none => "INF"
  | some v => toString v

def asgStr (N : NameTable) : Option (List (Literal ℕ)) → String
  | none => ""
  | some ρ => " : " ++ " ".intercalate (ρ.map (litStr N))

def conclStr (N : NameTable) : Conclusion → String
  | .unsat q => s!"UNSAT : {q}"
  | .sat asg => "SAT" ++ asgStr N asg
  | .bounds lb q ub asg => s!"BOUNDS {boundStr lb} : {q} {boundStr ub}" ++ asgStr N asg
  | .noClaim => "NONE"
  | .enumPartial n => s!"ENUMERATION_PARTIAL {n}"
  | .enumComplete n q => s!"ENUMERATION_COMPLETE {n} : {q}"

def guaranteeStr : Guarantee → String
  | .derivable => "DERIVABLE"
  | .equisatisfiable => "EQUISATISFIABLE"
  | .equioptimal => "EQUIOPTIMAL"
  | .equienumerable => "EQUIENUMERABLE"

/-- Write the kernel proof as text. -/
def emit (h : IO.FS.Handle) (m : ℕ) (r : Elab.Result) : IO Unit := do
  h.putStr s!"pseudo-Boolean proof version 3.0\nf {m};\n"
  let N := NameTable.ofNames r.names
  for s in r.proof.steps do h.putStr (topStr N s)
  h.putStr (match r.output with
    | none => "output NONE;\n"
    | some (g, b) => s!"output {guaranteeStr g} {if b then "FILE" else "IMPLICIT"};\n")
  h.putStr s!"conclusion {conclStr N r.proof.conclusion};\nend pseudo-Boolean proof;\n"

end VeriPBElab

open VeriPBElab in
def main (args : List String) : IO UInt32 := do
  let cnf := args.contains "--cnf"
  let noCheck := args.contains "--no-check"
  let rec emitOf : List String → Option String
    | "--emit" :: p :: _ => some p
    | _ :: rest => emitOf rest
    | [] => none
  let out := emitOf args
  let files := (args.filter fun a => !a.startsWith "--" && some a != out)
  let [fml, pbp] := files | IO.eprintln "usage: veripb_elab [--cnf] [--emit OUT] FML PBP"; return 2
  let t₀ ← IO.monoMsNow
  let fmlText ← IO.FS.readFile fml
  let pbpText ← IO.FS.readFile pbp
  if args.contains "--kernel" then
    let r := if cnf then Text.checkDIMACS fmlText pbpText else Text.checkOPB fmlText pbpText
    let t₁ ← IO.monoMsNow
    IO.println s!"c kernel text check {t₁ - t₀} ms"
    match r with
    | some c => IO.println s!"s VERIFIED {conclStr default c}"; return 0
    | none => IO.println "s REJECTED kernel text check"; return 1
  -- The names of an OPB text are scanned once, for parsing and elaboration alike.
  let names : Option Text.Names := if cnf then none else some (Text.opbNames fmlText)
  let inst : Option Instance := match names with
    | none => (Text.parseDIMACS fmlText).map fun φ => ⟨φ.map Clause.toPB, none, none⟩
    | some N => Text.parseOPBWith N fmlText
  let some I := inst | IO.println "s REJECTED formula does not parse"; return 1
  let t₁ ← IO.monoMsNow
  IO.println s!"c read and parse formula {t₁ - t₀} ms ({I.constraints.length} constraints)"
  let r := match names with
    | none => Elab.elaborate I.constraints I.objective I.preserved pbpText
    | some N => Elab.elaborate I.constraints I.objective I.preserved pbpText N
  match r with
  | .error e => IO.println s!"s REJECTED elaboration: {e}"; return 1
  | .ok res =>
    let t₂ ← IO.monoMsNow
    IO.println s!"c elaborate {t₂ - t₁} ms ({res.proof.steps.length} kernel steps)"
    if let some p := out then
      IO.FS.withFile p .write fun h => emit h I.constraints.length res
      let t₃ ← IO.monoMsNow
      IO.println s!"c emit {t₃ - t₂} ms"
    if noCheck then IO.println "s ELABORATED"; return 0
    let t₃ ← IO.monoMsNow
    let c := Elab.checkResult I.constraints I.objective I.preserved (.ok res)
    match c with
    | some c =>
      let t₄ ← IO.monoMsNow
      IO.println s!"c kernel check {t₄ - t₃} ms"
      IO.println s!"s VERIFIED {conclStr (.ofNames res.names) c}"
      return 0
    | none =>
      let t₄ ← IO.monoMsNow
      IO.println s!"c kernel check {t₄ - t₃} ms"
      -- Locate the first rejected step, for diagnosis.
      let mut st := State.init I.constraints I.objective I.preserved
      let mut i := 0
      let mut failed := false
      for t in res.proof.steps do
        match stepTop I.constraints I.objective st t with
        | some st' => st := st'; i := i + 1
        | none =>
          let ts := (topStr (.ofNames res.names) t).take 300
          IO.println s!"c first rejected kernel step {i}: {ts}"
          failed := true
          break
      if !failed then IO.println "c all steps accepted; the conclusion or output is rejected"
      IO.println "s REJECTED kernel check"
      return 1
