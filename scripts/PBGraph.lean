/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso

/-!
# The verified graph checkers on files

`lake exe pb_graph iso PATTERN.lad TARGET.lad [PROOF.pbp]` and
`lake exe pb_graph clique GRAPH.dimacs [PROOF.pbp]` are the compiled counterparts of CakePB's
`cake_pb_iso` and `cake_pb_clique`. With a proof, they run
`Cslib.Logic.PL.VeriPB.Graph.checkSubgraphIso` or `Cslib.Logic.PL.VeriPB.Graph.checkClique` on the
texts of the files and print the verdict in CakePB's words (`s VERIFIED SUBGRAPH ISOMORPHIC`,
`s VERIFIED NOT SUBGRAPH ISOMORPHIC`, `s VERIFIED MAX CLIQUE SIZE |CLIQUE| = k`, or
`s VERIFIED BOUNDS l <= |CLIQUE| <= u`), exiting with `0`; otherwise `s REJECTED` and `1`. The
end-to-end theorems of those checkers (`isContained_iff_of_checkSubgraphIso`,
`clique_bounds_of_checkClique`) give the meaning of the verdict; the file reading, the printing
and Lean's compiler are trusted.

Without a proof, they print the encoding that the checker reads, `printOPB` of the encoding with
its names, with CakePB's constraint labels (`@al1a`, `@am1a`, `@injU`, `@adjA_U_B`;
`@noedgeX_Y`) put in front of the constraint lines, as `cake_pb_iso` and `cake_pb_clique` print
theirs. The labels are for the elaborator of the VeriPB tool: the Glasgow Subgraph Solver's proofs
refer to constraints by these labels, and `veripb ENCODING.opb PROOF.pbp --elaborate CORE.pbp`
turns them into constraint numbers. The labels are not verified and the Lean checker does not
read them: the checker reads `printOPB` of the encoding, which numbers the constraints in the
same order. A wrong label can only make the elaboration or the check fail.

The pipeline for a proof of the Glasgow Subgraph Solver (`--prove NAME` writes `NAME.pbp`):
```
lake exe pb_graph iso P.lad T.lad > NAME.enc.opb
veripb NAME.enc.opb NAME.pbp --elaborate NAME.core.pbp
lake exe pb_graph iso P.lad T.lad NAME.core.pbp
```
-/

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Graph

namespace PBGraph

/-- CakePB's labels of the subgraph isomorphism encoding, in the order of
`Cslib.Logic.PL.VeriPB.Graph.isoConstraints`, for a target on `Fin t`: they depend only on `t`
and the pattern. -/
def isoLabels {p : ℕ} (P : SimpleGraph (Fin p)) [DecidableRel P.Adj] (t : ℕ) : List String :=
  (List.finRange p).map (fun a => s!"al1{a}") ++ (List.finRange p).map (fun a => s!"am1{a}") ++
    (List.finRange t).map (fun u => s!"inj{u}") ++
    (List.finRange t).flatMap fun u => (List.finRange p).flatMap fun a =>
      ((List.finRange p).filter (P.Adj a ·)).map fun b => s!"adj{a}_{u}_{b}"

/-- CakePB's labels of the clique encoding, in the order of
`Cslib.Logic.PL.VeriPB.Graph.cliqueConstraints`. -/
def cliqueLabels {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List String :=
  (List.finRange n).flatMap fun x =>
    ((List.finRange n).filter fun y => decide (x < y ∧ ¬ G.Adj x y)).map fun y =>
      s!"noedge{x.val + 1}_{y.val + 1}"

/-- Put the labels in front of the constraint lines of a printed OPB text, the lines after the
header comment and the `min:` and `preserved:` lines. -/
def label (opb : String) (labels : List String) : String := Id.run do
  let mut out := ""
  let mut ls := labels
  for line in opb.splitOn "\n" do
    if line.isEmpty then continue
    if line.startsWith "*" || line.startsWith "min:" || line.startsWith "preserved:" then
      out := out ++ line ++ "\n"
    else
      match ls with
      | l :: rest => out := out ++ "@" ++ l ++ " " ++ line ++ "\n"; ls := rest
      | [] => out := out ++ line ++ "\n"
  return out

def usage : String :=
  "usage: pb_graph iso PATTERN.lad TARGET.lad [PROOF.pbp]\n" ++
    "       pb_graph clique GRAPH.dimacs [PROOF.pbp]"

end PBGraph

open PBGraph in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["iso", pf, tf] =>
    let (some gp, some gt) := (Graph.parseLAD (← IO.FS.readFile pf),
        Graph.parseLAD (← IO.FS.readFile tf))
      | IO.println "s REJECTED graph does not parse"; return 1
    IO.print (label (Text.printOPB ⟨isoConstraints gp.graph gt.graph, none, none⟩
      (isoNames gp.n gt.n)) (isoLabels gp.graph gt.n))
    return 0
  | ["iso", pf, tf, prf] =>
    let t₀ ← IO.monoMsNow
    let r := checkSubgraphIso (← IO.FS.readFile pf) (← IO.FS.readFile tf) (← IO.FS.readFile prf)
    let t₁ ← IO.monoMsNow
    IO.println s!"c check {t₁ - t₀} ms"
    match r with
    | some true => IO.println "s VERIFIED SUBGRAPH ISOMORPHIC"; return 0
    | some false => IO.println "s VERIFIED NOT SUBGRAPH ISOMORPHIC"; return 0
    | none => IO.println "s REJECTED"; return 1
  | ["clique", gf] =>
    let some g := Graph.parseDIMACSGraph (← IO.FS.readFile gf)
      | IO.println "s REJECTED graph does not parse"; return 1
    IO.print (label (Text.printOPB (encodeClique g.graph)) (cliqueLabels g.graph))
    return 0
  | ["clique", gf, prf] =>
    let t₀ ← IO.monoMsNow
    let r := checkClique (← IO.FS.readFile gf) (← IO.FS.readFile prf)
    let t₁ ← IO.monoMsNow
    IO.println s!"c check {t₁ - t₀} ms"
    match r with
    | some (l, u) =>
      if l = u then IO.println s!"s VERIFIED MAX CLIQUE SIZE |CLIQUE| = {l}"
      else IO.println s!"s VERIFIED BOUNDS {l} <= |CLIQUE| <= {u}"
      return 0
    | none => IO.println "s REJECTED"; return 1
  | _ => IO.eprintln usage; return 2
