/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso
import Mathlib.Combinatorics.SimpleGraph.Hasse
-- `import all`: the kernel evaluates the graph readers and their private helpers, `printOPB` and
-- its private word builders, the parsers and checkers of `Text` and the step `stepTop` of
-- `Redundance`, whose bodies are not exposed, and the unexposed checkers of `Clique` and
-- `SubgraphIso`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Dimacs
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Lad
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Proofs of the Glasgow Subgraph Solver, checked end to end by the kernel.

The proofs were made by the pipeline of the solver's `dev_docs/proof-logging.md` ("Verifying
with the CakePB checker"), on the solver at commit `01ef6cae` (`glasgow_subgraph_solver
--format lad --no-clique-detection --prove NAME P T`, `glasgow_clique_solver --format dimacs
--prove NAME G`): the solver writes a proof in the augmented format, which refers to the
constraints of CakePB's encoding by their labels (`@al10`, `@inj1`, `@adj0_0_1`, `@noedge2_5`);
VeriPB 3.0.2 elaborates it (`veripb ENC.opb NAME.pbp --elaborate NAME.core.pbp`) against the
encoding that `cake_pb_iso` or `cake_pb_clique` (CakePB `438b8f8`, CakeML `14856fcf`) prints, into
a kernel proof with constraint numbers; CakePB checks that kernel proof, and so does the kernel
here, unchanged. `lake exe pb_graph` prints the same encoding with the same labels; VeriPB's
elaboration against it gives the same kernel proofs, up to the choice of RUP hints, which varies
between runs of VeriPB.

For `SAT`, the solver logs its solution with `solx`, which needs a preserved set that CakePB's
encoding does not declare, so neither VeriPB nor CakePB accepts it against that encoding; it is
replaced by `sol` before elaboration, an edit of the untrusted proof. The elaborated `UNSAT` proof
uses the implication `ia C : j`, read here as RUP from the negation of `C` and `j`.

* The triangle has no copy in the path `0 - 1 - 2 - 3` (`UNSAT`; `s VERIFIED NOT SUBGRAPH
  ISOMORPHIC` from `cake_pb_iso`).
* `K₂` has a copy in that path (`SAT`; `s VERIFIED SUBGRAPH ISOMORPHIC`).
* A graph on five vertices has clique number `3` (`BOUNDS 2 2` for the number of vertices not
  chosen; `s VERIFIED MAX CLIQUE SIZE |CLIQUE| = 3` from `cake_pb_clique`).

Larger proofs of the solver, thousands of steps and more, are out of reach of `decide +kernel`
and are checked by the compiled checkers of `lake exe pb_graph`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBGlasgowDecide

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text Cslib.Logic.PL.VeriPB.Graph

/-! ### Subgraph isomorphism -/

/-- The triangle. -/
def k3Text : String := "3\n2 1 2\n2 0 2\n2 0 1\n"

/-- The edge `K₂`. -/
def k2Text : String := "2\n1 1\n1 0\n"

/-- The path `0 - 1 - 2 - 3`. -/
def p4Text : String := "4\n1 1\n2 0 2\n2 1 3\n1 2\n"

example : parseLAD p4Text = some ⟨4, [[1], [0, 2], [1, 3], [2]]⟩ := by decide +kernel

-- The path read is Mathlib's.
example : (parseLAD p4Text).map (fun g => isoConstraints (⊤ : SimpleGraph (Fin 3)) g.graph) =
    some (isoConstraints (⊤ : SimpleGraph (Fin 3)) (SimpleGraph.pathGraph 4)) := by
  decide +kernel

/-- The solver's proof that the triangle has no copy in the path, elaborated by VeriPB: no
vertex of the triangle can go to an end of the path, whose one neighbour leaves no room for the
two other vertices, and then the three vertices have two targets. -/
def k3p4Proof : String := "pseudo-Boolean proof version 3.0
f 34;
pol 11 12 + 8 + s;
ia 1 ~x0_0 >= 1 : 35;
deld 35;
pol 29 30 + 9 + s;
ia 1 ~x0_3 >= 1 : 37;
deld 37;
pol 13 14 + 8 + s;
ia 1 ~x1_0 >= 1 : 39;
deld 39;
pol 31 32 + 9 + s;
ia 1 ~x1_3 >= 1 : 41;
deld 41;
pol 15 16 + 8 + s;
ia 1 ~x2_0 >= 1 : 43;
deld 43;
pol 33 34 + 9 + s;
ia 1 ~x2_3 >= 1 : 45;
deld 45;
pol 1 2 + 3 + 8 + 9 +;
rup >= 1 : 46 44 42 40 38 36 47;
output NONE ;
conclusion UNSAT : 48;
end pseudo-Boolean proof;
"

theorem k3p4_accepted : checkSubgraphIso k3Text p4Text k3p4Proof = some false := by
  decide +kernel

/-- **End to end from LAD text, `UNSAT`**, with the solver's proof. -/
example : ∃ gp gt, parseLAD k3Text = some gp ∧ parseLAD p4Text = some gt ∧
    ¬ gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, h⟩ := isContained_iff_of_checkSubgraphIso k3p4_accepted
  exact ⟨gp, gt, hp, ht, fun hc => absurd (h.1 hc) (by decide)⟩

theorem k3p4Graph_accepted : checkSubgraphIsoGraph (⊤ : SimpleGraph (Fin 3))
    (SimpleGraph.pathGraph 4) k3p4Proof = some false := by
  decide +kernel

/-- **The triangle is not a subgraph of the path on four vertices**, for Mathlib's graphs. -/
example : ¬ (⊤ : SimpleGraph (Fin 3)).IsContained (SimpleGraph.pathGraph 4) := fun h =>
  absurd ((isContained_iff_of_checkSubgraphIsoGraph k3p4Graph_accepted).1 h) (by decide)

/-- The encoding of the triangle into the path, as the checker prints it. -/
def k3p4OPB : String :=
  printOPB ⟨isoConstraints (⊤ : SimpleGraph (Fin 3)) (SimpleGraph.pathGraph 4), none, none⟩
    (isoNames 3 4)

-- The first implication of the proof is accepted; with its hint changed to the at-least-one
-- constraint of the vertex `0`, which does not imply it, it is rejected.
example : checkOPB k3p4OPB "pseudo-Boolean proof version 3.0\nf 34;\npol 11 12 + 8 + s;\n\
    ia 1 ~x0_0 >= 1 : 35;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n" =
    some .noClaim := by
  decide +kernel
example : checkOPB k3p4OPB "pseudo-Boolean proof version 3.0\nf 34;\npol 11 12 + 8 + s;\n\
    ia 1 ~x0_0 >= 1 : 1;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n" =
    none := by
  decide +kernel

/-- The solver's proof that `K₂` has a copy in the path, `0 ↦ 2` and `1 ↦ 1`, elaborated by
VeriPB, with its `solx` replaced by `sol`. -/
def k2p4Proof : String := "pseudo-Boolean proof version 3.0
f 16;
sol ~x0_0 ~x0_1 x0_2 ~x0_3 ~x1_0 x1_1 ~x1_2 ~x1_3;
output NONE ;
conclusion SAT;
end pseudo-Boolean proof;
"

theorem k2p4_accepted : checkSubgraphIso k2Text p4Text k2p4Proof = some true := by
  decide +kernel

/-- **End to end from LAD text, `SAT`**, with the solver's proof. -/
example : ∃ gp gt, parseLAD k2Text = some gp ∧ parseLAD p4Text = some gt ∧
    gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, h⟩ := isContained_iff_of_checkSubgraphIso k2p4_accepted
  exact ⟨gp, gt, hp, ht, h.2 rfl⟩

/-! ### Maximum clique -/

/-- A graph on five vertices: the triangles `{1, 2, 3}`, `{2, 3, 4}` and `{3, 4, 5}`. -/
def g5Text : String := "p edge 5 7\ne 1 2\ne 1 3\ne 2 3\ne 3 4\ne 4 5\ne 3 5\ne 2 4\n"

/-- The solver's proof that the graph has clique number `3`, elaborated by VeriPB: it logs three
growing cliques, the last `{1, 2, 3}`, and refutes a clique of four vertices with the non-edge
constraints. -/
def g5Proof : String := "pseudo-Boolean proof version 3.0
f 3;
soli ~x1 ~x2 x3 ~x4 ~x5;
soli x1 ~x2 x3 ~x4 ~x5;
soli x1 x2 x3 ~x4 ~x5;
rup 1 ~x1 1 ~x3 >= 1 : ~ 1 2 6;
pol 3 6 +;
rup 1 ~x3 >= 1 : 8 1;
deld 7 8;
pol 3 1 6 + +;
rup 1 ~x1 1 ~x2 1 ~x3 1 ~x4 1 ~x5 >= 2 : 9 6 3;
output NONE ;
conclusion BOUNDS 2 : 10 2;
end pseudo-Boolean proof;
"

theorem g5_accepted : checkClique g5Text g5Proof = some (3, 3) := by decide +kernel

/-- **The clique number of a DIMACS graph**, with the solver's proof. -/
example : ∃ g, parseDIMACSGraph g5Text = some g ∧ g.graph.cliqueNum = 3 :=
  cliqueNum_eq_of_checkClique g5_accepted

end CslibFrontierTests.Logics.Propositional.VeriPBGlasgowDecide
