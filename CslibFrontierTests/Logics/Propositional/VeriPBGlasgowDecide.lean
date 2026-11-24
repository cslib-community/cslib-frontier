/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso
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

* `K₂` has no copy in two vertices without an edge (`UNSAT`; `s VERIFIED NOT SUBGRAPH
  ISOMORPHIC` from `cake_pb_iso`).
* `K₂` has a copy in the path `0 - 1 - 2` (`SAT`; `s VERIFIED SUBGRAPH ISOMORPHIC`).
* A triangle with a pendant vertex has clique number `3` (`BOUNDS 1 1` for the number of
  vertices not chosen; `s VERIFIED MAX CLIQUE SIZE |CLIQUE| = 3` from `cake_pb_clique`).

The instances are as small as those of the hand-written fixtures: evaluating the printer and the
parsers in the kernel takes gigabytes already for these, so `decide +kernel` cannot check the
encodings of larger graphs. Larger proofs of the solver, thousands of steps and more, are
checked by the compiled checkers of `lake exe pb_graph`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBGlasgowDecide

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text Cslib.Logic.PL.VeriPB.Graph

/-! ### Subgraph isomorphism -/

/-- The edge `K₂`. -/
def k2Text : String := "2\n1 1\n1 0\n"

/-- Two vertices, no edge. -/
def e2Text : String := "2\n0\n0\n"

/-- The path `0 - 1 - 2`. -/
def p3Text : String := "3\n1 1\n2 0 2\n1 1\n"

/-- The solver's proof that `K₂` has no copy in two vertices without an edge, elaborated by
VeriPB: neither target vertex has a neighbour for the image of the vertex `1`, so the vertex `0`
goes to neither (the two implications `ia`), and its at-least-one constraint is violated. -/
def k2e2Proof : String := "pseudo-Boolean proof version 3.0
f 10;
pol 7 s;
ia 1 ~x0_0 >= 1 : 11;
deld 11;
pol 9 s;
ia 1 ~x0_1 >= 1 : 13;
deld 13;
pol 1;
rup >= 1 : 10 8 2;
output NONE ;
conclusion UNSAT : 16;
end pseudo-Boolean proof;
"

theorem k2e2_accepted : checkSubgraphIso k2Text e2Text k2e2Proof = some false := by
  decide +kernel

/-- **End to end from LAD text, `UNSAT`**, with the solver's proof. -/
example : ∃ gp gt, parseLAD k2Text = some gp ∧ parseLAD e2Text = some gt ∧
    ¬ gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, h⟩ := isContained_iff_of_checkSubgraphIso k2e2_accepted
  exact ⟨gp, gt, hp, ht, fun hc => absurd (h.1 hc) (by decide)⟩

-- With the hint of its first implication changed to a constraint that does not imply it (the
-- at-least-one constraint of the vertex `0`), the proof is rejected.
example : checkSubgraphIso k2Text e2Text "pseudo-Boolean proof version 3.0\nf 10;\npol 7 s;\n\
    ia 1 ~x0_0 >= 1 : 1;\noutput NONE ;\nconclusion NONE;\nend pseudo-Boolean proof;\n" =
    none := by
  decide +kernel

/-- The solver's proof that `K₂` has a copy in the path, `0 ↦ 2` and `1 ↦ 1`, elaborated by
VeriPB, with its `solx` replaced by `sol`. -/
def k2p3Proof : String := "pseudo-Boolean proof version 3.0
f 13;
sol ~x0_0 ~x0_1 x0_2 ~x1_0 x1_1 ~x1_2;
output NONE ;
conclusion SAT;
end pseudo-Boolean proof;
"

theorem k2p3_accepted : checkSubgraphIso k2Text p3Text k2p3Proof = some true := by
  decide +kernel

/-- **End to end from LAD text, `SAT`**, with the solver's proof. -/
example : ∃ gp gt, parseLAD k2Text = some gp ∧ parseLAD p3Text = some gt ∧
    gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, h⟩ := isContained_iff_of_checkSubgraphIso k2p3_accepted
  exact ⟨gp, gt, hp, ht, h.2 rfl⟩

/-! ### Maximum clique -/

/-- The triangle `{1, 2, 3}` with the pendant vertex `4` on `3`. -/
def g4Text : String := "p edge 4 4\ne 1 2\ne 1 3\ne 2 3\ne 3 4\n"

/-- The solver's proof that the graph has clique number `3`, elaborated by VeriPB: it logs the
cliques `{2}` and `{1, 2, 3}`, and refutes a clique of four vertices with a non-edge
constraint. -/
def g4Proof : String := "pseudo-Boolean proof version 3.0
f 2;
soli ~x1 x2 ~x3 ~x4;
soli x1 x2 x3 ~x4;
rup 1 ~x2 >= 1 : 4 2;
pol 1 4 +;
rup 1 ~x1 1 ~x2 1 ~x3 1 ~x4 >= 1 : 4 5;
output NONE ;
conclusion BOUNDS 1 : 6 1;
end pseudo-Boolean proof;
"

theorem g4_accepted : checkClique g4Text g4Proof = some (3, 3) := by decide +kernel

/-- **The clique number of a DIMACS graph**, with the solver's proof. -/
example : ∃ g, parseDIMACSGraph g4Text = some g ∧ g.graph.cliqueNum = 3 :=
  cliqueNum_eq_of_checkClique g4_accepted

end CslibFrontierTests.Logics.Propositional.VeriPBGlasgowDecide
