/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso
import Mathlib.Combinatorics.SimpleGraph.Hasse
-- `import all`: the kernel evaluates the LAD reader and its private helpers, `printOPB` and its
-- private word builders, the parsers and checkers of `Text` and the step `stepTop` of
-- `Redundance`, whose bodies are not exposed, and the unexposed checkers of `SubgraphIso`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Lad
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Subgraph isomorphism end to end, checked by the kernel.

* The LAD reader on accepted and rejected texts. Each verdict is the one of CakePB's `cake_pb_iso`
  (CakeML `14856fcf`) on the same text, except for the loop, which CakePB accepts.
* The encoding of the edge `K₂` into the path `0 - 1 - 2`, printed: it is CakePB's
  (`cake_pb_iso` prints the same constraints in the same order, with the same variable names
  `xa_u`, with labels `@al10 …`, and with the per-pattern at-most-one constraints as `… <= 1`;
  its per-target `@inj` constraints are the `>=` constraints printed here).
* **Clients**, with proofs written by hand in the kernel format: `K₂` has a copy in the path
  (`SAT`, with the copy `0 ↦ 0`, `1 ↦ 1`); `K₂` has none in the graph with two vertices and no
  edge (`UNSAT`: summing `x₀₀ + x₀₁ ≥ 1`, `~x₀₀ ≥ 1` and `~x₀₁ ≥ 1` gives `0 ≥ 1`); the triangle
  has none in `K₂` (`UNSAT`: the sum of the three at-least-one constraints and the two injectivity
  constraints is `0 ≥ 1`); the empty pattern has a copy in `K₂`; a pattern vertex has none in
  the empty target. Each is accepted against the LAD texts and the first three against Mathlib's
  graphs.

VeriPB 3.0.2 accepts the five client proofs against the printed encoding, and `veripb --elaborate`
returns them unchanged up to spacing. CakePB's `cake_pb_iso` accepts the same five against the LAD
texts, reporting `SUBGRAPH ISOMORPHIC` or `NOT SUBGRAPH ISOMORPHIC` as here. In the last two the
at-most-one rows without a literal differ: `>= 0` here, `>= -1` for CakePB's `@inj0` and `@inj1`
(empty pattern) and `<= 1` for its `@am10` (empty target). The empty target's at-least-one row
`@al10` has no literal either but is `>= 1` in both; it is the constraint `1` of the `UNSAT` proof.
Proofs of the Glasgow Subgraph Solver, elaborated by VeriPB and accepted by CakePB, are checked in
`CslibFrontierTests.Logics.Propositional.VeriPBGlasgowDecide`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBSubgraphIsoDecide

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text Cslib.Logic.PL.VeriPB.Graph

/-! ### The LAD reader -/

/-- The edge `K₂`. -/
def k2Text : String := "2\n1 1\n1 0\n"

/-- The path `0 - 1 - 2`. -/
def p3Text : String := "3\n1 1\n2 0 2\n1 1\n"

/-- Two vertices, no edge. -/
def e2Text : String := "2\n0\n0\n"

/-- The triangle. -/
def k3Text : String := "3\n2 1 2\n2 0 2\n2 0 1\n"

example : parseLAD k2Text = some ⟨2, [[1], [0]]⟩ := by decide +kernel
example : parseLAD p3Text = some ⟨3, [[1], [0, 2], [1]]⟩ := by decide +kernel

-- Accepted: no final newline; spaces, tabs and carriage returns; leading zeros; a repeated
-- neighbour; fewer vertex lines than vertices; no vertex at all.
example : parseLAD "2\n1 1\n1 0" = some ⟨2, [[1], [0]]⟩ := by decide +kernel
example : parseLAD "  2 \n\t1  1\r\n1 0\n" = some ⟨2, [[1], [0]]⟩ := by decide +kernel
example : parseLAD "02\n1 01\n1 0\n" = some ⟨2, [[1], [0]]⟩ := by decide +kernel
example : parseLAD "2\n2 1 1\n1 0\n" = some ⟨2, [[1, 1], [0]]⟩ := by decide +kernel
example : parseLAD "3\n1 1\n1 0\n" = some ⟨3, [[1], [0]]⟩ := by decide +kernel
example : parseLAD "0\n" = some ⟨0, []⟩ := by decide +kernel

-- Rejected: a blank line, in the middle or at the end; neighbours listed in one direction only;
-- a neighbour beyond `n`; more vertex lines than vertices; a wrong count; a header of two
-- numbers; a digit separator; an empty text.
example : parseLAD "2\n1 1\n\n1 0\n" = none := by decide +kernel
example : parseLAD "2\n1 1\n1 0\n\n\n" = none := by decide +kernel
example : parseLAD "2\n1 1\n0\n" = none := by decide +kernel
example : parseLAD "2\n1 2\n1 0\n" = none := by decide +kernel
example : parseLAD "2\n1 1\n1 0\n0\n" = none := by decide +kernel
example : parseLAD "2\n2 1\n1 0\n" = none := by decide +kernel
example : parseLAD "2 0\n1 1\n1 0\n" = none := by decide +kernel
example : parseLAD "2\n1 1_0\n1 0\n" = none := by decide +kernel
example : parseLAD "" = none := by decide +kernel

-- Rejected here, accepted by CakePB: the loop on `0`.
example : parseLAD "2\n2 0 1\n1 0\n" = none := by decide +kernel

/-! ### The encoding -/

-- `K₂` into the path `0 - 1 - 2`, in CakePB's order.
example : printOPB ⟨isoConstraints (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph 3), none,
    none⟩ (isoNames 2 3) = "* #variable= 6 #constraint= 13 \n\
    1 x0_0 1 x0_1 1 x0_2 >= 1 ; \n1 x1_0 1 x1_1 1 x1_2 >= 1 ; \n\
    1 ~x0_0 1 ~x0_1 1 ~x0_2 >= 2 ; \n1 ~x1_0 1 ~x1_1 1 ~x1_2 >= 2 ; \n\
    1 ~x0_0 1 ~x1_0 >= 1 ; \n1 ~x0_1 1 ~x1_1 >= 1 ; \n1 ~x0_2 1 ~x1_2 >= 1 ; \n\
    1 ~x0_0 1 x1_1 >= 1 ; \n1 ~x1_0 1 x0_1 >= 1 ; \n\
    1 ~x0_1 1 x1_0 1 x1_2 >= 1 ; \n1 ~x1_1 1 x0_0 1 x0_2 >= 1 ; \n\
    1 ~x0_2 1 x1_1 >= 1 ; \n1 ~x1_2 1 x0_1 >= 1 ; \n" := by
  decide +kernel

-- The graphs read from LAD have the encodings of Mathlib's.
example : (parseLAD k2Text).map (fun gp => (parseLAD p3Text).map fun gt =>
    isoConstraints gp.graph gt.graph) =
    some (some (isoConstraints (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph 3))) := by
  decide +kernel

/-! ### Clients -/

/-- **`K₂` has a copy in the path**: the assignment of the copy `0 ↦ 0`, `1 ↦ 1`. -/
def k2p3Proof : String := "pseudo-Boolean proof version 3.0
f 13;
output NONE;
conclusion SAT : x0_0 ~x0_1 ~x0_2 ~x1_0 x1_1 ~x1_2 ;
end pseudo-Boolean proof;
"

theorem k2p3_accepted :
    checkSubgraphIsoGraph (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph 3) k2p3Proof =
      some true := by
  decide +kernel

example : (⊤ : SimpleGraph (Fin 2)).IsContained (SimpleGraph.pathGraph 3) :=
  (isContained_iff_of_checkSubgraphIsoGraph k2p3_accepted).2 rfl

theorem k2p3Text_accepted : checkSubgraphIso k2Text p3Text k2p3Proof = some true := by
  decide +kernel

/-- **End to end from LAD text, `SAT`**: both texts parse, and the pattern read has a copy in the
target read. -/
example : ∃ gp gt, parseLAD k2Text = some gp ∧ parseLAD p3Text = some gt ∧
    gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, h⟩ := isContained_iff_of_checkSubgraphIso k2p3Text_accepted
  exact ⟨gp, gt, hp, ht, h.2 rfl⟩

/-- **`K₂` has no copy in two vertices without an edge**: the at-least-one constraint of the
vertex `0` and its two edge constraints `~x₀ᵤ ≥ 1` sum to `0 ≥ 1`. -/
def k2e2Proof : String := "pseudo-Boolean proof version 3.0
f 10;
pol 1 7 + 9 +;
output NONE;
conclusion UNSAT : 11;
end pseudo-Boolean proof;
"

theorem k2e2_accepted :
    checkSubgraphIsoGraph (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) k2e2Proof =
      some false := by
  decide +kernel

example : ¬ (⊤ : SimpleGraph (Fin 2)).IsContained (⊥ : SimpleGraph (Fin 2)) := fun h =>
  absurd ((isContained_iff_of_checkSubgraphIsoGraph k2e2_accepted).1 h) (by decide)

theorem k2e2Text_accepted : checkSubgraphIso k2Text e2Text k2e2Proof = some false := by
  decide +kernel

/-- **End to end from LAD text, `UNSAT`**: both texts parse, and the pattern read has no copy in
the target read. -/
example : ∃ gp gt, parseLAD k2Text = some gp ∧ parseLAD e2Text = some gt ∧
    ¬ gp.graph.IsContained gt.graph := by
  obtain ⟨gp, gt, hp, ht, h⟩ := isContained_iff_of_checkSubgraphIso k2e2Text_accepted
  exact ⟨gp, gt, hp, ht, fun hc => absurd (h.1 hc) (by decide)⟩

/-- **The triangle has no copy in `K₂`**: the three at-least-one constraints say
`∑ xₐᵤ ≥ 3` and the two injectivity constraints `∑ ~xₐᵤ ≥ 4`, over the six variables. -/
def k3k2Proof : String := "pseudo-Boolean proof version 3.0
f 20;
pol 1 2 + 3 + 7 + 8 +;
output NONE;
conclusion UNSAT : 21;
end pseudo-Boolean proof;
"

theorem k3k2_accepted :
    checkSubgraphIsoGraph (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 2)) k3k2Proof =
      some false := by
  decide +kernel

example : ¬ (⊤ : SimpleGraph (Fin 3)).IsContained (⊤ : SimpleGraph (Fin 2)) := fun h =>
  absurd ((isContained_iff_of_checkSubgraphIsoGraph k3k2_accepted).1 h) (by decide)

example : checkSubgraphIso k3Text k2Text k3k2Proof = some false := by decide +kernel

/-! ### Boundaries -/

-- The empty pattern has a copy in `K₂`: the encoding is the two trivial injectivity
-- constraints, and the empty solution is logged.
example : printOPB ⟨isoConstraints (⊥ : SimpleGraph (Fin 0)) (⊤ : SimpleGraph (Fin 2)), none,
    none⟩ = "* #variable= 0 #constraint= 2 \n>= 0 ; \n>= 0 ; \n" := by
  decide +kernel
example : checkSubgraphIso "0\n" k2Text "pseudo-Boolean proof version 3.0\nf 2;\nsol ;\n\
    output NONE;\nconclusion SAT;\nend pseudo-Boolean proof;\n" = some true := by
  decide +kernel

-- A pattern vertex has no copy in the empty target: its at-least-one constraint is `0 ≥ 1`.
example : checkSubgraphIso "1\n0\n" "0\n" "pseudo-Boolean proof version 3.0\nf 2;\n\
    output NONE;\nconclusion UNSAT : 1;\nend pseudo-Boolean proof;\n" = some false := by
  decide +kernel

-- A proof with another conclusion gives no answer; a wrong proof is rejected.
example : checkSubgraphIso k2Text p3Text "pseudo-Boolean proof version 3.0\nf 13;\n\
    output NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n" = none := by decide +kernel
example : checkSubgraphIso k2Text p3Text k2e2Proof = none := by decide +kernel

-- A text the reader rejects gives no answer, even with a proof that would be accepted for the
-- graph with its loop dropped.
example : checkSubgraphIso "2\n2 0 1\n1 0\n" p3Text k2p3Proof = none := by decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBSubgraphIsoDecide
