/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
-- `import all`: the kernel evaluates the DIMACS graph reader and its private helpers, `printOPB`
-- and its private word builders, the parsers and checkers of `Text` and the step `stepTop` of
-- `Redundance`, whose bodies are not exposed.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Dimacs
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Maximum clique end to end, checked by the kernel.

* The DIMACS graph reader on accepted and rejected texts: comments, blank lines, `p col`, a loop
  and an edge listed twice are accepted; a vertex `0` or beyond `n`, a missing header, an edge
  before the header and a malformed line are rejected.
* The encoding of the 5-cycle, printed: it is CakePB's (`cake_pb_clique` prints
  `min: 1 ~x1 … ~x5 ;` and the same five constraints in the same order, with labels
  `@noedge1_3 …`).
* **Clients.** A proof written by hand that the 5-cycle has clique number `2`: log the clique
  `{1, 2}`, sum the five non-edge constraints and halve, which gives `∑ ~xᵥ ≥ 3`, and add the
  objective-improving constraint `∑ ~xᵥ ≤ 2` of the logged solution for a contradiction. It is
  accepted against Mathlib's `SimpleGraph.cycleGraph 5` and against a DIMACS text, so
  `(cycleGraph 5).cliqueNum = 2`. A second proof shows that a triangle with a pendant vertex has
  clique number `3`.

Both proofs are in the kernel format: VeriPB 3.0.2 accepts them against the printed encodings,
`veripb --elaborate` returns them unchanged, and CakePB's `cake_pb_clique` (CakeML `14856fcf`)
accepts them against the DIMACS texts, reporting `|CLIQUE| = 2` and `|CLIQUE| = 3`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBClique

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text Cslib.Logic.PL.VeriPB.Graph

/-! ### The DIMACS graph reader -/

/-- The 5-cycle `1 - 2 - 3 - 4 - 5 - 1`. -/
def c5Text : String := "c the 5-cycle\np edge 5 5\ne 1 2\ne 2 3\ne 3 4\ne 4 5\ne 5 1\n"

/-- The 5-cycle as read: the vertex `u` of the file is `u - 1`. -/
def c5 : DimacsGraph := ⟨5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]⟩

example : parseDIMACSGraph c5Text = some c5 := by decide +kernel

-- Comments, blank lines, `p col`, a loop and a repeated edge (in the other direction).
example : parseDIMACSGraph "c x\n\np col 3 9\nc y\ne 1 1\ne 1 2\n\ne 2 1\n" =
    some ⟨3, [(0, 0), (0, 1), (1, 0)]⟩ := by decide +kernel
-- The edge count of the header is not checked; a graph may have no edges.
example : parseDIMACSGraph "p edge 2 7" = some ⟨2, []⟩ := by decide +kernel

-- Rejected: vertices `0` and `n + 1`, no header, an edge before the header, a second header, a
-- malformed edge line and a malformed header.
example : parseDIMACSGraph "p edge 3 1\ne 0 1\n" = none := by decide +kernel
example : parseDIMACSGraph "p edge 3 1\ne 1 4\n" = none := by decide +kernel
example : parseDIMACSGraph "c only a comment\n" = none := by decide +kernel
example : parseDIMACSGraph "e 1 2\np edge 3 1\n" = none := by decide +kernel
example : parseDIMACSGraph "p edge 3 1\np edge 3 1\n" = none := by decide +kernel
example : parseDIMACSGraph "p edge 3 1\ne 1 2 3\n" = none := by decide +kernel
example : parseDIMACSGraph "p cnf 3 1\n" = none := by decide +kernel

-- The loop `e 1 1` is dropped: the graph is simple.
example : ¬ (⟨3, [(0, 0)]⟩ : DimacsGraph).graph.Adj 0 0 := by decide
example : (⟨3, [(1, 0)]⟩ : DimacsGraph).graph.Adj 0 1 := by decide

/-! ### The encoding -/

-- The non-edges of the 5-cycle, in CakePB's order, and the objective `∑ᵥ -xᵥ + 5`.
example : printOPB (encodeClique (SimpleGraph.cycleGraph 5)) = "* #variable= 5 #constraint= 5 \n\
    min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 5 ; \n1 ~x1 1 ~x3 >= 1 ; \n1 ~x1 1 ~x4 >= 1 ; \n\
    1 ~x2 1 ~x4 >= 1 ; \n1 ~x2 1 ~x5 >= 1 ; \n1 ~x3 1 ~x5 >= 1 ; \n" := by
  decide +kernel

-- The 5-cycle read from DIMACS has the same encoding as Mathlib's.
example : encodeClique c5.graph = encodeClique (SimpleGraph.cycleGraph 5) := by decide +kernel

/-! ### Clients -/

/-- **The clique number of the 5-cycle is `2`**: a proof written by hand in the kernel format. -/
def c5Proof : String := "pseudo-Boolean proof version 3.0
f 5;
soli x1 x2 ~x3 ~x4 ~x5;
pol 1 2 + 3 + 4 + 5 + 2 d;
pol 6 7 +;
output NONE;
conclusion BOUNDS 3 : 8 3;
end pseudo-Boolean proof;
"

theorem c5_accepted : checkCliqueGraph (SimpleGraph.cycleGraph 5) c5Proof = some (2, 2) := by
  decide +kernel

/-- **Mathlib's 5-cycle has clique number `2`**, from the acceptance of the proof. -/
example : (SimpleGraph.cycleGraph 5).cliqueNum = 2 := cliqueNum_eq_of_checkCliqueGraph c5_accepted

theorem c5Text_accepted : checkClique c5Text c5Proof = some (2, 2) := by decide +kernel

/-- **End to end from DIMACS text**: the text parses to a graph whose cliques have at most `2`
vertices, one of them `2`. -/
example : ∃ g, parseDIMACSGraph c5Text = some g ∧
    (∀ s : Finset (Fin g.n), g.graph.IsClique (s : Set (Fin g.n)) → s.card ≤ 2) ∧
    ∃ s : Finset (Fin g.n), g.graph.IsClique (s : Set (Fin g.n)) ∧ 2 ≤ s.card :=
  clique_bounds_of_checkClique c5Text_accepted

/-- A triangle `1 2 3` with the pendant vertex `4` on `3`. -/
def k3pText : String := "p edge 4 4\ne 1 2\ne 2 3\ne 1 3\ne 3 4\n"

/-- **The clique number of `k3pText` is `3`**: log the triangle; the non-edge constraint
`~x1 + ~x4 ≥ 1` plus the objective-improving constraint `x1 + x2 + x3 + x4 ≥ 4` is the
contradiction `x2 + x3 ≥ 3`. -/
def k3pProof : String := "pseudo-Boolean proof version 3.0
f 2;
soli x1 x2 x3 ~x4;
pol 1 3 +;
output NONE;
conclusion BOUNDS 1 : 4 1;
end pseudo-Boolean proof;
"

theorem k3p_parsed : parseDIMACSGraph k3pText = some ⟨4, [(0, 1), (1, 2), (0, 2), (2, 3)]⟩ := by
  decide +kernel

theorem k3p_accepted :
    checkCliqueGraph (⟨4, [(0, 1), (1, 2), (0, 2), (2, 3)]⟩ : DimacsGraph).graph k3pProof =
      some (3, 3) := by
  decide +kernel

example : ∃ g, parseDIMACSGraph k3pText = some g ∧ g.graph.cliqueNum = 3 :=
  ⟨_, k3p_parsed, cliqueNum_eq_of_checkCliqueGraph k3p_accepted⟩

-- A proof with another conclusion gives no bounds.
example : checkClique k3pText "pseudo-Boolean proof version 3.0\nf 2;\noutput NONE;\n\
    conclusion NONE;\nend pseudo-Boolean proof;\n" = none := by decide +kernel

end CslibFrontierTests.Logics.Propositional.VeriPBClique
