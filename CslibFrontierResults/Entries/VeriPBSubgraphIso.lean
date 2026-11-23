/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.SubgraphIso

/-!
# Collected results: the verified subgraph isomorphism encoding of CakePB
-/

register_result "cakepb-subgraph-iso-encode-correct" where
  title := "CakePB's subgraph isomorphism encoding: its solutions are the copies of the pattern"
  topic := "propositional logic"
  sources := [
    { paper := GochtMcCreeshMyreenNordstromOertelTan2024,
      theorem := "Figure 2 (has_subgraph_iso) and §3.2, the subgraph isomorphism encoder \
        (CakeML encode_correct)",
      locator := "Figure 2, p. 8039; §3.2, p. 8041; CakeML 14856fcf, \
        examples/pseudo_bool/graph_encoding/subgraph_isoScript.sml (has_subgraph_iso_def, \
        encode_def, encode_correct, full_encode_correct)" }
  ]
  theorems := [
    Cslib.Logic.PL.VeriPB.Graph.forall_holds_isoConstraints_iff,
    Cslib.Logic.PL.VeriPB.Graph.exists_holds_isoConstraints_iff
  ]
  scope := "For all p, t and graphs P : SimpleGraph (Fin p), T : SimpleGraph (Fin t) with \
    decidable adjacency, an assignment satisfies isoConstraints P T (CakePB's encode: \
    at-least-one and at-most-one per pattern vertex, at-most-one per target vertex, and the \
    edge-mapping constraints, in CakePB's order, the at-most-one constraints in their \
    normalized ≥ form) exactly when it is the graph of some f : P.Copy T, so the constraints \
    are satisfiable exactly when P.IsContained T. CakePB's has_subgraph_iso (an injective map \
    sending edges to edges, non-induced) is SimpleGraph.IsContained, not the induced \
    embedding P ↪g T, and good_graph is the type SimpleGraph (Fin n)."

register_result "cakepb-subgraph-iso-of-check" where
  title := "Subgraph isomorphism from a VeriPB proof accepted against CakePB's encoding"
  topic := "propositional logic"
  sources := [
    { paper := GochtMcCreeshMyreenNordstromOertelTan2024,
      theorem := "§3.3, the CakePBGraph checkers (stated in the paper for clique only; CakeML \
        full_encode_sem_concl and check_unsat_3_sem for subgraph isomorphism)",
      locator := "§3.3, p. 8042; CakeML 14856fcf, \
        examples/pseudo_bool/graph_encoding/subgraph_isoScript.sml (full_encode_sem_concl), \
        graph_basicScript.sml (parse_lad, check_good_graph) and \
        examples/pseudo_bool/array/subgraph_isoProgScript.sml (check_unsat_3_sem_def)" }
  ]
  theorems := [
    Cslib.Logic.PL.VeriPB.Graph.isContained_iff_of_checkSubgraphIsoGraph,
    Cslib.Logic.PL.VeriPB.Graph.isContained_iff_of_checkSubgraphIso
  ]
  scope := "Pure functional statements: if the Lean VeriPB checker accepts a proof text against \
    the printed OPB encoding of P and T (or of the graphs read from two LAD texts by parseLAD) \
    with the conclusion SAT, the result true, or UNSAT, the result false, then P.IsContained T \
    holds exactly when the result is true. This is check_unsat_3_sem, not CakePB's \
    main_semantics, a theorem about the compiled x64 machine code, its file and command-line \
    I/O and its output strings, none of which is covered. The LAD reader accepts exactly the \
    texts CakePB's parse_lad and check_good_graph accept, except that it rejects a loop, which \
    CakePB accepts; the simple graph of a graph it reads has exactly the edges listed \
    (adj_iff_of_parseLAD, in Graph/Lad.lean)."
