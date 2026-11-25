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
    edge-mapping constraints, in CakePB's order; CakePB writes the per-pattern has_mapping_am1 \
    rows with ≤ and they are printed here in their normalized ≥ form, while its per-target \
    one_one rows are already ≥ rows over negated literals; an at-most-one row (has_mapping_am1 \
    or one_one) with no literal, for p = 0 or t = 0, has degree 0 here and -1 in CakePB, both \
    trivial, while an empty has_mapping_al1 row, for t = 0, is 0 ≥ 1, of degree 1 in both) \
    exactly when it is the graph of \
    some f : P.Copy T, so the constraints are satisfiable exactly when P.IsContained T. \
    CakePB's has_subgraph_iso (an injective map sending edges to edges, non-induced) is \
    SimpleGraph.IsContained, not the induced embedding P ↪g T, and SimpleGraph (Fin n) is the \
    loop-free part of CakePB's good_graph model (a symmetric edge set on vertices below n, \
    where CakePB also allows loops). Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7944#pullrequestreview-6024571013"

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
    CakePB accepts; on an accepted text it gives the same adjacency relation as CakePB, though \
    it keeps the neighbour lists as written (a repeated neighbour included) where CakePB stores \
    sets, and the simple graph of a graph it reads has exactly the edges listed \
    (adj_iff_of_parseLAD, in Graph/Lad.lean). The encoding is printed with CakePB's variable \
    names xa_u and constraint order, so kernel proofs for cake_pb_iso's encoding (such as the \
    Glasgow Subgraph Solver's, elaborated by VeriPB) are read unchanged. No theorem relates the \
    Lean checker to CakePB's; acceptance of the same proofs by cake_pb_iso was checked only on \
    the test fixtures: five written by hand, two of which have trivial empty at-most-one rows \
    (degree 0 here, -1 in CakePB), the empty-target one's UNSAT proof using its empty \
    at-least-one row 0 ≥ 1, of degree 1 in both; and two proofs of the Glasgow Subgraph \
    Solver. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7944#pullrequestreview-6024571013"
