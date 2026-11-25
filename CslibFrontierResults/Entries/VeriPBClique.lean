/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Logics.Propositional.PseudoBoolean.Graph.Clique

/-!
# Collected results: the verified maximum clique encoding of CakePB
-/

register_result "cakepb-clique-encode-correct" where
  title := "CakePB's maximum clique encoding: its solutions are the cliques"
  topic := "propositional logic"
  sources := [
    { paper := GochtMcCreeshMyreenNordstromOertelTan2024,
      theorem := "§3.2, the maximum clique encoder (CakeML encode_correct)",
      locator := "§3.2, p. 8041; Figure 2, p. 8039; CakeML 14856fcf, \
        examples/pseudo_bool/graph_encoding/cliqueScript.sml (encode_correct_1, \
        encode_correct_2, encode_correct)" }
  ]
  theorems := [
    Cslib.Logic.PL.VeriPB.Graph.forall_holds_cliqueConstraints_iff,
    Cslib.Logic.PL.VeriPB.Graph.exists_chosen_eq,
    Cslib.Logic.PL.VeriPB.Graph.eval_cliqueObjective
  ]
  scope := "For every n and every graph G : SimpleGraph (Fin n) with decidable adjacency, an \
    assignment satisfies the constraints of encodeClique G (~x + ~y ≥ 1 for each non-edge \
    x < y, in CakePB's mk_constraint order) exactly when the vertices it chooses form a \
    clique; every set of vertices is chosen by some assignment; and the objective, written in \
    normal form as ∑ᵥ -xᵥ + n instead of CakePB's ∑ᵥ ~xᵥ, has value n minus the number of \
    vertices chosen. CakePB's good_graph (v, e) is the type SimpleGraph (Fin n), is_clique is \
    SimpleGraph.IsClique on a Finset, and a listed loop is dropped. The maximal clique \
    encoding (mencode_correct) is not covered. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7675#pullrequestreview-6015059703"

register_result "cakepb-clique-bounds-of-check" where
  title := "Clique bounds from a VeriPB proof accepted against CakePB's clique encoding"
  topic := "propositional logic"
  sources := [
    { paper := GochtMcCreeshMyreenNordstromOertelTan2024,
      theorem := "§3.3, the semantics clique_sem behind Figure 5 (CakeML full_encode_sem_concl \
        and full_encode_sem_concl_check)",
      locator := "§3.3, pp. 8042–8043; CakeML 14856fcf, \
        examples/pseudo_bool/graph_encoding/cliqueScript.sml (conv_concl_def, \
        full_encode_sem_concl, full_encode_sem_concl_check) and \
        examples/pseudo_bool/array/cliqueProgScript.sml (clique_sem_def)" }
  ]
  theorems := [
    Cslib.Logic.PL.VeriPB.Graph.clique_bounds_of_checkCliqueGraph,
    Cslib.Logic.PL.VeriPB.Graph.cliqueNum_eq_of_checkCliqueGraph,
    Cslib.Logic.PL.VeriPB.Graph.clique_bounds_of_checkClique,
    Cslib.Logic.PL.VeriPB.Graph.cliqueNum_eq_of_checkClique
  ]
  scope := "Pure functional statements: if the Lean VeriPB checker accepts a proof text \
    against the printed OPB encoding of G (or of the graph read from a DIMACS text) with a \
    BOUNDS conclusion that convConcl (CakePB's conv_concl) turns into (l, u), then every \
    clique has at most u vertices and some clique has at least l; equal bounds k give \
    SimpleGraph.cliqueNum = k, CakePB's max_clique_size. This is clique_sem, not Figure 5: \
    Figure 5 (main_semantics) is a theorem about the compiled x64 machine code, its file and \
    command-line I/O and its output strings, none of which is covered. The DIMACS reader \
    accepts some files that CakePB's parse_dimacs rejects (blank lines, comment words \
    starting with c, digit separators). Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7675#pullrequestreview-6015059703"
