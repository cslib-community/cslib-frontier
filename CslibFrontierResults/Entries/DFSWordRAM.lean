/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.WordRAM.DFS

/-!
# Collected results: linear-time depth-first search on the word RAM
-/

register_result "topological-sort-wordram" where
  title := "Depth-first-search topological sort in O(n + m) word-RAM instructions"
  topic := "algorithms"
  sources := [
    { paper := CLRS2009, theorem := "§22.4 TOPOLOGICAL-SORT and Theorem 22.12",
      locator := "3rd ed., §22.4 TOPOLOGICAL-SORT & cost paragraph (printed p. 613) and \
        Theorem 22.12 (p. 614)" }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.DFS.Graph.inputFits_encodeCSR,
    Cslib.Algorithms.WordRAM.DFS.topoCode_spec,
    Cslib.Algorithms.WordRAM.DFS.computesListInTime_topoProgram
  ]
  scope := "Standard-basis Word-RAM (Cslib.WordRAM.Basis.standard) iterative explicit-stack \
    depth-first search on a directed multigraph G : Graph on Fin n (parallel arcs counted with \
    multiplicity) given in the CSR input encoding Graph.encodeCSR ([n, m, offsets, arcs]). At \
    every word width w with Fits w G.wordBound (where G.wordBound = 16 * (n + m + 1)), \
    topoProgram outputs topoWords G = (Cslib.Algorithms.Lean.DFS.topologicalSort G.adj \
    (List.finRange n)).map Fin.val within 128 * (n + m + 1) instructions (including halt). \
    Whereas CLRS proves correctness on DAGs, Lean returns reverse DFS finishing order on every \
    graph (with no acyclicity flag output), and by \
    Cslib.Algorithms.Lean.DFS.isTopologicalOrder_topologicalSort_iff (registered in \
    topological-sort) this order is a topological order if and only if G is acyclic."

register_result "kosaraju-scc-wordram" where
  title := "Kosaraju's strongly connected components in O(n + m) word-RAM instructions"
  topic := "algorithms"
  sources := [
    { paper := CLRS2009, theorem := "§22.5 STRONGLY-CONNECTED-COMPONENTS and Theorem 22.16",
      locator := "3rd ed., §22.5 STRONGLY-CONNECTED-COMPONENTS & cost paragraph (p. 617), \
        Theorem 22.16 (pp. 619–620), and condensation-order paragraph (p. 620)" }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.DFS.sccIndexCode_spec,
    Cslib.Algorithms.WordRAM.DFS.sccCode_spec,
    Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram
  ]
  scope := "Standard-basis Word-RAM (Cslib.WordRAM.Basis.standard) two-pass Kosaraju algorithm \
    (forward explicit-stack DFS, CSR transpose, and peeling in reverse finishing order) on a \
    directed multigraph G : Graph on Fin n (parallel arcs counted with multiplicity) in the CSR \
    input encoding Graph.encodeCSR. At every word width w with Fits w G.wordBound (where \
    G.wordBound = 16 * (n + m + 1)), sccProgram outputs sccWords G, the component label \
    indexComponents (sccs G.adj (List.finRange n)) v of each vertex v, within \
    256 * (n + m + 1) instructions (including halt). See kosaraju-scc for the pure \
    partition and condensation-ordering bridges (isSCCCondensation_sccs, \
    IsSCCCondensation.indexComponents_eq_iff, and IsSCCCondensation.indexComponents_le_of_edge)."
