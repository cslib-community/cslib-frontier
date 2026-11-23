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
    { paper := CLRS2009, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.DFS.Graph.inputFits_encodeCSR,
    Cslib.Algorithms.WordRAM.DFS.topoCode_spec,
    Cslib.Algorithms.WordRAM.DFS.computesListInTime_topoProgram
  ]
  scope := "Standard-basis Word-RAM (Cslib.WordRAM.Basis.standard) iterative explicit-stack \
    depth-first search on a directed multigraph G : Graph given in the CSR input encoding \
    Graph.encodeCSR ([n, m, offsets, arcs]). At every word width w with \
    Fits w G.wordBound (16 * (n + m + 1)), topoProgram outputs topoWords G, the pure \
    Cslib.Algorithms.Lean.DFS.topologicalSort of G (reverse DFS finishing order), within \
    128 * (n + m + 1) instructions; by isTopologicalOrder_topologicalSort_iff this is a \
    topological order exactly when G is acyclic. No acyclicity flag is output."

register_result "kosaraju-scc-wordram" where
  title := "Kosaraju's strongly connected components in O(n + m) word-RAM instructions"
  topic := "algorithms"
  sources := [
    { paper := CLRS2009, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.DFS.sccIndexCode_spec,
    Cslib.Algorithms.WordRAM.DFS.sccCode_spec,
    Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram
  ]
  scope := "Standard-basis Word-RAM two-pass Kosaraju algorithm (forward explicit-stack DFS, CSR \
    transpose, and peeling in reverse finishing order) on the CSR input encoding \
    Graph.encodeCSR. At every word width w with Fits w G.wordBound, sccProgram outputs \
    sccWords G, the topological component index indexComponents (sccs G.adj (List.finRange n)) v \
    of each vertex v, within 256 * (n + m + 1) instructions."
