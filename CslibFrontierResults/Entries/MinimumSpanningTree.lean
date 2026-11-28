/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.Driver
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MinimumSpanningTree

register_result "gallager-humblet-spira-blue-rule-mst-uniqueness" where
  title := "Minimum-weight outgoing cut property and distinct-weight minimum spanning tree \
    uniqueness on finite simple graphs"
  topic := "graph algorithms"
  sources := [
    { paper := GallagerHumbletSpira1983,
      theorem := "Property 1 and Property 2",
      locator := "§2, printed p. 68 (PDF p. 3)" }
  ]
  theorems := [
    SimpleGraph.IsMST.exists_sup_edge_of_isMOE,
    SimpleGraph.IsMOE.mem_edgeSet_of_isMST_of_injOn,
    SimpleGraph.IsMST.eq_of_injOn,
    SimpleGraph.existsUnique_isMST_of_injOn
  ]
  scope := "Undirected simple graphs G : SimpleGraph V over finite vertex types [Finite V] \
    (plus G.Connected for existence in SimpleGraph.existsUnique_isMST_of_injOn) with edge weights \
    w : Sym2 V → W in a linearly ordered cancellative additive commutative monoid W and \
    spanning-tree objective SimpleGraph.edgeWeightSum T w = ∑ᶠ e ∈ T.edgeSet, w e. \
    SimpleGraph.IsMST.exists_sup_edge_of_isMOE proves Property 1 without distinct weights: \
    extending any subgraph H ≤ T with edges internal to S : Finset V of an MST T by any \
    minimum-weight outgoing edge s(u, v) of S yields a subgraph of an MST T'. Under \
    Set.InjOn w G.edgeSet, SimpleGraph.IsMOE.mem_edgeSet_of_isMST_of_injOn, \
    SimpleGraph.IsMST.eq_of_injOn, and SimpleGraph.existsUnique_isMST_of_injOn prove that every \
    cut-MOE belongs to every MST and that the MST is unique (Property 2), bridged to sequential \
    Kruskal in Algorithms.Lean.Kruskal.SimpleGraph.kruskalGraph_isMST. The companion event-driven \
    fragment-phase GHS protocol and 5 N log₂ N + 2 E message bound in \
    Computability.Distributed.MinimumSpanningTree.GHS remain unregistered as a milestone step \
    toward #7508."

register_result "pettie-ramachandran-optimal-mst-wordram" where
  title := "Optimal deterministic minimum spanning tree on the word RAM"
  topic := "graph algorithms"
  sources := [
    { paper := PettieRamachandran2002,
      theorem := "Proposition 5.1 and Theorem 5.8",
      locator := "JACM 49(1), §2, p. 18 and §5.1, pp. 25–27" }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSF_simpleGraph_isMST_spec
  ]
  scope := "One deterministic, width-blind (¬prog.ReadsWidth), random-free (prog.IsRandFree) \
    standard-basis Word-RAM program (Cslib.WordRAM.Basis.standard) independent of the word \
    width w. Given a connected undirected simple graph G : SimpleGraph (Fin n) with \
    m = G.edgeFinset.card edges and word-representable natural weights wt : Sym2 (Fin n) → ℕ \
    (allowing ties) encoded via Kruskal.encode (graphEdges G wt), for every word width w \
    satisfying Fits w (optimalMSFWordBound n m) (logarithmic width suffices for the workspace \
    threshold, with the additional Fits w condition for edge weights, and any larger width is \
    allowed), ExecutesList halts in at most C * (optDepthMN m n + 1) instructions and outputs \
    Kruskal.encodeEdges msfEs for a SimpleGraph.IsMST of G, where optDepthMN m n agrees with \
    exact-(m, n) decision-tree depth via optDepthMN_eq_exact. The companion raw-multigraph \
    driver theorem optimalMSF_wordRAM_spec outputs a minimum spanning forest in \
    C * (optDepthMN m n + m + n + 1) instructions (covering m > n.choose 2 saturation and \
    isolated vertices). Unlike the paper's distinct real weights, Lean uses word-representable \
    natural weights with ties and an additive + 1 small-input term; Section 6's pointer-machine \
    realization and the downstream linear-time DLMST objective remain separate and open under \
    #8624."
