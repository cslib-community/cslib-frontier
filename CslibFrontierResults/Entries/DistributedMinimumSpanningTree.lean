/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Distributed.MinimumSpanningTree.BlueRule

register_result "gallager-humblet-spira-blue-rule-mst-uniqueness" where
  title := "Minimum-weight outgoing cut property and distinct-weight minimum spanning tree \
    uniqueness on finite simple graphs"
  topic := "distributed computing"
  sources := [
    { paper := GallagerHumbletSpira1983,
      theorem := "Property 1 and Property 2",
      locator := "§2, printed p. 68 (PDF p. 3)" }
  ]
  theorems := [
    Cslib.Distributed.MinimumSpanningTree.IsMST.exists_sup_edge_of_isMOE,
    Cslib.Distributed.MinimumSpanningTree.IsMOE.mem_edgeSet_of_isMST_of_injOn,
    Cslib.Distributed.MinimumSpanningTree.IsMST.eq_of_injOn,
    Cslib.Distributed.MinimumSpanningTree.existsUnique_isMST_of_injOn
  ]
  scope := "Undirected simple graphs G : SimpleGraph V over finite vertex types [Finite V] \
    (plus G.Connected for existence in existsUnique_isMST_of_injOn) with edge weights \
    w : Sym2 V → W in a linearly ordered cancellative additive commutative monoid W and \
    spanning-tree objective edgeWeightSum T w = ∑ᶠ e ∈ T.edgeSet, w e. \
    IsMST.exists_sup_edge_of_isMOE proves Property 1 without distinct weights: extending any \
    subgraph H ≤ T with edges internal to S : Finset V of an MST T by any minimum-weight \
    outgoing edge s(u, v) of S yields a subgraph of an MST T'. Under Set.InjOn w G.edgeSet, \
    IsMOE.mem_edgeSet_of_isMST_of_injOn, IsMST.eq_of_injOn, and existsUnique_isMST_of_injOn \
    prove that every cut-MOE belongs to every MST and that the MST is unique (Property 2). \
    The companion event-driven fragment-phase GHS protocol and 5 N log₂ N + 2 E message bound \
    in Computability.Distributed.MinimumSpanningTree.GHS remain unregistered as a milestone \
    step toward #7508."
