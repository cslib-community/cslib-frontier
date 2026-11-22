/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Sparse
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet.Sparse
public import CslibFrontier.Computability.Complexity.Problems.VertexCover

/-!
# Subexponential-time reductions from 3-SAT to graph problems

Classic linear-size polynomial-time reductions from `ThreeSAT` transfer subexponential-time
deciders for graph problems unconditionally to subexponential-time deciders for `ThreeSAT` in clause
count (`List.length`) [ImpagliazzoPaturiZane2001] [CyganEtAl2015, Chapter 14]
[LokshtanovMarxSaurabh2011]: any `2 ^ o(|V| + |E|)` decider for 3-coloring, independent set, vertex
cover, or Hamiltonian paths and cycles (directed or undirected), and any `2 ^ o(|V|)` decider for
independent set or clique, yields `DecidableInSubexpTime ThreeSAT encCNF List.length`
(`Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_reduction`):

* for 3-coloring, the gadget reduction `Cslib.Complexity.SAT.toThreeColoring`, whose graph has at
  most `(24 k + 12) m + 9` vertices and edges on clauses of at most `k` literals
  (`Cslib.Complexity.SAT.length_toThreeColoring_le`);
* for independent set, the reduction with variable edges
  `Cslib.Complexity.SAT.toSparseIndependentSet`, with at most `(k ^ 2 + 5 k) m`
  (`Cslib.Complexity.SAT.length_toSparseIndependentSet_le`). Karp's reduction
  `Cslib.Complexity.SAT.toIndependentSet` has at most `3 m` vertices on formulas with clauses of
  at most three literals, but can have quadratically many edges;
* for vertex cover, the same graph with the complementary target
  (`Cslib.Complexity.IndependentSet.toVertexCover`);
* for clique, the complement of the same graph on its vertices (`Cslib.Complexity.Graph.compl`),
  which has as many vertices but can have quadratically many edges;
* for Hamiltonian paths and cycles, the diamond construction with one slot for each occurrence of
  a variable (`Cslib.Complexity.SAT.toSparseDirHamPath`), with at most `(23 k + 1) m + 1`
  vertices and arcs (`Cslib.Complexity.SAT.length_sparseDiamondGraph_le`), closed into a cycle
  and split into an undirected graph (`Cslib.Complexity.SAT.toSparseHamCycle`); for undirected
  paths, the vertex splitting of the path instance (`Cslib.Complexity.DirHamPath.toHamPath`).
  Sipser's construction `Cslib.Complexity.SAT.toDirHamPath` gives every row a pair of nodes for
  each clause, so it has up to `Θ(m ^ 2)` vertices and arcs.

A graph (`Cslib.Complexity.Graph`) is a list of declared vertices and a list of edges, and the
measures `|V|` and `|E|` are the lengths of these lists. Because `CountingNativeEndpoint.not_ETH`
refutes `ETH` in this library's native machine model, we state these results as unconditional
subexponential-time transfers rather than vacuous `ETH → ¬DecidableInSubexpTime …` implications.

## Main results

* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_reduction`: general subexponential-time
  transfer to `ThreeSAT` along a linear-size polynomial-time reduction on 3-CNF formulas.
* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_ThreeColoring`: `2 ^ o(|V| + |E|)` transfer
  from 3-coloring.
* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_IndependentSet`,
  `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_IndependentSet_vertices`: `2 ^ o(|V| + |E|)`
  and `2 ^ o(|V|)` transfers from independent set.
* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_VertexCover`: `2 ^ o(|V| + |E|)` transfer
  from vertex cover.
* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_Clique`: `2 ^ o(|V|)` transfer from clique.
* `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_HamCycle`,
  `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_HamPath`,
  `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_DirHamCycle`,
  `Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_DirHamPath`: `2 ^ o(|V| + |E|)` transfers
  from Hamiltonian cycles and paths, undirected or directed.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Lower bounds based on the Exponential Time
  Hypothesis*][LokshtanovMarxSaurabh2011]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Subexponential-time transfers to `ThreeSAT` -/

/-- **Subexponential-time transfer from 3-coloring in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]: deciding `ThreeColoring` in time `2 ^ o(|V| + |E|)` decides `ThreeSAT`
in time `2 ^ o(m)`. -/
theorem DecidableInSubexpTime.threeSAT_of_ThreeColoring
    (h : DecidableInSubexpTime ThreeColoring encGraph
      fun G => G.vertices.length + G.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction SAT.computableInPolyTime_toThreeColoring
    -- `(24 * 3 + 12) m + 9 ≤ 93 m + 93`
    (fun φ _ => SAT.toThreeColoring_mem_iff φ) (k := 93) fun φ hφ => by
      have := SAT.length_toThreeColoring_le hφ
      nlinarith

/-- **Subexponential-time transfer from independent set in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_IndependentSet
    (h : DecidableInSubexpTime IndependentSet encIndependentSetInstance
      fun x => x.graph.vertices.length + x.graph.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction SAT.computableInPolyTime_toSparseIndependentSet
    (fun φ _ => SAT.toSparseIndependentSet_mem_iff φ) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- **Subexponential-time transfer from independent set in `|V|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_IndependentSet_vertices
    (h : DecidableInSubexpTime IndependentSet encIndependentSetInstance
      fun x => x.graph.vertices.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction SAT.computableInPolyTime_toSparseIndependentSet
    (fun φ _ => SAT.toSparseIndependentSet_mem_iff φ) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- **Subexponential-time transfer from vertex cover in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_VertexCover
    (h : DecidableInSubexpTime VertexCover encVertexCoverInstance
      fun x => x.graph.vertices.length + x.graph.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction
    (IndependentSet.computableInPolyTime_toVertexCover.comp
      SAT.computableInPolyTime_toSparseIndependentSet)
    (fun φ _ => (IndependentSet.toVertexCover_mem_iff _).trans
      (SAT.toSparseIndependentSet_mem_iff φ)) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Function.comp_apply, IndependentSet.toVertexCover] at this ⊢
      omega

/-- **Subexponential-time transfer from clique in `|V|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_Clique
    (h : DecidableInSubexpTime Clique encCliqueInstance fun x => x.graph.vertices.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction
    (computableInPolyTime_independentSetToClique.comp
      SAT.computableInPolyTime_toSparseIndependentSet)
    (fun φ _ => (independentSetToClique_mem_iff _).trans (SAT.toSparseIndependentSet_mem_iff φ))
    (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Function.comp_apply, independentSetToClique, Graph.compl] at this ⊢
      omega

/-- **Subexponential-time transfer from Hamiltonian cycle in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_HamCycle
    (h : DecidableInSubexpTime HamCycle encGraph fun G => G.vertices.length + G.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction SAT.computableInPolyTime_toSparseHamCycle
    (fun φ _ => SAT.toSparseHamCycle_mem_iff φ) (k := 350) fun φ hφ => by
      have := SAT.length_toSparseHamCycle_le hφ
      omega

/-- **Subexponential-time transfer from directed Hamiltonian cycle in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_DirHamCycle
    (h : DecidableInSubexpTime DirHamCycle encGraph fun G => G.vertices.length + G.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction SAT.computableInPolyTime_toSparseDirHamCycle
    (fun φ _ => SAT.toSparseDirHamCycle_mem_iff φ) (k := 70) fun φ hφ => by
      have := SAT.length_toSparseDirHamCycle_le hφ
      omega

/-- **Subexponential-time transfer from directed Hamiltonian path in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_DirHamPath
    (h : DecidableInSubexpTime DirHamPath encPathInstance
      fun x => x.graph.vertices.length + x.graph.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction SAT.computableInPolyTime_toSparseDirHamPath
    (fun φ _ => SAT.toSparseDirHamPath_mem_iff φ) (k := 70) fun φ hφ => by
      have := SAT.length_sparseDiamondGraph_le hφ
      simp only [SAT.toSparseDirHamPath]
      omega

/-- **Subexponential-time transfer from Hamiltonian path in `|V| + |E|` to `ThreeSAT`**
[CyganEtAl2015, Chapter 14]. -/
theorem DecidableInSubexpTime.threeSAT_of_HamPath
    (h : DecidableInSubexpTime HamPath encPathInstance
      fun x => x.graph.vertices.length + x.graph.edges.length) :
    DecidableInSubexpTime ThreeSAT encCNF List.length :=
  h.threeSAT_of_reduction
    (DirHamPath.computableInPolyTime_toHamPath.comp
      SAT.computableInPolyTime_toSparseDirHamPath)
    (fun φ _ => (DirHamPath.toHamPath_mem_iff _).trans (SAT.toSparseDirHamPath_mem_iff φ))
    (k := 350) fun φ hφ => by
      have := SAT.length_sparseDiamondGraph_le hφ
      simp only [Function.comp_apply, DirHamPath.toHamPath, SAT.toSparseDirHamPath,
        Graph.length_split_fst, Graph.length_split_snd]
      omega

end Cslib.Complexity
