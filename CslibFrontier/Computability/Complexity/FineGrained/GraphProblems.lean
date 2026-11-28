/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SatisfiabilityHypothesis
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Sparse
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet.Sparse
public import CslibFrontier.Computability.Complexity.Problems.VertexCover

/-!
# Fine-grained lower bounds for graph problems

Under the Satisfiability Hypothesis (`Cslib.Complexity.SH`), the linear-size reductions
from 3SAT rule out running time `2 ^ (C * (μ + 1) ^ p)` times a polynomial in the encoded
input length, for every fixed `0 < p < 1` and constant `C`. The parameter `μ` counts the
declared vertices plus edges or arcs. For 3-coloring, independent set and clique there are
also bounds in the number of declared vertices. The reductions used are

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

The graph measures are the lengths of the vertex and edge lists. The transfer uses
`Cslib.Complexity.SH.not_decidableInPowerExpTime_of_linear_reduction`.
The ETH-based analyses of these reductions are described in [CyganEtAl2015, Chapter 14]
and [LokshtanovMarxSaurabh2011].

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

/-! ### Satisfiability Hypothesis lower bounds -/

/-- Under SH, 3-coloring has no fixed power saving below one in the exponent, measured in
the number of declared vertices and edges. -/
theorem SH.not_decidableInPowerExpTime_ThreeColoring (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime ThreeColoring encGraph
      (fun G => G.vertices.length + G.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1 SAT.computableInPolyTime_toThreeColoring
    (fun φ _ => (SAT.toThreeColoring_mem_iff φ).symm) (K := 93) fun φ hφ => by
      have := SAT.length_toThreeColoring_le hφ
      nlinarith

/-- Under SH, 3-coloring has no fixed power saving below one in the exponent measured in
the number of declared vertices. -/
theorem SH.not_decidableInPowerExpTime_ThreeColoring_vertices (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime ThreeColoring encGraph (fun x => x.vertices.length) p :=
  fun hFast => h.not_decidableInPowerExpTime_ThreeColoring hp hp1
    (hFast.mono_measure (fun _ => Nat.le_add_right _ _) hp.le)

/-- Under SH, Independent Set has no fixed power saving below one in the exponent
measured in the number of declared vertices plus edges. -/
theorem SH.not_decidableInPowerExpTime_IndependentSet (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime IndependentSet encIndependentSetInstance
      (fun x => x.graph.vertices.length + x.graph.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1
    SAT.computableInPolyTime_toSparseIndependentSet
    (fun φ _ => (SAT.toSparseIndependentSet_mem_iff φ).symm) (K := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- Under SH, Independent Set has no fixed power saving below one in the exponent measured in
the number of declared vertices. -/
theorem SH.not_decidableInPowerExpTime_IndependentSet_vertices (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime IndependentSet encIndependentSetInstance
      (fun x => x.graph.vertices.length) p :=
  fun hFast => h.not_decidableInPowerExpTime_IndependentSet hp hp1
    (hFast.mono_measure (fun _ => Nat.le_add_right _ _) hp.le)

/-- Under SH, Vertex Cover has no fixed power saving below one in the exponent
measured in the number of declared vertices plus edges. -/
theorem SH.not_decidableInPowerExpTime_VertexCover (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime VertexCover encVertexCoverInstance
      (fun x => x.graph.vertices.length + x.graph.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1
    (IndependentSet.computableInPolyTime_toVertexCover.comp
      SAT.computableInPolyTime_toSparseIndependentSet)
    (fun φ _ => ((IndependentSet.toVertexCover_mem_iff _).trans
      (SAT.toSparseIndependentSet_mem_iff φ)).symm) (K := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Function.comp_apply, IndependentSet.toVertexCover] at this ⊢
      omega

/-- Under SH, Clique has no fixed power saving below one in the exponent
measured in the number of declared vertices. -/
theorem SH.not_decidableInPowerExpTime_Clique (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime Clique encCliqueInstance (fun x => x.graph.vertices.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1
    (computableInPolyTime_independentSetToClique.comp
      SAT.computableInPolyTime_toSparseIndependentSet)
    (fun φ _ => ((independentSetToClique_mem_iff _).trans
      (SAT.toSparseIndependentSet_mem_iff φ)).symm)
    (K := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Function.comp_apply, independentSetToClique, Graph.compl] at this ⊢
      omega

/-- Under SH, Hamiltonian Cycle has no fixed power saving below one in the exponent
measured in the number of declared vertices plus edges. -/
theorem SH.not_decidableInPowerExpTime_HamCycle (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime HamCycle encGraph (fun G => G.vertices.length + G.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1 SAT.computableInPolyTime_toSparseHamCycle
    (fun φ _ => (SAT.toSparseHamCycle_mem_iff φ).symm) (K := 350) fun φ hφ => by
      have := SAT.length_toSparseHamCycle_le hφ
      omega

/-- Under SH, Directed Hamiltonian Cycle has no fixed power saving below one in the exponent
measured in the number of declared vertices plus arcs. -/
theorem SH.not_decidableInPowerExpTime_DirHamCycle (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime DirHamCycle encGraph (fun G => G.vertices.length + G.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1
    SAT.computableInPolyTime_toSparseDirHamCycle
    (fun φ _ => (SAT.toSparseDirHamCycle_mem_iff φ).symm) (K := 70) fun φ hφ => by
      have := SAT.length_toSparseDirHamCycle_le hφ
      omega

/-- Under SH, Directed Hamiltonian Path has no fixed power saving below one in the exponent
measured in the number of declared vertices plus arcs. -/
theorem SH.not_decidableInPowerExpTime_DirHamPath (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime DirHamPath encPathInstance
      (fun x => x.graph.vertices.length + x.graph.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1
    SAT.computableInPolyTime_toSparseDirHamPath
    (fun φ _ => (SAT.toSparseDirHamPath_mem_iff φ).symm) (K := 70) fun φ hφ => by
      have := SAT.length_sparseDiamondGraph_le hφ
      simp only [SAT.toSparseDirHamPath]
      omega

/-- Under SH, Hamiltonian Path has no fixed power saving below one in the exponent
measured in the number of declared vertices plus edges. -/
theorem SH.not_decidableInPowerExpTime_HamPath (h : SH) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    ¬DecidableInPowerExpTime HamPath encPathInstance
      (fun x => x.graph.vertices.length + x.graph.edges.length) p :=
  h.not_decidableInPowerExpTime_of_linear_reduction hp hp1
    (DirHamPath.computableInPolyTime_toHamPath.comp
      SAT.computableInPolyTime_toSparseDirHamPath)
    (fun φ _ => ((DirHamPath.toHamPath_mem_iff _).trans (SAT.toSparseDirHamPath_mem_iff φ)).symm)
    (K := 350) fun φ hφ => by
      have := SAT.length_sparseDiamondGraph_le hφ
      simp only [Function.comp_apply, DirHamPath.toHamPath, SAT.toSparseDirHamPath,
        Graph.length_split_fst, Graph.length_split_snd]
      omega

end Cslib.Complexity
