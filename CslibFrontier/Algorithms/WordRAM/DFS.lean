/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.CSR
public import CslibFrontier.Algorithms.WordRAM.DFS.Visit
public import CslibFrontier.Algorithms.WordRAM.DFS.ForwardDFS
public import CslibFrontier.Algorithms.WordRAM.DFS.Transpose
public import CslibFrontier.Algorithms.WordRAM.DFS.Kosaraju
public import CslibFrontier.Algorithms.WordRAM.DFS.Programs

/-!
# Linear-time depth-first search on the word RAM

Iterative depth-first search with an explicit stack on the standard-basis word RAM
(`Cslib.WordRAM.Basis.standard`), after [Tarjan][Tarjan1972] and [Cormen et al., Sections
22.3–22.5][CLRS2009]: DFS finishing order, topological sort, CSR transposition and Kosaraju's
strongly connected components, each in `O(N + M)` instructions on a graph with `N` vertices and
`M` arcs, proved equal to the pure functions of `CslibFrontier.Algorithms.Lean.DFS`.

## Representation

A graph `adj : Fin N → List (Fin N)` is held in compressed sparse row form (`CSRAt`): an offset
array `csrOffset adj 0, …, csrOffset adj N` followed by the successor lists in order. All passes
work in one scratch layout based at an address `wb` (`kOffAddr`, …, `kTopAddr`), with `Mc` words
reserved for each arc array. The DFS stack holds `3` words per frame (vertex, next arc, arc end),
so no recursion is needed. The engine (`forwardDFSCode`, `transposeCSRCode`,
`kosarajuIndexCode`, `sccIndexCode` and their CSR primitives) is shared with
`CslibFrontier.Algorithms.WordRAM.TwoSAT`.

The end-to-end programs read a `Graph` in the CSR input encoding `Graph.encodeCSR`
(`[n, m, off 0, …, off n] ++ arcs`), so the input already is the forward CSR graph of the layout
based at `wb = 3`, and return a list through `Cslib.WordRAM.ExecutesList`.

## Main definitions

* `Cslib.Algorithms.WordRAM.DFS.csrOffset`, `Cslib.Algorithms.WordRAM.DFS.CSRAt`: CSR offsets and
  the CSR memory invariant.
* `Cslib.Algorithms.WordRAM.DFS.forwardDFSCode`, `Cslib.Algorithms.WordRAM.DFS.transposeCSRCode`,
  `Cslib.Algorithms.WordRAM.DFS.kosarajuIndexCode`, `Cslib.Algorithms.WordRAM.DFS.sccIndexCode`:
  the structured passes.
* `Cslib.Algorithms.WordRAM.DFS.Graph`, `Cslib.Algorithms.WordRAM.DFS.Graph.m`,
  `Cslib.Algorithms.WordRAM.DFS.Graph.encodeCSR`, `Cslib.Algorithms.WordRAM.DFS.Graph.wordBound`:
  graph instances, arc count, CSR input encoding and word-size envelope.
* `Cslib.Algorithms.WordRAM.DFS.topoWords`, `Cslib.Algorithms.WordRAM.DFS.sccWords`: outputs.
* `Cslib.Algorithms.WordRAM.DFS.topoProgram`, `Cslib.Algorithms.WordRAM.DFS.sccProgram`: flat
  programs.

## Main results

* `Cslib.Algorithms.WordRAM.DFS.forwardDFSCode_spec`: the forward pass writes the DFS finishing
  order `(topologicalSort adj (List.finRange N)).reverse` in `87 * N + 36 * Mc + 10` instructions.
* `Cslib.Algorithms.WordRAM.DFS.transposeCSRCode_spec`: CSR transposition (`transposeAdj`).
* `Cslib.Algorithms.WordRAM.DFS.kosarajuIndexCode_spec`: Kosaraju component peeling and indexing
  from a transposed CSR graph and finishing order.
* `Cslib.Algorithms.WordRAM.DFS.sccIndexCode_spec`: Kosaraju component indices
  `indexComponents (sccs adj (List.finRange N))` in `220 * N + 92 * Mc + 42` instructions.
* `Cslib.Algorithms.WordRAM.DFS.Graph.csrAt_init`,
  `Cslib.Algorithms.WordRAM.DFS.Graph.inputFits_encodeCSR`: the input encoding is a CSR graph
  whose words fit.
* `Cslib.Algorithms.WordRAM.DFS.topoCode_spec`,
  `Cslib.Algorithms.WordRAM.DFS.computesListInTime_topoProgram`: topological sort within
  `128 * (n + m + 1)` instructions at every width `w` with `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.DFS.sccCode_spec`,
  `Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram`: strongly connected component
  indices within `256 * (n + m + 1)` instructions.
* `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_topoProgram`,
  `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_sccProgram`: width independence.

## References

* [R. E. Tarjan, *Depth-first search and linear graph algorithms*][Tarjan1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/
