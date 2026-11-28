/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Matrix

/-!
# The adjacency-matrix encoding of undirected graphs

An undirected graph instance (`Cslib.Complexity.UGraphInstance`) is a simple graph on `Fin n`,
given by a symmetric adjacency matrix with zero diagonal. It is encoded
(`Cslib.Complexity.encUGraph`) as its digraph (`Cslib.Complexity.encDigraph`): the unary header
`1^n 0` followed by the adjacency matrix row by row, so that the bit at `n + 1 + (a * n + b)` is
the entry of the row `a` and the column `b`.

## Main definitions

* `Cslib.Complexity.UGraphInstance.toDigraph`: the digraph of an instance.
* `Cslib.Complexity.encUGraph`: the encoding of instances.

## Main results

* `Cslib.Complexity.UGraphInstance.encode_injective`: the encoding is injective.
* `Cslib.Complexity.UGraphInstance.length_encode`,
  `Cslib.Complexity.UGraphInstance.getElem?_encode_n`,
  `Cslib.Complexity.UGraphInstance.getElem?_encode_matrix`: the length of the encoding, and its
  bits read by position.
-/

@[expose] public section

namespace Cslib.Complexity

namespace UGraphInstance

variable (G : UGraphInstance)

/-- The digraph of an instance, with an arc in each direction for every edge. -/
def toDigraph : DigraphInstance := ⟨G.n, G.adj⟩

theorem toDigraph_injective : Function.Injective toDigraph := by
  rintro ⟨n, adj, symm, loopless⟩ ⟨n', adj', symm', loopless'⟩ h
  simp only [toDigraph, DigraphInstance.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  subst h
  rfl

/-- The encoding of an instance, that of its digraph (`Cslib.Complexity.encDigraph`): the unary
header `1^n 0`, then the adjacency matrix row by row. -/
def encode : List Bool := G.toDigraph.encode

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode :=
  DigraphInstance.encode_injective.comp toDigraph_injective

/-- The length of the encoding: the header and the `n ^ 2` entries of the matrix. -/
theorem length_encode : G.encode.length = G.n + 1 + G.n * G.n :=
  G.toDigraph.length_encode

/-- The header, read by position: the bit at `i ≤ n` is set exactly when `i < n`. -/
theorem getElem?_encode_n {i : ℕ} (h : i ≤ G.n) : G.encode[i]? = some (decide (i < G.n)) :=
  G.toDigraph.getElem?_encode_n h

/-- **The entries of the matrix, read by position**: the bit at `n + 1 + (a * n + b)` is the entry
of the row `a` and the column `b`. -/
theorem getElem?_encode_matrix {a b : ℕ} (ha : a < G.n) (hb : b < G.n) :
    G.encode[G.n + 1 + (a * G.n + b)]? = some (G.adj ⟨a, ha⟩ ⟨b, hb⟩) :=
  G.toDigraph.getElem?_encode_matrix ha hb

end UGraphInstance

/-- The encoding of undirected graphs: the unary header `1^n 0`, then the adjacency matrix row by
row. -/
def encUGraph : UGraphInstance ↪ List Bool :=
  ⟨UGraphInstance.encode, UGraphInstance.encode_injective⟩

@[simp]
theorem encUGraph_apply (G : UGraphInstance) : encUGraph G = G.encode := rfl

end Cslib.Complexity
