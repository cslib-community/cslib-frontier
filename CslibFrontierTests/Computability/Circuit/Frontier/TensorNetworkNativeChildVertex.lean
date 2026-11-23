/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildVertex

public section

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.NativeChild

namespace Cslib.Tests.TensorNetworkNativeChildVertex

/-- Two disjoint row-column edges, with the same descriptor on every parent vertex. -/
def parent : DescribedNetwork (VertexDesc ℕ) :=
  ⟨2, [([0], .inl 7), ([1], .inl 7), ([0], .inl 7), ([1], .inl 7)]⟩

private def packing : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  (([[1], [0]], [[1], [0]]), 2, [(0, 3), (1, 5)])

private def child : DescribedNetwork (VertexDesc ℕ) :=
  nativeChild [1] 1 0 1 (-1) [2] 2 parent packing [10, 11, 12, 13] 1

-- Retained vertices need not be a prefix, and their descriptors need not distinguish them.
example : parent.IsRowsFirstBipartite 2 := by decide

example : groupsOf 2 0 parent.vertices.length packing.1 = [1, 0, 1, 0] := by decide

example : child.vertices[0]? = some ([0], .inl 7) :=
  getElem?_vertices_nativeChild_retained [1] 1 0 1 (-1) [2] 2 parent packing
    [10, 11, 12, 13] 1 (v := 0) (by decide) (by decide)

example : child.vertices[1]? = some ([1], .inl 7) :=
  getElem?_vertices_nativeChild_retained [1] 1 0 1 (-1) [2] 2 parent packing
    [10, 11, 12, 13] 1 (v := 2) (by decide) (by decide)

-- Packet zero follows both retained vertices and tags both ends of its parent edge.
example : child.vertices[2]? =
    some ([0, 1], .inr (packetCtx [1] 1 0 1 (-1) [2] 1 0,
      [(true, 3), (false, 3)], [10, 11])) :=
  getElem?_vertices_nativeChild_packet [1] 1 0 1 (-1) [2] 2 parent packing
    [10, 11, 12, 13] 1 (q := 0) (by decide)

-- Even a packet with no ports occupies its own number and retains its own exponent slice.
example : child.vertices[3]? =
    some ([], .inr (packetCtx [1] 1 0 1 (-1) [2] 1 1, [], [12, 13])) :=
  getElem?_vertices_nativeChild_packet [1] 1 0 1 (-1) [2] 2 parent packing
    [10, 11, 12, 13] 1 (q := 1) (by decide)

example : child.vertices.length = 4 := by
  rw [child, length_vertices_nativeChild]
  decide

-- A child lookup does not return the default vertex at or above the exact child length.
example : child.vertices[4]? = none := by decide

-- Equal retained descriptors do not lose the numerical predecessor: position one came from two.
example (v : ℕ) (hv : v < parent.vertices.length)
    (hg : (groupsOf 2 0 parent.vertices.length packing.1).getD v 0 = 1)
    (hrank : ((groupsOf 2 0 parent.vertices.length packing.1).take v).count 1 = 1) : v = 2 := by
  change v < 4 at hv
  interval_cases v <;> simp_all [parent, packing, groupsOf]

-- The reverse theorem is used with an arbitrary successful child lookup, not just a toy value.
example {k : ℕ} {vertex : List ℕ × VertexDesc ℕ}
    (h : child.vertices[k]? = some vertex) :
    (∃ v, v < parent.vertices.length ∧
      (groupsOf 2 0 parent.vertices.length packing.1).getD v 0 = 1 ∧
      ((groupsOf 2 0 parent.vertices.length packing.1).take v).count 1 = k) ∨
      ∃ q, q < 2 ∧ 2 + q = k := by
  rcases (getElem?_vertices_nativeChild_iff [1] 1 0 1 (-1) [2] 2 parent packing
    [10, 11, 12, 13] 1).mp h with ⟨v, hv, hg, hrank, _⟩ | ⟨q, hq, hoffset, _⟩
  · exact Or.inl ⟨v, hv, hg, hrank⟩
  · exact Or.inr ⟨q, hq, hoffset⟩

end Cslib.Tests.TensorNetworkNativeChildVertex
