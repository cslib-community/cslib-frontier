/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Quiver.Path.Vertices

public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector

/-!
# Paths in layered digraphs

A layered digraph is a digraph equipped with a natural-number layer for each vertex.
Each edge advances exactly one layer. Paths use Mathlib's `Quiver.Path`, with one arrow
for each adjacent pair, so parallel edges are excluded.

## Main results

* `LayeredDigraph.Path.existsUnique_vertex`: a path visits exactly one vertex in each layer
  between its endpoints, including the endpoint layers.
* `LayeredDigraph.Path.exists_eq_comp_of_layer`: a path splits at any such layer.
* `LayeredDigraph.Path.internalWeight_comp`: the weight of a concatenation is the sum of the
  internal weights of its two pieces and the weight of their common endpoint.
-/

public section

namespace Cslib

/-- A digraph whose edges advance exactly one layer. -/
structure LayeredDigraph (V : Type*) extends Digraph V where
  /-- The layer of each vertex. -/
  layer : V → ℕ
  /-- Every edge goes to the next layer. -/
  layer_adj {a b : V} : Adj a b → layer b = layer a + 1

namespace LayeredDigraph

variable {V : Type*}

/-- The quiver with one arrow for each adjacent pair. -/
abbrev toQuiver (G : LayeredDigraph V) : Quiver V where
  Hom a b := PLift (G.Adj a b)

instance (G : LayeredDigraph V) (a b : V) :
    Subsingleton (@Quiver.Hom V G.toQuiver a b) :=
  inferInstanceAs (Subsingleton (PLift (G.Adj a b)))

/-- Directed paths in the underlying quiver of a layered digraph. -/
abbrev Path (G : LayeredDigraph V) (a b : V) := @Quiver.Path V G.toQuiver a b

namespace Path

variable {G : LayeredDigraph V} {a b c : V}

/-- The number of edges of a path. -/
abbrev length (p : G.Path a b) : ℕ := @Quiver.Path.length V G.toQuiver a b p

/-- The vertices of a path in order, including both endpoints. -/
abbrev vertices (p : G.Path a b) : List V := @Quiver.Path.vertices V G.toQuiver a b p

/-- Concatenate paths with a common endpoint. -/
abbrev comp (p : G.Path a b) (q : G.Path b c) : G.Path a c :=
  @Quiver.Path.comp V G.toQuiver a b c p q

/-- An edge viewed as a length-one path. -/
abbrev ofAdj (h : G.Adj a b) : G.Path a b :=
  @Quiver.Hom.toPath V G.toQuiver a b ⟨h⟩

/-- The last layer of a path is its first layer plus its length. -/
theorem layer_end (p : G.Path a b) : G.layer b = G.layer a + p.length := by
  induction p with
  | nil => simp
  | cons p e ih =>
    change G.layer _ = G.layer a + (length p + 1)
    rw [← Nat.add_assoc, ← ih, G.layer_adj e.down]

/-- A path splits at any layer in its closed endpoint interval. -/
theorem exists_eq_comp_of_layer (p : G.Path a b) {k : ℕ}
    (ha : G.layer a ≤ k) (hb : k ≤ G.layer b) :
    ∃ (v : V) (q : G.Path a v) (r : G.Path v b), p = q.comp r ∧ G.layer v = k := by
  let _ := G.toQuiver
  have hk : k - G.layer a ≤ p.length := by
    have := p.layer_end
    omega
  obtain ⟨v, q, r, h, hq⟩ := p.exists_eq_comp_of_le_length hk
  refine ⟨v, q, r, h, ?_⟩
  change length q = _ at hq
  rw [layer_end q, hq, Nat.add_sub_of_le ha]

/-- The vertex at position `i` lies `i` layers after the source. -/
theorem layer_getElem_vertices (p : G.Path a b) (i : ℕ) (hi : i < p.vertices.length) :
    G.layer p.vertices[i] = G.layer a + i := by
  let _ := G.toQuiver
  obtain ⟨v, q, _, _, hlen, hv⟩ := p.exists_eq_comp_and_length_eq_of_lt_length i hi
  change length q = i at hlen
  rw [← hv, layer_end q, hlen]

private theorem vertices_length (p : G.Path a b) : p.vertices.length = p.length + 1 :=
  @Quiver.Path.vertices_length V G.toQuiver a b p

/-- A path visits exactly one vertex in each layer between its endpoints. -/
theorem existsUnique_vertex (p : G.Path a b) {k : ℕ}
    (ha : G.layer a ≤ k) (hb : k ≤ G.layer b) :
    ∃! v, v ∈ p.vertices ∧ G.layer v = k := by
  have hi : k - G.layer a < p.vertices.length := by
    rw [vertices_length]
    have := p.layer_end
    omega
  refine ⟨p.vertices[k - G.layer a], ⟨List.getElem_mem hi, ?_⟩, ?_⟩
  · rw [p.layer_getElem_vertices, Nat.add_sub_of_le ha]
  · rintro v ⟨hv, hlayer⟩
    obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hv
    rw [p.layer_getElem_vertices] at hlayer
    obtain rfl : i = k - G.layer a := by omega
    rfl

instance [Finite V] : Finite (G.Path a b) := by
  let _ := G.toQuiver
  have length_toList {v : V} (p : G.Path a v) : p.toList.length = p.length := by
    induction p with
    | nil => rfl
    | cons p e ih =>
      simp only [Quiver.Path.toList, List.length_cons, ih]
      rfl
  refine Finite.of_injective (β := List.Vector V (G.layer b - G.layer a))
    (fun p : G.Path a b ↦ ⟨p.toList, ?_⟩) ?_
  · rw [length_toList, p.layer_end, Nat.add_sub_cancel_left]
  · intro p q h
    exact (Quiver.Path.toList_injective a b) (congrArg Subtype.val h)

/-- With at most one edge between the endpoint layers, any two paths coincide. -/
theorem eq_of_layer_le_succ (h : G.layer b ≤ G.layer a + 1) (p q : G.Path a b) : p = q := by
  let _ := G.toQuiver
  have short {v : V} (r : G.Path a v) (hv : G.layer v ≤ G.layer a + 1) :
      r.toList = if r.length = 0 then [] else [a] := by
    cases r with
    | nil => simp
    | cons r e =>
      have hlen := layer_end (G := G) (r.cons e)
      change G.layer _ = G.layer a + (r.length + 1) at hlen
      have hz : r.length = 0 := by omega
      obtain rfl := r.eq_of_length_zero hz
      rw [r.eq_nil_of_length_zero hz]
      simp
  apply Quiver.Path.toList_injective a b
  rw [short p h, short q h]
  have hp := p.layer_end
  have hq := q.layer_end
  rw [show p.length = q.length by omega]

/-- The vertices strictly between the endpoints, in path order. -/
@[expose] def internalVertices (p : G.Path a b) : List V := p.vertices.dropLast.tail

/-- On an internal layer, the unique vertex on the path belongs to its internal list. -/
theorem mem_internalVertices_iff (p : G.Path a b) {v : V} :
    v ∈ p.internalVertices ↔
      v ∈ p.vertices ∧ G.layer a < G.layer v ∧ G.layer v < G.layer b := by
  have hlen := p.layer_end
  simp only [internalVertices, List.mem_iff_getElem, List.length_tail, List.length_dropLast,
    vertices_length]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.getElem_tail, List.getElem_dropLast, p.layer_getElem_vertices]
    exact ⟨⟨i + 1, by omega, rfl⟩, by omega, by omega⟩
  · rintro ⟨⟨i, hi, rfl⟩, ha, hb⟩
    rw [p.layer_getElem_vertices] at ha hb
    refine ⟨i - 1, by omega, ?_⟩
    simp only [List.getElem_tail, List.getElem_dropLast, Nat.sub_add_cancel (by omega : 1 ≤ i)]

/-- The internal vertices of a concatenation are those of the first path, the common
endpoint, and those of the second path, in that order. -/
theorem internalVertices_comp (p : G.Path a b) (q : G.Path b c)
    (hp : G.layer a < G.layer b) (hq : G.layer b < G.layer c) :
    (p.comp q).internalVertices = p.internalVertices ++ b :: q.internalVertices := by
  let _ := G.toQuiver
  have dropLast_ne_nil {u v : V} (r : G.Path u v) (h : G.layer u < G.layer v) :
      r.vertices.dropLast ≠ [] := by
    have hlen := r.layer_end
    exact List.ne_nil_of_length_pos (by rw [List.length_dropLast, vertices_length]; omega)
  have hhead : q.vertices.dropLast.head? = some b := by
    calc
      _ = (q.vertices.dropLast ++ [c]).head? :=
        (List.head?_append_of_ne_nil _ (dropLast_ne_nil q hq)).symm
      _ = some b := by rw [q.dropLast_append_end_eq, q.vertices_head?]
  have hcons : q.vertices.dropLast = b :: q.internalVertices :=
    (List.cons_head?_tail (by simp [hhead])).symm
  change (Quiver.Path.comp p q).vertices.dropLast.tail = _
  rw [Quiver.Path.vertices_comp, List.dropLast_append_of_ne_nil q.vertices_ne_nil,
    List.tail_append_of_ne_nil (dropLast_ne_nil p hp), hcons]
  rfl

/-- The sum of the weights of the internal vertices. -/
@[expose] def internalWeight {M : Type*} [AddMonoid M] (weight : V → M) (p : G.Path a b) : M :=
  (p.internalVertices.map weight).sum

/-- At an internal split, the common endpoint contributes its weight exactly once. -/
theorem internalWeight_comp {M : Type*} [AddMonoid M] (weight : V → M)
    (p : G.Path a b) (q : G.Path b c) (hp : G.layer a < G.layer b) (hq : G.layer b < G.layer c) :
    (p.comp q).internalWeight weight =
      p.internalWeight weight + weight b + q.internalWeight weight := by
  simp [internalWeight, internalVertices_comp p q hp hq, add_assoc]

/-- The vertex visited at a layer, with the source as the default outside the path. -/
@[expose] def vertexAtLayer (p : G.Path a b) (k : ℕ) : V :=
  p.vertices[k - G.layer a]?.getD a

/-- Within the path's layer interval, the lookup returns the unique vertex at that layer. -/
theorem vertexAtLayer_eq (p : G.Path a b) {k : ℕ} {v : V}
    (hv : v ∈ p.vertices) (hk : G.layer v = k) : p.vertexAtLayer k = v := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  rw [p.layer_getElem_vertices] at hk
  have hidx : k - G.layer a = i := by omega
  rw [vertexAtLayer, hidx, List.getElem?_eq_getElem hi]
  rfl

/-- Sum internal weights in order of layer. -/
theorem internalWeight_eq_sum_layers {M : Type*} [AddCommMonoid M] (weight : V → M)
    (p : G.Path a b) :
    p.internalWeight weight =
      ∑ k ∈ Finset.Icc (G.layer a + 1) (G.layer b - 1), weight (p.vertexAtLayer k) := by
  classical
  have hnodup : p.vertices.Nodup := by
    apply List.nodup_iff_injective_getElem.mpr
    intro i j h
    apply Fin.ext
    have h' := congrArg G.layer h
    rw [p.layer_getElem_vertices, p.layer_getElem_vertices] at h'
    omega
  have hnodupInternal : p.internalVertices.Nodup :=
    (hnodup.sublist (List.dropLast_sublist p.vertices)).tail
  rw [internalWeight, ← List.sum_toFinset weight hnodupInternal]
  refine Finset.sum_bij (fun v _ => G.layer v) ?_ ?_ ?_ ?_
  · intro v hv
    have h := (p.mem_internalVertices_iff.mp (List.mem_toFinset.mp hv)).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro u hu v hv heq
    have h₁ := (p.mem_internalVertices_iff.mp (List.mem_toFinset.mp hu)).1
    have h₂ := (p.mem_internalVertices_iff.mp (List.mem_toFinset.mp hv)).1
    exact (p.vertexAtLayer_eq h₁ heq).symm.trans (p.vertexAtLayer_eq h₂ rfl)
  · intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    have hk₂' : k < G.layer b := by omega
    obtain ⟨v, ⟨hv, heq⟩, _⟩ := p.existsUnique_vertex (by omega : G.layer a ≤ k) hk₂'.le
    refine ⟨v, List.mem_toFinset.mpr (p.mem_internalVertices_iff.mpr ⟨hv, ?_, ?_⟩), heq⟩
    · omega
    · omega
  · intro v hv
    rw [p.vertexAtLayer_eq (p.mem_internalVertices_iff.mp (List.mem_toFinset.mp hv)).1 rfl]

end Path
end LayeredDigraph
end Cslib
