/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import CslibFrontier.Foundations.Geometry.Orthogonal.Directions
public import CslibFrontier.Foundations.Geometry.Orthogonal.Reverse
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Orientation-independent supplied incidence routes

Normalize each actual route from the second listed graph endpoint to the first. The
normalization preserves its complete real support, point and segment counts, wire cost,
proper orthogonality and continuous simplicity. Generic endpoint and exit-direction facts
are shared by the positive SAT drawing compiler and the polygonal embedding transport.

These are the original finite-route normalization proofs extracted from the SAT compiler;
the graph and drawing representations, raw fallbacks and computations are unchanged.
-/

@[expose] public section

namespace Cslib.Complexity.Graph.OrthogonalDrawing

open Cslib.Orthogonal

/-- The second endpoint of a listed edge, with a fixed fallback for invalid indices. -/
def sourceStart (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  Graph.drawingPosition G d (G.edges.getD i (0, 0)).2

/-- The first endpoint of a listed edge, with a fixed fallback for invalid indices. -/
def sourceFinish (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  Graph.drawingPosition G d (G.edges.getD i (0, 0)).1

/-- Normalize the supplied incidence route to begin at its second listed endpoint. -/
def sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Route :=
  if (d.2.getD i []).head? = some (sourceStart G d i) then d.2.getD i []
  else (d.2.getD i []).reverse

/-- Declared vertices with equal positions are equal in a valid drawing. -/
theorem drawingPosition_injOn {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {v w : ℕ} (hv : v ∈ G.vertices) (hw : w ∈ G.vertices)
    (he : Graph.drawingPosition G d v = Graph.drawingPosition G d w) : v = w := by
  have hi := List.idxOf_lt_length_of_mem hv
  have hj := List.idxOf_lt_length_of_mem hw
  have hi' : G.vertices.idxOf v < d.1.length := by rw [hd.vertexCount]; exact hi
  have hj' : G.vertices.idxOf w < d.1.length := by rw [hd.vertexCount]; exact hj
  simp only [Graph.drawingPosition, List.getD_eq_getElem _ _ hi',
    List.getD_eq_getElem _ _ hj'] at he
  have he' := hd.positionsNodup.getElem_inj_iff.mp he
  exact (List.idxOf_inj hv).mp he'

/-- Normalization preserves the complete continuous support of each supplied route. -/
theorem support_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    support (sourceRoute G d i) = support (d.2.getD i []) := by
  unfold sourceRoute
  split
  · rfl
  · exact support_reverse _

/-- Normalization preserves the number of route points. -/
theorem length_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    (sourceRoute G d i).length = (d.2.getD i []).length := by
  unfold sourceRoute
  split <;> simp

/-- Normalization preserves the number of segments. -/
theorem consecutivePairs_length_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing)
    (i : ℕ) :
    (sourceRoute G d i).consecutivePairs.length = (d.2.getD i []).consecutivePairs.length := by
  unfold sourceRoute
  split
  · rfl
  · exact consecutivePairs_length_reverse _

/-- Normalization preserves the total Manhattan wire cost. -/
theorem wireLength_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    wireLength (sourceRoute G d i) = wireLength (d.2.getD i []) := by
  unfold sourceRoute
  split
  · rfl
  · exact wireLength_reverse _

/-- The normalized route begins at the second endpoint and ends at the first. -/
theorem sourceRoute_endpoints {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.edges.length) :
    (sourceRoute G d i).head? = some (sourceStart G d i) ∧
      (sourceRoute G d i).getLast? = some (sourceFinish G d i) := by
  have he := hd.endpoints i hi
  dsimp only at he
  have hs : sourceStart G d i = Graph.drawingPosition G d G.edges[i].2 := by
    rw [sourceStart, List.getD_eq_getElem _ _ hi]
  have hf : sourceFinish G d i = Graph.drawingPosition G d G.edges[i].1 := by
    rw [sourceFinish, List.getD_eq_getElem _ _ hi]
  rw [← hs, ← hf] at he
  unfold sourceRoute
  split_ifs with hh
  · rcases he with ⟨h₁, h₂⟩ | he
    · have heq : sourceFinish G d i = sourceStart G d i := Option.some.inj (h₁.symm.trans hh)
      exact ⟨hh, heq ▸ h₂⟩
    · exact he
  · rcases he with ⟨h₁, h₂⟩ | ⟨h₁, _⟩
    · simpa only [List.head?_reverse, List.getLast?_reverse] using And.intro h₂ h₁
    · exact False.elim (hh h₁)

/-- The two listed endpoints occupy different points. -/
theorem sourceStart_ne_finish {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.edges.length) :
    sourceStart G d i ≠ sourceFinish G d i := by
  have hm := hd.endpointsDeclared _ (List.getElem_mem hi)
  have hn := hd.loopless _ (List.getElem_mem hi)
  unfold sourceStart sourceFinish
  rw [List.getD_eq_getElem _ _ hi]
  exact fun h => hn (drawingPosition_injOn hd hm.1 hm.2 h.symm)

/-- Every normalized valid incidence has at least two listed points. -/
theorem sourceRoute_length_ge_two {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.edges.length) :
    2 ≤ (sourceRoute G d i).length := by
  have he := sourceRoute_endpoints hd hi
  have hn := sourceStart_ne_finish hd hi
  generalize hr : sourceRoute G d i = r at he ⊢
  rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩
  · simp at he
  · simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at he
    exact False.elim (hn (he.1.symm.trans he.2))
  · simp

/-- Normalization preserves proper orthogonality and continuous simplicity. -/
theorem sourceRoute_regular {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.edges.length) :
    IsOrthogonal (sourceRoute G d i) ∧ IsSimple (sourceRoute G d i) := by
  unfold sourceRoute
  split
  · exact ⟨hd.orthogonal i hi, hd.simple i hi⟩
  · exact ⟨(isOrthogonal_reverse_iff _).mpr (hd.orthogonal i hi),
      (isSimple_reverse_iff _).mpr (hd.simple i hi)⟩

/-- A normalized incidence starts with its actual second endpoint and a proper next point. -/
theorem sourceRoute_shape {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.edges.length) :
    ∃ b r, sourceRoute G d i = sourceStart G d i :: b :: r := by
  have hh := (sourceRoute_endpoints hd hi).1
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.mp hh
  cases r with
  | nil => have hlen := sourceRoute_length_ge_two hd hi; simp [hr] at hlen
  | cons b r => exact ⟨b, r, hr⟩

/-- The cardinal exit direction of a normalized source incidence. -/
def sourceDirection (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  direction (sourceStart G d i) ((sourceRoute G d i).getD 1 (0, 0))

/-- Incidences at the same second endpoint leave in different cardinal directions. -/
theorem sourceDirection_ne {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i j : ℕ}
    (hi : i < G.edges.length) (hj : j < G.edges.length) (hij : i ≠ j)
    (hc : G.edges[i].2 = G.edges[j].2) : sourceDirection G d i ≠ sourceDirection G d j := by
  obtain ⟨b, r, hr⟩ := sourceRoute_shape hd hi
  obtain ⟨c, s, hs⟩ := sourceRoute_shape hd hj
  have he : sourceStart G d i = sourceStart G d j := by grind [sourceStart]
  have ho₁ := (sourceRoute_regular hd hi).1
  have ho₂ := (sourceRoute_regular hd hj).1
  rw [hr] at ho₁
  rw [hs, ← he] at ho₂
  have h₁ := ho₁ (sourceStart G d i, b) (by simp [List.consecutivePairs])
  have h₂ := ho₂ (sourceStart G d i, c) (by simp [List.consecutivePairs])
  have hdir := direction_ne_of_grid_contacts h₁ h₂ (fun p hp hq => ?_)
  · simpa [sourceDirection, hr, hs, he, List.getD] using hdir
  · have hp' : p ∈ support (d.2.getD i []) := by
      rw [← support_sourceRoute, hr, support_cons_cons]
      exact Or.inl hp
    have hq' : p ∈ support (d.2.getD j []) := by
      rw [← support_sourceRoute, hs, ← he, support_cons_cons]
      exact Or.inl hq
    obtain ⟨v, _, _, _, hv⟩ := hd.contacts i hi j hj hij p hp' hq'
    exact ⟨Graph.drawingPosition G d v, hv⟩

end Cslib.Complexity.Graph.OrthogonalDrawing
