/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColors
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceDartColors
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Opposite orders of three drawn paths

For three edge-disjoint paths with shared endpoints, odd crossings within one path can
contribute to its individual dart equations but cancel in the sum along the path.
If distinct paths cross evenly, the two orders of the three paths are opposite.
This gives the three-path comparison in [FulekKynclPalvolgyi2017], §3, Claim B,
using the original regular polygonal drawing and Boolean dart colors.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Cslib.Polygonal

private theorem vertexEven_of_two_paths {G : Graph} {r : RotationSystem G}
    {m n : ℕ} (p : Fin (m + 1) → Dart G) (q : Fin (n + 1) → Dart G)
    (hp : Function.Injective fun i => (p i).1) (hq : Function.Injective fun i => (q i).1)
    (hdisjoint : ∀ i j, (p i).1 ≠ (q j).1)
    (hpStep : ∀ i : Fin m, r.rotate.symm (p i.castSucc).reverse = p i.succ)
    (hqStep : ∀ i : Fin n, r.rotate.symm (q i.castSucc).reverse = q i.succ)
    (hstart : (p 0).vertex = (q 0).vertex)
    (hfinish : (p (Fin.last m)).reverse.vertex = (q (Fin.last n)).reverse.vertex)
    {x : Fin G.edges.length → Bool}
    (hx : ∀ e, x e = true ↔ (∃ i, (p i).1 = e) ∨ (∃ i, (q i).1 = e)) :
    G.VertexEven x := by
  classical
  intro v
  let atVertex (d : Dart G) : Bool := decide (d.vertex = v)
  let ends (e : Fin G.edges.length) := atVertex (e, false) + atVertex (e, true)
  let pEdge : Fin (m + 1) ↪ Fin G.edges.length := ⟨fun i => (p i).1, hp⟩
  let qEdge : Fin (n + 1) ↪ Fin G.edges.length := ⟨fun i => (q i).1, hq⟩
  let P := Finset.univ.map pEdge
  let Q := Finset.univ.map qEdge
  have memP (e : Fin G.edges.length) : e ∈ P ↔ ∃ i, (p i).1 = e := by simp [P, pEdge]
  have memQ (e : Fin G.edges.length) : e ∈ Q ↔ ∃ i, (q i).1 = e := by simp [Q, qEdge]
  have hd : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro e he hf
    obtain ⟨i, hi⟩ := (memP e).mp he
    obtain ⟨j, hj⟩ := (memQ e).mp hf
    exact hdisjoint i j (hi.trans hj.symm)
  have count (d : Dart G) : (if d.vertex = v then true else 0) = atVertex d := by
    by_cases h : d.vertex = v <;> simp [atVertex, h, Bool.zero_eq_false]
  have hsum : G.vertexParity x v = ∑ e ∈ P ∪ Q, ends e := by
    unfold vertexParity
    change (∑ d : Fin G.edges.length × Bool, if Dart.vertex (G := G) d = v then x d.1 else 0) = _
    rw [Fintype.sum_prod_type]
    trans ∑ e, if x e = true then ends e else 0
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Fintype.sum_bool]
      cases x e
      · simp [← Bool.zero_eq_false]
      · change ((if Dart.vertex (G := G) (e, true) = v then true else 0) +
            (if Dart.vertex (G := G) (e, false) = v then true else 0)) = ends e
        simp only [count, ends, add_comm]
    · rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext e
      simp [memP, memQ, hx]
  have hend (d : Dart G) : ends d.1 = atVertex d + atVertex d.reverse := by
    rcases d with ⟨e, b⟩
    cases b
    · rfl
    · exact add_comm _ _
  have pathSum {k : ℕ} (arm : Fin (k + 1) → Dart G)
      (step : ∀ i : Fin k, r.rotate.symm (arm i.castSucc).reverse = arm i.succ) :
      (∑ i, ends (arm i).1) = atVertex (arm 0) + atVertex (arm (Fin.last k)).reverse := by
    have vertexStep (i : Fin k) : (arm i.succ).vertex = (arm i.castSucc).reverse.vertex := by
      rw [← step i, ← r.vertex_rotate (r.rotate.symm (arm i.castSucc).reverse),
        r.rotate.apply_symm_apply]
    have telescope := Fin.sum_univ_adjacent_differences
      (fun i => atVertex (arm i)) (fun i => atVertex (arm i).reverse)
    simp_rw [BooleanRing.sub_eq_add] at telescope
    have cancel (i : Fin k) : atVertex (arm i.succ) + atVertex (arm i.castSucc).reverse = 0 := by
      have he : atVertex (arm i.succ) = atVertex (arm i.castSucc).reverse := by
        unfold atVertex
        rw [vertexStep]
      rw [he, BooleanRing.add_self]
    simp only [cancel, Finset.sum_const_zero, add_zero] at telescope
    simpa only [hend, add_comm] using telescope
  rw [hsum, Finset.sum_union hd, Finset.sum_map, Finset.sum_map]
  change (∑ i, ends (p i).1) + (∑ j, ends (q j).1) = false
  rw [pathSum p hpStep, pathSum q hqStep]
  have sameStart : atVertex (p 0) = atVertex (q 0) := by unfold atVertex; rw [hstart]
  have sameFinish : atVertex (p (Fin.last m)).reverse = atVertex (q (Fin.last n)).reverse := by
    unfold atVertex
    rw [hfinish]
  rw [sameStart, sameFinish, BooleanRing.add_self, Bool.zero_eq_false]

/-- In a regular polygonal drawing of three edge-disjoint nonempty paths, their cyclic
orders at their shared ends are opposite if each edge crosses every edge on another path
evenly. The paths are indexed by `Fin 3`. The two port equivalences enumerate their actual
darts at the ends. Internal turns follow the inverse vertex rotation, as they do when the
internal vertices have degree two in the restricted drawing. Edges of the same path may
cross oddly. This gives the three-path comparison used in Claim B of
[FulekKynclPalvolgyi2017], §3. -/
theorem HasRegularContacts.inverse_rotate_iff_not_inverse_rotate_of_three_paths
    {G : Graph} {D : PolygonalDrawing G} {r : RotationSystem G}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple) (hR : D.Realizes r)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) {u v : ℕ}
    {length : Fin 3 → ℕ} (path : ∀ k, Fin (length k + 1) → Dart G)
    (start : Fin 3 ≃ {d : Dart G // d.vertex = u})
    (finish : Fin 3 ≃ {d : Dart G // d.vertex = v})
    (hstart : ∀ k, (start k).val = path k 0)
    (hfinish : ∀ k, (finish k).val = (path k (Fin.last (length k))).reverse)
    (hstep : ∀ k (i : Fin (length k)), r.rotate.symm (path k i.castSucc).reverse = path k i.succ)
    (hinj : Function.Injective fun i : (k : Fin 3) × Fin (length k + 1) => (path i.1 i.2).1)
    (heven : ∀ (a b : Fin 3), a ≠ b → ∀ i j,
      (D.route (path a i).1).intersectionParity (D.route (path b j).1) = false) :
    r.rotate.symm (start 0).val = (start 2).val ↔
      r.rotate.symm (finish 0).val ≠ (finish 2).val := by
  classical
  let label (e : Fin G.edges.length) : Bool :=
    decide (∃ k : Fin 3, k ≠ 2 ∧ ∃ i, (path k i).1 = e)
  have hlabel (e : Fin G.edges.length) :
      label e = true ↔ ∃ k : Fin 3, k ≠ 2 ∧ ∃ i, (path k i).1 = e := by
    simp [label]
  have distinct {a b : Fin 3} (hab : a ≠ b) (i : Fin (length a + 1)) (j : Fin (length b + 1)) :
      (path a i).1 ≠ (path b j).1 := fun he =>
    hab (congrArg Sigma.fst (hinj (a₁ := ⟨a, i⟩) (a₂ := ⟨b, j⟩) he))
  have eachInjective (k : Fin 3) : Function.Injective fun i => (path k i).1 := by
    intro i j hij
    have h := hinj (a₁ := ⟨k, i⟩) (a₂ := ⟨k, j⟩) hij
    exact eq_of_heq (Sigma.mk.inj h).2
  have selected (e : Fin G.edges.length) :
      label e = true ↔ (∃ i, (path 0 i).1 = e) ∨ (∃ i, (path 1 i).1 = e) := by
    rw [hlabel]
    constructor
    · rintro ⟨k, hk, i, hi⟩
      fin_cases k
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr ⟨i, hi⟩
      · exact (hk rfl).elim
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨0, by decide, i, hi⟩
      · exact ⟨1, by decide, i, hi⟩
  have unselected (i : Fin (length 2 + 1)) : label (path 2 i).1 = false := by
    cases h : label (path 2 i).1
    · rfl
    · obtain ⟨k, hk, j, hj⟩ := (hlabel _).mp h
      exact (distinct hk j i hj).elim
  have hs (k : Fin 3) : (path k 0).vertex = u :=
    hstart k ▸ (start k).property
  have ht (k : Fin 3) : (path k (Fin.last (length k))).reverse.vertex = v :=
    hfinish k ▸ (finish k).property
  have hl : G.VertexEven label :=
    vertexEven_of_two_paths (path 0) (path 1) (eachInjective 0) (eachInjective 1)
      (distinct (by decide)) (hstep 0) (hstep 1) ((hs 0).trans (hs 1).symm)
      ((ht 0).trans (ht 1).symm) selected
  obtain ⟨color, hedge, hsector⟩ := hD.exists_dart_colors hsimple hR hG label hl
  let crossings (f e : Fin G.edges.length) : Bool :=
    if f = e then 0 else (D.route f).intersectionParity (D.route e)
  have edge (d : Dart G) :
      color d + color d.reverse = label d.1 + ∑ f, label f * crossings f d.1 := by
    rcases d with ⟨e, tag⟩
    have he : (∑ f, label f * crossings f e) =
        ∑ f, (if f = e then 0 else label f) * (D.route f).intersectionParity (D.route e) := by
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases h : f = e <;> simp [crossings, h]
    cases tag
    · exact (hedge e).trans (congrArg (label e + ·) he.symm)
    · exact (add_comm _ _).trans ((hedge e).trans (congrArg (label e + ·) he.symm))
  apply r.inverse_rotate_iff_not_inverse_rotate_of_three_paths path start finish hstart hfinish
    hstep (eachInjective 0) color label hlabel unselected crossings _ _ _ edge hsector
  · intro e f
    by_cases h : e = f
    · subst e
      rfl
    · have h' : f ≠ e := Ne.symm h
      simpa only [crossings, ite_eq_right h, ite_eq_right h'] using
        Route.intersectionParity_symm (D.route e) (D.route f)
  · intro e
    simp [crossings]
  · intro a b hab i j
    simpa only [crossings, ite_eq_right (distinct hab i j), Bool.zero_eq_false] using
      heven a b hab i j

end Cslib.Complexity.Graph.PolygonalDrawing
