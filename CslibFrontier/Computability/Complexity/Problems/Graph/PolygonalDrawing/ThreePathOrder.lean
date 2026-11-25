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
  let P := Finset.univ.map ⟨fun i => (p i).1, hp⟩
  let Q := Finset.univ.map ⟨fun i => (q i).1, hq⟩
  have hd : Disjoint P Q := by
    rw [Finset.disjoint_left]
    simp only [P, Q, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact hdisjoint i j hj.symm
  have count (d : Dart G) : (if d.vertex = v then true else 0) = atVertex d := by
    by_cases h : d.vertex = v <;> simp [atVertex, h, Bool.zero_eq_false]
  have hsum : G.vertexParity x v = ∑ e ∈ P ∪ Q, ends e := by
    rw [vertexParity, Fintype.sum_prod_type]
    trans ∑ e, if x e = true then ends e else 0
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Fintype.sum_bool]
      cases x e
      · simp [← Bool.zero_eq_false]
      · change ((if Dart.vertex (G := G) (e, true) = v then true else 0) +
            (if Dart.vertex (G := G) (e, false) = v then true else 0)) = ends e
        simp only [count, ends, add_comm]
    · rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext e; simp [P, Q, hx]) fun _ _ => rfl
  have pathSum {k : ℕ} (arm : Fin (k + 1) → Dart G)
      (step : ∀ i : Fin k, r.rotate.symm (arm i.castSucc).reverse = arm i.succ) :
      (∑ i, ends (arm i).1) = atVertex (arm 0) + atVertex (arm (Fin.last k)).reverse := by
    have cancel (i : Fin k) : atVertex (arm i.succ) + atVertex (arm i.castSucc).reverse = 0 := by
      have : (arm i.succ).vertex = (arm i.castSucc).reverse.vertex := by
        rw [← step i, ← r.vertex_rotate (r.rotate.symm _), r.rotate.apply_symm_apply]
      simp only [atVertex, this, BooleanRing.add_self]
    have hend (d : Dart G) : ends d.1 = atVertex d + atVertex d.reverse := by
      rcases d with ⟨_, false | true⟩
      · rfl
      · exact add_comm _ _
    have tel := Fin.sum_univ_adjacent_differences
      (fun i => atVertex (arm i)) (fun i => atVertex (arm i).reverse)
    simpa only [BooleanRing.sub_eq_add, cancel, Finset.sum_const_zero, add_zero, zero_add, hend,
      add_comm] using tel
  rw [hsum, Finset.sum_union hd, Finset.sum_map, Finset.sum_map]
  change (∑ i, ends (p i).1) + (∑ j, ends (q j).1) = false
  rw [pathSum p hpStep, pathSum q hqStep]
  simp only [atVertex, hstart, hfinish, BooleanRing.add_self, Bool.zero_eq_false]

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
  have eachInjective (k : Fin 3) : Function.Injective fun i => (path k i).1 := fun _ _ hij =>
    eq_of_heq (Sigma.mk.inj (hinj (a₁ := ⟨k, _⟩) (a₂ := ⟨k, _⟩) hij)).2
  have selected (e : Fin G.edges.length) :
      label e = true ↔ (∃ i, (path 0 i).1 = e) ∨ (∃ i, (path 1 i).1 = e) := by
    rw [hlabel]
    exact ⟨fun ⟨k, hk, i, hi⟩ => by
        fin_cases k; exacts [.inl ⟨i, hi⟩, .inr ⟨i, hi⟩, (hk rfl).elim],
      by rintro (⟨i, hi⟩ | ⟨i, hi⟩); exacts [⟨0, by decide, i, hi⟩, ⟨1, by decide, i, hi⟩]⟩
  have unselected (i : Fin (length 2 + 1)) : label (path 2 i).1 = false :=
    Bool.eq_false_iff.mpr fun h => let ⟨_, hk, _, hj⟩ := (hlabel _).mp h; distinct hk _ i hj
  have hs (k : Fin 3) : (path k 0).vertex = u := hstart k ▸ (start k).property
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
    have he (e) : (∑ f, label f * crossings f e) =
        ∑ f, (if f = e then 0 else label f) * (D.route f).intersectionParity (D.route e) :=
      Finset.sum_congr rfl fun f _ => by by_cases h : f = e <;> simp [crossings, h]
    rcases d with ⟨e, false | true⟩
    · exact (hedge e).trans (congrArg (label e + ·) (he e).symm)
    · exact (add_comm _ _).trans ((hedge e).trans (congrArg (label e + ·) (he e).symm))
  refine r.inverse_rotate_iff_not_inverse_rotate_of_three_paths path start finish hstart hfinish
    hstep (eachInjective 0) color label hlabel unselected crossings ?_
    (fun _ => by simp [crossings]) (fun a b hab i j => ?_) edge hsector
  · intro e f
    by_cases h : e = f
    · subst h; rfl
    · simpa only [crossings, ite_eq_right h, ite_eq_right (Ne.symm h)] using
        Route.intersectionParity_symm (D.route e) (D.route f)
  · simpa only [crossings, ite_eq_right (distinct hab i j), Bool.zero_eq_false] using
      heven a b hab i j

end Cslib.Complexity.Graph.PolygonalDrawing
