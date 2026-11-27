/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexTransport
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic

/-!
# Prescribed positions for all vertices of a polygonal embedding

A common translate of the target positions avoids both finite sets of occupied points.
Transporting through these intermediate positions lets even an entire cycle of vertices
exchange positions. Each sweep preserves the original germ rays and costs at most a factor
of 25 in segment count per distinct declared name.

This is an original finite geometry result about vertex positions and clockwise order.
The edge routes are allowed to deform.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open RotationSystem

-- Place a subset of the names in one sweep when the entire target set is vacant.
private theorem place_subset {G : Graph} {D : PolygonalDrawing G} (hD : D.IsEmbedding)
    (hG : G.incidenceVertices ⊆ G.vertices) (q : ℕ → ℂ)
    (hq : Set.InjOn q {v | v ∈ G.vertices})
    (hvacant : ∀ v ∈ G.vertices, ∀ w ∈ G.vertices, q v ≠ D.vertex w)
    (s : Finset ℕ) (hs : s ⊆ G.vertices.toFinset) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧
      (∀ v ∈ G.vertices, E.vertex v = if v ∈ s then q v else D.vertex v) ∧
      (∀ a : Dart G, ∃ c : ℝ, 0 < c ∧ E.germ a = c • D.germ a) ∧
      (∀ e, (E.route e).segments ≤ 25 ^ s.card * (D.route e).segments) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨D, hD, ?_, fun _ => ⟨1, zero_lt_one, (one_smul ℝ _).symm⟩, ?_⟩
    · intro v _
      simp
    · intro e
      simp
  | @insert v s hv ih =>
    have hvs : v ∈ G.vertices := List.mem_toFinset.mp (hs (Finset.mem_insert_self v s))
    obtain ⟨E, hE, hpos, hgerm, hcount⟩ :=
      ih (fun _ hw => hs (Finset.mem_insert_of_mem hw))
    have hfree : ∀ w ∈ G.vertices, w ≠ v → q v ≠ E.vertex w := by
      intro w hw hwv
      rw [hpos w hw]
      split_ifs
      · exact fun he => hwv (hq hvs hw he).symm
      · exact hvacant v hvs w hw
    obtain ⟨F, hF, hfpos, hfgerm, _, hfcount, _⟩ :=
      hE.exists_single_vertex_transport hG v hvs (q v) hfree
    refine ⟨F, hF, ?_, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst w
        simpa only [ite_true, Finset.mem_insert_self] using hfpos v hw
      · simpa only [hwv, ite_false, Finset.mem_insert, false_or, hpos w hw] using hfpos w hw
    · intro a
      obtain ⟨c, hc, he⟩ := hgerm a
      obtain ⟨d, hd, hf⟩ := hfgerm a
      exact ⟨d * c, mul_pos hd hc, by rw [hf, he, mul_smul]⟩
    · intro e
      rw [Finset.card_insert_of_notMem hv, pow_succ', mul_assoc]
      exact (hfcount e).trans (Nat.mul_le_mul_left _ (hcount e))

/-- Assign distinct prescribed positions to all declared vertices of an actual embedding.
Both ends of every edge keep their original germ rays, so all dart directions and clockwise
orders agree. Each edge has at most `625 ^ n` times its original segment count, where `n`
counts distinct declared names. If the prescribed positions already agree, the original
drawing itself is returned. -/
theorem IsEmbedding.exists_vertex_placement {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : G.incidenceVertices ⊆ G.vertices) (q : ℕ → ℂ)
    (hq : Set.InjOn q {v | v ∈ G.vertices}) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧
      (∀ v ∈ G.vertices, E.vertex v = q v) ∧
      (∀ a : Dart G, ∃ c : ℝ, 0 < c ∧ E.germ a = c • D.germ a) ∧
      (∀ a : Dart G, E.direction a = D.direction a) ∧
      (∀ e, (E.route e).segments ≤ 625 ^ G.vertices.toFinset.card * (D.route e).segments) ∧
      ((∀ v ∈ G.vertices, D.vertex v = q v) → E = D) := by
  classical
  by_cases hsame : ∀ v ∈ G.vertices, D.vertex v = q v
  · refine ⟨D, hD, hsame, fun _ => ⟨1, zero_lt_one, (one_smul ℝ _).symm⟩,
      fun _ => rfl, ?_, fun _ => rfl⟩
    intro e
    have hpow : 1 ≤ (625 : ℕ) ^ G.vertices.toFinset.card := pow_pos (by decide : 0 < (625 : ℕ)) _
    simpa only [one_mul] using Nat.mul_le_mul_right (D.route e).segments hpow
  let s := G.vertices.toFinset
  let pairs := s ×ˢ s
  let bad := pairs.image (fun p => D.vertex p.2 - q p.1) ∪
    pairs.image (fun p => q p.2 - q p.1)
  obtain ⟨z, hz⟩ := bad.exists_notMem
  let u (v : ℕ) := q v + z
  have hpair {v w : ℕ} (hv : v ∈ G.vertices) (hw : w ∈ G.vertices) :
      (v, w) ∈ pairs :=
    Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, List.mem_toFinset.mpr hw⟩
  have hu : Set.InjOn u {v | v ∈ G.vertices} :=
    fun _ hv _ hw he => hq hv hw (add_right_cancel he)
  have huD (v : ℕ) (hv : v ∈ G.vertices) (w : ℕ) (hw : w ∈ G.vertices) :
      u v ≠ D.vertex w := by
    intro he
    exact hz (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(v, w), hpair hv hw, (eq_sub_of_add_eq' he).symm⟩))
  have huq (v : ℕ) (hv : v ∈ G.vertices) (w : ℕ) (hw : w ∈ G.vertices) :
      u v ≠ q w := by
    intro he
    exact hz (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(v, w), hpair hv hw, (eq_sub_of_add_eq' he).symm⟩))
  obtain ⟨F, hF, hfpos, hfgerm, hfcount⟩ := place_subset hD hG u hu huD s (by rfl)
  have hFpos (w : ℕ) (hw : w ∈ G.vertices) : F.vertex w = u w := by
    have hw' : w ∈ s := List.mem_toFinset.mpr hw
    simpa only [hw', ite_true] using hfpos w hw
  obtain ⟨E, hE, hepos, hegerm, hecount⟩ := place_subset hF hG q hq
    (fun v hv w hw => by rw [hFpos w hw]; exact (huq w hw v hv).symm) s (by rfl)
  have hg (a : Dart G) : ∃ c : ℝ, 0 < c ∧ E.germ a = c • D.germ a := by
    obtain ⟨c, hc, he⟩ := hfgerm a
    obtain ⟨d, hd, hf⟩ := hegerm a
    exact ⟨d * c, mul_pos hd hc, by rw [hf, he, mul_smul]⟩
  refine ⟨E, hE, ?_, hg, ?_, ?_, fun he => (hsame he).elim⟩
  · intro v hv
    have hv' : v ∈ s := List.mem_toFinset.mpr hv
    simpa only [hv', ite_true] using hepos v hv
  · intro a
    obtain ⟨c, hc, he⟩ := hg a
    simp only [direction, he, Complex.real_smul, Complex.arg_real_mul _ hc]
  · intro e
    calc
      _ ≤ 25 ^ s.card * (F.route e).segments := hecount e
      _ ≤ 25 ^ s.card * (25 ^ s.card * (D.route e).segments) :=
        Nat.mul_le_mul_left _ (hfcount e)
      _ = _ := by
        rw [← mul_assoc, ← mul_pow]
        rfl

end Cslib.Complexity.Graph.PolygonalDrawing
