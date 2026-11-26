/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferencePatchAssembly
import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual global regularization of reference crossings

An internally constructed named-field patch assembly retains its literal free words,
frozen original routes, vertices, endpoints, simple routes, vertex contacts and positive
germs. Exhaustive actual consecutive-node classification separates local pieces from
original gaps. The common horizontal slab excludes incident gaps, including its boundary
endpoints; disjoint neighborhoods exclude distinct patches and nonincident gaps.

## Main results

* `exists_reference_crossing_regularization`: from `Valid I` alone, the actual local
  pair-contact map bijects old common strict-interior points onto ALL global pair support
  contacts away the declared vertex image. These contacts are transverse at actual open
  global segment parameters, and no three distinct supports meet away declared vertices.

The frozen global route remains literally original: its cut is classified locally without
subdividing that route. Multiple supports at declared vertex stars remain permitted.
This is original finite coordinate geometry. Move parity, frozen placement/isotopy,
Hanani–Tutte, the query/source criterion and full recognition remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

-- This is the actual parameter change used when the global member is the literal
-- original line. Strict source cuts keep every local open contact globally open.
private theorem frozen_parameter_open {α β t : ℝ}
    (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ 1) (ht : t ∈ Set.Ioo 0 1) :
    α + (β - α) * t ∈ Set.Ioo 0 1 := by
  have hl := (left_lt_lineMap_iff_lt ht.1).mpr hαβ
  have hu := (lineMap_lt_right_iff_lt ht.2).mpr hαβ
  rw [AffineMap.lineMap_apply_ring'] at hl hu
  exact ⟨by linarith, by linarith⟩

-- Read the *actual vectors*, not slopes, from an all-real local/global evaluation
-- equation. The affine-map linear-part API supplies the difference calculation.
private theorem vector_of_reparameterization (p q : Route)
    (i : Fin p.segments) (j : Fin q.segments) (α β : ℝ)
    (heval : ∀ t : ℝ, q.eval j (α + (β - α) * t) = p.eval i t) :
    p.point i.succ - p.point i.castSucc =
      (β - α) • (q.point j.succ - q.point j.castSucc) := by
  have hzero : AffineMap.lineMap (q.point j.castSucc) (q.point j.succ) α = p.point i.castSucc := by
    simpa only [mul_zero, add_zero, Route.eval, AffineMap.lineMap_apply_zero] using heval 0
  have hone : AffineMap.lineMap (q.point j.castSucc) (q.point j.succ) β = p.point i.succ := by
    simpa only [mul_one, add_sub_cancel, Route.eval, AffineMap.lineMap_apply_one] using heval 1
  have hlinear := (AffineMap.lineMap (q.point j.castSucc) (q.point j.succ) :
    ℝ →ᵃ[ℝ] ℂ).linear_apply_vsub β α
  simpa only [AffineMap.lineMap_linear, LinearMap.smulRight_apply, LinearMap.id_apply,
    vsub_eq_sub, hone, hzero] using hlinear.symm

-- Transversality is transported using the actual local/global vector factors.
-- This retains the factor 2 of the protected one-segment local member.
private theorem transverse_of_vector_factors
    {a b A B : ℂ} {c d : ℝ}
    (ha : a = c • A) (hb : b = d • B)
    (hab : a.re * b.im - a.im * b.re ≠ 0) :
    A.re * B.im - A.im * B.re ≠ 0 := by
  have hdet : a.re * b.im - a.im * b.re = (c * d) * (A.re * B.im - A.im * B.re) := by
    simp only [ha, hb, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring
  exact (mul_ne_zero_iff.mp (hdet ▸ hab)).2

-- An actual local transverse pair together with its two affine segment embeddings
-- yields actual global OPEN segment parameters and the global determinant. This is
-- private proof composition; the public result constructs the embeddings.
private theorem transport_local_transverse
    (p q P Q : Route) (i : Fin p.segments) (j : Fin q.segments)
    (I : Fin P.segments) (J : Fin Q.segments)
    {α β γ δ u v : ℝ} {w : ℂ}
    (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ 1)
    (hγ : 0 ≤ γ) (hγδ : γ < δ) (hδ : δ ≤ 1)
    (hu : u ∈ Set.Ioo 0 1) (hv : v ∈ Set.Ioo 0 1)
    (hp : p.eval i u = w) (hq : q.eval j v = w)
    (hP : ∀ t : ℝ, P.eval I (α + (β - α) * t) = p.eval i t)
    (hQ : ∀ t : ℝ, Q.eval J (γ + (δ - γ) * t) = q.eval j t)
    (hdet :
      (p.point i.succ - p.point i.castSucc).re * (q.point j.succ - q.point j.castSucc).im -
      (p.point i.succ - p.point i.castSucc).im * (q.point j.succ - q.point j.castSucc).re ≠ 0) :
    ∃ s t : ℝ, s ∈ Set.Ioo 0 1 ∧ t ∈ Set.Ioo 0 1 ∧
      P.eval I s = w ∧ Q.eval J t = w ∧
      0 < β - α ∧ 0 < δ - γ ∧
      (P.point I.succ - P.point I.castSucc).re * (Q.point J.succ - Q.point J.castSucc).im -
      (P.point I.succ - P.point I.castSucc).im * (Q.point J.succ - Q.point J.castSucc).re ≠ 0 :=
  ⟨α + (β - α) * u, γ + (δ - γ) * v,
    frozen_parameter_open hα hαβ hβ hu, frozen_parameter_open hγ hγδ hδ hv,
    (hP u).trans hp, (hQ v).trans hq, sub_pos.mpr hαβ, sub_pos.mpr hγδ,
    transverse_of_vector_factors
      (vector_of_reparameterization p P i I α β hP)
      (vector_of_reparameterization q Q j J γ δ hQ) hdet⟩

-- Forward transport does not assume global contact classification. Completeness supplies
-- the actual ordinal, and both branches embed the same local route in A.drawing.
private theorem actual_patch_segment_embedding {I : FixedRotationInput}
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z) (j : Fin (A.patch z e).segments) :
    ∃ (i : Fin (A.drawing.route e.val).segments) (α β : ℝ),
      0 ≤ α ∧ α < β ∧ β ≤ 1 ∧ ∀ t : ℝ,
        (A.drawing.route e.val).eval i (α + (β - α) * t) = (A.patch z e).eval j t := by
  classical
  let c : ReferencePatchAssembly.EdgeCenter I e.val := ⟨z.val, z.property, e.property⟩
  obtain ⟨q, hq_lt, hq⟩ := List.getElem_of_mem (A.centers_complete e.val c)
  have hembed := A.patch_embedding e.val ⟨q, hq_lt⟩
  rw [Fin.getElem_fin, hq] at hembed
  cases hf : ((subdivide I)[e.val.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.val.isLt)).frozen with
  | false =>
    obtain ⟨i, _, hi⟩ := hembed.1 hf j
    exact ⟨i, 0, 1, le_rfl, zero_lt_one, le_rfl, fun t => by
      simpa only [sub_zero, one_mul, zero_add] using hi t⟩
  | true =>
    have hn : (A.patch z e).segments = 1 := by rw [A.frozen_patch z e hf]; rfl
    have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp (hn ▸ j.isLt))
    exact ⟨0, A.startParam z e, A.finishParam z e,
      (A.cut_bounds z e).1.le, (A.cut_bounds z e).2.1, (A.cut_bounds z e).2.2.le,
      fun t => hj ▸ hembed.2 hf t⟩

-- Each actual local transverse contact is a global transverse nonvertex contact.
-- The converse (excluding extra global contacts) is proved separately below.
private theorem local_contact_global {I : FixedRotationInput}
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e f : ReferencePatchAssembly.IncidentEdge I z) (hef : e ≠ f)
    {w : ℂ} (he : w ∈ (A.patch z e).support) (hf : w ∈ (A.patch z f).support) :
    w ∈ (A.drawing.route e.val).support ∧ w ∈ (A.drawing.route f.val).support ∧
    (∀ v ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex v) ∧
    ∃ (i : Fin (A.drawing.route e.val).segments)
      (j : Fin (A.drawing.route f.val).segments) (u v : ℝ),
      u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
      (A.drawing.route e.val).eval i u = w ∧ (A.drawing.route f.val).eval j v = w ∧
      let a := (A.drawing.route e.val).point i.succ - (A.drawing.route e.val).point i.castSucc
      let b := (A.drawing.route f.val).point j.succ - (A.drawing.route f.val).point j.castSucc
      a.re * b.im - a.im * b.re ≠ 0 := by
  obtain ⟨i, j, u, v, hu, hv, heu, hfv, hdet⟩ := A.patch_transverse z e f hef w he hf
  obtain ⟨i', α, β, hα, hαβ, hβ, hi⟩ := actual_patch_segment_embedding A z e i
  obtain ⟨j', γ, δ, hγ, hγδ, hδ, hj⟩ := actual_patch_segment_embedding A z f j
  obtain ⟨u', v', hu', hv', heu', hfv', _, _, hdet'⟩ :=
    transport_local_transverse (A.patch z e) (A.patch z f)
      (A.drawing.route e.val) (A.drawing.route f.val) i j i' j'
      hα hαβ hβ hγ hγδ hδ hu hv heu hfv hi hj hdet
  exact ⟨heu' ▸ (A.drawing.route e.val).at_mem_support i' ⟨hu'.1.le, hu'.2.le⟩,
    hfv' ▸ (A.drawing.route f.val).at_mem_support j' ⟨hv'.1.le, hv'.2.le⟩,
    fun v hv heq => A.avoids_vertices z.val z.property v hv (Metric.ball_subset_closedBall
      (by simpa only [heq, A.vertex_eq] using A.patch_support z e he)),
    i', j', u', v', hu', hv', heu', hfv', hdet'⟩

-- A closed gap in the COMPLETE sorted cut list misses the open interior of EVERY
-- selected cut, including nonadjacent cuts. End cuts use source endpoints 0 and 1;
-- there is no assumed global disjointness of horizontal projections or patch balls.
private theorem ordered_gap_avoids_all_cuts {ι : Type*}
    (L : List ι) (α β : ι → ℝ)
    (hcut : ∀ z ∈ L, α z < β z)
    (hsorted : L.Pairwise (fun z w => β z < α w))
    (k : Fin (L.length + 1)) {t : ℝ}
    (hlower : ∀ hk : 0 < k.val, β (L[k.val - 1]'(by omega)) ≤ t)
    (hupper : ∀ hk : k.val < L.length, t ≤ α (L[k.val]'hk)) :
    ∀ q : Fin L.length, t ∉ Set.Ioo (α L[q]) (β L[q]) := by
  intro q ht
  by_cases hqk : q.val < k.val
  · have hk : 0 < k.val := Nat.zero_lt_of_lt hqk
    have hprev : k.val - 1 < L.length := by omega
    refine (not_lt_of_ge ?_) ht.2
    by_cases heq : q.val = k.val - 1
    · simpa only [Fin.getElem_fin, heq] using hlower hk
    · have hpair := (List.pairwise_iff_getElem.mp hsorted) q.val (k.val - 1) q.isLt hprev (by omega)
      exact hpair.le.trans ((hcut _ (List.getElem_mem hprev)).le.trans (hlower hk))
  · have hk : k.val < L.length := lt_of_le_of_lt (Nat.le_of_not_gt hqk) q.isLt
    refine (not_lt_of_ge ?_) ht.1
    by_cases heq : k.val = q.val
    · simpa only [Fin.getElem_fin, heq] using hupper hk
    · have hpair := (List.pairwise_iff_getElem.mp hsorted) k.val q.val hk q.isLt (by omega)
      exact (hupper hk).trans ((hcut _ (List.getElem_mem hk)).le.trans hpair.le)

-- The boundary case carries an ACTUAL consecutive center pair, not an arbitrary
-- earlier/later pair. Tags are local proof bookkeeping and never change the word.
private theorem patch_word_pair_cases {ι : Type*} (L : List ι) (a b : ℂ)
    (left middle right : ι → ℂ) {x y : ℂ}
    (hxy : (x, y) ∈ List.consecutivePairs
      (a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b])) :
    (∃ z ∈ L, (x = left z ∧ y = middle z) ∨ (x = middle z ∧ y = right z)) ∨
    (L = [] ∧ x = a ∧ y = b) ∨
    (∃ h : L ≠ [], x = a ∧ y = left (L.head h)) ∨
    (∃ h : L ≠ [], x = right (L.getLast h) ∧ y = b) ∨
    (∃ z w, (z, w) ∈ List.consecutivePairs L ∧ x = right z ∧ y = left w) := by
  let emit : Bool ⊕ ι → List ℂ
    | .inl false => [a]
    | .inl true => [b]
    | .inr z => [left z, middle z, right z]
  let tags : List (Bool ⊕ ι) := .inl false :: L.map Sum.inr ++ [.inl true]
  have hnonempty : ∀ tag, emit tag ≠ [] := by rintro ((_ | _) | _) <;> simp [emit]
  have hword : tags.flatMap emit =
      a :: L.flatMap (fun z => [left z, middle z, right z]) ++ [b] := by
    simp only [tags, List.flatMap_cons, List.flatMap_append, List.flatMap_map,
      emit, List.singleton_append]; rfl
  rw [← hword] at hxy
  rcases (List.mem_consecutivePairs_flatMap (by simp [tags]) hnonempty).mp hxy with
    ⟨tag, htag, hp⟩ | ⟨⟨tag, next⟩, hp, hx, hy⟩
  · rcases tag with v | z
    · cases v <;> simp [emit] at hp
    · exact Or.inl ⟨z, by simpa [tags] using htag, by
        simpa only [emit, List.consecutivePairs_cons_cons, List.consecutivePairs_singleton,
          List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] using hp⟩
  · dsimp only [tags] at hp
    cases L with
    | nil =>
      obtain ⟨rfl, rfl⟩ : tag = .inl false ∧ next = .inl true := by
        simpa only [List.map_nil, List.cons_append, List.nil_append,
          List.consecutivePairs_cons_cons, List.consecutivePairs_singleton,
          List.mem_singleton, Prod.mk.injEq] using hp
      exact Or.inr (Or.inl ⟨rfl, hx, hy⟩)
    | cons z zs =>
      rw [List.consecutivePairs_append (by simp) (by simp), List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.map_cons, List.consecutivePairs_cons_cons, List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
          exact Or.inr (Or.inr (Or.inl ⟨List.cons_ne_nil _ _, hx, hy⟩))
        · obtain ⟨k, hk, rfl, rfl⟩ :
              ∃ k, ∃ hk : k + 1 < (z :: zs).length,
                Sum.inr (z :: zs)[k] = tag ∧ Sum.inr (z :: zs)[k + 1] = next := by
            simpa only [← List.map_cons, List.mem_consecutivePairs_iff_exists_getElem,
              List.length_map, List.getElem_map] using hp
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(z :: zs)[k], (z :: zs)[k + 1],
            List.getElem_mem_consecutivePairs (z :: zs) k hk, hx, hy⟩)))
      · obtain ⟨rfl, rfl⟩ :
            tag = Sum.inr ((z :: zs).getLast (List.cons_ne_nil _ _)) ∧ next = Sum.inl true := by
          simpa only [List.consecutivePairs_singleton, List.mem_cons, List.not_mem_nil, or_false,
            List.head_cons, List.getLast_cons (by simp : (z :: zs).map Sum.inr ≠ []),
            List.getLast_map, Prod.mk.injEq] using hp
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨List.cons_ne_nil _ _, hx, hy⟩)))

private theorem gap_interpolation_avoids_cuts {ι : Type*}
    (L : List ι) (α β : ι → ℝ) (a b : ℂ)
    (hcut : ∀ z ∈ L, α z < β z)
    (hsorted : L.Pairwise (fun z w => β z < α w))
    (k : Fin (L.length + 1)) {u v t : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) (ht : t ∈ Set.Icc 0 1)
    (hprev : ∀ hk : 0 < k.val, β (L[k.val - 1]'(by omega)) = u)
    (hnext : ∀ hk : k.val < L.length, α (L[k.val]'hk) = v) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) t =
        AffineMap.lineMap a b s ∧
      ∀ z ∈ L, s ∉ Set.Ioo (α z) (β z) := by
  let s := AffineMap.lineMap u v t
  have hs : s ∈ Set.Icc u v := by
    simpa only [segment_eq_Icc huv] using lineMap_mem_segment ℝ u v ht
  refine ⟨s, ⟨hu.trans hs.1, hs.2.trans hv⟩,
    ((AffineMap.lineMap a b : ℝ →ᵃ[ℝ] ℂ).apply_lineMap u v t).symm, fun z hz => ?_⟩
  obtain ⟨q, hq_lt, rfl⟩ := List.getElem_of_mem hz
  exact ordered_gap_avoids_all_cuts L α β hcut hsorted k
    (fun hk => (hprev hk).symm ▸ hs.1) (fun hk => (hnext hk).symm ▸ hs.2) ⟨q, hq_lt⟩

-- A point on ANY emitted node pair is either on an actual local piece or on
-- an original closed gap avoiding every open cut. Adjacent cuts alone bound gaps.
private theorem patch_word_contact_cases {ι : Type*}
    (L : List ι) (α β : ι → ℝ) (a b : ℂ) (middle : ι → ℂ)
    (hcut : ∀ z ∈ L, 0 < α z ∧ α z < β z ∧ β z < 1)
    (hsorted : L.Pairwise (fun z w => β z < α w))
    {x y : ℂ} {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hxy : (x, y) ∈ List.consecutivePairs
      (a :: L.flatMap (fun z => [AffineMap.lineMap a b (α z), middle z,
        AffineMap.lineMap a b (β z)]) ++ [b])) :
    (∃ z ∈ L, AffineMap.lineMap x y t ∈
      segment ℝ (AffineMap.lineMap a b (α z)) (middle z) ∪
      segment ℝ (middle z) (AffineMap.lineMap a b (β z))) ∨
    (∃ s ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap x y t = AffineMap.lineMap a b s ∧
      ∀ z ∈ L, s ∉ Set.Ioo (α z) (β z)) := by
  have hcuts : ∀ z ∈ L, α z < β z := fun z hz => (hcut z hz).2.1
  rcases patch_word_pair_cases L a b
      (fun z => AffineMap.lineMap a b (α z)) middle
      (fun z => AffineMap.lineMap a b (β z)) hxy with
    ⟨z, hz, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hL, rfl, rfl⟩ |
      ⟨hL, rfl, rfl⟩ | ⟨hL, rfl, rfl⟩ | ⟨z, w, hp, rfl, rfl⟩
  · exact Or.inl ⟨z, hz, Or.inl (lineMap_mem_segment ℝ _ _ ht)⟩
  · exact Or.inl ⟨z, hz, Or.inr (lineMap_mem_segment ℝ _ _ ht)⟩
  · exact Or.inr ⟨t, ht, rfl, by simp only [hL, List.not_mem_nil, false_implies, implies_true]⟩
  · have hf := hcut (L.head hL) (List.head_mem hL)
    simpa only [AffineMap.lineMap_apply_zero] using Or.inr <|
      gap_interpolation_avoids_cuts L α β x b hcuts hsorted 0 le_rfl hf.1.le
        (hf.2.1.trans hf.2.2).le ht (fun hk => (Nat.lt_irrefl 0 hk).elim)
        (fun _ => by simp only [List.head_eq_getElem hL, Fin.val_zero])
  · have hl := hcut (L.getLast hL) (List.getLast_mem hL)
    simpa only [AffineMap.lineMap_apply_one] using Or.inr <|
      gap_interpolation_avoids_cuts L α β a y hcuts hsorted (Fin.last L.length)
        (hl.1.trans hl.2.1).le hl.2.2.le le_rfl ht
        (fun _ => by simp only [List.getLast_eq_getElem hL, Fin.val_last])
        (fun hk => (Nat.lt_irrefl L.length hk).elim)
  · obtain ⟨k, hk, hkz, hkw⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp hp
    have hz := hcut z (hkz ▸ List.getElem_mem (show k < L.length by omega))
    have hw := hcut w (hkw ▸ List.getElem_mem hk)
    have hzw := (List.pairwise_iff_getElem.mp hsorted) k (k + 1) (by omega) hk (by omega)
    rw [hkz, hkw] at hzw
    exact Or.inr <| gap_interpolation_avoids_cuts L α β a b hcuts hsorted ⟨k + 1, by omega⟩
      (hz.1.trans hz.2.1).le hzw.le (hw.2.1.trans hw.2.2).le ht
      (fun _ => by simpa only [Nat.add_sub_cancel] using congrArg β hkz) (fun _ => congrArg α hkw)

private theorem free_patch_piece_support {I : FixedRotationInput}
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z)
    (hf : ((subdivide I)[e.val.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.val.isLt)).frozen = false) :
    let mid : ℂ := z.val + ⟨0, A.height z e⟩
    segment ℝ (A.patch z e).start mid ∪ segment ℝ mid (A.patch z e).finish ⊆
      (A.patch z e).support := by
  dsimp only
  intro w hw
  have hp := A.patch_eq z e
  simp only [hf, Bool.false_eq_true, ↓reduceIte] at hp
  obtain ⟨hmid, hn⟩ : (A.patch z e).point (0 : Fin (A.patch z e).segments).succ =
      z.val + (⟨0, A.height z e⟩ : ℂ) ∧ (A.patch z e).bends = 1 := by
    rw [hp]; cases decide (((referenceDrawing I).route e.val).finish.re <
      ((referenceDrawing I).route e.val).start.re) <;> exact ⟨rfl, rfl⟩
  rcases hw with hw | hw <;> rw [segment_eq_image_lineMap ℝ _ _] at hw <;>
    obtain ⟨t, ht, heq⟩ := hw <;> apply ((A.patch z e).mem_support_iff w).mpr
  · exact ⟨0, t, ht, by simpa only [Route.eval, Fin.castSucc_zero, Route.start, hmid] using heq⟩
  · have hindex : (Fin.last (A.patch z e).bends).castSucc =
        (0 : Fin (A.patch z e).segments).succ :=
      Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last, Fin.val_succ, Fin.val_zero, hn])
    exact ⟨Fin.last (A.patch z e).bends, t, ht, by
      simpa only [Route.eval, hindex, hmid, Fin.succ_last, Route.finish] using heq⟩

private theorem assembled_support_cases {I : FixedRotationInput}
    (A : ReferencePatchAssembly I) (e : Fin (subdivisionGraph I).edges.length)
    {w : ℂ} (hw : w ∈ (A.drawing.route e).support) :
    (∃ z : ReferencePatchAssembly.EdgeCenter I e,
      w ∈ (A.patch ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩).support) ∨
    (∃ t ∈ Set.Icc (0 : ℝ) 1, ((referenceDrawing I).route e).eval 0 t = w ∧
      ∀ z : ReferencePatchAssembly.EdgeCenter I e,
        t ∉ Set.Ioo (A.startParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩)
          (A.finishParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩)) := by
  classical
  let D := referenceDrawing I
  let Z := ReferencePatchAssembly.EdgeCenter I e
  let α : Z → ℝ := fun z => A.startParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩
  let β : Z → ℝ := fun z => A.finishParam ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩
  let mid : Z → ℂ := fun z => z.val + ⟨0, A.height ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩⟩
  have hroute := A.route_eq e
  have hcut (z : Z) := A.cut_bounds ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩
  cases hf : ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen with
  | true =>
    have hroute' : A.drawing.route e = D.route e := by simpa only [hf, ↓reduceIte] using hroute
    rw [hroute'] at hw
    obtain ⟨i, t, ht, heq⟩ := ((D.route e).mem_support_iff w).mp hw
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    by_cases hpatch : ∃ z : Z, t ∈ Set.Ioo (α z) (β z)
    · obtain ⟨z, hz⟩ := hpatch
      refine Or.inl ⟨z, ?_⟩
      rw [A.frozen_patch ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩ hf, Route.support_line]
      change w ∈ segment ℝ (AffineMap.lineMap (D.route e).start (D.route e).finish (α z))
        (AffineMap.lineMap (D.route e).start (D.route e).finish (β z))
      rw [← image_segment ℝ (AffineMap.lineMap (D.route e).start (D.route e).finish) (α z) (β z),
        segment_eq_Icc (hcut z).2.1.le]
      exact ⟨t, ⟨hz.1.le, hz.2.le⟩, heq⟩
    · exact Or.inr ⟨t, ht, heq, fun z hz => hpatch ⟨z, hz⟩⟩
  | false =>
    let word := (D.route e).start :: (A.centers e).flatMap
      (fun z => [AffineMap.lineMap (D.route e).start (D.route e).finish (α z), mid z,
        AffineMap.lineMap (D.route e).start (D.route e).finish (β z)]) ++ [(D.route e).finish]
    obtain ⟨i, t, ht, heq⟩ := ((A.drawing.route e).mem_support_iff w).mp hw
    have hnodes : ∃ x y : ℂ, (x, y) ∈ List.consecutivePairs word ∧
        (A.drawing.route e).eval i t = AffineMap.lineMap x y t := by
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hroute
      clear heq
      revert i
      rw [hroute]
      cases hL : A.centers e with
      | nil =>
        exact fun j => ⟨(D.route e).start, (D.route e).finish,
          by simp [word, hL, List.consecutivePairs_cons_cons, List.consecutivePairs_singleton],
          Route.eval_line _ _ j t⟩
      | cons z zs =>
        intro j
        let nodes := [mid z, AffineMap.lineMap (D.route e).start (D.route e).finish (β z)] ++
          zs.flatMap (fun u => [AffineMap.lineMap (D.route e).start (D.route e).finish (α u),
            mid u, AffineMap.lineMap (D.route e).start (D.route e).finish (β u)]) ++
            [(D.route e).finish]
        have hword : word = (D.route e).start ::
            AffineMap.lineMap (D.route e).start (D.route e).finish (α z) :: nodes := by
          simp only [word, hL, List.flatMap_cons, List.cons_append, List.nil_append, nodes]
        have hj : j.val + 1 < word.length := by
          have h := j.isLt
          simp only [Route.segments_foldl_append] at h
          change j.val < 1 + nodes.length at h
          rw [hword, List.length_cons, List.length_cons]; omega
        refine ⟨word[j.val], word[j.val + 1], List.getElem_mem_consecutivePairs word j.val hj, ?_⟩
        simpa only [hword] using Route.eval_foldl_append_line (D.route e).start
          (AffineMap.lineMap (D.route e).start (D.route e).finish (α z)) nodes j t
    obtain ⟨x, y, hxy, hev⟩ := hnodes
    rcases patch_word_contact_cases (A.centers e) α β (D.route e).start
        (D.route e).finish mid (fun z _ => hcut z) (A.centers_ordered e) ht hxy with
      ⟨z, _, hz⟩ | ⟨s, hs, hsw, hav⟩
    · have hp := free_patch_piece_support A ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩ hf
      rw [A.patch_start, A.patch_finish] at hp
      exact Or.inl ⟨z, heq ▸ (hev.symm ▸ hp hz)⟩
    · exact Or.inr ⟨s, hs, hsw.symm.trans (hev.symm.trans heq),
        fun z => hav z (A.centers_complete e z)⟩

-- Only a local route's two actual endpoints can lie on the boundary of the
-- common horizontal slab. This is stronger than mere containment in its ball.
private theorem patch_strict_slab_or_ends {I : FixedRotationInput}
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z) {w : ℂ}
    (hw : w ∈ (A.patch z e).support) :
    w = (A.patch z e).start ∨ w = (A.patch z e).finish ∨
      w.re ∈ Set.Ioo (z.val.re - A.extent z) (z.val.re + A.extent z) := by
  have hr := A.extent_pos z
  let r := A.extent z
  let s := ((referenceDrawing I).route e.val).start.re +
    ((referenceDrawing I).route e.val).finish.re
  let keep := ((subdivide I)[e.val.val]'(by
    simpa only [subdivisionGraph, List.length_map] using e.val.isLt)).frozen
  let raw := if keep then Route.line (⟨-r, -r * s⟩ : ℂ) ⟨r, r * s⟩
    else Route.slopeDetour r s (A.height z e)
  have hraw : ∀ v ∈ raw.support, v = raw.start ∨ v = raw.finish ∨ v.re ∈ Set.Ioo (-r) r := by
    dsimp only [raw]
    cases hf : keep <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals intro v hv; obtain ⟨i, t, ht, he⟩ := (Route.mem_support_iff _ v).mp hv
    · rw [Route.eval_slopeDetour] at he
      by_cases hi : i.val = 0
      · rw [ite_eq_left hi] at he
        by_cases ht0 : t = 0
        · exact Or.inl <| by simpa only [raw, hf, Bool.false_eq_true, ↓reduceIte, ht0,
            AffineMap.lineMap_apply_zero, Route.start_slopeDetour] using he.symm
        · have hx := congrArg Complex.re he
          simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
            smul_eq_mul, mul_zero, add_zero] at hx
          have htpos := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          exact Or.inr <| Or.inr ⟨by linarith [mul_pos htpos hr],
            by linarith [mul_nonneg (sub_nonneg.mpr ht.2) hr.le]⟩
      · rw [ite_eq_right hi] at he
        by_cases ht1 : t = 1
        · exact Or.inr <| Or.inl <| by simpa only [raw, hf, Bool.false_eq_true, ↓reduceIte, ht1,
            AffineMap.lineMap_apply_one, Route.finish_slopeDetour] using he.symm
        · have hx := congrArg Complex.re he
          simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
            smul_eq_mul, mul_zero, zero_add] at hx
          have h1t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
          exact Or.inr <| Or.inr ⟨by linarith [mul_nonneg ht.1 hr.le], by linarith [mul_pos h1t hr]⟩
    · rw [Route.eval_line] at he
      by_cases ht0 : t = 0
      · exact Or.inl <| by simpa only [raw, hf, ↓reduceIte, ht0,
          AffineMap.lineMap_apply_zero, Route.start_line] using he.symm
      · by_cases ht1 : t = 1
        · exact Or.inr <| Or.inl <| by simpa only [raw, hf, ↓reduceIte, ht1,
            AffineMap.lineMap_apply_one, Route.finish_line] using he.symm
        · have hx := congrArg Complex.re he
          simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
            smul_eq_mul] at hx
          have htpos := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have h1t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
          exact Or.inr <| Or.inr ⟨by linarith [mul_pos htpos hr], by linarith [mul_pos h1t hr]⟩
  have hp := A.patch_eq z e
  change A.patch z e = (if decide (((referenceDrawing I).route e.val).finish.re <
    ((referenceDrawing I).route e.val).start.re) then raw.reverse else raw).translate z.val at hp
  rw [hp, Route.support_translate] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  have hv' : v ∈ raw.support := by
    cases hflip : decide (((referenceDrawing I).route e.val).finish.re <
        ((referenceDrawing I).route e.val).start.re) <;>
      simp_all only [Bool.false_eq_true, ↓reduceIte, Route.support_reverse]
  have hend {u : ℂ} (hu : u = raw.start ∨ u = raw.finish) :
      z.val + u = (A.patch z e).start ∨ z.val + u = (A.patch z e).finish := by
    change z.val + u = (A.patch z e).endpoint false ∨ z.val + u = (A.patch z e).endpoint true
    rw [hp]
    cases decide (((referenceDrawing I).route e.val).finish.re <
        ((referenceDrawing I).route e.val).start.re) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Route.endpoint_translate,
        Route.endpoint_reverse] <;> rcases hu with rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl
  rcases hraw v hv' with rfl | rfl | hx
  · rcases hend (Or.inl rfl) with h | h <;> simp [h]
  · rcases hend (Or.inr rfl) with h | h <;> simp [h]
  · exact Or.inr <| Or.inr <| by
      simp only [Complex.add_re]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem reference_open_of_support {I : FixedRotationInput} (hI : Valid I)
    (e : Fin (subdivisionGraph I).edges.length) {w : ℂ}
    (hw : w ∈ ((referenceDrawing I).route e).support)
    (hvertex : ∀ v ∈ (subdivisionGraph I).vertices, w ≠ (referenceDrawing I).vertex v) :
    w ∈ openSegment ℝ ((referenceDrawing I).route e).start
      ((referenceDrawing I).route e).finish := by
  have hend (tag : Bool) : w ≠ ((referenceDrawing I).route e).endpoint tag :=
    (referenceDrawing I).endpoint_eq e tag ▸
      hvertex _ (((referenceOrder_enumerates hI).2 _).mp ((subdivision_endpoint_spec hI e).1 tag))
  exact mem_openSegment_of_ne_left_right (hend false).symm (hend true).symm
    (Route.support_line _ _ ▸ hw)

private theorem old_support_pair_eq_center {I : FixedRotationInput} (hI : Valid I)
    (z : referenceCrossingPoints I) (e f : ReferencePatchAssembly.IncidentEdge I z)
    (hef : e ≠ f) {w : ℂ}
    (he : w ∈ ((referenceDrawing I).route e.val).support)
    (hf : w ∈ ((referenceDrawing I).route f.val).support)
    (hvertex : ∀ v ∈ (subdivisionGraph I).vertices, w ≠ (referenceDrawing I).vertex v) :
    w = z.val :=
  have hzv : ∀ v ∈ (subdivisionGraph I).vertices, z.val ≠ (referenceDrawing I).vertex v :=
    fun _ hv => referenceDrawing_crossing_ne_vertex hI z.property hv
  referenceDrawing_open_inter_subsingleton hI e.val f.val (fun h => hef (Subtype.ext h))
    ⟨reference_open_of_support hI e.val he hvertex, reference_open_of_support hI f.val hf hvertex⟩
    ⟨reference_open_of_support hI e.val e.property hzv,
      reference_open_of_support hI f.val f.property hzv⟩

private theorem patch_real_ends {I : FixedRotationInput}
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z) :
    let back := ((referenceDrawing I).route e.val).finish.re <
      ((referenceDrawing I).route e.val).start.re
    ((A.patch z e).start.re = z.val.re + (if back then A.extent z else -A.extent z)) ∧
    ((A.patch z e).finish.re = z.val.re + (if back then -A.extent z else A.extent z)) := by
  simp only [A.patch_eq]
  by_cases hb : ((referenceDrawing I).route e.val).finish.re <
      ((referenceDrawing I).route e.val).start.re <;>
    simp only [hb, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
    split_ifs <;> constructor <;> rfl

private theorem old_gap_outside_slab {I : FixedRotationInput} (hI : Valid I)
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e : ReferencePatchAssembly.IncidentEdge I z) {t : ℝ}
    (ht : t ∉ Set.Ioo (A.startParam z e) (A.finishParam z e)) :
    (((referenceDrawing I).route e.val).eval 0 t).re ≤ z.val.re - A.extent z ∨
      z.val.re + A.extent z ≤ (((referenceDrawing I).route e.val).eval 0 t).re := by
  have hends := patch_real_ends A z e
  set a := ((referenceDrawing I).route e.val).start.re
  set b := ((referenceDrawing I).route e.val).finish.re
  have hne : a ≠ b := fun heq =>
    (Route.isSimple_line_iff _ _).mp (referenceDrawing_simple hI e.val) (congrArg parabolaPoint heq)
  have hproj (u : ℝ) : (AffineMap.lineMap ((referenceDrawing I).route e.val).start
      ((referenceDrawing I).route e.val).finish u).re = AffineMap.lineMap a b u :=
    Complex.reCLM.toLinearMap.toAffineMap.apply_lineMap _ _ u
  rw [A.patch_start, A.patch_finish, hproj, hproj] at hends
  have hside : t ≤ A.startParam z e ∨ A.finishParam z e ≤ t :=
    (not_and_or.mp ht).imp le_of_not_gt le_of_not_gt
  have hev : (((referenceDrawing I).route e.val).eval 0 t).re = AffineMap.lineMap a b t := hproj t
  rw [hev]
  rcases lt_or_gt_of_ne hne with hab | hba
  · simp only [not_lt.mpr hab.le, ↓reduceIte] at hends
    rcases hside with ht | ht
    · exact Or.inl <| by linarith [(lineMap_le_lineMap_iff_of_lt' hab).mpr ht, hends.1]
    · exact Or.inr <| by linarith [(lineMap_le_lineMap_iff_of_lt' hab).mpr ht, hends.2]
  · simp only [hba, ↓reduceIte] at hends
    rcases hside with ht | ht <;> have h := (lineMap_le_lineMap_iff_of_lt' hba).mpr
      (sub_le_sub_left ht 1) <;>
      rw [AffineMap.lineMap_apply_one_sub, AffineMap.lineMap_apply_one_sub] at h
    · exact Or.inr <| by linarith [hends.1]
    · exact Or.inl <| by linarith [hends.2]

private theorem incident_gap_excludes_other_patch {I : FixedRotationInput} (hI : Valid I)
    (A : ReferencePatchAssembly I) (z : referenceCrossingPoints I)
    (e f : ReferencePatchAssembly.IncidentEdge I z) (hef : e ≠ f)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hgap : t ∉ Set.Ioo (A.startParam z f) (A.finishParam z f)) :
    ((referenceDrawing I).route f.val).eval 0 t ∉ (A.patch z e).support := by
  intro hw
  let w := ((referenceDrawing I).route f.val).eval 0 t
  have hwv : ∀ v ∈ (subdivisionGraph I).vertices, w ≠ (referenceDrawing I).vertex v := fun v hv h =>
    A.avoids_vertices z.val z.property v hv <|
      Metric.ball_subset_closedBall (h ▸ A.patch_support z e hw)
  have hf : w ∈ ((referenceDrawing I).route f.val).support :=
    ((referenceDrawing I).route f.val).at_mem_support 0 ht
  have hnotend {p : ℝ} (hp : p ∈ Set.Icc 0 1)
      (hwe : w = AffineMap.lineMap ((referenceDrawing I).route e.val).start
        ((referenceDrawing I).route e.val).finish p)
      (habs : (A.patch z e).start.re = w.re ∨ (A.patch z e).finish.re = w.re) : False := by
    have he : w ∈ ((referenceDrawing I).route e.val).support :=
      hwe ▸ Route.support_line _ _ ▸ lineMap_mem_segment ℝ _ _ hp
    have hwz := old_support_pair_eq_center hI z e f hef he hf hwv
    have hends := patch_real_ends A z e
    rcases habs with h | h <;> [have := hends.1; have := hends.2] <;>
      rw [h, congrArg Complex.re hwz] at this <;> split_ifs at this <;> linarith [A.extent_pos z]
  have hcb := A.cut_bounds z e
  rcases patch_strict_slab_or_ends A z e hw with hwstart | hwfinish | hwslab
  · exact hnotend ⟨hcb.1.le, (hcb.2.1.trans hcb.2.2).le⟩ (A.patch_start z e ▸ hwstart)
      (Or.inl (congrArg Complex.re hwstart.symm))
  · exact hnotend ⟨(hcb.1.trans hcb.2.1).le, hcb.2.2.le⟩ (A.patch_finish z e ▸ hwfinish)
      (Or.inr (congrArg Complex.re hwfinish.symm))
  · exact (old_gap_outside_slab hI A z f hgap).elim (not_lt_of_ge · hwslab.1)
      (not_lt_of_ge · hwslab.2)

-- The frozen original line is partitioned semantically into its literal local cuts
-- and retained gaps as well. It is NOT globally subdivided or altered by this proof.
private theorem global_contact_same_patch {I : FixedRotationInput} (hI : Valid I)
    (A : ReferencePatchAssembly I) (e f : Fin (subdivisionGraph I).edges.length)
    (hef : e ≠ f) {w : ℂ}
    (he : w ∈ (A.drawing.route e).support) (hf : w ∈ (A.drawing.route f).support)
    (hvertex : ∀ v ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex v) :
    ∃ (z : referenceCrossingPoints I)
      (hez : z.val ∈ ((referenceDrawing I).route e).support)
      (hfz : z.val ∈ ((referenceDrawing I).route f).support),
      w ∈ (A.patch z ⟨e, hez⟩).support ∧ w ∈ (A.patch z ⟨f, hfz⟩).support := by
  have hvertex' : ∀ v ∈ (subdivisionGraph I).vertices, w ≠ (referenceDrawing I).vertex v := by
    simpa only [A.vertex_eq] using hvertex
  have patch_gap (e f : Fin (subdivisionGraph I).edges.length) (hef : e ≠ f)
      (z : ReferencePatchAssembly.EdgeCenter I e)
      (hp : w ∈ (A.patch ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩).support)
      (t : ℝ) (ht : t ∈ Set.Icc 0 1) (heval : ((referenceDrawing I).route f).eval 0 t = w)
      (hg : ∀ c : ReferencePatchAssembly.EdgeCenter I f,
        t ∉ Set.Ioo (A.startParam ⟨c.val, c.property.1⟩ ⟨f, c.property.2⟩)
          (A.finishParam ⟨c.val, c.property.1⟩ ⟨f, c.property.2⟩)) : False := by
    by_cases hz : z.val ∈ ((referenceDrawing I).route f).support
    · exact incident_gap_excludes_other_patch hI A ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩
        ⟨f, hz⟩ (fun h => hef (congrArg Subtype.val h)) ht (hg ⟨z.val, z.property.1, hz⟩)
        (heval.symm ▸ hp)
    · exact Set.disjoint_left.mp (A.avoids_nonincident z.val z.property.1 f hz)
        (Metric.ball_subset_closedBall (A.patch_support ⟨z.val, z.property.1⟩ ⟨e, z.property.2⟩ hp))
        (heval ▸ ((referenceDrawing I).route f).at_mem_support 0 ht)
  rcases assembled_support_cases A e he with ⟨z, hp⟩ | ⟨t, ht, hte, htg⟩ <;>
    rcases assembled_support_cases A f hf with ⟨c, hq⟩ | ⟨u, hu, hue, hug⟩
  · rcases z with ⟨z, hzc, hze⟩; rcases c with ⟨c, hcc, hcf⟩
    obtain rfl : z = c := Classical.byContradiction fun hne =>
      Set.disjoint_left.mp (A.balls_disjoint hzc hcc hne)
        (Metric.ball_subset_closedBall (A.patch_support ⟨z, hzc⟩ ⟨e, hze⟩ hp))
        (Metric.ball_subset_closedBall (A.patch_support ⟨c, hcc⟩ ⟨f, hcf⟩ hq))
    exact ⟨⟨z, hzc⟩, hze, hcf, hp, hq⟩
  · exact (patch_gap e f hef z hp u hu hue hug).elim
  · exact (patch_gap f e hef.symm c hq t ht hte htg).elim
  · have heold := hte ▸ ((referenceDrawing I).route e).at_mem_support 0 ht
    let z : referenceCrossingPoints I := ⟨w, e, f, hef,
      reference_open_of_support hI e heold hvertex',
      reference_open_of_support hI f (hue ▸ ((referenceDrawing I).route f).at_mem_support 0 hu)
        hvertex'⟩
    rcases hte ▸ old_gap_outside_slab hI A z ⟨e, heold⟩ (htg ⟨w, z.property, heold⟩) with h | h <;>
      linarith [A.extent_pos z]

/-- Construct an actual global reference crossing regularization from valid input alone.
The output assembly retains its literal route construction and all named preservation
properties. The map on each old pair crossing is its actual corresponding local contact;
it bijects onto ALL global common support points away the declared vertex image.
Every such point is transverse at actual open global segment parameters, and no three
indexed supports meet away declared vertices. This does not assert move parity or HT. -/
theorem exists_reference_crossing_regularization {I : FixedRotationInput} (hI : Valid I) :
    let E := Fin (subdivisionGraph I).edges.length
    let old : E → E → Set ℂ := fun e f =>
      openSegment ℝ ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish ∩
      openSegment ℝ ((referenceDrawing I).route f).start ((referenceDrawing I).route f).finish
    ∃ A : ReferencePatchAssembly I, ∃ κ : E → E → ℂ → ℂ,
      let target : E → E → Set ℂ := fun e f => {w |
        w ∈ (A.drawing.route e).support ∧ w ∈ (A.drawing.route f).support ∧
        ∀ v ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex v}
      (∀ e f : E, e ≠ f →
        Set.BijOn (κ e f) (old e f) (target e f) ∧
        (∀ z ∈ old e f,
          ∃ (hz : z ∈ referenceCrossingPoints I)
            (he : z ∈ ((referenceDrawing I).route e).support)
            (hf : z ∈ ((referenceDrawing I).route f).support),
            κ e f z ∈ (A.patch ⟨z, hz⟩ ⟨e, he⟩).support ∧
            κ e f z ∈ (A.patch ⟨z, hz⟩ ⟨f, hf⟩).support) ∧
        (∀ w ∈ target e f,
          ∃ (i : Fin (A.drawing.route e).segments) (j : Fin (A.drawing.route f).segments)
            (u v : ℝ), u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
            (A.drawing.route e).eval i u = w ∧ (A.drawing.route f).eval j v = w ∧
            let a := (A.drawing.route e).point i.succ - (A.drawing.route e).point i.castSucc
            let b := (A.drawing.route f).point j.succ - (A.drawing.route f).point j.castSucc
            a.re * b.im - a.im * b.re ≠ 0)) ∧
      (∀ e f g : E, e ≠ f → e ≠ g → f ≠ g → ∀ w : ℂ,
        (∀ v ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex v) →
        w ∈ (A.drawing.route e).support → w ∈ (A.drawing.route f).support →
        w ∉ (A.drawing.route g).support) := by
  classical
  obtain ⟨A⟩ := exists_reference_patch_assembly hI
  let E := Fin (subdivisionGraph I).edges.length
  let old : E → E → Set ℂ := fun e f =>
    openSegment ℝ ((referenceDrawing I).route e).start ((referenceDrawing I).route e).finish ∩
    openSegment ℝ ((referenceDrawing I).route f).start ((referenceDrawing I).route f).finish
  have hsupport (e f : E) (z : ℂ) (hz : z ∈ old e f) :
      z ∈ ((referenceDrawing I).route e).support ∧ z ∈ ((referenceDrawing I).route f).support :=
    ⟨Route.support_line _ _ ▸ openSegment_subset_segment ℝ _ _ hz.1,
      Route.support_line _ _ ▸ openSegment_subset_segment ℝ _ _ hz.2⟩
  let κ : E → E → ℂ → ℂ := fun e f z =>
    if h : e ≠ f ∧ z ∈ old e f then
      Classical.choose (A.patch_pair_unique ⟨z, e, f, h.1, h.2.1, h.2.2⟩
        ⟨e, (hsupport e f z h.2).1⟩ ⟨f, (hsupport e f z h.2).2⟩
        (fun heq => h.1 (congrArg Subtype.val heq)))
    else 0
  have hκ (e f : E) (hef : e ≠ f) (z : ℂ) (hz : z ∈ old e f) :
      ∃ (hzC : z ∈ referenceCrossingPoints I)
        (hez : z ∈ ((referenceDrawing I).route e).support)
        (hfz : z ∈ ((referenceDrawing I).route f).support),
        κ e f z ∈ (A.patch ⟨z, hzC⟩ ⟨e, hez⟩).support ∧
        κ e f z ∈ (A.patch ⟨z, hzC⟩ ⟨f, hfz⟩).support := by
    refine ⟨⟨e, f, hef, hz.1, hz.2⟩, (hsupport e f z hz).1, (hsupport e f z hz).2, ?_⟩
    dsimp only [κ]; rw [dite_eq_left ⟨hef, hz⟩]
    exact (Classical.choose_spec (A.patch_pair_unique _ _ _ (ne_of_apply_ne Subtype.val hef))).1
  let target : E → E → Set ℂ := fun e f => {w |
    w ∈ (A.drawing.route e).support ∧ w ∈ (A.drawing.route f).support ∧
    ∀ v ∈ (subdivisionGraph I).vertices, w ≠ A.drawing.vertex v}
  refine ⟨A, κ, fun e f hef => ?_, fun e f g hef heg hfg w hvertex he hf hg => ?_⟩
  · have hmaps : Set.MapsTo (κ e f) (old e f) (target e f) := fun z hz => by
      obtain ⟨hzC, hez, hfz, he, hf⟩ := hκ e f hef z hz
      obtain ⟨hE, hF, hV, _⟩ := local_contact_global A ⟨z, hzC⟩ ⟨e, hez⟩ ⟨f, hfz⟩
        (ne_of_apply_ne Subtype.val hef) he hf
      exact ⟨hE, hF, hV⟩
    have hinj : Set.InjOn (κ e f) (old e f) := fun _ hx _ hy _ =>
      referenceDrawing_open_inter_subsingleton hI e f hef hx hy
    have hsurj : Set.SurjOn (κ e f) (old e f) (target e f) := fun w hw => by
      obtain ⟨z, hez, hfz, he, hf⟩ := global_contact_same_patch hI A e f hef hw.1 hw.2.1 hw.2.2
      have hzv (v) := referenceDrawing_crossing_ne_vertex (v := v) hI z.property
      have hz : z.val ∈ old e f :=
        ⟨reference_open_of_support hI e hez hzv, reference_open_of_support hI f hfz hzv⟩
      obtain ⟨_, _, _, hκe, hκf⟩ := hκ e f hef z.val hz
      obtain ⟨_, _, huniq⟩ :=
        A.patch_pair_unique z ⟨e, hez⟩ ⟨f, hfz⟩ (ne_of_apply_ne Subtype.val hef)
      exact ⟨z.val, hz, (huniq _ ⟨hκe, hκf⟩).trans (huniq _ ⟨he, hf⟩).symm⟩
    refine ⟨⟨hmaps, hinj, hsurj⟩, hκ e f hef, fun w hw => ?_⟩
    obtain ⟨z, hez, hfz, he, hf⟩ := global_contact_same_patch hI A e f hef hw.1 hw.2.1 hw.2.2
    exact (local_contact_global A z ⟨e, hez⟩ ⟨f, hfz⟩ (ne_of_apply_ne Subtype.val hef) he hf).2.2.2
  · obtain ⟨z, hez, hfz, hpe, hpf⟩ := global_contact_same_patch hI A e f hef he hf hvertex
    obtain ⟨q, heq, hgq, hqe, hqg⟩ := global_contact_same_patch hI A e g heg he hg hvertex
    obtain rfl : z = q := Subtype.ext <| Classical.byContradiction fun hne =>
      Set.disjoint_left.mp (A.balls_disjoint z.property q.property hne)
        (Metric.ball_subset_closedBall (A.patch_support z ⟨e, hez⟩ hpe))
        (Metric.ball_subset_closedBall (A.patch_support q ⟨e, heq⟩ hqe))
    exact A.patch_no_triple z ⟨e, hez⟩ ⟨f, hfz⟩ ⟨g, hgq⟩ (ne_of_apply_ne Subtype.val hef)
      (ne_of_apply_ne Subtype.val heg) (ne_of_apply_ne Subtype.val hfg) w hpe hpf hqg

end Cslib.Complexity.Graph.RotationRecognition
