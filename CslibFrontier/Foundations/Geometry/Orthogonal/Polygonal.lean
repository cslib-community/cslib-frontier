/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Orthogonal.Simple
public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import Mathlib.Analysis.Complex.Basic

/-!
# Integer routes as polygonal routes

An integer route with at least two listed points gives a polygonal route with exactly the
same segments, in the same order. The coordinate identification sends `(x,y)` to `x + yi`.
Continuous endpoint-contact simplicity implies injectivity of the complete chain parameter;
the proof does not sample lattice points or replace full segments by discrete traces.

This is original representation transport. The consumer is the conversion of supplied
orthogonal incidence drawings to the existing polygonal embedding model.
-/

public section

namespace Cslib.Orthogonal

/-- Include an integer planar point in the complex plane, preserving the orientation. -/
@[expose] noncomputable def complexPoint (p : Point) : ℂ :=
  Complex.equivRealProdCLM.symm (realPoint p)

/-- The complex coordinate identification retains both real coordinates. -/
theorem equivRealProd_complexPoint (p : Point) :
    Complex.equivRealProdCLM (complexPoint p) = realPoint p :=
  Complex.equivRealProdCLM.apply_symm_apply _

/-- Different integer points stay different in the complex plane. -/
theorem complexPoint_injective : Function.Injective complexPoint :=
  Complex.equivRealProdCLM.symm.injective.comp realPoint_injective

/-- Retain every listed point and every consecutive segment of an integer route. -/
@[expose] noncomputable def toPolygonalRoute (r : Route) (h : 2 ≤ r.length) :
    Polygonal.Route where
  bends := r.length - 2
  point i := complexPoint (r[i.val]'(by have := i.isLt; omega))

private theorem segment_succ_lt (r : Route) (h : 2 ≤ r.length)
    (i : Fin (toPolygonalRoute r h).segments) : i.val + 1 < r.length := by
  have hi := i.isLt
  change i.val < r.length - 2 + 1 at hi
  omega

/-- The first polygonal point is the original first listed point. -/
@[simp] theorem start_toPolygonalRoute (r : Route) (h : 2 ≤ r.length) :
    (toPolygonalRoute r h).start = complexPoint r[0] := rfl

/-- The last polygonal point is the original last listed point. -/
theorem finish_toPolygonalRoute (r : Route) (h : 2 ≤ r.length) :
    (toPolygonalRoute r h).finish = complexPoint r[r.length - 1] := by
  change complexPoint r[r.length - 2 + 1] = _
  congr 2; omega

private theorem segment_mem_toPolygonalRoute (r : Route) (h : 2 ≤ r.length)
    (i : Fin (toPolygonalRoute r h).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProdCLM ((toPolygonalRoute r h).eval i t) ∈
      segment (r[i.val]'((Nat.lt_succ_self _).trans (segment_succ_lt r h i)))
        (r[i.val + 1]'(segment_succ_lt r h i)) := by
  have hic := segment_succ_lt r h i
  have hi : i.val < r.length := by omega
  have he := AffineMap.apply_lineMap Complex.equivRealProdCLM.toLinearMap.toAffineMap
    (complexPoint r[i.val]) (complexPoint r[i.val + 1]) t
  change Complex.equivRealProdCLM ((toPolygonalRoute r h).eval i t) =
    AffineMap.lineMap (Complex.equivRealProdCLM (complexPoint r[i.val]))
      (Complex.equivRealProdCLM (complexPoint r[i.val + 1])) t at he
  rw [equivRealProd_complexPoint, equivRealProd_complexPoint] at he
  rw [he]
  exact lineMap_mem_segment ℝ _ _ ht

/-- Every real point on a converted segment belongs to the original continuous support. -/
theorem eval_toPolygonalRoute_mem_support (r : Route) (h : 2 ≤ r.length)
    (i : Fin (toPolygonalRoute r h).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProdCLM ((toPolygonalRoute r h).eval i t) ∈ support r := by
  have hic := segment_succ_lt r h i
  have hi : i.val < r.length := by omega
  exact Or.inr ⟨(r[i.val], r[i.val + 1]), List.getElem_mem_consecutivePairs r i.val hic,
    segment_mem_toPolygonalRoute r h i ht⟩

private theorem point_injective_toPolygonalRoute {r : Route} (hr : r.Nodup)
    (h : 2 ≤ r.length) : Function.Injective (toPolygonalRoute r h).point := by
  intro i j hij
  apply Fin.ext
  exact hr.getElem_inj_iff.mp (complexPoint_injective hij)

private theorem parameter_eq_of_eval_eq_point {r : Route} (hr : r.Nodup)
    (h : 2 ≤ r.length) (i : Fin (toPolygonalRoute r h).segments)
    (j : Fin ((toPolygonalRoute r h).bends + 2)) (t : ℝ)
    (he : (toPolygonalRoute r h).eval i t = (toPolygonalRoute r h).point j)
    (hj : j = i.castSucc ∨ j = i.succ) :
    (toPolygonalRoute r h).position i t = j.val := by
  have hinj := point_injective_toPolygonalRoute hr h
  have hne : (toPolygonalRoute r h).point i.castSucc ≠
      (toPolygonalRoute r h).point i.succ := fun he => by
    have := congrArg Fin.val (hinj he)
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  rcases hj with rfl | rfl
  · have ht : t = 0 := (AffineMap.lineMap_eq_left_iff.mp he).resolve_left hne
    simp [Polygonal.Route.position, ht]
  · have ht : t = 1 := (AffineMap.lineMap_eq_right_iff.mp he).resolve_left hne
    simp [Polygonal.Route.position, ht, Nat.cast_add, Nat.cast_one]

/-- Continuous simplicity of the integer route implies injectivity of the converted
route's complete real chain parameter, including all intermediate segment endpoints. -/
theorem position_eq_of_eval_toPolygonalRoute_eq {r : Route} (hr : IsSimple r)
    (h : 2 ≤ r.length) (i j : Fin (toPolygonalRoute r h).segments) (s t : ℝ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (toPolygonalRoute r h).eval i s = (toPolygonalRoute r h).eval j t) :
    (toPolygonalRoute r h).position i s = (toPolygonalRoute r h).position j t := by
  have hinj := point_injective_toPolygonalRoute hr.1 h
  by_cases hij : i = j
  · subst j
    have hne : (toPolygonalRoute r h).point i.castSucc ≠
        (toPolygonalRoute r h).point i.succ := fun hq => by
      have := congrArg Fin.val (hinj hq)
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    exact congrArg ((toPolygonalRoute r h).position i)
      (AffineMap.lineMap_injective ℝ hne he)
  · have hic := segment_succ_lt r h i
    have hjc := segment_succ_lt r h j
    have hpair : (r[i.val], r[i.val + 1]) ≠ (r[j.val], r[j.val + 1]) := by
      intro hp
      apply hij
      exact Fin.ext (hr.1.getElem_inj_iff.mp (congrArg Prod.fst hp))
    obtain ⟨hi, hj⟩ := hr.2 _ (List.getElem_mem_consecutivePairs r _ hic)
      _ (List.getElem_mem_consecutivePairs r _ hjc) hpair
      _ (segment_mem_toPolygonalRoute r h i hs)
      (he.symm ▸ segment_mem_toPolygonalRoute r h j ht)
    have hpoint (k : Fin (toPolygonalRoute r h).segments) (u : ℝ)
        (hk : Complex.equivRealProdCLM ((toPolygonalRoute r h).eval k u) =
          realPoint (r[k.val]'((Nat.lt_succ_self _).trans (segment_succ_lt r h k))) ∨
          Complex.equivRealProdCLM ((toPolygonalRoute r h).eval k u) =
            realPoint (r[k.val + 1]'(segment_succ_lt r h k))) :
        ∃ a : Fin ((toPolygonalRoute r h).bends + 2),
          (toPolygonalRoute r h).eval k u = (toPolygonalRoute r h).point a ∧
          (toPolygonalRoute r h).position k u = a.val := by
      rcases hk with hk | hk
      · have hq : (toPolygonalRoute r h).eval k u =
            (toPolygonalRoute r h).point k.castSucc :=
          Complex.equivRealProdCLM.injective (hk.trans (equivRealProd_complexPoint _).symm)
        exact ⟨k.castSucc, hq, parameter_eq_of_eval_eq_point hr.1 h k _ u hq (.inl rfl)⟩
      · have hq : (toPolygonalRoute r h).eval k u =
            (toPolygonalRoute r h).point k.succ :=
          Complex.equivRealProdCLM.injective (hk.trans (equivRealProd_complexPoint _).symm)
        exact ⟨k.succ, hq, parameter_eq_of_eval_eq_point hr.1 h k _ u hq (.inr rfl)⟩
    obtain ⟨a, ha, hpa⟩ := hpoint i s hi
    obtain ⟨b, hb, hpb⟩ := hpoint j t (by simpa only [he] using hj)
    rw [hpa, hpb, hinj (ha.symm.trans (he.trans hb))]

/-- The conversion meets the existing polygonal simplicity contract, with no extra
identifications of endpoints. -/
theorem isSimple_toPolygonalRoute {r : Route} (hr : IsSimple r) (h : 2 ≤ r.length) :
    (toPolygonalRoute r h).IsSimple :=
  fun i j s t hs ht he => .inl (position_eq_of_eval_toPolygonalRoute_eq hr h i j s t hs ht he)

/-- An endpoint of a converted simple route is visited only at its actual global endpoint
parameter. This supplies the vertex-contact obligation of a polygonal embedding. -/
theorem eval_toPolygonalRoute_eq_endpoint_iff {r : Route} (hr : IsSimple r)
    (h : 2 ≤ r.length) (i : Fin (toPolygonalRoute r h).segments) (t : ℝ)
    (ht : t ∈ Set.Icc 0 1) (side : Bool) :
    (toPolygonalRoute r h).eval i t = (toPolygonalRoute r h).endpoint side ↔
      (toPolygonalRoute r h).AtEnd i t side := by
  refine ⟨fun he => ?_, (toPolygonalRoute r h).at_eq_endpoint i ht side⟩
  cases side
  · have hz : (toPolygonalRoute r h).eval i t = (toPolygonalRoute r h).eval 0 0 := by
      simpa only [Polygonal.Route.endpoint, Bool.false_eq_true, ↓reduceIte,
        Polygonal.Route.eval, AffineMap.lineMap_apply_zero, Polygonal.Route.start,
        Fin.castSucc_zero] using he
    have hp := position_eq_of_eval_toPolygonalRoute_eq hr h i 0 t 0 ht (by simp) hz
    simpa only [Polygonal.Route.AtEnd, Bool.false_eq_true, ↓reduceIte,
      Polygonal.Route.position, Fin.val_zero, Nat.cast_zero, zero_add] using hp
  · let last : Fin (toPolygonalRoute r h).segments := Fin.last (toPolygonalRoute r h).bends
    have hz : (toPolygonalRoute r h).eval i t = (toPolygonalRoute r h).eval last 1 := by
      simpa only [Polygonal.Route.endpoint, ↓reduceIte, Polygonal.Route.eval,
        AffineMap.lineMap_apply_one, last, Fin.succ_last, Polygonal.Route.finish,
        Polygonal.Route.segments] using he
    have hp := position_eq_of_eval_toPolygonalRoute_eq hr h i last t 1 ht (by simp) hz
    simpa only [Polygonal.Route.AtEnd, ↓reduceIte, Polygonal.Route.position, last,
      Fin.val_last, Polygonal.Route.segments, Nat.cast_add, Nat.cast_one] using hp

end Cslib.Orthogonal
