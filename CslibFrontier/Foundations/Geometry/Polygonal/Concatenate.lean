/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Concatenating polygonal routes

A concatenation keeps the first route and appends the nodes after the second route's
start. When the ends match, it preserves every actual segment and joins their supports.
Two simple open routes stay simple under the stated contact condition, which also allows
the two remaining ends to close the concatenation. This is original geometry.
-/

public section

namespace Cslib.Polygonal.Route

private abbrev followingNodes (q : Route) : List ℂ :=
  List.ofFn fun j : Fin q.segments => q.point j.succ

/-- Retain the first route, then append the second route's nodes after its start.
When the first finish equals the second start, the route contains exactly the two
original segment chains in traversal order. -/
def concat (p q : Route) : Route := (followingNodes q).foldl Route.append p

/-- Concatenation lists precisely the sum of the two original segment counts. -/
@[simp] theorem segments_concat (p q : Route) :
    (p.concat q).segments = p.segments + q.segments := by
  simp only [concat, segments_foldl_append, followingNodes, List.length_ofFn]

/-- Every joined segment has its original evaluation for all real times, with its original
index on the left and an index shifted by the first segment count on the right. -/
theorem concat_eval_cases (p q : Route) (h : p.finish = q.start)
    (i : Fin (p.concat q).segments) (t : ℝ) :
    (∃ j : Fin p.segments, i.val = j.val ∧ (p.concat q).eval i t = p.eval j t) ∨
      (∃ j : Fin q.segments, i.val = p.segments + j.val ∧ (p.concat q).eval i t = q.eval j t) := by
  rcases foldl_append_eval_cases p (followingNodes q) i t with ⟨j, hj, he, _⟩ | ⟨j, hj, he, _⟩
  · exact Or.inl ⟨j, hj, he⟩
  · let k : Fin q.segments := ⟨j.val, by
      simpa only [followingNodes, List.length_ofFn] using j.isLt⟩
    have hright : (followingNodes q)[j] = q.point k.succ := by
      change (followingNodes q)[j.val] = _
      dsimp only [followingNodes]
      rw [List.getElem_ofFn]
    have hnode (m : ℕ) (hm : m < q.segments) :
        (p.finish :: followingNodes q)[m]'(by
          simp only [List.length_cons, followingNodes, List.length_ofFn]
          omega) = q.point (⟨m, hm⟩ : Fin q.segments).castSucc := by
      cases m with
      | zero => exact h
      | succ n =>
        rw [List.getElem_cons_succ]
        dsimp only [followingNodes]
        rw [List.getElem_ofFn]
        exact congrArg q.point (Fin.ext rfl)
    have hleft : (p.finish :: followingNodes q)[j.castSucc] = q.point k.castSucc :=
      hnode j.val k.isLt
    refine Or.inr ⟨k, hj, ?_⟩
    change ((followingNodes q).foldl Route.append p).eval i t =
      AffineMap.lineMap (q.point k.castSucc) (q.point k.succ) t
    rw [he, hleft, hright]

private theorem eval_left (p q : Route) (h : p.finish = q.start)
    (i : Fin (p.concat q).segments) (j : Fin p.segments) (hij : i.val = j.val) (t : ℝ) :
    (p.concat q).eval i t = p.eval j t := by
  rcases concat_eval_cases p q h i t with ⟨k, hk, he⟩ | ⟨k, hk, _⟩
  · exact he.trans (congrArg (fun a => p.eval a t) (Fin.ext (hk.symm.trans hij)))
  · exact (by have := j.isLt; omega : False).elim

private theorem eval_right (p q : Route) (h : p.finish = q.start)
    (i : Fin (p.concat q).segments) (j : Fin q.segments)
    (hij : i.val = p.segments + j.val) (t : ℝ) : (p.concat q).eval i t = q.eval j t := by
  rcases concat_eval_cases p q h i t with ⟨k, hk, _⟩ | ⟨k, hk, he⟩
  · exact (by have := k.isLt; omega : False).elim
  · exact he.trans (congrArg (fun a => q.eval a t) (Fin.ext (by omega)))

private theorem eval_end_concat (p q : Route) (h : p.finish = q.start) (b : Bool) (t : ℝ) :
    (p.concat q).eval ((p.concat q).endSegment b) t =
      if b then q.eval (q.endSegment b) t else p.eval (p.endSegment b) t := by
  cases b
  · exact eval_left p q h _ _ rfl t
  · apply eval_right p q h
    have hn := segments_concat p q
    simp only [endSegment, ↓reduceIte, Fin.val_last, segments] at hn ⊢
    omega

/-- With matching ends, the concatenation keeps the two outer endpoints. -/
theorem endpoint_concat (p q : Route) (h : p.finish = q.start) (b : Bool) :
    (p.concat q).endpoint b = if b then q.endpoint b else p.endpoint b := by
  have he := eval_end_concat p q h b (endTime b 0)
  cases b <;> simpa only [↓reduceIte, eval_near_end, zero_smul, add_zero] using he

/-- With matching ends, the concatenation keeps the two outer outgoing germs. -/
theorem germ_concat (p q : Route) (h : p.finish = q.start) (b : Bool) :
    (p.concat q).germ b = if b then q.germ b else p.germ b := by
  have he := eval_end_concat p q h b (endTime b 1)
  simp only [eval_near_end, one_smul, endpoint_concat p q h] at he
  cases b <;> exact add_left_cancel he

/-- With matching ends, the support is exactly the union of the two old supports. -/
theorem support_concat (p q : Route) (h : p.finish = q.start) :
    (p.concat q).support = p.support ∪ q.support := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, t, ht, he⟩ := ((p.concat q).mem_support_iff x).mp hx
    rcases concat_eval_cases p q h i t with ⟨j, _, hj⟩ | ⟨j, _, hj⟩
    · exact Or.inl ((p.mem_support_iff x).mpr ⟨j, t, ht, hj.symm.trans he⟩)
    · exact Or.inr ((q.mem_support_iff x).mpr ⟨j, t, ht, hj.symm.trans he⟩)
  · rintro (hp | hq)
    · obtain ⟨j, t, ht, hj⟩ := (p.mem_support_iff x).mp hp
      let i : Fin (p.concat q).segments := ⟨j.val, by
        rw [segments_concat]
        exact j.isLt.trans_le (Nat.le_add_right _ _)⟩
      exact ((p.concat q).mem_support_iff x).mpr
        ⟨i, t, ht, (eval_left p q h i j rfl t).trans hj⟩
    · obtain ⟨j, t, ht, hj⟩ := (q.mem_support_iff x).mp hq
      let i : Fin (p.concat q).segments := ⟨p.segments + j.val, by
        rw [segments_concat]
        exact Nat.add_lt_add_left j.isLt _⟩
      exact ((p.concat q).mem_support_iff x).mpr
        ⟨i, t, ht, (eval_right p q h i j rfl t).trans hj⟩

private theorem position_left (p q : Route) (i : Fin (p.concat q).segments)
    (j : Fin p.segments) (hij : i.val = j.val) (t : ℝ) :
    (p.concat q).position i t = p.position j t := by simp only [position, hij]

private theorem position_right (p q : Route) (i : Fin (p.concat q).segments)
    (j : Fin q.segments) (hij : i.val = p.segments + j.val) (t : ℝ) :
    (p.concat q).position i t = (p.segments : ℝ) + q.position j t := by
  simp only [position, hij, Nat.cast_add]
  ring

/-- Simple open routes concatenate to a simple route when cross contacts are the shared
join or the two remaining ends of a closed concatenation. The contact condition is on
actual closed segment parameters and allows the outer ends to coincide only geometrically. -/
theorem IsSimple.concat {p q : Route} (hp : p.IsSimple) (hq : q.IsSimple)
    (hpopen : p.start ≠ p.finish) (hqopen : q.start ≠ q.finish) (h : p.finish = q.start)
    (hcontact : ∀ (i : Fin p.segments) (j : Fin q.segments) (s t : ℝ),
      s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 → p.eval i s = q.eval j t →
      (p.AtEnd i s true ∧ q.AtEnd j t false) ∨ (p.AtEnd i s false ∧ q.AtEnd j t true)) :
    (p.concat q).IsSimple := by
  have cross (i j : Fin (p.concat q).segments) (k : Fin p.segments) (l : Fin q.segments)
      {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
      (hi : i.val = k.val) (hj : j.val = p.segments + l.val)
      (he : p.eval k s = q.eval l t) :
      (p.concat q).position i s = (p.concat q).position j t ∨
        ((p.concat q).AtEnd i s false ∧ (p.concat q).AtEnd j t true) := by
    have hleft := position_left p q i k hi s
    have hright := position_right p q j l hj t
    rcases hcontact k l s t hs ht he with ⟨hps, hqt⟩ | ⟨hps, hqt⟩
    · left
      rw [hleft, hright, show p.position k s = p.segments from hps,
        show q.position l t = 0 from hqt, add_zero]
    · right
      refine ⟨hleft.trans hps, ?_⟩
      change (p.concat q).position j t = ((p.concat q).segments : ℝ)
      have hpos : (p.concat q).position j t = (p.segments : ℝ) + q.segments := by
        rw [hright, show q.position l t = q.segments from hqt]
      simpa only [segments_concat, Nat.cast_add] using hpos
  intro i j s t hs ht he
  rcases concat_eval_cases p q h i s with ⟨a, ha, hea⟩ | ⟨a, ha, hea⟩ <;>
    rcases concat_eval_cases p q h j t with ⟨b, hb, heb⟩ | ⟨b, hb, heb⟩
  · left
    rw [position_left p q i a ha, position_left p q j b hb]
    exact hp.position_eq_of_eval_eq hpopen a b hs ht (hea.symm.trans (he.trans heb))
  · rcases cross i j a b hs ht ha hb (hea.symm.trans (he.trans heb)) with heq | hends
    · exact Or.inl heq
    · exact Or.inr (Or.inl hends)
  · rcases cross j i b a ht hs hb ha (heb.symm.trans (he.symm.trans hea)) with heq | hends
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inr ⟨hends.2, hends.1⟩)
  · left
    rw [position_right p q i a ha, position_right p q j b hb,
      hq.position_eq_of_eval_eq hqopen a b hs ht (hea.symm.trans (he.trans heb))]

end Cslib.Polygonal.Route
