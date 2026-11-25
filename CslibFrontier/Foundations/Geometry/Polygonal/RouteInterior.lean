/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Tactic.Linarith

/-!
# Interior parameters of polygonal routes

An interior parameter of any listed segment lies strictly between the two original
route ends. This separates actual segment interiors from permitted loop closure contacts.
`IsSimple.index_time_eq_of_eval_eq_of_mem_Ioo` identifies the piece and parameter
at a contact in a simple route.
-/

public section

namespace Cslib.Polygonal.Route

/-- An interior segment parameter is never either original route end. -/
theorem not_atEnd_of_mem_Ioo (p : Route) (i : Fin p.segments)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) (tag : Bool) : ¬p.AtEnd i t tag := by
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast i.isLt
  cases tag <;> simp only [AtEnd, position, Bool.false_eq_true, ↓reduceIte]
  · linarith [ht.1]
  · linarith [ht.2]

/-- A segment endpoint parameter evaluates to its listed point, with global position
equal to that point's list index. -/
theorem exists_point_at_end_parameter {p : Route} (k : Fin p.segments) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hopen : u ∉ Set.Ioo 0 1) :
    ∃ a : Fin (p.segments + 1), p.eval k u = p.point a ∧ p.position k u = (a.val : ℝ) := by
  have he : u ∈ ({0, 1} : Set ℝ) :=
    Set.Icc_sdiff_Ioo_same (show (0 : ℝ) ≤ 1 from zero_le_one) ▸ ⟨hu, hopen⟩
  rcases Set.mem_insert_iff.mp he with rfl | he
  · exact ⟨k.castSucc, AffineMap.lineMap_apply_zero _ _, add_zero _⟩
  · rw [Set.mem_singleton_iff] at he
    subst u
    exact ⟨k.succ, AffineMap.lineMap_apply_one _ _, by simp only [position, Fin.val_succ,
      Nat.cast_add, Nat.cast_one]⟩

/-- A route is simple if its listed points are distinct, miss all open segments,
and the open segments are pairwise disjoint. -/
theorem isSimple_of_disjoint_openSegments {p : Route} (hnodes : Function.Injective p.point)
    (hends : ∀ (n : Fin (p.segments + 1)) (i : Fin p.segments),
      p.point n ∉ openSegment ℝ (p.point i.castSucc) (p.point i.succ))
    (hdisj : Pairwise fun (i j : Fin p.segments) =>
      Disjoint (openSegment ℝ (p.point i.castSucc) (p.point i.succ))
        (openSegment ℝ (p.point j.castSucc) (p.point j.succ))) : p.IsSimple := by
  have hnode (n : Fin (p.segments + 1)) (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
      p.point n ≠ p.eval i t :=
    fun h => hends n i (h.symm ▸ lineMap_mem_openSegment ℝ _ _ ht)
  intro i j s t hs ht he
  left
  by_cases hso : s ∈ Set.Ioo 0 1
  · by_cases hto : t ∈ Set.Ioo 0 1
    · have hij : i = j := by
        by_contra h
        have hsi : p.eval i s ∈ openSegment ℝ (p.point i.castSucc) (p.point i.succ) :=
          lineMap_mem_openSegment ℝ _ _ hso
        have htj : p.eval j t ∈ openSegment ℝ (p.point j.castSucc) (p.point j.succ) :=
          lineMap_mem_openSegment ℝ _ _ hto
        exact Set.disjoint_left.mp (hdisj h) hsi (he.symm ▸ htj)
      subst j
      have hne : i.castSucc ≠ i.succ := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hval
        omega
      rw [AffineMap.lineMap_injective ℝ (hnodes.ne hne) he]
    · obtain ⟨n, hn, _⟩ := exists_point_at_end_parameter j ht hto
      exact (hnode n i hso ((he.trans hn).symm)).elim
  · obtain ⟨n, hn, hposn⟩ := exists_point_at_end_parameter i hs hso
    by_cases hto : t ∈ Set.Ioo 0 1
    · exact (hnode n j hto (hn.symm.trans he)).elim
    · obtain ⟨m, hm, hposm⟩ := exists_point_at_end_parameter j ht hto
      rw [hposn, hposm, hnodes (hn.symm.trans (he.trans hm))]

/-- A contact in an open segment of a simple route identifies its index and parameter,
even when the other parameter is initially only known to be in the closed unit interval. -/
theorem IsSimple.index_time_eq_of_eval_eq_of_mem_Ioo {p : Route} (hp : p.IsSimple)
    (i j : Fin p.segments) {s t : ℝ} (hs : s ∈ Set.Ioo 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : p.eval i s = p.eval j t) : i = j ∧ s = t := by
  have hpos : p.position i s = p.position j t := by
    rcases hp i j s t ⟨hs.1.le, hs.2.le⟩ ht heq with h | ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact (p.not_atEnd_of_mem_Ioo i hs false h).elim
    · exact (p.not_atEnd_of_mem_Ioo i hs true h).elim
  dsimp only [position] at hpos
  have hij : i.val < j.val + 1 := by
    exact_mod_cast (show (i.val : ℝ) < (j.val : ℝ) + 1 by linarith [hs.1, ht.2])
  have hji : j.val < i.val + 1 := by
    exact_mod_cast (show (j.val : ℝ) < (i.val : ℝ) + 1 by linarith [hs.2, ht.1])
  have hi : i = j := Fin.ext (by omega)
  subst j
  exact ⟨rfl, add_left_cancel hpos⟩

end Cslib.Polygonal.Route
