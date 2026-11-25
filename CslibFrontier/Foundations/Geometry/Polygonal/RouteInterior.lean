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
