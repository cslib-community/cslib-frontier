/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import Mathlib.Tactic.Linarith

/-!
# Interior parameters of polygonal routes

An interior parameter of any listed segment lies strictly between the two original
route ends. This separates actual segment interiors from permitted loop closure contacts.
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

/-- An open segment of a simple route contains neither outer endpoint of the route. -/
theorem IsSimple.eval_notMem_range_endpoint_of_mem_Ioo {p : Route} (hp : p.IsSimple)
    (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    p.eval i t ∉ Set.range p.endpoint := by
  rintro ⟨b, hb⟩
  have hend : p.eval (p.endSegment b) (endTime b 0) = p.endpoint b := by
    rw [p.eval_near_end, zero_smul, add_zero]
  rcases hp i (p.endSegment b) t (endTime b 0) ⟨ht.1.le, ht.2.le⟩
    (endTime_mem b ⟨le_rfl, zero_le_one⟩) (hb.symm.trans hend.symm) with h | ⟨h, _⟩ | ⟨h, _⟩
  · apply p.not_atEnd_of_mem_Ioo i ht b
    simpa only [AtEnd, position_near_end, sub_zero] using h
  · exact p.not_atEnd_of_mem_Ioo i ht false h
  · exact p.not_atEnd_of_mem_Ioo i ht true h

end Cslib.Polygonal.Route
