/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.QBF

/-!
# Word assignments to Boolean-formula variables

`QBF.updates` assigns a word of truth values along a list of variables, in order.
Later occurrences override earlier occurrences. Distinct variables read back the assigned word.
-/

public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*} [DecidableEq V]

/-- An assignment updated at a list of variables, in order, by a list of values. -/
@[expose] def updates (σ : V → Bool) : List V → List Bool → V → Bool
  | v :: vs, b :: bs => updates (Function.update σ v b) vs bs
  | _, _ => σ

/-- Updating other variables does not change the value of a variable. -/
theorem updates_of_notMem {σ : V → Bool} {vs : List V} {x : V} (hx : x ∉ vs) (bs : List Bool) :
    updates σ vs bs x = σ x := by
  induction vs generalizing σ bs with
  | nil => cases bs <;> rfl
  | cons v vs ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [List.mem_cons, not_or] at hx
      rw [updates, ih hx.2, Function.update_of_ne hx.1]

/-- Updating distinct variables by as many values sets them to these values. -/
theorem map_updates {σ : V → Bool} {vs : List V} (hvs : vs.Nodup) {bs : List Bool}
    (hlen : bs.length = vs.length) : vs.map (updates σ vs bs) = bs := by
  induction vs generalizing σ bs with
  | nil => exact (List.length_eq_zero_iff.mp hlen).symm
  | cons v vs ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      rw [List.nodup_cons] at hvs
      rw [List.map_cons, updates, updates_of_notMem hvs.1, Function.update_self,
        ih hvs.2 (by simpa using hlen)]

end Cslib.Logic.PL.QBF
