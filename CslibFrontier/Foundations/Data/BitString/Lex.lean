/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn

/-!
# Lexicographic order on fixed-width bit strings

`Cslib.BitString.lexSwap` tells a caller whether to swap two strings to put them in
lexicographic order. It can also be used to permute data associated with the coordinates.
-/

public section

namespace Cslib.BitString

/-- Whether lexicographic sorting interchanges `a` and `b`. Ties preserve input order. -/
@[expose] def lexSwap {n : ℕ} (a b : Fin n → Bool) : Bool :=
  decide (List.ofFn b < List.ofFn a)

/-- The all-false string comes first in lexicographic order, including at a tie. -/
@[simp] theorem lexSwap_zero_left {n : ℕ} (b : Fin n → Bool) :
    lexSwap 0 b = false := by
  change lexSwap (fun _ => false) b = false
  rw [lexSwap, decide_eq_false_iff_not]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    intro h
    by_cases hb : b 0 = false
    · rw [hb] at h
      change List.Lex (· < ·) (false :: _) (false :: _) at h
      exact ih (fun i => b i.succ) (List.lex_cons_iff.mp h)
    · have hle : b 0 ≤ false := List.head_le_of_lt h
      cases hbit : b 0
      · exact hb hbit
      · rw [hbit] at hle
        exact (by decide : ¬ true ≤ false) hle

/-- Reversing distinct inputs reverses the sorting decision. -/
theorem lexSwap_reverse {n : ℕ} {a b : Fin n → Bool} (h : a ≠ b) :
    lexSwap b a = !(lexSwap a b) := by
  have hn : List.ofFn a ≠ List.ofFn b := fun he => h (List.ofFn_injective he)
  rcases lt_or_gt_of_ne hn with hab | hba
  · simp [lexSwap, hab, not_lt_of_ge hab.le]
  · simp [lexSwap, hba, not_lt_of_ge hba.le]

end Cslib.BitString
