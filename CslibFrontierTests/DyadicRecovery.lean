/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Algorithms.Lean.DyadicRecovery
meta import CslibFrontier.Algorithms.Lean.DyadicRecovery
import Mathlib.Tactic.NormNum

/-! Checked clients for exact-precision rational recovery. -/

open Turing.MultiTapeTM

-- The prefix 101101 at bound 7 has scale 64. The left endpoint alone misses Legendre's bound.
example : (5 : ℚ) / 7 - 45 / 64 > 1 / (2 * (7 : ℚ) ^ 2) := by norm_num

example : ComputableInPolyTime (fun p : ℕ × ℕ => Rat.recoverDyadic p.1 p.2)
      (encPair encNat encNat) (encOption encRat) ∧
    (Rat.recoverDyadic 7 45).map (fun q => (q.num, q.den)) = some (5, 7) := by
  refine ⟨Rat.recoverDyadic_polyTime, ?_⟩
  let q : ℚ := ⟨5, 7, by decide, by decide⟩
  have hq : (5 : ℚ) / 7 = q := q.num_div_den
  have h : Rat.recoverDyadic 7 45 = some q := by
    apply Rat.recoverDyadic_eq_some
    · decide
    · rw [← hq, show Nat.clog 2 7 = 3 by decide]
      norm_num
    · rw [← hq, show Nat.clog 2 7 = 3 by decide]
      norm_num
  rw [h]
  rfl

-- A terminating binary expansion uses its left endpoint. The preceding cell excludes it.
/-- info: true -/
#guard_msgs in
#eval Rat.recoverDyadic 2 2 == some (1 / 2) && Rat.recoverDyadic 2 1 == none

-- The certificate is total, including a zero denominator bound.
/-- info: true -/
#guard_msgs in
#eval Rat.recoverDyadic 0 45 == none

-- Zero fractional bits at bound one, and a prefix supplied together with its integer part.
/-- info: true -/
#guard_msgs in
#eval Rat.recoverDyadic 1 0 == some 0 && Rat.recoverDyadic 7 (64 + 45) == some (12 / 7)
