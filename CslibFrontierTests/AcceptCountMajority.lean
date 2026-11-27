/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.AcceptCount.Majority

/-! Exercise error bounds with zero-width trials and with prefixes of different widths. -/

set_option linter.privateModule false

open Cslib.BitString Cslib.Complexity

example (r : ℕ) (hr : 0 < r) :
    acceptCount (fun p =>
      listStrictMajority ((listRows (2 * r) 0 p.2).map (fun _ => true)) != true)
      () ((2 * r) * 0) = 0 := by
  have h := acceptCount_listStrictMajority_ne_le (fun _ => true) () 0 r true (ε := 0)
    le_rfl (by norm_num) (by simp)
  have hzero : (4 * (0 : ℝ) * (1 - 0)) ^ r = 0 := by
    simp [zero_pow hr.ne']
  rw [hzero, zero_mul] at h
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast h)

/-- Two overlapping error events read one and three bits of the same seed. -/
example :
    acceptCount (fun p : Unit × List Bool =>
      (p.2.take 1).headD false || ((p.2.take 3).getD 1 false && (p.2.take 3).getD 2 false))
      () 3 ≤ 6 := by
  let V (i : Bool) (p : Unit × List Bool) :=
    if i then p.2.headD false else p.2.getD 1 false && p.2.getD 2 false
  let width (i : Bool) := if i then 1 else 3
  let W (p : Unit × List Bool) :=
    V true (p.1, p.2.take (width true)) || V false (p.1, p.2.take (width false))
  change acceptCount W () 3 ≤ 6
  have h := acceptCount_le_sum_of_take_cover Finset.univ V width W () 3
    (fun i _ => by cases i <;> decide)
    (fun w _ hw => by
      rcases Bool.or_eq_true_iff.mp hw with hfirst | hlast
      · exact ⟨true, Finset.mem_univ _, hfirst⟩
      · exact ⟨false, Finset.mem_univ _, hlast⟩)
  exact h.trans_eq (by decide)
