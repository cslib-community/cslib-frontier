/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.AcceptCount.Majority

/-! Exercise the majority error bound with empty seed blocks and a varying repetition count. -/

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
