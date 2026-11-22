/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Corollaries
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingFinal

/-!
# Corollary 1.2 (iv): unbounded-error probabilistic time is strictly inside linear space

Theorem 7.1 for `PPTIME` (`Crossing.pptime_subset_dspace_sqrtLog_general`) and the space hierarchy
theorem give `PPTIME[t] ⊊ DSPACE[t]` for every space-constructible `t(n) ≥ n`, and hence
`PPTIME[n] ⊊ DSPACE[n]` and `BPTIME[n] ⊊ DSPACE[n]`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Crossing

open NtimeDspace.Cross

/-- **Corollary 1.2 (iv):** `PPTIME[t] ⊊ DSPACE[t]` for every space-constructible `t(n) ≥ n`. -/
theorem pptime_ssubset_dspace_general (t : ℕ → ℕ) (hsc : Cslib.Complexity.SpaceConstructible t)
    (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.PPTIME Turing.MultiTapeTM.encBits t ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits t :=
  lt_of_le_of_lt (pptime_subset_dspace_sqrtLog_general t ht)
    (Cslib.Complexity.DSPACE_ssubset_DSPACE hsc (fun n => (Nat.log2_le_self n).trans (ht n))
      (eventually_sqrtLog_comp_gap ht))

/-- **Corollary 1.2 (iv), linear time:** `PPTIME[n] ⊊ DSPACE[n]`. -/
theorem pptime_ssubset_dspace :
    Cslib.Complexity.PPTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) :=
  pptime_ssubset_dspace_general _ Cslib.Complexity.spaceConstructible_id (fun _ => le_rfl)

/-- **Corollary 1.2 (iv), bounded error:** `BPTIME[n] ⊊ DSPACE[n]`. -/
theorem bptime_ssubset_dspace :
    Cslib.Complexity.BPTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) :=
  lt_of_le_of_lt (bptime_subset_dspace_sqrtLog_general _ (fun _ => le_rfl))
    (Cslib.Complexity.DSPACE_ssubset_DSPACE Cslib.Complexity.spaceConstructible_id
      (fun n => Nat.log2_le_self n)
      (eventually_sqrtLog_comp_gap (fun _ => le_rfl)))

end Cslib.Complexity.NtimeDspace.Crossing
