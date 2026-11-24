/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module

import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingAtFinal

/-! Clients of the `NTIME[t] ⊆ DSPACE[t / √log t]` endpoints under module encapsulation. -/

open Cslib.Complexity Turing.MultiTapeTM

-- Theorem 1.1 at a time bound that is not linear.
example : NTIME encBits (fun n => n ^ 2) ⊆
    DSPACE encBits (fun n => n ^ 2 / Nat.sqrt (n ^ 2).log2 + 1) :=
  NTIME_subset_DSPACE_div_sqrt_log fun n => Nat.le_self_pow two_ne_zero n

-- The simulating machine of Theorem 1.1, applied to a given language.
example {A : Set (List Bool)} (hA : A ∈ NTIME encBits (fun n => n)) :
    ∃ C, DecidableInTimeAndSpace A encBits
      (fun a => 2 ^ (C * (a.length / Nat.sqrt a.length.log2 + 1)))
      (fun a => C * (a.length / Nat.sqrt a.length.log2 + 1)) :=
  exists_decidableInTimeAndSpace_of_mem_NTIME_div_sqrt_log _ (fun _ => le_rfl) hA

-- Corollary 1.2: the linear-time separations.
example : NTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) := NTIME_id_ssubset_DSPACE_id
example : PPTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) := PPTIME_id_ssubset_DSPACE_id

-- The general-scale route of §8 has satisfiable hypotheses: at `D = SqrtLog` it gives back
-- Theorem 1.1 and Theorem 7.1 for `PPTIME` and `BPTIME`.
section
open Cslib.Complexity.NtimeDspace.Cross

example (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊆ DSPACE encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  ntime_subset_dspace_of_blockBitsAt scale_sqrtLog Exact.carryFits_sqrtLog cubeBlockBits t ht

example (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    PPTIME encBits t ⊆ DSPACE encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  pptime_subset_dspace_of_blockBitsAt scale_sqrtLog Exact.carryFits_sqrtLog cubeBlockBits t ht

example (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    BPTIME encBits t ⊆ DSPACE encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  bptime_subset_dspace_of_blockBitsAt scale_sqrtLog Exact.carryFits_sqrtLog cubeBlockBits t ht

-- At `D = SqrtLog` the general column adder and count test give back the fixed-scale ones.
example (h : Exact.BlockBits) : Exact.ClockedBits :=
  Exact.clockedBitsAt_of_blockBitsAt log2_add_one_le_sqrtLog Exact.carryFits_sqrtLog h

example (h : Exact.ClockedBits) : ClockedCounting :=
  Exact.clockedCountingAt_of_clockedBitsAt log2_add_one_le_sqrtLog h

end
