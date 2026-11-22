/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Corollaries
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeFinal
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.GeneralTheorem

/-!
# Theorem 1.1 and Corollary 1.2, unconditionally

Theorem 2.3 for the block networks (`cubeBlockBits`, CubeFinal.lean: bit `j` of every block network
by the explicit formula of §6), the column adder over schedules (`Exact.clockedBits_of_blockBits`,
ColumnAdder.lean), the count test (`Exact.clockedCounting_of_clockedBits`) and the transfer theorem
with doubling clocks (`generalSimulation_of_clocked`, GeneralTheorem.lean) give Theorem 1.1 for
every
`t(n) ≥ n` (`generalSimulation`); `t` need not be constructible. The corollaries follow
(Corollaries.lean).

The statements below spell out `SqrtLog m = m / ⌊√⌊log₂ m⌋⌋ + 1`, so that they use only
Complexitylib's definitions; the comparator challenge `NtimeChallengeGeneral` states them verbatim.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Crossing

open NtimeDspace.Cross

/-- Theorem 1.1 for every `t(n) ≥ n`, as `GeneralSimulation`. -/
theorem generalSimulation : GeneralSimulation :=
  generalSimulation_of_clocked
    (Exact.clockedCounting_of_clockedBits (Exact.clockedBits_of_blockBits cubeBlockBits))

/-- **Theorem 1.1.** For every `t(n) ≥ n` (not necessarily constructible), every language in
`NTIME[t]` is decided in simultaneous deterministic time `2^(C·(t/⌊√⌊log₂ t⌋⌋ + 1))` and space
`C·(t/⌊√⌊log₂ t⌋⌋ + 1)`. -/
theorem ntime_decidable_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) {A : Set (List Bool)}
    (hA : A ∈ Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * (t a.length / Nat.sqrt (t a.length).log2 + 1)))
      (fun a => C * (t a.length / Nat.sqrt (t a.length).log2 + 1)) :=
  generalSimulation t ht hA

/-- **Theorem 1.1, as a class inclusion:** `NTIME[t] ⊆ DSPACE[t/√log t]` for every `t(n) ≥ n`. -/
theorem ntime_subset_dspace_sqrtLog_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  ntime_subset_dspace_sqrtLog_of_general generalSimulation ht

/-- **Corollary 1.2 (i):** `NTIME[t] ⊊ DSPACE[t]` for every space-constructible `t(n) ≥ n`. -/
theorem ntime_ssubset_dspace_general (t : ℕ → ℕ) (hsc : Cslib.Complexity.SpaceConstructible t)
    (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits t :=
  ntime_ssubset_dspace_of_general generalSimulation hsc ht

/-- **Corollary 1.2 (i):** `NTIME[t] ⊊ NSPACE[t]`, so `NTIME[t] ≠ NSPACE[t]`, for every
space-constructible `t(n) ≥ n`. -/
theorem ntime_ssubset_nspace_general (t : ℕ → ℕ) (hsc : Cslib.Complexity.SpaceConstructible t)
    (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits t ⊂
      Cslib.Complexity.NSPACE Turing.MultiTapeTM.encBits t :=
  ntime_ssubset_nspace_of_general generalSimulation hsc ht

/-- **Corollary 1.2 (ii):** `NTIME[t·√log t] ⊆ DSPACE[t]` for every `t(n) ≥ n`. -/
theorem ntime_mul_sqrtLog_subset_dspace_general (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => t n * Nat.sqrt (Nat.log2 (t n))) ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits t :=
  ntime_mul_sqrtLog_subset_dspace generalSimulation ht

/-- **Corollary 1.2 (iii):** a language in `DSPACE[n]` such that every nondeterministic machine
deciding it or its complement takes at least `n·⌊√⌊log₂ n⌋⌋ / C` steps on some input of every
large length `n`, for some `C ≥ 1`. -/
theorem exists_dspace_linear_ntime_lower_bound_general :
    ∃ L : Set (List Bool), L ∈ Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) ∧
      ∀ (k : ℕ) (State : Type) [Finite State] (ntm : Turing.MultiTapeNTM k Bool State)
        (B : Set (List Bool)), (B = L ∨ B = Lᶜ) →
        (∀ x, (∃ t, ntm.RunsInTime x t) ∧ (x ∈ B ↔ ntm.Accepts x)) →
        ∃ C, 1 ≤ C ∧ ∀ᶠ n in Filter.atTop,
          ∃ x : List Bool, x.length = n ∧ ¬ ntm.RunsInTime x (n * Nat.sqrt n.log2 / C) :=
  exists_dspace_linear_ntime_lower_bound generalSimulation

end Cslib.Complexity.NtimeDspace.Crossing
