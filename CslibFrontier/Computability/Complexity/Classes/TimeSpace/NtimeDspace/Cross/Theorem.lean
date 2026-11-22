/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.GeneralFinal

/-!
# Theorem 1.1 at linear time, unconditionally

Theorem 1.1 at `t(n) = n` and Corollary 1.2 (i) at `t(n) = n`, as the specializations of the general
simulation (`Crossing.generalSimulation`, GeneralFinal.lean) by
`Cross.ntime_decidable_sqrtLog_linear`
and its siblings (Corollaries.lean): every language in `NTIME[n]` is decided in simultaneous
deterministic time `2^(C·SqrtLog n)` and space `C·SqrtLog n`, where `SqrtLog n = n / ⌊√⌊log₂ n⌋⌋ +
1`.

The statements below spell out `SqrtLog`, so that they use only Complexitylib's definitions; the
comparator challenge `NtimeChallengeCross` states them verbatim.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Crossing


/-- **Theorem 1.1 for `t(n) = n`.** Every language in `NTIME[n]` is decided in simultaneous
deterministic time `2^(C·(n/⌊√⌊log₂ n⌋⌋ + 1))` and space `C·(n/⌊√⌊log₂ n⌋⌋ + 1)`. -/
theorem ntime_decidable_sqrtLog {A : Set (List Bool)}
    (hA : A ∈ Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n)) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * (a.length / Nat.sqrt a.length.log2 + 1)))
      (fun a => C * (a.length / Nat.sqrt a.length.log2 + 1)) :=
  Cross.ntime_decidable_sqrtLog_linear generalSimulation hA

/-- **Theorem 1.1 for `t(n) = n`, as a class inclusion:** `NTIME[n] ⊆ DSPACE[n/√log n]`. -/
theorem ntime_subset_dspace_sqrtLog :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊆
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n / Nat.sqrt n.log2 + 1) :=
  Cross.ntime_subset_dspace_sqrtLog_linear generalSimulation

/-- **Corollary 1.2 (i) for `t(n) = n`:** `NTIME[n] ⊊ DSPACE[n]`, from the general simulation. -/
theorem ntime_ssubset_dspace :
    Cslib.Complexity.NTIME Turing.MultiTapeTM.encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE Turing.MultiTapeTM.encBits (fun n => n) :=
  Cross.ntime_ssubset_dspace_linear generalSimulation

end Cslib.Complexity.NtimeDspace.Crossing
