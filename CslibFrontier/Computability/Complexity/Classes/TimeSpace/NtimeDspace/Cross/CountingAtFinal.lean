/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingAt
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeFinal
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.DivLogScale

/-!
# The remark of §8 at `D = SqrtLog` and at `D = n / log n`

§8 of the paper: "Our method also cannot tell nondeterminism from counting: it puts `PPTIME[t]`
in the same space as `NTIME[t]` (Theorem 7.1), so improving Theorem 1.1 this way would improve the
simulation of `PPTIME[t]` as well", where "this way" is computing the counts of the block networks
(Theorem 2.3) in a smaller space. `CountingAt.lean` proves this for every scale `D` with `Scale D`
and `CarryFits D`. Here the hypotheses are checked at the two scales that matter.

* `D = SqrtLog`. Both hypotheses hold (`scale_sqrtLog`, `Exact.carryFits_sqrtLog`) and so does
  Theorem 2.3 at this scale (`cubeBlockBits`), so the general endpoints give back Theorem 1.1 and
  Theorem 7.1 for `PPTIME` and `BPTIME` unconditionally; the test module
  `CslibFrontierTests/NtimeDspace/Endpoints.lean` checks this, so the hypotheses of
  `CountingAt.lean` are not vacuous.
* `D(n) = n / log n`, the target scale of the remark. The hypotheses hold for
  `DivLog n = n / (log₂ n + 1) + log₂ n + 1` (`scale_divLog`, `carryFits_divLog`), and Theorem 2.3
  at this scale is the same whether written with `DivLog` or with `n / (log₂ n + 1) + 1`
  (`blockBitsAt_divLog_iff`). So: if the bits of the block networks are computed in values below
  `2 ^ (C · (τ / (log₂ τ + 1) + 1))`, then `NTIME[t]`, `PPTIME[t]` and `BPTIME[t]` are all in
  `DSPACE[t / (log₂ t + 1)]` for every `t(n) ≥ n` (`ntime_subset_dspace_divLog_of_blockBitsAt`,
  `pptime_subset_dspace_divLog_of_blockBitsAt`, `bptime_subset_dspace_divLog_of_blockBitsAt`), in
  simultaneous time `2 ^ O(t / log t)` (`generalSimulationAt_divLog_of_blockBitsAt`,
  `pptime_decidedAt_divLog_of_blockBitsAt`). These are conditional: Theorem 2.3 is proved only at
  `SqrtLog`.

Below `n / log n` the route stops: every scale fitting the carry of the column adder is
`Ω(n / log n)` (`Exact.CarryFits.div_log_le`).
-/

public section

namespace Cslib.Complexity.NtimeDspace.Crossing

open NtimeDspace.Cross Cslib.Complexity _root_.Turing.MultiTapeTM

/-! ### `D = SqrtLog`: the existing endpoints by the general route -/

/-! ### `D = n / log n`: the target of the remark -/

/-- Theorem 2.3 at the scale `n / log n` is the same with `DivLog` or with `n / (log₂ n + 1) + 1`.
-/
theorem blockBitsAt_divLog_iff :
    Exact.BlockBitsAt (fun n => n / (n.log2 + 1) + 1) ↔ Exact.BlockBitsAt DivLog :=
  ⟨Exact.BlockBitsAt.mono (c := 1) fun n => by unfold DivLog; omega,
    Exact.BlockBitsAt.mono (c := 10) fun n => by have := divLog_le n; omega⟩

section DivLog

variable (h : Exact.BlockBitsAt (fun n => n / (n.log2 + 1) + 1))
include h

/-- **Theorem 1.1 at `n / log n`, from Theorem 2.3 at `n / log n`**: every problem in `NTIME[t]`,
`t(n) ≥ n`, is decided in simultaneous time `2 ^ (C · DivLog (t n))` and space
`C · DivLog (t n)`. -/
theorem generalSimulationAt_divLog_of_blockBitsAt : GeneralSimulationAt DivLog :=
  generalSimulationAt_of_blockBitsAt scale_divLog carryFits_divLog (blockBitsAt_divLog_iff.mp h)

/-- **`NTIME[t] ⊆ DSPACE[t / log t]` from Theorem 2.3 at `n / log n`**, for every `t(n) ≥ n`. -/
theorem ntime_subset_dspace_divLog_of_blockBitsAt (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊆ DSPACE encBits (fun n => t n / ((t n).log2 + 1)) :=
  (ntime_subset_dspace_of_blockBitsAt scale_divLog carryFits_divLog (blockBitsAt_divLog_iff.mp h)
    t ht).trans (DSPACE_mono_of_le_mul_add (C := 5) fun n => divLog_le (t n))

/-- **Theorem 7.1 for `PPTIME` at `n / log n`, from Theorem 2.3 at `n / log n`**: every problem
in `PPTIME[t]`, `t(n) ≥ n`, is decided in simultaneous time `2 ^ (C · DivLog (t n))` and space
`C · DivLog (t n)`. -/
theorem pptime_decidedAt_divLog_of_blockBitsAt {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n)
    {A : Set (List Bool)} (hA : A ∈ PPTIME encBits t) : DecidedAt DivLog t A :=
  pptime_decidedAt_of_blockBitsAt scale_divLog carryFits_divLog (blockBitsAt_divLog_iff.mp h) ht hA

/-- **`PPTIME[t] ⊆ DSPACE[t / log t]` from Theorem 2.3 at `n / log n`**, for every `t(n) ≥ n`. -/
theorem pptime_subset_dspace_divLog_of_blockBitsAt (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    PPTIME encBits t ⊆ DSPACE encBits (fun n => t n / ((t n).log2 + 1)) :=
  (pptime_subset_dspace_of_blockBitsAt scale_divLog carryFits_divLog (blockBitsAt_divLog_iff.mp h)
    t ht).trans (DSPACE_mono_of_le_mul_add (C := 5) fun n => divLog_le (t n))

/-- **`BPTIME[t] ⊆ DSPACE[t / log t]` from Theorem 2.3 at `n / log n`**, for every `t(n) ≥ n`. -/
theorem bptime_subset_dspace_divLog_of_blockBitsAt (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n) :
    BPTIME encBits t ⊆ DSPACE encBits (fun n => t n / ((t n).log2 + 1)) :=
  (bptime_subset_dspace_of_blockBitsAt scale_divLog carryFits_divLog (blockBitsAt_divLog_iff.mp h)
    t ht).trans (DSPACE_mono_of_le_mul_add (C := 5) fun n => divLog_le (t n))

end DivLog

end Cslib.Complexity.NtimeDspace.Crossing
