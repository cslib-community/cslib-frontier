/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.PolySchedule

/-!
# Tests for the polynomial schedule of hardness amplification

Concrete values of the schedule `polyBlock`, `polyBlocks`, `polyArity` at `n = 0`, `s = 2`, and
the numeric premise `hev : (2 ^ 27 * M ^ 3 + 4608 * M + 128) * B ^ 6 ≤ 2 ^ (B / 4)` of
`Cslib.HardnessEncoding.exists_isAverageCaseHard_polyEncode`:

* the schedule at `n = 0`, `s = 2` has block length `2176`, one block, and arity `17408`;
* the premise `hev` holds at `M = 1`, `B = polyBlock 0 2`, so the schedule is not vacuous;
* the premise is not automatic: it fails for a short block `B = 100`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.HardnessAmplification.PolySchedule

open Cslib.HardnessEncoding

/-- `⌊log₂ 3⌋ = 1`, so the block length at `n = 0`, `s = 2` is `64 * 2 + 2048`. -/
example : polyBlock 0 2 = 2176 := by
  have : Nat.log 2 3 = 1 := by decide
  simp [polyBlock, this]

example : polyBlocks 0 2 = 1 := by
  have : Nat.log 2 3 = 1 := by decide
  simp [polyBlocks, polyBlock, this]

/-- The arity is `m w + w` for `w = 4 b = 8704`. -/
example : polyArity 0 2 = 17408 := by
  have : Nat.log 2 3 = 1 := by decide
  simp [polyArity, polyBlocks, polyBlock, this]

set_option exponentiation.threshold 600 in
/-- **Nonvacuity of the numeric premise** at `M = 1`, `B = polyBlock 0 2`. -/
example : (2 ^ 27 * 1 ^ 3 + 4608 * 1 + 128) * polyBlock 0 2 ^ 6 ≤ 2 ^ (polyBlock 0 2 / 4) := by
  have : Nat.log 2 3 = 1 := by decide
  norm_num [polyBlock, this]

/-- The premise fails at a block of length `100`, so it constrains the schedule. -/
example : ¬ (2 ^ 27 * 1 ^ 3 + 4608 * 1 + 128) * 100 ^ 6 ≤ 2 ^ (100 / 4) := by
  norm_num

end CslibFrontierTests.Computability.Circuit.Boolean.HardnessAmplification.PolySchedule
