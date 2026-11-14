/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.BaseSampler

/-!
# Tests for Falcon v1.2 BaseSampler

These ordinary-import clients exercise both endpoints and strict-equality boundaries of Algorithm
12's reverse-cumulative table. They also check the fixed source-level component counts. The exact
distribution theorem supplies all 19 masses; these examples do not claim the later `SamplerZ`
rejection law or Falcon's Rényi discrepancy bound.
-/

namespace CslibFrontierTests.Crypto.FalconBaseSampler

open Cslib.Crypto.Falcon

public section

/-- Zero lies below every positive RCDT entry. -/
example : baseSamplerFromWord 0 = (18 : BaseSamplerOutput) := by decide

/-- Equality with the final threshold `1` is rejected by that strict comparison. -/
example : baseSamplerFromWord 1 = (17 : BaseSamplerOutput) := by decide

/-- The word immediately below RCDT entry 16 sees that threshold, while equality does not. -/
example : baseSamplerFromWord 197 = (17 : BaseSamplerOutput) ∧
    baseSamplerFromWord 198 = (16 : BaseSamplerOutput) := by decide

/-- The word immediately below the largest threshold has output one; equality has output zero. -/
example : baseSamplerFromWord 3024686241123004913665 = (1 : BaseSamplerOutput) ∧
    baseSamplerFromWord 3024686241123004913666 = (0 : BaseSamplerOutput) := by decide

/-- The largest 72-bit word is above every RCDT entry. -/
example : baseSamplerFromWord (2 ^ 72 - 1) = (0 : BaseSamplerOutput) := by decide

/-- All 19 exact integer masses fill the 72-bit word range. -/
example : baseSamplerProbabilityNumerators.sum = 2 ^ 72 :=
  baseSampler_probabilityNumerators_sum

/-- Every output has positive exact mass. -/
example (z : BaseSamplerOutput) : z ∈ (ProbComp.eval baseSampler).support := by
  simp

/-- The source-level scan has fixed component counts and a 1296-bit threshold payload. -/
example : baseSamplerRandomBits = 72 ∧
    baseSamplerThresholdComparisons = 18 ∧
    baseSamplerConditionalIncrements = 18 ∧
    baseSamplerThresholdPayloadBits = 1296 := by decide

end

end CslibFrontierTests.Crypto.FalconBaseSampler
