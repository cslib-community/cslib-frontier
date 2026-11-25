/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Interactive.Debate.CopyChain

/-!
# Tests for the constants of the source

For `K = 1` the parameters `Params.figure1` of
`CslibFrontier/Computability/Interactive/Debate/CopyChain.lean` have `d = 150`: the verifier's
tolerance is `1 / (4 d) = 1 / 600`, the honest challenger's is `1 / (2 d) = 1 / 300`, and there
are `T` rounds.
-/

public section

namespace CslibFrontierTests.DebateCopyChain

open Cslib Cslib.Interactive.Debate
open scoped NNReal

/-- `⌈150 K⌉ = 150` at `K = 1`. -/
theorem ceil_d : ⌈150 * ((1 : ℝ≥0) : ℝ)⌉₊ = 150 := by
  rw [NNReal.coe_one, mul_one]
  exact Nat.ceil_natCast 150

example (T : ℕ) : (Params.figure1 1 T).verifierTolerance = 1 / 600 := by
  change 1 / (4 * ((⌈150 * ((1 : ℝ≥0) : ℝ)⌉₊ : ℕ) : ℝ)) = 1 / 600
  rw [ceil_d]
  norm_num

example (T : ℕ) : (Params.figure1 1 T).challengerTolerance = 1 / 300 := by
  change 1 / (2 * ((⌈150 * ((1 : ℝ≥0) : ℝ)⌉₊ : ℕ) : ℝ)) = 1 / 300
  rw [ceil_d]
  norm_num

example (T : ℕ) : (Params.figure1 1 T).rounds = T := rfl

/-- The grid is the honest challenger's sample count. -/
example (T : ℕ) : (Params.figure1 1 T).grid = (Params.figure1 1 T).challengerSamples := rfl

end CslibFrontierTests.DebateCopyChain
