/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Interactive.Debate.CopyChain

/-!
# Tests for the copy chain and the constants of the source

Checks for `CslibFrontier/Computability/Interactive/Debate/CopyChain.lean`:

* the step law of the copy chain against any oracle is the point mass at the previous bit;
* its run outputs `false` with probability `1` (`evalWith_run_copyChain`);
* the two refutations at their smallest numbers of steps: `T = 51`, that is `52` steps, with the
  constants of `Params.default 1 T`, and `T = 307` steps with the constants of
  `Params.figure1 1 T`.

And for `Params.figure1` of `CslibFrontier/Computability/Interactive/Debate.lean`: for `K = 1`
it has `d = 150`, so the verifier's tolerance is `1 / (4 d) = 1 / 600`, the honest challenger's
is `1 / (2 d) = 1 / 300`, and there are `T` rounds.
-/

public section

namespace CslibFrontierTests.DebateCopyChain

open Cslib Cslib.Interactive.Debate
open OracleComp (sumHandler)
open scoped NNReal

variable {Query : Type}

/-- The step law of the copy chain against any oracle: the point mass at the previous bit. -/
example (O : Query → PMF Bool) :
    (copyChain : Machine Query).stepLaw O = fun bits => PMF.pure (bits.headD false) :=
  rfl

/-- The run of the copy chain outputs `false` with probability `1`, whatever the oracle. -/
example (O : Query → PMF Bool) (n : ℕ) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O) ((copyChain : Machine Query).run n) =
      PMF.pure false :=
  evalWith_run_copyChain O n

/-- The refutation with the constants of `Params.default` at the smallest `T`, `T = 51`, that is
`52` steps. -/
example (O : Query → PMF Bool) :
    ∃ A : Proposer (Params.default 1 51).grid, ∀ B : Challenger (Params.default 1 51).grid,
      2 / 5 < OracleComp.evalWith
        (sumHandler ProbComp.unifOracle ((copyChain : Machine Query).stepLaw O))
        (run (Params.default 1 51) A B) true :=
  (not_sound_default_of_lipschitzAt_run 51 le_rfl O).2.2

/-- The refutation with the constants of Figure 1 at the smallest number of steps, `T = 307`. -/
example (O : Query → PMF Bool) :
    ∃ A : Proposer (Params.figure1 1 307).grid, ∀ B : Challenger (Params.figure1 1 307).grid,
      2 / 5 < OracleComp.evalWith
        (sumHandler ProbComp.unifOracle ((copyChain : Machine Query).stepLaw O))
        (run (Params.figure1 1 307) A B) true :=
  (not_sound_figure1_of_lipschitzAt_run 307 le_rfl O).2.2

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
