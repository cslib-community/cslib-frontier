/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Interactive.Debate.TwoBlock

/-!
# Tests for the two-block machine

Checks for `CslibFrontier/Computability/Interactive/Debate/TwoBlock.lean`:

* the steps of the machine with `m = 1`, which has five steps: the empty address, the previous
  bit, the empty address, the previous bit, and the pair of the bits written second and fourth;
* the oracle at each kind of address;
* the claims of the attacking proposer along one transcript;
* the machine with the fair start law also accepts with probability `c` and is `1`-Lipschitz;
* the two refutations at their smallest block lengths, `m = 601` for `K = 1` and `m = 1201` for
  `K = 2`.
-/

public section

namespace CslibFrontierTests.DebateTwoBlock

open Cslib Cslib.Interactive.Debate
open OracleComp (sumHandler)
open ProbOracleComp (LipschitzAt)

/-- The five steps of the machine with `m = 1`, along the transcript `0, 1, 0, 0`. -/
example (O : TwoBlockQuery → PMF Bool) :
    (twoBlockMachine 1).stepLaw O [] = O (.inl ()) ∧
      (twoBlockMachine 1).stepLaw O [false] = O (.inr (.inl false)) ∧
      (twoBlockMachine 1).stepLaw O [true, false] = O (.inl ()) ∧
      (twoBlockMachine 1).stepLaw O [false, true, false] = O (.inr (.inl false)) ∧
      (twoBlockMachine 1).stepLaw O [false, false, true, false] =
        O (.inr (.inr (true, false))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The oracle at the empty address and at the one-bit addresses. -/
example (start : PMF Bool) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : 2 * c ≤ 1) (u : Bool) :
    twoBlockOracle start c hc0 hc1 (.inl ()) = start ∧
      twoBlockOracle start c hc0 hc1 (.inr (.inl u)) = PMF.pure u :=
  ⟨rfl, rfl⟩

/-- The oracle at the pairs: `2 c` at `(1, 0)`, `0` at `(0, 1)` and `c` on the diagonal. -/
example (start : PMF Bool) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : 2 * c ≤ 1) :
    twoBlockOracle start c hc0 hc1 (.inr (.inr (true, false))) true = ENNReal.ofReal (2 * c) ∧
      twoBlockOracle start c hc0 hc1 (.inr (.inr (false, true))) true = 0 ∧
      twoBlockOracle start c hc0 hc1 (.inr (.inr (true, true))) true = ENNReal.ofReal c ∧
      twoBlockOracle start c hc0 hc1 (.inr (.inr (false, false))) true = ENNReal.ofReal c := by
  simp [twoBlockOracle, Probability.PMF.coin_apply]

/-- The claims of the attacking proposer with `m = 1` on the grid `8`, with `k = 1`, `κ₁ = 4`
and `κ₀ = 2`, along the transcript `0, 1, 0, 0`: the truth `0` at the two block starts, the
lie `1 / 8` at the address `false` in the first block, the truth `0` at the address `false` in
the second block, and `4 / 8` at the pair `(1, 0)`. -/
example :
    twoBlockClaim (N := 8) 1 1 4 2 [] = 0 ∧
      twoBlockClaim (N := 8) 1 1 4 2 [false] = 1 ∧
      twoBlockClaim (N := 8) 1 1 4 2 [true, false] = 0 ∧
      twoBlockClaim (N := 8) 1 1 4 2 [false, true, false] = 0 ∧
      twoBlockClaim (N := 8) 1 1 4 2 [false, false, true, false] = 4 := by
  decide

/-- With a fair start the machine still accepts with probability `c`. -/
example (m : ℕ) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle
      (twoBlockOracle (Probability.PMF.uniformOfFintype Bool) (1 / 4) (by norm_num)
        (by norm_num))) ((twoBlockMachine m).run (2 * m + 3)) true = ENNReal.ofReal (1 / 4) :=
  evalWith_run_twoBlockMachine m _ _ _ _

/-- With a fair start the machine is `1`-Lipschitz at its oracle. -/
example (m : ℕ) :
    LipschitzAt 1 (twoBlockOracle (Probability.PMF.uniformOfFintype Bool) (1 / 4) (by norm_num)
      (by norm_num)) ((twoBlockMachine m).run (2 * m + 3)) :=
  lipschitzAt_run_twoBlockMachine m _ _ _ _

/-- The refutation with the constants for `K = 1` at the smallest block length, `m = 601`, that
is `1205` steps. -/
example :
    ∃ A : Proposer (Params.figure1 1 1205).grid, ∀ B : Challenger (Params.figure1 1 1205).grid,
      2 / 5 < OracleComp.evalWith
        (sumHandler ProbComp.unifOracle ((twoBlockMachine 601).stepLaw
          (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))))
        (run (Params.figure1 1 1205) A B) true :=
  (not_sound_figure1_of_lipschitzAt_run_twoBlockMachine 601 le_rfl).2.2

/-- The refutation with the constants for `K = 2` at the smallest block length, `m = 1201`,
that is `2405` steps. -/
example :
    ∃ A : Proposer (Params.figure1 2 2405).grid, ∀ B : Challenger (Params.figure1 2 2405).grid,
      2 / 5 < OracleComp.evalWith
        (sumHandler ProbComp.unifOracle ((twoBlockMachine 1201).stepLaw
          (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))))
        (run (Params.figure1 2 2405) A B) true :=
  (not_sound_figure1_two_of_lipschitzAt_run_twoBlockMachine 1201 le_rfl).2.2

end CslibFrontierTests.DebateTwoBlock
