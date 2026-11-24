/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.QUADEQ.Gap

/-! Checked clients of the gap problem of quadratic equations (Goldreich, Exercise 10.6): linear
combinations on a concrete system, both kinds of instances of `GapQUADEQ`, the size of a
concrete amplification, and the source's thresholds `1/3` and `1/2 - ε`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.QUADEQGap

open Cslib Cslib.Logic.PL Cslib.Complexity

/-- `u₀ u₁ = 1` and `u₀ = 0`: inconsistent, since the first forces `u₀ = 1`. -/
def clash : QuadSystem ℕ := [⟨[(0, 1)], true⟩, ⟨[(0, 0)], false⟩]

-- The mask `[true, true]` adds both equations: monomials concatenated, right-hand sides added.
example : clash.linearCombination [true, true] = ⟨[(0, 1), (0, 0)], true⟩ := by decide

-- Unselected and missing mask positions drop equations.
example : clash.linearCombination [false] = ⟨[], false⟩ := by decide

-- At `u₀ = u₁ = 1` only the second equation is violated, so the combination of both is violated
-- (one violated equation selected) and the combination of the first alone holds.
example : ¬(clash.linearCombination [true, true]).Holds fun _ => true := by decide
example : (clash.linearCombination [true, false]).Holds fun _ => true := by decide

/-- `0 = 1`: every assignment violates its only equation. -/
def contradiction : QuadSystem ℕ := [⟨[], true⟩]

-- A no-instance at threshold `1/3`, so the hypotheses of the theorems are satisfiable.
example : contradiction ∈ (GapQUADEQ (1 / 3)).no := by
  refine ⟨by norm_num, fun a => ?_⟩
  have : contradiction.countViolated a = 1 := by
    simp [contradiction, QuadSystem.countViolated, QuadEquation.Holds]
  rw [this]
  norm_num [contradiction]

-- The empty system is a yes-instance, hence never a no-instance.
example (δ : ℝ) : ([] : QuadSystem ℕ) ∈ (GapQUADEQ δ).yes :=
  ⟨fun _ => false, by simp [QuadSystem.Holds]⟩

-- The amplification of a one-equation system with `k = 1` has `(2 ^ 1) ^ 2 = 4` equations, and
-- every assignment violates at least none of them, as `1 - 1/1 = 0`.
example : (QUADEQ.amplify 1 contradiction).length = 4 := by
  rw [QUADEQ.amplify, List.length_map, (BitString.poweringMasks_size _ _).1]
  decide

-- With `k = 3`, every assignment violates at least a third of the amplified equations.
example (a : ℕ → Bool) :
    1 / 3 ≤ ((QUADEQ.amplify 3 contradiction).countViolated a : ℝ) /
      (QUADEQ.amplify 3 contradiction).length := by
  have := QUADEQ.le_countViolated_amplify (k := 3) (by norm_num) (F := contradiction) (a := a)
    fun h => by simpa [QuadEquation.Holds] using h _ List.mem_cons_self
  norm_num at this ⊢
  linarith

/-! ### The source's thresholds -/

-- Goldreich, Exercise 10.6: violation threshold one third.
example : PromiseProblem.NPHard QUADEQ.encoding (GapQUADEQ (1 / 3)) :=
  GapQUADEQ_npHard (by norm_num) (by norm_num)

-- The `ε`-biased variant: threshold `1/2 - ε`, for `0 < ε < 1/2`.
example {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    PromiseProblem.NPHard QUADEQ.encoding (GapQUADEQ (1 / 2 - ε)) :=
  GapQUADEQ_npHard (by linarith) (by linarith)

-- NP-completeness: also in promise-NP.
example : GapQUADEQ (1 / 3) ∈ PromiseNP QUADEQ.encoding := GapQUADEQ_mem_PromiseNP _

end CslibFrontierTests.QUADEQGap
