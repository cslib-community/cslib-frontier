/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PolyTime.BitString.SmallBias
import CslibFrontier.Foundations.Data.BitString.List.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Checked clients of the uniform small-bias constructor, including empty width and the
constant-error schedule required by the gap-quadratic-system application. -/

set_option linter.privateModule false

open Cslib.BitString Turing.MultiTapeTM
open Cslib.Probability

-- Degree one works at empty width: four seeds, and no parity constraints.
example : poweringMasks 0 6 = [[], [], [], []] := by decide

-- Exercise the actual modulus search, table multiplication and parity evaluation together.
-- For each of the seven nonzero characters in dimension three, the imbalance is at most
-- half of the sixteen seeds (the sharper AGHP bound at this parameter).
example :
    let rows := poweringMasks 3 1
    rows.length = 16 ∧
      (∀ row ∈ rows, row.length = 3) ∧
      (enumList 3).all (fun z => z == [false, false, false] ||
        decide (2 * (rows.countP fun row => listDot row z) ≥ 8 ∧
          2 * (rows.countP fun row => listDot row z) ≤ 24)) = true := by decide

-- Fixing the error parameter still gives one uniform machine for all widths.
example : ComputableInPolyTime (fun n => poweringMasks n 6) encUnary (encList encBits) :=
  ComputableInPolyTime.comp (f := fun p : ℕ × ℕ => poweringMasks p.1 p.2)
    (g := fun n => (n, 6)) poweringMasks_polyTime
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 6))

-- A later reduction can use both the number of equations and its soundness parameter.
example (n : ℕ) :
    IsSmallBias (1 / 6 : ℝ)
      ((PMF.uniformOfFintype (Fin (poweringMasks n 6).length)).map
        fun i : Fin (poweringMasks n 6).length =>
        ofList n ((poweringMasks n 6).getD i [])) ∧
      (poweringMasks n 6).length ≤ 4 * (6 * n + 1) ^ 2 := by
  refine ⟨isSmallBias_poweringMasks n (by decide), ?_⟩
  simpa only [Nat.mul_comm n 6] using (poweringMasks_size n 6).2.1
