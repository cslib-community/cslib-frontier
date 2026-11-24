/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

module

import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.WalshRigidity
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.WalshCounts

/-! Application tests with a nontrivial rank cutoff and different total and row budgets. -/

namespace CslibFrontierTests.WalshRigidity

-- With central weights 1 and 2 and overlap band {1}, both tails contribute.
example : let x : Finset (Fin 4) := {0, 1}
    (Finset.univ.filter fun y : Finset (Fin 4) => 1 ≤ y.card ∧ y.card ≤ 2 ∧
      ((x ∩ y).card < 1 ∨ 2 ≤ (x ∩ y).card)).card = 4 := by
  exact (Cslib.card_off_band_row 4 1 2 1 1 {0, 1}).trans (by decide)

example : (Finset.univ.filter fun p : Finset (Fin 4) × Finset (Fin 4) =>
    1 ≤ p.1.card ∧ p.1.card ≤ 2 ∧ 1 ≤ p.2.card ∧ p.2.card ≤ 2 ∧
      ((p.1 ∩ p.2).card < 1 ∨ 2 ≤ (p.1 ∩ p.2).card)).card = 48 := by
  exact (Cslib.card_off_band_pair 4 1 2 1 1).trans (by decide)

example (K : Type*) [Field K] : (Matrix.sylvesterHadamard K 8).rigidity 73 ≤ 9240 := by
  exact (Matrix.rigidity_sylvesterHadamard_le K 8 2 6 1 3).trans (by decide)

example (K : Type*) [Field K] :
    ∃ B : Matrix (Fin 256) (Fin 256) K, B.rank ≤ 73 ∧
      ∀ i, ({j | Matrix.sylvesterHadamard K 8 i j ≠ B i j} : Set _).ncard ≤ 80 := by
  apply (Matrix.exists_rank_le_sylvesterHadamard_row_edits_le_of_row_sum_le K 8 2 6 1 3 80 ?_).2
  intro a ha hlo hhi
  interval_cases a <;> decide

end CslibFrontierTests.WalshRigidity
