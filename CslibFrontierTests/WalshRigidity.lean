/-
Copyright (c) 2026 Samuel Schlesinger, Shengye Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Shengye Tao
-/

import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.WalshRigidity

/-! Application tests with a nontrivial rank cutoff and different total and row budgets. -/

namespace CslibFrontierTests.WalshRigidity

example (K : Type*) [Field K] : (Matrix.sylvesterHadamard K 8).rigidity 73 ≤ 9240 := by
  exact (Cslib.sylvesterHadamardRigidityFinite K 8 2 6 1 3).trans (by decide)

example (K : Type*) [Field K] :
    ∃ B : Matrix (Fin 256) (Fin 256) K, B.rank ≤ 73 ∧
      ∀ i, ({j | Matrix.sylvesterHadamard K 8 i j ≠ B i j} : Set _).ncard ≤ 80 := by
  apply (Cslib.sylvesterHadamardRowWitness K 8 2 6 1 3 80 ?_).2
  intro a ha hlo hhi
  interval_cases a <;> decide

end CslibFrontierTests.WalshRigidity
