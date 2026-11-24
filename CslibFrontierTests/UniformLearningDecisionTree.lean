/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.UniformLearning.LowDegreeClasses
import Mathlib.Tactic.NormNum

/-! # Tests for learning small decision trees by the low-degree algorithm

The conjunction of the first two of three bits is computed by a decision tree with three leaves,
so it lies in the class of trees with at most three leaves. With `s = 3` and `ε = 1 / 2`, the
degree `t = 3 = ⌈log₂ (3 / (1 / 2))⌉` satisfies `2 · 3 ≤ (1 / 2) · 2 ^ 4`, so some number of
examples lets the low-degree algorithm of degree `3` learn that class with error and confidence
`1 / 2`. -/

public section

namespace CslibFrontierTests.UniformLearningDecisionTree

open Cslib Cslib.MachineLearning.UniformLearning Cslib.MachineLearning.PACLearning Finset

/-- The conjunction of the first two of three bits is computed by a decision tree with three
leaves. -/
theorem and_mem_decisionTreeClass :
    (fun x : Fin 3 → Bool => x 0 && x 1) ∈ decisionTreeClass (Fin 3) 3 := by
  refine ⟨.node 0 (.leaf false) (.node 1 (.leaf false) (.leaf true)), ?_, le_rfl⟩
  rw [DecisionTree.computes_iff]
  funext x
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> simp [h₀, h₁]

/-- Decision trees with at most three leaves on three bits are learned with error and confidence
`1 / 2` at degree `3`, from the number of examples the low-degree algorithm asks for. -/
theorem learns_decisionTreeClass_three :
    ∃ m, Learns (lowDegreeLearner (Fin 3) 3 m) (decisionTreeClass (Fin 3) 3) (1 / 2) (1 / 2) :=
  ⟨_, lowDegreeLearner_learns_decisionTreeClass (by norm_num) (by norm_num) (by norm_num)
    (Nat.le_ceil _)⟩

end CslibFrontierTests.UniformLearningDecisionTree
