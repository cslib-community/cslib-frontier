/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.PartialSynthesis

/-! General partial synthesis supplies native circuits for arbitrary labels on the support.
The finite extension also covers empty supports and the constant functions on zero inputs. -/

namespace CslibFrontierTests.PartialSynthesis

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- The source's labels need only be defined on the support; no total-function hypothesis
restricts them. The linear overhead is the same `24 n` for every accuracy parameter. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ W : ℕ, ∀ (n : ℕ) (D : Finset (BitString n)), W ≤ D.card →
      ∀ label : D → Bool, ∃ c : Circuit signature n 1,
        (∀ x : D, c.eval interpretation x 0 = label x) ∧
        (c.size : ℝ) ≤ (1 + ε) * D.card / Real.logb 2 D.card + 24 * n := by
  classical
  obtain ⟨W, hW⟩ := PartialSynthesis.eventually_complexityOn_le ε hε
  refine ⟨W, fun n D hD label => ?_⟩
  let u : BooleanFunction n := fun x => if h : x ∈ D then label ⟨x, h⟩ else false
  obtain ⟨c, hc, hsize⟩ := exists_computesOn_size_eq_complexityOn
    (I := interpretation) (S := (D : Set _)) (f := single u)
  refine ⟨c, fun x => ?_, ?_⟩
  · simpa only [single_apply, u, dite_eq_left x.property] using congrFun (hc x.property) 0
  · rw [hsize]
    exact hW n D hD u

/-- Zero and one specified inputs do not require a positivity assumption on their logarithm. -/
example : ∃ C : ℝ, 0 < C ∧
    (∀ (n : ℕ) (u : BooleanFunction n),
      (complexityOn interpretation (∅ : Set (BitString n)) (single u) : ℝ) ≤ C * (n + 1)) ∧
    ∀ u : BooleanFunction 0,
      (complexityOn interpretation ({fun i => Fin.elim0 i} : Set (BitString 0))
        (single u) : ℝ) ≤ C := by
  obtain ⟨C, hC, h⟩ := PartialSynthesis.complexityOn_le 1 (by norm_num)
  refine ⟨C, hC, fun n u => ?_, fun u => ?_⟩
  · simpa using h n ∅ u
  · simpa using h 0 {fun i => Fin.elim0 i} u

end CslibFrontierTests.PartialSynthesis
