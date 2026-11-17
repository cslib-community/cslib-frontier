/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Toda.FormulaAmplification

/-! Checked clients of Arora–Barak, draft Lemma 9.19 (`Toda.exists_formulaAmplification`): model
counts of small formulas that are not in conjunctive normal form, and the two residues of the
transformation on them. -/

set_option linter.privateModule false

namespace CslibFrontierTests.TodaFormula

open Cslib.Complexity Cslib.Logic.PL

/-- `x₀ ∨ x₁` has three satisfying assignments of its two variables. -/
example : (QBF.or (.var 0) (.var 1) : QBF ℕ).modelCount = 3 := by decide

/-- `¬(x₀ ∧ x₀)` counts assignments of its one free variable, once. -/
example : (QBF.not (.and (.var 0) (.var 0)) : QBF ℕ).modelCount = 1 := by decide

/-- `x₀ ∧ ¬x₀` has none. -/
example : (QBF.and (.var 0) (.not (.var 0)) : QBF ℕ).modelCount = 0 := by decide

/-- The odd count of `x₀ ∨ x₁` becomes `-1` modulo `2 ^ (m + 1)`, here `8`, and the even count of
`x₀ ∧ ¬x₀` becomes `0`. -/
example : ∃ T : QBF ℕ × ℕ → CNF ℕ,
    (SharpSAT (T (.or (.var 0) (.var 1), 2)) : ZMod 8) = -1 ∧
      (SharpSAT (T (.and (.var 0) (.not (.var 0)), 2)) : ZMod 8) = 0 := by
  obtain ⟨T, -, hT⟩ := Toda.exists_formulaAmplification
  exact ⟨T, (hT _ (by simp) 2).1 (by decide), (hT _ (by simp) 2).2 (by decide)⟩

end CslibFrontierTests.TodaFormula
