/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Toda.RandomParitySAT

/-! Checked client of the two-sided form of Arora–Barak, draft Lemma 9.18
(`Toda.exists_boundedError_ParitySAT_alternation`): with one existential block, the true formula
`∃ x₀, x₀` is mapped into `⊕SAT` for at least two thirds of the random strings and the false
formula `∃ x₀, x₀ ∧ ¬x₀` for at most a third. -/

set_option linter.privateModule false

namespace CslibFrontierTests.TodaRandomParitySAT

open Cslib.Complexity Cslib.Logic.PL

open Classical in
example : ∃ (ρ : Polynomial ℕ) (A : PrenexQBF × List Bool → CNF ℕ),
    BoundedErrorAt encPrenexQBF ρ (fun x => decide (A x ∈ ParitySAT)) ⟨[[0]], .var 0⟩ true ∧
      BoundedErrorAt encPrenexQBF ρ (fun x => decide (A x ∈ ParitySAT))
        ⟨[[0]], .and (.var 0) (.not (.var 0))⟩ false := by
  obtain ⟨ρ, A, -, h⟩ := Toda.exists_boundedError_ParitySAT_alternation 1 true
  refine ⟨ρ, A, ?_, ?_⟩
  · have he : (PrenexQBF.formula true ⟨[[0]], .var 0⟩).eval (fun _ => false) = true := by
      decide
    simpa [he] using h ⟨[[0]], .var 0⟩ (by decide)
  · have he : (PrenexQBF.formula true ⟨[[0]], .and (.var 0) (.not (.var 0))⟩).eval
        (fun _ => false) = false := by
      decide
    simpa [he] using h ⟨[[0]], .and (.var 0) (.not (.var 0))⟩ (by decide)

end CslibFrontierTests.TodaRandomParitySAT
