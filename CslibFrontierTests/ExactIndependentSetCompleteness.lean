/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.IndependentSet.ExactCompleteness

/-!
# Exact independent set completeness clients

The reduction accepts an empty satisfiable formula paired with a formula containing an empty
clause. Two satisfiable formulas with opposite requirements on the same original variable remain
jointly satisfiable after relabeling and exceed the exact target. An unsatisfiable first formula
falls short of the target even when the second formula is unsatisfiable.
-/

set_option linter.privateModule false

open Cslib.Complexity Cslib.Logic.PL

example : SATUNSAT.toExactIndependentSet ([], [[]]) ∈ ExactIndependentSet := by
  apply (SATUNSAT.toExactIndependentSet_mem_iff _).2
  change (∃ σ : ℕ → Bool, CNF.eval σ [] = true) ∧
    ¬∃ σ : ℕ → Bool, CNF.eval σ [[]] = true
  simp

example : SATUNSAT.toExactIndependentSet ([[(0, true)]], [[(0, false)]]) ∉ ExactIndependentSet := by
  rw [SATUNSAT.toExactIndependentSet_mem_iff]
  rintro ⟨_, hn⟩
  apply hn
  exact ⟨fun _ => false, by simp⟩

example : SATUNSAT.toExactIndependentSet ([[]], [[]]) ∉ ExactIndependentSet := by
  rw [SATUNSAT.toExactIndependentSet_mem_iff]
  rintro ⟨⟨σ, hs⟩, _⟩
  simp at hs
