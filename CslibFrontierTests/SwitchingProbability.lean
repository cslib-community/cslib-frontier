/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.DecisionTree.SwitchingProbability
import CslibFrontier.Foundations.Data.Nat.Choose.Ratio
import Mathlib.Tactic.NormNum

/-! # Checked clients for Arora–Barak, Lemma 13.2 (for `k ≠ 1`) and Exercise 13.3(a)

The hypotheses are satisfiable: the conjunction `x₀ ∧ x₁` is a `2`-DNF, and the corrected
binomial inequality applies at `n = 5`, `t = 3`. -/

set_option linter.privateModule false

open Finset Cslib Cslib.Logic.PL Cslib.BitString

open Classical in
/-- Lemma 13.2 for the `2`-DNF `x₀ ∧ x₁` on `n ≥ 2` variables. -/
example (n s t : ℕ) (hn : 2 ≤ n) :
    (#{ρ ∈ PartialAssignment.withFree (Fin n) (n - t) |
        ¬ ∃ G : CNF (Fin n), (∀ c ∈ G, c.length ≤ s) ∧
          ∀ x, CNF.eval x G = (ρ.fill x ⟨0, by omega⟩ && ρ.fill x ⟨1, by omega⟩)} : ℝ) /
      #(PartialAssignment.withFree (Fin n) (n - t)) ≤
    (((n - t : ℕ) : ℝ) * 2 ^ 10 / n) ^ ((s : ℝ) / 2) := by
  have h := DNF.card_filter_not_cnf_div_card_le (n := n) (s := s) (t := t) (k := 2) (by norm_num)
    (f := fun x => x ⟨0, by omega⟩ && x ⟨1, by omega⟩)
    ⟨[[(⟨0, by omega⟩, true), (⟨1, by omega⟩, true)]], by simp, fun x => by
      simp [DNF.eval, Term.eval, Literal.eval]⟩
  exact_mod_cast h

/-- Exercise 13.3(a), corrected, at `n = 5`, `t = 3`, `k = 1`. -/
example : ((5 : ℕ).choose (3 + 1) : ℝ) ≤ (5 : ℕ).choose 3 * (((5 - 3 : ℕ) : ℝ) / 3) ^ 1 :=
  (Nat.choose_add_le_choose_mul_div_pow (by norm_num)).1
