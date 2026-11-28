/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.SharpP.ApproximateCounting

/-! # Clients of Stockmeyer's approximate counting

Checked instances of the hypotheses of `FNP.exists_approxCount_SAT` (Goldreich, Theorem 6.27)
and its `#P` step `SharpP.exists_approxCount_SAT`, of the sieve query of Goldreich's Exercise
6.34, the factor-`1 / 2` form of Arora–Barak's Exercise 9 §6(a) as the case `ε = 1 / 2` of
`SharpP.exists_approx_of_NP_subset_P`, and its deterministic form, Exercise 9 §6(c), from
`SharpP.exists_deterministic_approx_of_NP_subset_P`.
-/

set_option linter.privateModule false

open Cslib Cslib.Complexity Cslib.BitString Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

-- The step toward Goldreich, Theorem 6.27, for the constant precision `1`: the hypothesis on `q`
-- is satisfiable.
example {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ (ℓ : Polynomial ℕ) (E : α × List Bool → ℕ),
      ComputableInPolyTimeWithOracle (encCNF '' SAT) E (encPair enc encBits) encNat ∧
      ∀ a, dens {r : BitString (ℓ.eval (enc a).length) |
        (f a : ℚ) / (Polynomial.C 1 : Polynomial ℕ).eval (enc a).length <
          |(E (a, List.ofFn r) : ℚ) - f a|} ≤ (2 ^ (enc a).length)⁻¹ :=
  SharpP.exists_approxCount_SAT hf _ fun _ => by simp

-- Goldreich, Theorem 6.27, for the witnesses of an exact-length NP relation, which form a
-- balanced PC relation.
example (R : NPRelation enc) :
    ∃ (ℓ : Polynomial ℕ) (E : α × List Bool → ℕ),
      ComputableInPolyTimeWithOracle (encCNF '' SAT) E (encPair enc encBits) encNat ∧
      ∀ a, dens {r : BitString (ℓ.eval (enc a).length) |
        (searchCount R.IsWitness a : ℚ) / (Polynomial.C 1 : Polynomial ℕ).eval (enc a).length <
          |(E (a, List.ofFn r) : ℚ) - searchCount R.IsWitness a|} ≤ (2 ^ (enc a).length)⁻¹ :=
  FNP.exists_approxCount_SAT R.isWitness_mem_FNP _ fun _ => by simp

-- Goldreich, Exercise 6.34: the sieve queries are in `NP`.
example (R : NPRelation enc) : R.sieveQuery.language ∈ NP (encHashQuery α enc) :=
  R.sieveQuery.language_mem_NP

-- A sieve query asking for no solution is always answered yes.
example (R : NPRelation enc) (a : α) (j : ℕ) (s : List Bool) :
    (⟨a, 0, j, s⟩ : HashQuery α) ∈ R.sieveQuery.language :=
  (R.mem_sieveQuery_language_iff _).2 (Nat.zero_le _)

-- Arora–Barak, Exercise 9 §6(a): under `NP ⊆ P`, approximation within the factor `1 / 2`.
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) {f : α → ℕ}
    (hf : f ∈ SharpP enc) :
    ∃ (ℓ : Polynomial ℕ) (A : α × List Bool → ℕ),
      ComputableInPolyTime A (encPair enc encBits) encNat ∧
      ∀ a, 2 / 3 ≤ dens {r : BitString (ℓ.eval (enc a).length) |
        (f a : ℚ) / 2 ≤ A (a, List.ofFn r) ∧ (A (a, List.ofFn r) : ℚ) ≤ 2 * f a} := by
  obtain ⟨ℓ, A, hA, hdens⟩ := SharpP.exists_approx_of_NP_subset_P h hf (ε := 1 / 2) (by norm_num)
  refine ⟨ℓ, A, hA, fun a => (hdens a).trans (dens_le_dens fun r hr => ?_)⟩
  simp only [mem_filter, mem_univ, true_and] at hr ⊢
  constructor <;> linarith [hr.1, hr.2]

-- Arora–Barak, Exercise 9 §6(c): under `NP ⊆ P`, deterministic approximation within the factor
-- `1 / 2`, for every instance.
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) {f : α → ℕ}
    (hf : f ∈ SharpP enc) :
    ∃ A : α → ℕ, ComputableInPolyTime A enc encNat ∧
      ∀ a, (f a : ℚ) / 2 ≤ A a ∧ (A a : ℚ) ≤ 2 * f a := by
  obtain ⟨A, hA, hAf⟩ :=
    SharpP.exists_deterministic_approx_of_NP_subset_P h hf (ε := 1 / 2) (by norm_num)
  exact ⟨A, hA, fun a => by constructor <;> linarith [hAf a]⟩

-- Deterministic approximation within relative error `1 / (n + 1)`, `n` the encoded length.
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) {f : α → ℕ}
    (hf : f ∈ SharpP enc) :
    ∃ A : α → ℕ, ComputableInPolyTime A enc encNat ∧
      ∀ a, f a ≤ A a ∧ ((enc a).length + 1) * A a ≤ ((enc a).length + 1 + 1) * f a := by
  obtain ⟨A, hA, hAf⟩ :=
    SharpP.exists_deterministic_approxCount_of_NP_subset_P h hf (Polynomial.X + 1) fun _ => by simp
  refine ⟨A, hA, fun a => ?_⟩
  simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using hAf a
