/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.PairwiseIndependentHash.Affine
import CslibFrontier.Probability.PairwiseIndependentHash.Retention
import Mathlib.Algebra.Field.ZMod

/-! Checked instances of the hitting bounds for pairwise independent generators
(Goldreich, Exercise 7.23): the shape of the exercise, a generator
`G : {0,1}^{2n} → ({0,1}^n)^n`, and a concrete affine family. -/

set_option linter.privateModule false

open Finset Cslib.Probability

/-- Exercise 7.23 in Goldreich's form: one of the `n` outputs of a pairwise independence generator
lies in `T` with probability at least `min (n α) 1 / 2`, and at least `0.75 n α` if
`α ≤ 1 / (2 n)`. -/
example {n : ℕ} (G : (Fin (2 * n) → Bool) → Fin n → Fin n → Bool)
    (hG : IsPairwiseIndependentHash G) (T : Finset (Fin n → Bool)) :
    min (n * dens T) 1 / 2 ≤ dens {s | ∃ j, G s j ∈ T} ∧
      (2 * n * dens T ≤ 1 → 3 / 4 * (n * dens T) ≤ dens {s | ∃ j, G s j ∈ T}) := by
  have h1 := hG.min_mul_div_two_le_dens_filter_exists_apply_mem univ T
  have h2 := fun hT => hG.three_quarters_mul_le_dens_filter_exists_apply_mem (S := univ) (B := T) hT
  simp only [card_univ, Fintype.card_fin, mem_univ, true_and] at h1 h2
  exact ⟨h1, h2⟩

/-- The affine maps `x ↦ A x + b` on `𝔽₂`, applied to both points of `𝔽₂`, hit `{0}` with
probability at least `1 / 2`. -/
example : (1 / 2 : ℚ≥0) ≤
    dens {p | ∃ x ∈ (univ : Finset (Fin 1 → ZMod 2)),
      affineHash (F := ZMod 2) (m := Fin 1) (n := Fin 1) p x ∈
        ({0} : Finset (Fin 1 → ZMod 2))} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := (isPairwiseIndependentHash_affineHash (F := ZMod 2) (m := Fin 1)
    (n := Fin 1)).min_mul_div_two_le_dens_filter_exists_apply_mem univ {0}
  have hS : #(univ : Finset (Fin 1 → ZMod 2)) = 2 := by
    rw [card_univ, Fintype.card_pi, prod_const, ZMod.card, card_univ, Fintype.card_fin]; rfl
  have hT : dens ({0} : Finset (Fin 1 → ZMod 2)) = 1 / 2 := by
    rw [dens_singleton, Fintype.card_pi, prod_const, ZMod.card, card_univ, Fintype.card_fin]
    norm_num
  rw [hS, hT] at key
  norm_num at key ⊢
  exact key
