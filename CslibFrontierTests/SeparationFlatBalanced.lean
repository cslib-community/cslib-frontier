/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.BalancedProducts

/-! Tests of balanced products, as a client that sees only the public statements: the product of
two variables in two blocks, computed with three nodes, and the case of a polynomial that is
already set-multilinear on all blocks, which is then itself the sum of balanced products. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatBalanced

open Finset MvPolynomial Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation.Flat

/-- Two blocks of one variable each. The product `X 0 * X 1` has a circuit with three nodes, so
it is a sum of three products for each of the sets `S` of one block, with a factor on `S` and a
factor on the other block. -/
example : ∃ g h : Finset (Fin 2) → Fin (1 + 1 + 1) → MvPolynomial (Fin 2) ℚ,
    (∀ S δ, IsSetMultilinear id S (g S δ)) ∧ (∀ S δ, IsSetMultilinear id Sᶜ (h S δ)) ∧
      (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) =
        ∑ S with 2 ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * 2, ∑ δ, g S δ * h S δ := by
  obtain ⟨g, h, hg, hh, e⟩ := exists_balanced_products
    ((computedWithin_X (K := ℚ) (0 : Fin 2)).mul (computedWithin_X 1)) id le_rfl
  refine ⟨g, h, hg, hh, e ▸ (IsSetMultilinear.smProj_eq_self ?_).symm⟩
  have h01 : (univ : Finset (Fin 2)) = {id 0} ∪ {id 1} := by decide
  exact h01 ▸ (isSetMultilinear_X id 0).mul (isSetMultilinear_X id 1) (by decide)

/-- A polynomial with a small circuit that is set-multilinear on all blocks is a sum of balanced
products. -/
example {σ K : Type*} [CommSemiring K] {k s : ℕ} {P : MvPolynomial σ K}
    (hP : ComputedWithin P s) (blk : σ → Fin k) (hk : 2 ≤ k) (hsm : IsSetMultilinear blk univ P) :
    ∃ g h : Finset (Fin k) → Fin s → MvPolynomial σ K,
      (∀ S δ, IsSetMultilinear blk S (g S δ)) ∧ (∀ S δ, IsSetMultilinear blk Sᶜ (h S δ)) ∧
      P = ∑ S with k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k, ∑ δ, g S δ * h S δ := by
  obtain ⟨g, h, hg, hh, e⟩ := exists_balanced_products hP blk hk
  exact ⟨g, h, hg, hh, hsm.smProj_eq_self ▸ e⟩

end CslibFrontierTests.SeparationFlatBalanced
