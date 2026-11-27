/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Contracting.Accelerator
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Contracting.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube

/-! Tests of the circuit lemma (Lemma K.3) and the lower bound in the contracting case
(Theorem K.7), as a client that sees only the public statements.

* Lemma K.3 as printed: for a table of `ℤ` with one generator and the permanent over `ℚ`, small
  circuits give accelerators.
* Theorem K.7 over `ℚ`: the flat case holds, or circuits for the permanent have more than
  `2 ^ (c (log m) ^ 2 / log log m)` nodes; the same for the Hamiltonian cycle polynomial, as
  Theorem M.3 uses it.
* Under hypotheses: in the contracting case, one node does not suffice for a family complete for
  grid sums. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationContracting

open Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Interpreter Cslib.Circuits.Arithmetic.Separation.TwoCases

/-! ### Closed examples -/

/-- The table of `ℤ` with the one generator `[true]`, of value `1`. -/
private def oneGen : List Bool → ℤ := fun w => if w = [true] then 1 else 0

private theorem finite_support_oneGen : (Function.support oneGen).Finite :=
  (Set.finite_singleton [true]).subset fun w hw => by simpa [oneGen] using hw

/-- **Lemma K.3 as printed**, for the table `oneGen` of the ring `ℤ`, `H = 32` and the permanent
over `ℚ`, in which `2 ≠ 0`: a circuit with `v ^ a` nodes for `PERM_m`, `m ≥ v ^ B₀`, gives an
accelerator of size `v ^ (C (a + 1))` at the scale `v`. -/
example : ∃ B₀ C v₀ : ℕ, 0 < B₀ ∧ ∀ v, v₀ ≤ v → ∀ a, lg v ^ (C * a) ≤ v → ∀ m, v ^ B₀ ≤ m →
    ComputedWithin ((permFamily ℚ).poly m) (v ^ a) →
      HasAcc oneGen ℚ 32 v (v ^ (C * (a + 1))) := by
  obtain ⟨B₀, C, v₀, hB₀, h⟩ := Contracting.exists_hasAcc_of_computedWithin
    finite_support_oneGen le_rfl 3
  exact ⟨B₀, C, v₀, hB₀, h ℚ _ (gridComplete_permFamily (by norm_num))⟩

/-- **Theorem K.7 over `ℚ`**: the flat case holds, or there are `c > 0` and `m₀` such that for
`m ≥ m₀` every circuit for `PERM_m` has more than `2 ^ (c (log m) ^ 2 / log log m)` nodes. -/
example : FlatCase ℚ ∨ ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s,
    ComputedWithin ((permFamily ℚ).poly m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s :=
  (flatCase_or_contractingCase ℚ).imp_right fun hK => hK.perm_size_gt (by norm_num)

/-- **The Hamiltonian cycle polynomial over `ℚ`**, as Theorem M.3 uses the contracting case: the
flat case holds, or circuits for `HC_m` have more than `2 ^ (c (log m) ^ 2 / log log m)` nodes. -/
example : FlatCase ℚ ∨ ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s,
    ComputedWithin ((hcFamily ℚ).poly m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  refine (flatCase_or_contractingCase ℚ).imp_right fun hK => ?_
  obtain ⟨C, M₁, h⟩ := hK.not_computedWithin_pow gridComplete_hcFamily
  exact Contracting.exists_quasipoly_lt_of_not_pow (fun _ _ _ hst hs => hs.mono hst) h

/-! ### The contract under hypotheses -/

section Contract

variable {K : Type} [Field K]

/-- **One node is not enough**: in the contracting case, for a family `G` complete for grid sums,
`G.poly M` is not computed within `M ^ 0 = 1` node for large `M`. -/
example (hK : ContractingCase K) {G : PolynomialFamily K} {κ : ℕ} (hG : GridComplete G κ) :
    ∃ M₁ : ℕ, ∀ M ≥ M₁, ¬ ComputedWithin (G.poly M) 1 := by
  obtain ⟨C, M₁, h⟩ := hK.not_computedWithin_pow hG
  refine ⟨M₁ + 1, fun M hM hc => h M (by omega) 0 (by rw [Nat.mul_zero, pow_zero]; omega) ?_⟩
  rwa [pow_zero]

end Contract

end CslibFrontierTests.SeparationContracting
