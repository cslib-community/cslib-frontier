/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Permanent
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.AllFields
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Rate
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.MainTheorem
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! Tests of the rate in the flat case (Proposition E.10, Theorem E.11), of the main theorems
(Theorems L.1, L.2, Corollary L.3) and of their form over all fields (Theorem M.3, Corollary M.4),
as a client that sees only the public statements.

* Proposition E.10 over `ℚ` at `k = 4` and `ℓ = 200 = 100 √4`: `ℚ` is in the contracting case, or
  circuits for `f_{4,200}` have at least `2 ^ 100` nodes.
* Theorem E.11 over `ℚ`, and the flat case for the Hamiltonian cycle polynomial with one `m₀` for
  all fields in the flat case.
* Theorems L.1 and L.2 and Corollary L.3 over `ℝ` as stated in the paper, and Corollary L.3 over
  `ZMod 2` with the Hamiltonian cycle polynomial.
* Theorem M.3 as stated in the paper; Theorem M.3 for the permanent and Corollary M.4 over the
  field `ULift.{1} (ZMod 3)` of characteristic `3` in the universe `1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationRate

open Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Flat Cslib.Circuits.Arithmetic.Separation.TwoCases

/-! ### The flat case -/

/-- **Proposition E.10 over `ℚ`** at `k = 4` and `ℓ = 200 = 100 √4`: `ℚ` is in the contracting
case, or every circuit for `f_{4,200}` has at least `2 ^ (200 · 4 ^ (3/2) / 16) = 2 ^ 100`
nodes. -/
example : ContractingCase ℚ ∨
    ∀ s : ℕ, ComputedWithin (networkPolynomial ℚ 4 200) s → (2 : ℝ) ^ (100 : ℝ) ≤ s := by
  refine (flatCase_or_contractingCase ℚ).symm.imp_right fun hK s hs => ?_
  have h4 : ((4 : ℕ) : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  have h := networkPolynomial_size_ge_of_sqrt_le hK (by norm_num)
    (by rw [h4, Real.rpow_two, Real.sqrt_sq zero_le_two]; norm_num) hs
  rwa [h4, ← Real.rpow_mul zero_le_two, show (2 : ℝ) * (3 / 2) = 3 by norm_num,
    show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num, show ((200 : ℕ) : ℝ) * 8 / 16 = 100 by norm_num] at h

/-- **Theorem E.11 over `ℚ`**: the permanent has more than `2 ^ ((log m)^{4/3} / 1600²)` nodes for
large `m`, or `ℚ` is in the contracting case. -/
example : (∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ComputedWithin ((permFamily ℚ).poly m) s →
    (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) ∨ ContractingCase ℚ :=
  (flatCase_or_contractingCase ℚ).imp (fun hK => hK.perm_size_gt two_ne_zero) id

/-- **The flat case for the Hamiltonian cycle polynomial**, which is complete for grid sums with
blow-up `40`, with one `m₀` for all fields in the flat case. -/
example : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], FlatCase K → ∀ m ≥ m₀, ∀ s,
    ComputedWithin ((hcFamily K).poly m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s :=
  let ⟨m₀, h⟩ := size_gt_of_gridComplete 40
  ⟨m₀, fun K _ hK => h K hK _ gridComplete_hcFamily⟩

/-! ### The main theorems -/

/-- **Theorem L.1 as stated**: there are `c > 0` and `m₀` such that for `m ≥ m₀` every circuit
over `ℝ` for `PERM_m` has more than `m ^ (c (log m)^{1/3})` nodes; here `c = 1 / 1600²`. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    ComputedWithin ((permFamily ℝ).poly m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  obtain ⟨m₀, h⟩ := GridComplete.size_gt (gridComplete_permFamily (two_ne_zero (α := ℝ)))
  exact ⟨1 / 1600 ^ 2, by norm_num, m₀, fun m hm s hs => by
    rw [one_div_mul_eq_div]
    exact h m hm s hs⟩

/-- **Theorem L.2 as stated**: for every `C` there is `m₀` such that for `m ≥ m₀` no circuit over
`ℝ` with at most `m ^ C` nodes computes `PERM_m`. -/
example (C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ ComputedWithin ((permFamily ℝ).poly m) (m ^ C) :=
  GridComplete.not_computedWithin_pow (gridComplete_permFamily two_ne_zero) C

/-- **Corollary L.3 as stated**: over `ℝ`, `VP` is a proper subset of `VNP`. -/
example : VP ℝ ⊂ VNP ℝ :=
  GridComplete.VP_ssubset_VNP (gridComplete_permFamily two_ne_zero) permFamily_mem_VNP

/-- **Corollary L.3 in characteristic `2`**, with the Hamiltonian cycle polynomial in place of the
permanent: over `ZMod 2`, `VP` is a proper subset of `VNP`. -/
example : VP (ZMod 2) ⊂ VNP (ZMod 2) :=
  GridComplete.VP_ssubset_VNP gridComplete_hcFamily hcFamily_mem_VNP

/-! ### All fields -/

/-- **Theorem M.3 as stated**: there is `c > 0` such that for every `p`, zero or prime, there is
`m₀` such that over every field of characteristic `p` and for `m ≥ m₀`, circuits for `HC_m`, and
for `PERM_m` if `p ≠ 2`, have more than `m ^ (c (log m)^{1/3})` nodes. -/
example : ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ,
    ∀ (F : Type) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (ComputedWithin ((hcFamily F).poly m) s →
        (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → ComputedWithin ((permFamily F).poly m) s →
        (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
  refine ⟨1 / 1600 ^ 2, by norm_num, fun p hp => ?_⟩
  obtain ⟨m₀, h⟩ := size_gt_of_charP p hp
  refine ⟨m₀, fun F _ _ m hm s => ?_⟩
  rw [one_div_mul_eq_div]
  exact h F m hm s

/-- **Theorem M.3 in the universe `1`**: over `ULift.{1} (ZMod 3)`, of characteristic `3 ≠ 2`,
circuits for the permanent eventually have more than `m ^ ((log m)^{1/3} / 1600²)` nodes. -/
example : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    ComputedWithin ((permFamily (ULift.{1} (ZMod 3))).poly m) s →
      (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := size_gt_of_charP.{1} 3 (Or.inr Nat.prime_three)
  exact ⟨m₀, fun m hm s => (h (ULift.{1} (ZMod 3)) m hm s).2 (by norm_num)⟩

/-- **Corollary M.4 in the universe `1`**: over `ULift.{1} (ZMod 3)`, `VP` is a proper subset of
`VNP`. -/
example : VP (ULift.{1} (ZMod 3)) ⊂ VNP (ULift.{1} (ZMod 3)) :=
  VP_ssubset_VNP _

end CslibFrontierTests.SeparationRate
