/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.GridSum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Contracting.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Rate
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The main theorems: Theorems L.1, L.2 and Corollary L.3

By Theorem D.2 (`Separation.TwoCases.flatCase_or_contractingCase`) every field is in the flat or
in the contracting case of [AnthropicVPVNP2026]. Let `G` be a family complete for grid sums. In
the flat case Theorem E.11 (`Separation.Flat.size_gt_of_gridComplete`) shows that circuits for
`G.poly m` have more than `2 ^ ((log m)^{4/3} / 1600²)` nodes for large `m`. In the contracting
case Theorem K.7 (`Separation.TwoCases.ContractingCase.not_computedWithin_pow` with
`Separation.Contracting.exists_quasipoly_lt_of_not_pow`) gives the bound
`2 ^ (c (log m)² / log log m)`, which is eventually larger. As
`2 ^ ((log m)^{4/3} / 1600²) = m ^ ((log m)^{1/3} / 1600²)`, this is Theorem L.1 with
`c = 1 / 1600²` (`GridComplete.size_gt`). Theorem L.2 follows
(`GridComplete.not_computedWithin_pow`), and with it Corollary L.3: if such a family is in `VNP`,
then `VP ⊂ VNP` (`GridComplete.VP_ssubset_VNP`).

The paper states these results over `ℝ` and for the permanent. Here they hold over every field and
for every family complete for grid sums: the permanent when `2 ≠ 0` (`gridComplete_permFamily`,
in `VNP` by Ryser's formula, `permFamily_mem_VNP`) and the Hamiltonian cycle polynomial over every
field (`gridComplete_hcFamily`, `hcFamily_mem_VNP`).

## Main results

* `GridComplete.size_gt`: Theorem L.1.
* `GridComplete.not_computedWithin_pow`: Theorem L.2.
* `GridComplete.VP_ssubset_VNP`: Corollary L.3.
* `PolynomialFamily.not_mem_VP_of_rpow_lt`: a family with the bound of Theorem L.1 is not in `VP`,
  over a field in any universe.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem D.2 (p. 30), Theorems L.1, L.2 and Corollary L.3 (p. 59) with their proofs (p. 60);
  module `Paper.Rate`
-/

public section

namespace Cslib.Circuits.Arithmetic

open Filter Separation Separation.TwoCases

variable {K : Type} [Field K]

/-- The bound of the contracting case eventually exceeds that of the flat case:
`(log m)^{4/3} / 1600² ≤ c (log m)² / log log m` for large `m`, for every `c > 0`. -/
private theorem exists_le_quasipoly {c : ℝ} (hc : 0 < c) : ∃ m₀ : ℕ, ∀ m ≥ m₀,
    Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2 ≤
      c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m) := by
  have hev : ∀ᶠ x : ℝ in atTop, x ^ (4 / 3 : ℝ) / 1600 ^ 2 ≤ c * x ^ 2 / Real.logb 2 x := by
    filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).bound
      (by positivity : 0 < c * 1600 ^ 2 * Real.log 2), eventually_ge_atTop 2] with x hx h2
    have hx0 : 0 < x := by linarith
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
      Real.norm_of_nonneg (by positivity)] at hx
    have hlx : Real.logb 2 x ≤ c * 1600 ^ 2 * x ^ (2 / 3 : ℝ) := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      linarith
    rw [div_le_div_iff₀ (by norm_num) (Real.logb_pos one_lt_two (by linarith))]
    calc x ^ (4 / 3 : ℝ) * Real.logb 2 x ≤ x ^ (4 / 3 : ℝ) * (c * 1600 ^ 2 * x ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlx (by positivity)
      _ = c * x ^ (4 / 3 + 2 / 3 : ℝ) * 1600 ^ 2 := by rw [Real.rpow_add hx0]; ring
      _ = c * x ^ 2 * 1600 ^ 2 := by norm_num
  exact eventually_atTop.1 (((Real.tendsto_logb_atTop one_lt_two).comp
    tendsto_natCast_atTop_atTop).eventually hev)

/-- **The main theorem** (Theorem L.1 of [AnthropicVPVNP2026], p. 59), for every family complete
for grid sums over every field. If `G` is complete for grid sums with blow-up `κ`, there is `m₀`
such that for `m ≥ m₀` every circuit for `G.poly m` has more than `m ^ ((log m)^{1/3} / 1600²)`
nodes. For the permanent over `ℝ` (`gridComplete_permFamily`) this is Theorem L.1 with
`c = 1 / 1600²`. -/
theorem GridComplete.size_gt {G : PolynomialFamily K} {κ : ℕ} (hG : GridComplete G κ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ComputedWithin (G.poly m) s →
      (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s := by
  -- the bound `2 ^ ((log m)^{4/3} / 1600²)` in the flat and in the contracting case
  obtain ⟨m₀, h⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ComputedWithin (G.poly m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    rcases flatCase_or_contractingCase K with hK | hK
    · obtain ⟨m₀, h⟩ := Flat.size_gt_of_gridComplete κ
      exact ⟨m₀, h K hK G hG⟩
    · obtain ⟨C, M₁, h⟩ := hK.not_computedWithin_pow hG
      obtain ⟨c, hc, m₁, h1⟩ :=
        Contracting.exists_quasipoly_lt_of_not_pow (fun _ _ _ hst hs => hs.mono hst) h
      obtain ⟨m₂, h2⟩ := exists_le_quasipoly hc
      exact ⟨m₁ + m₂, fun m hm s hs => (Real.rpow_le_rpow_of_exponent_le one_le_two
        (h2 m (by omega))).trans_lt (h1 m (by omega) s hs)⟩
  -- `m ^ ((log m)^{1/3} / 1600²) = 2 ^ ((log m)^{4/3} / 1600²)`
  refine ⟨m₀ + 2, fun m hm s hs => (le_of_eq ?_).trans_lt (h m (by omega) s hs)⟩
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (Real.logb_pos one_lt_two hm1),
    Real.rpow_one, mul_div_assoc, Real.rpow_mul zero_le_two,
    Real.rpow_logb two_pos (by norm_num) (by linarith)]

section Universe

universe u

variable {F : Type u} [Field F] {G : PolynomialFamily F} {m₀ : ℕ}

/-- A bound beyond every polynomial: if every circuit for `G.poly m` has more than
`m ^ ((log m)^{1/3} / 1600²)` nodes for `m ≥ m₀`, then for every `C` there is `m₁` such that no
circuit with at most `m ^ C` nodes computes `G.poly m` for `m ≥ m₁`. -/
private theorem PolynomialFamily.not_computedWithin_pow_of_rpow_lt
    (h : ∀ m ≥ m₀, ∀ s, ComputedWithin (G.poly m) s →
      (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s) (C : ℕ) :
    ∃ m₁ : ℕ, ∀ m ≥ m₁, ¬ ComputedWithin (G.poly m) (m ^ C) := by
  obtain ⟨m₁, h1⟩ := eventually_atTop.1 ((((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop)).atTop_div_const
      (by norm_num : (0 : ℝ) < 1600 ^ 2)).eventually_ge_atTop (C : ℝ))
  refine ⟨m₀ + m₁ + 2, fun m hm hc => (h1 m (by omega)).not_gt ?_⟩
  have h2 := h m (by omega) _ hc
  rwa [Nat.cast_pow, ← Real.rpow_natCast (m : ℝ) C,
    Real.rpow_lt_rpow_left_iff (by exact_mod_cast (by omega : 1 < m))] at h2

/-- A family whose circuits eventually need more than `m ^ ((log m)^{1/3} / 1600²)` nodes is not
in `VP`. -/
theorem PolynomialFamily.not_mem_VP_of_rpow_lt
    (h : ∀ m ≥ m₀, ∀ s, ComputedWithin (G.poly m) s →
      (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s) : G ∉ VP F := fun hG => by
  obtain ⟨-, b, ⟨d, hd⟩, hb⟩ := mem_VP_iff.1 hG
  obtain ⟨m₁, hm₁⟩ := PolynomialFamily.not_computedWithin_pow_of_rpow_lt h d
  obtain ⟨m, hm, hbm⟩ := ((eventually_ge_atTop m₁).and hd).exists
  exact hm₁ m hm ((hb m).mono hbm)

end Universe

/-- **No circuits of polynomial size** (Theorem L.2 of [AnthropicVPVNP2026], p. 59), for every
family complete for grid sums over every field: for every `C` there is `m₀` such that for `m ≥ m₀`
no circuit with at most `m ^ C` nodes computes `G.poly m`. As in the paper, it follows from
Theorem L.1. -/
theorem GridComplete.not_computedWithin_pow {G : PolynomialFamily K} {κ : ℕ}
    (hG : GridComplete G κ) (C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ ComputedWithin (G.poly m) (m ^ C) :=
  let ⟨_, h⟩ := GridComplete.size_gt hG
  PolynomialFamily.not_computedWithin_pow_of_rpow_lt h C

/-- **VP ⊂ VNP** (Corollary L.3 of [AnthropicVPVNP2026], p. 59; proof p. 60), for every family
complete for grid sums: if `G` is complete for grid sums and in `VNP`, then `VP` is a proper
subset of `VNP`, because `G` is not in `VP` by Theorem L.2. The permanent is such a family when
`2 ≠ 0` (`gridComplete_permFamily`, `permFamily_mem_VNP` by Ryser's formula), which gives
Corollary L.3 over `ℝ`; the Hamiltonian cycle polynomial is one over every field
(`gridComplete_hcFamily`, `hcFamily_mem_VNP`). -/
theorem GridComplete.VP_ssubset_VNP {G : PolynomialFamily K} {κ : ℕ} (hG : GridComplete G κ)
    (hVNP : G ∈ VNP K) : VP K ⊂ VNP K :=
  let ⟨_, h⟩ := GridComplete.size_gt hG
  ⟨VP_subset_VNP, fun hVP => PolynomialFamily.not_mem_VP_of_rpow_lt h (hVP hVNP)⟩

end Cslib.Circuits.Arithmetic
