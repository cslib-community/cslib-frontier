/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Computability.Circuit.Arithmetic.HamiltonianCycle
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Arithmetic.GridSum
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.MainTheorem
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Transfer
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# VP ≠ VNP over every field: Theorem M.3 and Corollary M.4

Theorem L.1 (`GridComplete.size_gt`) holds over every field `K : Type` with the absolute constant
`1 / 1600²`, but its `m₀` depends on `K`. Theorem M.3 makes `m₀` depend only on the
characteristic `p`, and allows fields in every universe: by Lemma M.1
(`Separation.lem_transfer`), a circuit over a field of characteristic `p` for a polynomial with
integer coefficients gives one of the same size over the algebraic closure `K` of the prime field,
where Theorem L.1 applies to the Hamiltonian cycle polynomials (`gridComplete_hcFamily`, the
grid-sum completeness of Proposition M.2) and, when `p ≠ 2`, to the permanents
(`gridComplete_permFamily`). As `HC_m` is in `VNP` over every field (`hcFamily_mem_VNP`), it is not
in `VP` by Theorem M.3, so `VP F ⊂ VNP F` for every field `F` (Corollary M.4).

## Main results

* `Cslib.Circuits.Arithmetic.size_gt_of_charP`: Theorem M.3.
* `Cslib.Circuits.Arithmetic.VP_ssubset_VNP`: Corollary M.4.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma M.1 (p. 60), Theorem M.3 (p. 61) and Corollary M.4 (p. 62); module `Paper.Fields`
-/

public section

namespace Cslib.Circuits.Arithmetic

universe u

/-- An algebraically closed field of characteristic `p`, zero or prime: the algebraic closure of
the prime field. -/
private theorem exists_isAlgClosed_charP (p : ℕ) (hp : p = 0 ∨ p.Prime) :
    ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ CharP K p := by
  rcases hp with rfl | hp
  · exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance, inferInstance⟩
  · have := Fact.mk hp
    exact ⟨AlgebraicClosure (ZMod p), inferInstance, inferInstance, inferInstance⟩

/-- **Lower bound over all fields** (Theorem M.3 of [AnthropicVPVNP2026], p. 61), with
`c = 1 / 1600²`. For every `p`, zero or prime, there is `m₀` such that over every field of
characteristic `p` and for every `m ≥ m₀`, every circuit for the Hamiltonian cycle polynomial
`HC_m`, and every circuit for the permanent `PERM_m` if `p ≠ 2`, has more than
`m ^ ((log m)^{1/3} / 1600²)` nodes. -/
theorem size_gt_of_charP (p : ℕ) (hp : p = 0 ∨ p.Prime) : ∃ m₀ : ℕ,
    ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (ComputedWithin ((hcFamily F).poly m) s →
        (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s) ∧
      (p ≠ 2 → ComputedWithin ((permFamily F).poly m) s →
        (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s) := by
  obtain ⟨K, _, _, _⟩ := exists_isAlgClosed_charP p hp
  obtain ⟨m₁, h1⟩ := GridComplete.size_gt (gridComplete_hcFamily (K := K))
  obtain ⟨m₂, h2⟩ : ∃ m₂ : ℕ, p ≠ 2 → ∀ m ≥ m₂, ∀ s, ComputedWithin ((permFamily K).poly m) s →
      (m : ℝ) ^ (Real.logb 2 m ^ (1 / 3 : ℝ) / 1600 ^ 2) < s := by
    by_cases hp2 : p = 2
    · exact ⟨0, fun h => absurd hp2 h⟩
    · obtain ⟨m₂, h⟩ := GridComplete.size_gt
        (gridComplete_permFamily (K := K) (Ring.two_ne_zero (by rwa [ringChar.eq K p])))
      exact ⟨m₂, fun _ => h⟩
  refine ⟨m₁ + m₂, fun F _ _ m hm s => ⟨fun hs => h1 m (by omega) s ?_,
    fun hp2 hs => h2 hp2 m (by omega) s ?_⟩⟩
  · have h := Separation.lem_transfer (F := F) (KK := K) p (genericMatrix ℤ m).hamiltonianCycleSum
      (by rwa [map_hamiltonianCycleSum_genericMatrix])
    rwa [map_hamiltonianCycleSum_genericMatrix] at h
  · have h := Separation.lem_transfer (F := F) (KK := K) p (genericMatrix ℤ m).permanent
      (by rwa [map_permanent_genericMatrix])
    rwa [map_permanent_genericMatrix] at h

/-- **VP ≠ VNP over every field** (Corollary M.4 of [AnthropicVPVNP2026], p. 62). Over every field,
`VP` is a proper subset of `VNP`: the Hamiltonian cycle polynomials are in `VNP`
(`hcFamily_mem_VNP`) and, by Theorem M.3, not in `VP`. -/
theorem VP_ssubset_VNP (F : Type u) [Field F] : VP F ⊂ VNP F := by
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨m₀, h⟩ := size_gt_of_charP.{u} p (CharP.char_is_prime_or_zero F p).symm
  exact ⟨VP_subset_VNP, fun hVP => PolynomialFamily.not_mem_VP_of_rpow_lt
    (fun m hm s => (h F m hm s).1) (hVP hcFamily_mem_VNP)⟩

end Cslib.Circuits.Arithmetic
