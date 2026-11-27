/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Pairs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The numbers of the first lower bound for the complete network

The first lower bound for the polynomial of the complete network on `k` nodes with strings of `ℓ`
bits ([AnthropicVPVNP2026], Proposition E.5, flat case; module `Nc.CaseI.Lower`) compares three
sums of lengths: `S1` over the wires, `S2` over the ends of the wires and two hubs, and `S3`
between the hubs. With a placement whose distances are close to the given lengths up to a factor
`c ≤ ℓ / 100` and an error `δ = 1 / (150 k)`, an inequality `ℓ S1 ≤ k + ℓ S2 + S3 lg` forces
`ℓ k √k / 6 ≤ lg` (`Flat.lower_numbers`). The ends of the wires add the error `δ` once per end
(`Flat.sum_pair_add_add_swap`).

## Main results

* `Flat.sum_pair_add_add_swap`: a sum over the ends of the wires with an error for each end.
* `Flat.lower_numbers`: the numbers of the lower bound.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition E.5; module `Nc.CaseI.Lower`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset

variable {k : ℕ}

/-- A sum over the ends of the wires, with an error `δ` at each end, is the sum over the ordered
pairs of distinct nodes plus `δ` for each of the `k (k - 1)` ends. -/
theorem sum_pair_add_add_swap (G : Fin k → Fin k → ℝ) (δ : ℝ) :
    ∑ e : Pair k, ((G e.low e.high + δ) + (G e.high e.low + δ)) =
      (∑ a, ∑ b, if a = b then 0 else G a b) + 2 * ((k : ℝ) * (k - 1) / 2) * δ := by
  rw [← sum_pair_add_swap, ← sum_pair_one, mul_sum, sum_mul, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- **The numbers of the lower bound.** -/
theorem lower_numbers {k ℓ c N δ S1 S2 S3 lg : ℝ} (hk1 : 1 ≤ k) (hℓ0 : 0 ≤ ℓ) (hc : 0 ≤ c)
    (hN : N = k * (k - 1) / 2) (hδ : δ = 1 / (150 * k)) (hlog : 0 ≤ lg) (hℓc : 100 * c ≤ ℓ)
    (hw : N * (1 - δ) ≤ c * S1) (hh : c * S2 ≤ N - k / 12 + 2 * N * δ)
    (hm : c * S3 ≤ 1 / (3 * √k) + δ) (h1 : ℓ * S1 ≤ k + ℓ * S2 + S3 * lg) :
    ℓ * (k * √k) / 6 ≤ lg := by
  have h3 : ℓ * (N * (1 - δ)) ≤
      c * k + ℓ * (N - k / 12 + 2 * N * δ) + (1 / (3 * √k) + δ) * lg := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left hw hℓ0,
      mul_le_mul_of_nonneg_left hh hℓ0, mul_le_mul_of_nonneg_right hm hlog]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 1 ≤ s ∧ s ^ 2 = k :=
    ⟨√k, Real.one_le_sqrt.2 hk1, Real.sq_sqrt (by linarith)⟩
  rw [Real.sqrt_sq (by linarith)] at h3 ⊢
  subst hN hδ
  have hs0 : 0 < s := by linarith
  field_simp at h3
  -- `h3` says `ℓ (792 s⁴ + 108 s²) ≤ 10800 s⁴ c + (3600 s + 72) lg`.
  have h4 : 612 * (ℓ * s ^ 4) ≤ 3672 * (s * lg) := by
    nlinarith [mul_le_mul_of_nonneg_left hℓc (by positivity : (0 : ℝ) ≤ s ^ 4),
      mul_le_mul_of_nonneg_right hs hlog, mul_nonneg hℓ0 (sq_nonneg s)]
  by_contra h
  nlinarith [mul_lt_mul_of_pos_left (not_le.1 h) hs0]

end Cslib.Circuits.Arithmetic.Separation.Flat
