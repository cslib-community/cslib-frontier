/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Foundations.Algebra.BigOperators.IteMem
import CslibFrontier.Foundations.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The ends of the complete network, and two hubs for a balanced set

In the first lower bound for the complete network on `k` nodes of [AnthropicVPVNP2026]
(Proposition E.5, in the flat case; module `Nc.CaseI.Geo` and the estimate
`prop_flat_lower_lengths` of `Paper.Flat`), the wire between the nodes `a ≠ b` has
two ends, which stand in `ℝ ^ k` at `Flat.endPoint a b = (e_a - e_b) / (2 √2)` and at
`Flat.endPoint b a`, at distance one (`Flat.dist_endPoint`).

For a set `A` of nodes with `k / 3 ≤ |A| ≤ 2 k / 3` there is a point `x` of norm `1 / (6 √k)`
such that connecting the ends at the nodes of `A` to `x` and all other ends to `-x` costs at most
`k (k - 1) / 2 - k / 12` in all (`Flat.exists_norm_eq_sum_dist_endPoint_le`): this is `k / 12`
less than the `k (k - 1) / 2` wires of length one.

## Main definitions

* `Flat.endPoint`: the place of the end at `a` of the wire between `a` and `b`.

## Main results

* `Flat.dist_endPoint`: the two ends of a wire are at distance one.
* `Flat.exists_norm_eq_sum_dist_endPoint_le`: two hubs for a balanced set of nodes.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition E.5 (a first lower bound for the network polynomial), the lengths in its proof;
  modules `Nc.CaseI.Geo` and `Paper.Flat`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset

variable {k : ℕ}

/-- The unit vector `(e_a - e_b) / √2`. -/
private noncomputable def unitDiff (a b : Fin k) : EuclideanSpace ℝ (Fin k) :=
  (√2)⁻¹ • (EuclideanSpace.single a 1 - EuclideanSpace.single b 1)

private theorem unitDiff_swap (a b : Fin k) : unitDiff b a = -unitDiff a b := by
  rw [unitDiff, unitDiff, ← smul_neg, neg_sub]

private theorem norm_unitDiff {a b : Fin k} (h : a ≠ b) : ‖unitDiff a b‖ = 1 := by
  have h1 : ‖(EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 :
      EuclideanSpace ℝ (Fin k))‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, PiLp.norm_single, PiLp.norm_single, EuclideanSpace.inner_single_left]
    simp [h]
    norm_num
  rw [unitDiff, norm_smul, ← Real.sqrt_sq (norm_nonneg (_ - _)), h1, norm_inv,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (by positivity)

private theorem inner_unitDiff (a b : Fin k) (v : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (unitDiff a b) v = (√2)⁻¹ * (v a - v b) := by
  rw [unitDiff, real_inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left]
  simp

/-- The place of the end at `a` of the wire between the nodes `a` and `b`:
`(e_a - e_b) / (2 √2)`. -/
@[expose] noncomputable def endPoint (a b : Fin k) : EuclideanSpace ℝ (Fin k) :=
  (1 / 2 : ℝ) • (√2)⁻¹ • (EuclideanSpace.single a 1 - EuclideanSpace.single b 1)

private theorem endPoint_eq (a b : Fin k) : endPoint a b = (1 / 2 : ℝ) • unitDiff a b := rfl

/-- The two ends of a wire are at distance one. -/
theorem dist_endPoint {a b : Fin k} (h : a ≠ b) : dist (endPoint a b) (endPoint b a) = 1 := by
  rw [endPoint_eq, endPoint_eq, unitDiff_swap a b, dist_eq_norm, smul_neg, sub_neg_eq_add,
    ← add_smul]
  norm_num
  exact norm_unitDiff h

/-- The direction of the hubs for the set `A`: `k - |A|` at the nodes of `A` and `-|A|` at the
others. -/
private noncomputable def hubDir (A : Finset (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun a => if a ∈ A then (k : ℝ) - A.card else -(A.card : ℝ)

private theorem hubDir_apply (A : Finset (Fin k)) (a : Fin k) :
    hubDir A a = if a ∈ A then (k : ℝ) - A.card else -(A.card : ℝ) := rfl

private theorem norm_hubDir_sq (A : Finset (Fin k)) :
    ‖hubDir A‖ ^ 2 = A.card * ((k : ℝ) - A.card) * k := by
  have h (a : Fin k) : ‖hubDir A a‖ ^ 2 =
      if a ∈ A then ((k : ℝ) - A.card) ^ 2 else (A.card : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs, hubDir_apply]
    split_ifs <;> ring
  rw [EuclideanSpace.norm_sq_eq]
  simp only [h, Fintype.sum_ite_mem_const, Fintype.card_fin]
  ring

/-- The gain of the two hubs: the signed sum of the differences of `hubDir A`. -/
private theorem sum_sign_mul_hubDir_sub (A : Finset (Fin k)) :
    ∑ a, ∑ b, (if a ∈ A then (1 : ℝ) else -1) * (hubDir A a - hubDir A b) =
      2 * (A.card * ((k : ℝ) - A.card) * k) := by
  have h0 : ∑ b, hubDir A b = 0 := by
    simp only [hubDir_apply, Fintype.sum_ite_mem_const, Fintype.card_fin]
    ring
  have h (a : Fin k) : ∑ b, (if a ∈ A then (1 : ℝ) else -1) * (hubDir A a - hubDir A b) =
      if a ∈ A then k * ((k : ℝ) - A.card) else k * A.card := by
    rw [← mul_sum, sum_sub_distrib, h0, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      hubDir_apply]
    split_ifs <;> ring
  simp only [h, Fintype.sum_ite_mem_const, Fintype.card_fin]
  ring

/-- **Two hubs for a balanced set** ([AnthropicVPVNP2026], proof of Proposition E.5). For a set
`A` of nodes with `k / 3 ≤ |A| ≤ 2 k / 3` there is a point `x` of norm `1 / (6 √k)` such that the
distances from the ends at the nodes of `A` to `x` and from the other ends to `-x` add up to at
most `k (k - 1) / 2 - k / 12`. -/
theorem exists_norm_eq_sum_dist_endPoint_le (hk : 1 ≤ k) (A : Finset (Fin k))
    (h1 : k ≤ 3 * A.card) (h2 : 3 * A.card ≤ 2 * k) :
    ∃ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 1 / (6 * √k) ∧
      ∑ a, ∑ b, (if a = b then 0 else dist (endPoint a b) (if a ∈ A then x else -x)) ≤
        (k : ℝ) * (k - 1) / 2 - k / 12 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs1 : (k : ℝ) ≤ 3 * A.card := by exact_mod_cast h1
  have hs2 : 3 * (A.card : ℝ) ≤ 2 * k := by exact_mod_cast h2
  set Q : ℝ := A.card * ((k : ℝ) - A.card) * k
  have hQk : 2 / 9 * (k : ℝ) ^ 3 ≤ Q := by
    have hpos := mul_nonneg hk0.le (mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hs2))
    linarith [show (k : ℝ) * ((3 * (A.card : ℝ) - k) * (2 * k - 3 * A.card)) =
      9 * Q - 2 * (k : ℝ) ^ 3 by dsimp only [Q]; ring]
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQk
  set η : ℝ := 1 / (6 * √k)
  have hη0 : 0 < η := by positivity
  have hηsq : η ^ 2 = 1 / (36 * k) := by
    dsimp only [η]; rw [div_pow, mul_pow, Real.sq_sqrt hk0.le]; norm_num
  have hnormv : ‖hubDir A‖ = √Q := by
    dsimp only [Q]; rw [← norm_hubDir_sq, Real.sqrt_sq (norm_nonneg _)]
  have hnorm : ‖(η / √Q) • hubDir A‖ = η := by
    rw [norm_smul, hnormv, Real.norm_of_nonneg (by positivity)]
    exact div_mul_cancel₀ _ (Real.sqrt_pos.2 hQ0).ne'
  refine ⟨(η / √Q) • hubDir A, hnorm, ?_⟩
  -- every end pays at most its wire, plus `η ^ 2`, minus its gain in the direction of the hubs
  have hterm (a b : Fin k) : (if a = b then 0 else dist (endPoint a b)
      (if a ∈ A then (η / √Q) • hubDir A else -((η / √Q) • hubDir A))) ≤
      (1 / 2 + η ^ 2 - if a = b then 1 / 2 + η ^ 2 else 0) - η / √Q * (√2)⁻¹ *
        ((if a ∈ A then (1 : ℝ) else -1) * (hubDir A a - hubDir A b)) := by
    by_cases hab : a = b
    · simp [hab]
    · rw [ite_eq_right hab, ite_eq_right hab, sub_zero, endPoint_eq]
      refine (dist_half_smul_le (norm_unitDiff hab) _).trans (le_of_eq ?_)
      split_ifs <;>
        simp only [inner_neg_right, real_inner_smul_right, inner_unitDiff, norm_neg, hnorm] <;> ring
  refine (sum_le_sum fun a _ => sum_le_sum fun b _ => hterm a b).trans ?_
  have hsum : ∑ a, ∑ b, η / √Q * (√2)⁻¹ *
      ((if a ∈ A then (1 : ℝ) else -1) * (hubDir A a - hubDir A b)) =
      η / √Q * (√2)⁻¹ * (2 * Q) := by
    rw [show 2 * Q = _ from (sum_sign_mul_hubDir_sub A).symm, mul_sum]
    exact sum_congr rfl fun a _ => by rw [mul_sum]
  simp only [sum_sub_distrib, hsum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_ite_eq, mem_univ, ite_true]
  -- the gain is at least `k / 9`
  have hgain : k / 9 ≤ η / √Q * (√2)⁻¹ * (2 * Q) := by
    have e1 : η / √Q * (√2)⁻¹ * (2 * Q) = η * √(2 * Q) := by
      rw [Real.sqrt_mul (by norm_num) Q]
      calc η / √Q * (√2)⁻¹ * (2 * Q)
          = η * (√2 * √2 * (√2)⁻¹) * (√Q * √Q / √Q) := by
            rw [Real.mul_self_sqrt (by norm_num), Real.mul_self_sqrt hQ0.le]; ring
        _ = η * (√2 * √Q) := by
            rw [mul_inv_cancel_right₀ (Real.sqrt_ne_zero'.mpr (by norm_num)),
              mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hQ0).ne', mul_assoc]
    have e2 : 2 / 3 * k * √k ≤ √(2 * Q) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, mul_pow, Real.sq_sqrt hk0.le]
      linarith [show (2 / 3 * (k : ℝ)) ^ 2 * k = 4 / 9 * (k : ℝ) ^ 3 by ring]
    rw [e1]
    calc (k : ℝ) / 9 = η * (2 / 3 * k * √k) := by
          have : √(k : ℝ) ≠ 0 := by positivity
          dsimp only [η]; field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left e2 hη0.le
  have hloss : (k : ℝ) * (k - 1) * η ^ 2 ≤ k / 36 := by
    rw [hηsq, show (k : ℝ) * (k - 1) * (1 / (36 * k)) = (k - 1) / 36 by field_simp]
    linarith
  linarith

end Cslib.Circuits.Arithmetic.Separation.Flat
