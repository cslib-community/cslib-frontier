/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Pairs
public import Mathlib.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Foundations.Algebra.BigOperators.IteMem
import CslibFrontier.Foundations.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The ends at facet centres of a cube, and two hubs for a balanced set

In the lower bound for the complete network on `k` nodes with long strings of
[AnthropicVPVNP2026] (Proposition E.10, in the flat case; module `Nc.CaseI.Hub` and the estimates
`prop_flat_rate_direction`, `prop_flat_rate_lengths` of `Paper.Rate`), the two ends of the wire
between the nodes `a < b` stand both on the `a`-th coordinate axis, at `e_a / 2` for the end at
`a` and at `-e_a / 2` (not `-e_b / 2`) for the end at `b`: facet centres of the cube
`[-1/2, 1/2] ^ k`, at distance one (`Flat.cubeEndPoint`, `Flat.dist_cubeEndPoint`).

For a set `A` of nodes with `k / 3 ≤ |A| ≤ 2 k / 3` there is a point `x` of norm `2 / (9 √k)`
such that connecting the ends at the nodes of `A` to `x` and all other ends to `-x` costs at most
`k (k - 1) / 2 - 4 k / 81` in all (`Flat.exists_norm_eq_sum_dist_cubeEndPoint_le`).

## Main definitions

* `Flat.cubeEndPoint`: the place of an end of a wire.

## Main results

* `Flat.dist_cubeEndPoint`: the two ends of a wire are at distance one.
* `Flat.exists_norm_eq_sum_dist_cubeEndPoint_le`: two hubs for a balanced set of nodes.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition E.10 (lower bound for the network polynomial), the ends and the hubs in its proof;
  modules `Nc.CaseI.Hub` and `Paper.Rate`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset

variable {k : ℕ}

/-- The place of the end `i` of the wire between the nodes `a < b`: `e_a / 2` for the end at `a`
(`i = 0`), and `-e_a / 2` for the end at `b`. -/
@[expose] noncomputable def cubeEndPoint (e : Pair k) (i : Fin 2) : EuclideanSpace ℝ (Fin k) :=
  (if i = 0 then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single e.low 1

/-- The two ends of a wire are at distance one. -/
theorem dist_cubeEndPoint (e : Pair k) : dist (cubeEndPoint e 0) (cubeEndPoint e 1) = 1 := by
  simp only [cubeEndPoint, ite_true, Fin.reduceEq, ite_false, dist_eq_norm, ← sub_smul,
    norm_smul]
  norm_num

/-- The sign of a node: `1` on `A` and `-1` outside. -/
private noncomputable def sign (A : Finset (Fin k)) (a : Fin k) : ℝ := if a ∈ A then 1 else -1

/-- The direction of the hubs: at the node `a`, the number of wires to nodes `b > a` on the other
side of `A`, with the sign of `a`. -/
private noncomputable def cubeHubDir (A : Finset (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  ∑ e : Pair k with ¬(e.low ∈ A ↔ e.high ∈ A), sign A e.low • EuclideanSpace.single e.low 1

private theorem inner_cubeHubDir (A : Finset (Fin k)) (w : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (cubeHubDir A) w =
      ∑ e : Pair k, if ¬(e.low ∈ A ↔ e.high ∈ A) then sign A e.low * w e.low else 0 := by
  rw [cubeHubDir, sum_inner, sum_filter]
  refine sum_congr rfl fun e _ => ?_
  split_ifs
  · rfl
  · rw [real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp

/-- The number of wires that a set of nodes separates. -/
private theorem sum_separated (A : Finset (Fin k)) :
    ∑ e : Pair k, (if ¬(e.low ∈ A ↔ e.high ∈ A) then (1 : ℝ) else 0) =
      A.card * ((k : ℝ) - A.card) := by
  have h (e : Pair k) : (if ¬(e.low ∈ A ↔ e.high ∈ A) then (1 : ℝ) else 0) =
      (if e.low ∈ A ∧ e.high ∉ A then (1 : ℝ) else 0) +
        if e.high ∈ A ∧ e.low ∉ A then (1 : ℝ) else 0 := by
    by_cases ha : e.low ∈ A <;> by_cases hb : e.high ∈ A <;> simp [ha, hb]
  have h3 (a b : Fin k) : (if a = b then (0 : ℝ) else if a ∈ A ∧ b ∉ A then 1 else 0) =
      if a ∈ A then (if b ∈ A then 0 else 1) else 0 := by
    by_cases hab : a = b
    · subst hab
      by_cases ha : a ∈ A <;> simp [ha]
    · by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [hab, ha, hb]
  have h4 (a : Fin k) : (∑ b : Fin k, if a ∈ A then (if b ∈ A then (0 : ℝ) else 1) else 0) =
      if a ∈ A then (k : ℝ) - A.card else 0 := by
    by_cases ha : a ∈ A
    · simp only [ha, ite_true, Fintype.sum_ite_mem_const, Fintype.card_fin]
      ring
    · simp [ha]
  rw [sum_congr rfl fun e _ => h e, sum_pair_add_swap fun a b => if a ∈ A ∧ b ∉ A then (1 : ℝ)
    else 0]
  simp only [h3, h4, Fintype.sum_ite_mem_const, Fintype.card_fin]
  ring

/-- The direction of the hubs is long, by the Cauchy–Schwarz inequality. -/
private theorem le_norm_cubeHubDir (hk : 1 ≤ k) (A : Finset (Fin k)) (h1 : k ≤ 3 * A.card)
    (h2 : 3 * A.card ≤ 2 * k) : 2 / 9 * ((k : ℝ) * √k) ≤ ‖cubeHubDir A‖ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs1 : (k : ℝ) ≤ 3 * A.card := by exact_mod_cast h1
  have hs2 : 3 * (A.card : ℝ) ≤ 2 * k := by exact_mod_cast h2
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin k), w = WithLp.toLp 2 (sign A) := ⟨_, rfl⟩
  have hwn : ‖w‖ = √k := by
    have (a : Fin k) : ‖w a‖ ^ 2 = 1 := by
      simp only [hw, sign]
      split_ifs <;> simp
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hin : inner ℝ (cubeHubDir A) w = (A.card : ℝ) * ((k : ℝ) - A.card) := by
    rw [inner_cubeHubDir, ← sum_separated]
    refine sum_congr rfl fun e _ => ?_
    split_ifs
    · rfl
    · simp only [hw, sign]
      split_ifs <;> norm_num
  have hcs := real_inner_le_norm (cubeHubDir A) w
  rw [hwn, hin] at hcs
  have hs0 : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
  refine le_of_mul_le_mul_right ?_ hs0
  calc 2 / 9 * ((k : ℝ) * √k) * √k = 2 / 9 * (k : ℝ) ^ 2 := by
        rw [mul_assoc, mul_assoc, Real.mul_self_sqrt hk0.le]
        ring
    _ ≤ _ := le_trans (by nlinarith) hcs

/-- **Two hubs for a balanced set** ([AnthropicVPVNP2026], proof of Proposition E.10). For a set
`A` of nodes with `k / 3 ≤ |A| ≤ 2 k / 3` there is a point `x` of norm `2 / (9 √k)` such that the
distances from the ends at the nodes of `A` to `x` and from the other ends to `-x` add up to at
most `k (k - 1) / 2 - 4 k / 81`. -/
theorem exists_norm_eq_sum_dist_cubeEndPoint_le (hk : 1 ≤ k) (A : Finset (Fin k))
    (h1 : k ≤ 3 * A.card) (h2 : 3 * A.card ≤ 2 * k) :
    ∃ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 2 / (9 * √k) ∧
      ∑ e : Pair k, (dist (cubeEndPoint e 0) (if e.low ∈ A then x else -x) +
        dist (cubeEndPoint e 1) (if e.high ∈ A then x else -x)) ≤
        (k : ℝ) * (k - 1) / 2 - 4 / 81 * k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : 0 < √(k : ℝ) := Real.sqrt_pos.2 hk0
  have hv := le_norm_cubeHubDir hk A h1 h2
  have hv0 : 0 < ‖cubeHubDir A‖ := lt_of_lt_of_le (by positivity) hv
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 2 / (9 * √k) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := hγ ▸ by positivity
  obtain ⟨x, hx⟩ : ∃ x, x = (γ / ‖cubeHubDir A‖) • cubeHubDir A := ⟨_, rfl⟩
  have hn : ‖x‖ = γ := by
    rw [hx, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact div_mul_cancel₀ _ hv0.ne'
  refine ⟨x, hγ ▸ hn, ?_⟩
  have hterm (e : Pair k) : dist (cubeEndPoint e 0) (if e.low ∈ A then x else -x) +
      dist (cubeEndPoint e 1) (if e.high ∈ A then x else -x) ≤ (1 + 2 * γ ^ 2) -
        2 * (if ¬(e.low ∈ A ↔ e.high ∈ A) then sign A e.low * x e.low else 0) := by
    have hu : ‖(EuclideanSpace.single e.low (1 : ℝ) : EuclideanSpace ℝ (Fin k))‖ = 1 := by simp
    have hu' : ‖-(EuclideanSpace.single e.low (1 : ℝ) : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      simp
    have e0 : cubeEndPoint e 0 = (1 / 2 : ℝ) • EuclideanSpace.single e.low 1 := by
      simp [cubeEndPoint]
    have e1 : cubeEndPoint e 1 = (1 / 2 : ℝ) • -EuclideanSpace.single e.low 1 := by
      simp [cubeEndPoint, smul_neg, neg_smul]
    rw [e0, e1]
    refine (add_le_add (dist_half_smul_le hu _) (dist_half_smul_le hu' _)).trans (le_of_eq ?_)
    by_cases ha : e.low ∈ A <;> by_cases hb : e.high ∈ A <;>
      simp [sign, ha, hb, EuclideanSpace.inner_single_left, inner_neg_left, hn] <;> ring
  refine (sum_le_sum fun e _ => hterm e).trans ?_
  have hN : ∑ _e : Pair k, (1 + 2 * γ ^ 2) = (k : ℝ) * (k - 1) / 2 * (1 + 2 * γ ^ 2) := by
    rw [← sum_pair_one, sum_mul]
    simp
  rw [sum_sub_distrib, ← mul_sum, ← inner_cubeHubDir, hx, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hN,
    show γ / ‖cubeHubDir A‖ * ‖cubeHubDir A‖ ^ 2 = γ * ‖cubeHubDir A‖ by field_simp]
  have hgain : 4 / 81 * (k : ℝ) ≤ γ * ‖cubeHubDir A‖ :=
    calc 4 / 81 * (k : ℝ) = γ * (2 / 9 * ((k : ℝ) * √k)) := by
          rw [hγ]
          field_simp
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv hγ0.le
  have hloss : (k : ℝ) * (k - 1) * γ ^ 2 ≤ 4 / 81 * k := by
    have : γ ^ 2 * k = 4 / 81 := by
      rw [hγ, div_pow, mul_pow, Real.sq_sqrt hk0.le]
      field_simp
      norm_num
    calc (k : ℝ) * ((k : ℝ) - 1) * γ ^ 2 = γ ^ 2 * k * ((k : ℝ) - 1) := by ring
      _ = 4 / 81 * ((k : ℝ) - 1) := by rw [this]
      _ ≤ _ := by linarith
  linarith

end Cslib.Circuits.Arithmetic.Separation.Flat
