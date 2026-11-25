/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Random subsets containing a fixed set, and a weighted intersection tail

For a uniformly random `u`-subset `J` of an `n`-element set, a fixed set `T` lies inside `J` with
probability `C(n - #T, u - #T) / C(n, u) ≤ (u / n) ^ #T` (`card_filter_subset_powersetCard_le`,
from Mathlib's `Finset.card_filter_powersetCard_subset` and `Nat.choose_mul_pow_le`). Expanding
`(2y) ^ #(J ∩ V)` over the subsets of a fixed set `V` turns this into a bound on a weighted upper
tail of the hypergeometric variable `#(J ∩ V)`: the `u`-subsets `J` with `#(J ∩ V) ≥ r`, each
weighted by `(1/2) ^ #(V \ J)`, have total weight at most `C(n, u) (2u / (n + u)) ^ r`
(`sum_powersetCard_ite_half_pow_le`). This is the count behind the case `k = 1` of Håstad's
switching lemma in Arora and Barak's form (`DNF.card_filter_not_cnf_div_card_le`), where `V` is
the set of variables of the formula and `#(V \ J)` its fixed variables, each fixed to a falsifying
value with probability `1/2`.

## Main results

* `Cslib.card_filter_subset_powersetCard_le`: few `u`-subsets contain a fixed set.
* `Cslib.sum_powersetCard_ite_half_pow_le`: the weighted intersection tail.
-/

public section

open Finset

namespace Cslib

/-- The `u`-subsets of an `n`-set containing a fixed set `T` number at most
`C(n, u) (u / n) ^ #T`. -/
theorem card_filter_subset_powersetCard_le {n u : ℕ} (hun : u ≤ n) (T : Finset (Fin n)) :
    (#{J ∈ (univ : Finset (Fin n)).powersetCard u | T ⊆ J} : ℝ) ≤
      n.choose u * ((u : ℝ) / n) ^ #T := by
  rcases lt_or_ge u #T with htu | htu
  · rw [filter_false_of_mem fun J hJ hTJ =>
      (card_le_card hTJ).not_gt (by rwa [(mem_powersetCard.1 hJ).2]), card_empty, Nat.cast_zero]
    positivity
  have hT : #T ≤ n := by simpa using card_le_univ T
  rw [card_filter_powersetCard_subset T univ u (subset_univ _) htu, card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [show u = 0 by omega, show #T = 0 by omega]
  -- `C(n - t, u - t) n ^ t ≤ C(n, u) u ^ t`, from `C(n, u) C(u, t) = C(n, t) C(n - t, u - t)`
  have key : (n - #T).choose (u - #T) * n ^ #T ≤ n.choose u * u ^ #T := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.choose_pos hT)
    calc n.choose #T * ((n - #T).choose (u - #T) * n ^ #T)
        = n.choose u * (u.choose #T * n ^ #T) := by
          rw [← mul_assoc, ← Nat.choose_mul htu]; ring
      _ ≤ n.choose u * (n.choose #T * u ^ #T) :=
          Nat.mul_le_mul_left _ (Nat.choose_mul_pow_le hun #T)
      _ = n.choose #T * (n.choose u * u ^ #T) := by ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact_mod_cast key

/-- **A weighted tail of the intersection with a fixed set.** Summing `(1/2) ^ #(V \ J)` over the
`u`-subsets `J` of an `n`-set that contain at least `r` points of `V` gives at most
`C(n, u) (2u / (n + u)) ^ r`.
Weight each `J` by `y ^ (#(J ∩ V) - r) ≥ 1` with `y = (n + u) / (2u)` and expand
`(2y) ^ #(J ∩ V)` binomially: the subsets `T ⊆ V` contribute `(n / u) ^ #T` times the number of
`J ⊇ T`, at most `C(n, u) (u / n) ^ #T`. -/
theorem sum_powersetCard_ite_half_pow_le {n u r : ℕ} (hu : 0 < u) (hun : u ≤ n)
    (V : Finset (Fin n)) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
        (if r ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0) ≤
      n.choose u * (2 * u / (n + u) : ℝ) ^ r := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
  set y : ℝ := (n + u) / (2 * u) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hyinv : (2 * u / (n + u) : ℝ) = y⁻¹ := by rw [hy, inv_div]
  have h2y : (2 * y - 1) * ((u : ℝ) / n) = 1 := by
    rw [hy]; field_simp; ring
  -- each term is at most `y ^ (-r) (1/2) ^ #V (2y) ^ #(J ∩ V)`
  have hterm (J : Finset (Fin n)) :
      (if r ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0) ≤
        (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (2 * y) ^ #(J ∩ V) := by
    have hsplit : #(V \ J) + #(J ∩ V) = #V := by
      rw [inter_comm]; exact card_sdiff_add_card_inter V J
    split_ifs with hr
    · have hyj : y ^ r ≤ y ^ #(J ∩ V) := pow_le_pow_right₀ hy1 hr
      have he : (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (2 * y) ^ #(J ∩ V) =
          ((1 : ℝ) / 2) ^ #(V \ J) * (y ^ #(J ∩ V) / y ^ r) := by
        rw [← hsplit, mul_pow, pow_add]
        field_simp
        rw [← mul_pow]
        norm_num
      rw [he]
      exact le_mul_of_one_le_right (by positivity) ((one_le_div (by positivity)).2 hyj)
    · positivity
  -- the binomial expansion of `(2y) ^ #(J ∩ V)`, regrouped by `T ⊆ V`
  have hexp (J : Finset (Fin n)) : (2 * y) ^ #(J ∩ V) =
      ∑ T ∈ V.powerset, if T ⊆ J then (2 * y - 1) ^ #T else 0 := by
    have h := sum_pow_mul_eq_add_pow (2 * y - 1) 1 (J ∩ V)
    simp only [one_pow, mul_one, sub_add_cancel] at h
    rw [← h, ← sum_filter]
    refine sum_congr (ext fun T => ?_) fun _ _ => rfl
    simp only [mem_powerset, mem_filter, subset_inter_iff]
    tauto
  have hsum : ∑ J ∈ (univ : Finset (Fin n)).powersetCard u, (2 * y) ^ #(J ∩ V) ≤
      n.choose u * 2 ^ #V := by
    simp only [hexp]
    rw [sum_comm]
    calc ∑ T ∈ V.powerset, ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
          (if T ⊆ J then (2 * y - 1) ^ #T else 0)
        = ∑ T ∈ V.powerset,
            (#{J ∈ (univ : Finset (Fin n)).powersetCard u | T ⊆ J} : ℝ) * (2 * y - 1) ^ #T := by
          refine sum_congr rfl fun T _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ V.powerset, (n.choose u * ((u : ℝ) / n) ^ #T) * (2 * y - 1) ^ #T :=
          sum_le_sum fun T _ => mul_le_mul_of_nonneg_right
            (card_filter_subset_powersetCard_le hun T) (pow_nonneg (by linarith) _)
      _ = ∑ T ∈ V.powerset, (n.choose u : ℝ) := sum_congr rfl fun T _ => by
          rw [mul_assoc, ← mul_pow, mul_comm ((u : ℝ) / n), h2y, one_pow, mul_one]
      _ = n.choose u * 2 ^ #V := by simp [mul_comm]
  calc ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
        (if r ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0)
      ≤ ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
          (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (2 * y) ^ #(J ∩ V) := sum_le_sum fun J _ => hterm J
    _ ≤ (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (n.choose u * 2 ^ #V) := by rw [← mul_sum]; gcongr
    _ = n.choose u * (2 * u / (n + u) : ℝ) ^ r := by
        rw [hyinv, inv_pow, one_div, inv_pow]
        field_simp

end Cslib
