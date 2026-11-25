/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.BoxValues
public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.Tiling
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite preprocessing/query tradeoff for shared box tables

A threshold trades a geometric tail of the completed-leaf counts `beta` against a
weighted binomial prefix of the query counts `alpha`. The all-tile estimate charges
one retained box value for each box of each tile, while the query estimate charges
all requested occurrences separately. Neither estimate is a machine-running-time law.

## Main definitions

* `BoxTradeoff.rho`: geometric decay rate determined by the original depths.

## Main results

* `BoxTradeoff.sum_beta_le`: geometric tail estimate for retained-table construction.
* `BoxTradeoff.sum_alpha_le`: weighted binomial prefix estimate for one sparse query.
* `BoxTradeoff.total_boxes_le`: sum of retained-box counts over the actual finite tile set.

## References

Adapted from [AlmanWilliams2026, equation (7) and Section 4.4], specifically
[Theorem30.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/Theorem30.lean)
lines 53–102 and 253–287, and
[ParameterSteps.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean)
lines 147–172, at the pinned primary formal source. Both files were checked against
that revision. The tile estimate uses this library's padded dimension and therefore
has factor `4*padN²`; a separate band-size premise gives factor `16*N²`. This is a
constant-factor weakening of the source's finer unpadded tile estimate. The source's
analytic encoding-term domination, logarithmic estimates and final exponents are not
claimed here. No source machine or execution semantics is imported.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff

open Finset

/-- Every threshold admits a fully fixed box with no P0 coordinates, even at depth zero. -/
theorem card_boxes_pos (L m t : ℕ) : 0 < (boxes L m t).card := by
  refine Finset.card_pos.mpr ⟨Cube.ofLeaf (fun _ => Term.P 0 0), mem_boxes.mpr ?_⟩
  simp [IsBox, Cube.P0Levels_ofLeaf, P0Levels]

/-- The ratio envelope `9m/(L-m+1)`, with subtraction in the real numbers. -/
@[expose] noncomputable def rho (L m : ℕ) : ℝ := 9 * (m : ℝ) / ((L : ℝ) - m + 1)

/-- The decay rate is nonnegative whenever the total depth contains the inner depth. -/
theorem rho_nonneg {L m : ℕ} (hm : m ≤ L) : 0 ≤ rho L m := by
  exact div_nonneg (by positivity) (by linarith [show (m : ℝ) ≤ L by exact_mod_cast hm])

/-- The source's depth condition makes the geometric tail summable, including `m = 0`. -/
theorem rho_lt_one {L m : ℕ} (hL : 10 * m ≤ L) : rho L m < 1 := by
  have hL' : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  rw [rho, div_lt_one (by linarith [Nat.cast_nonneg (α := ℝ) m])]
  linarith [Nat.cast_nonneg (α := ℝ) m]

private theorem beta_step {L m d : ℕ} (hm : m ≤ L) (hd : d + 1 ≤ m) :
    (beta L m (d + 1) : ℝ) ≤ rho L m * (beta L m d : ℝ) := by
  have hm' : (m : ℝ) ≤ L := by exact_mod_cast hm
  have hd' : (d : ℝ) + 1 ≤ m := by exact_mod_cast hd
  have hb : (0 : ℝ) < beta L m d := by exact_mod_cast beta_pos hm d
  have hratio := congrArg (Rat.cast : ℚ → ℝ) (beta_ratio hm (d + 1) (by omega) hd)
  push_cast at hratio
  rw [← div_le_iff₀ hb, hratio]
  exact div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)

/-- Equation (7): the order-`d` completed-leaf count decays from the order-zero count `M`.
The inequality holds for every `m ≤ L`; summability is needed only for the tail theorem. -/
theorem beta_le {L m : ℕ} (hm : m ≤ L) (d : ℕ) (hd : d ≤ m) :
    (beta L m d : ℝ) ≤ rho L m ^ d * (M L m : ℝ) := by
  induction d with
  | zero => simp [beta_zero_eq_M]
  | succ d ih =>
    calc (beta L m (d + 1) : ℝ) ≤ rho L m * (beta L m d : ℝ) := beta_step hm hd
      _ ≤ rho L m * (rho L m ^ d * (M L m : ℝ)) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (rho_nonneg hm)
      _ = rho L m ^ (d + 1) * (M L m : ℝ) := by ring

/-- Theorem 30's retained-table estimate: all completed leaves through order `m`
above a threshold are bounded by a convergent geometric tail. No threshold premise
is required; an empty tail also satisfies this bound. -/
theorem sum_beta_le {L m : ℕ} (t : ℕ) (hL : 10 * m ≤ L) :
    ∑ d ∈ Icc t m, (beta L m d : ℝ) ≤
      (M L m : ℝ) * (rho L m ^ t / (1 - rho L m)) := by
  calc ∑ d ∈ Icc t m, (beta L m d : ℝ)
      ≤ ∑ d ∈ Icc t m, rho L m ^ d * (M L m : ℝ) :=
        sum_le_sum fun d hd => beta_le (by omega) d (mem_Icc.mp hd).2
    _ = (M L m : ℝ) * ∑ d ∈ Ico t (m + 1), rho L m ^ d := by
      rw [← sum_mul, mul_comm, Ico_add_one_right_eq_Icc]
    _ ≤ (M L m : ℝ) * (rho L m ^ t / (1 - rho L m)) :=
      mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (rho_nonneg (by omega)) (rho_lt_one hL))
        (Nat.cast_nonneg _)

/-- A box table has at most `m+1` descriptors for each completed-leaf choice. Combined
with the geometric tail, this bounds its actual finite number of retained values. -/
theorem card_boxes_le_geometric {L m t : ℕ} (hL : 10 * m ≤ L) (ht : t ≤ m) :
    ((boxes L m t).card : ℝ) ≤
      ((m : ℝ) + 1) * ((M L m : ℝ) * (rho L m ^ t / (1 - rho L m))) := by
  have hc : ((boxes L m t).card : ℝ) ≤
      ((m : ℝ) + 1) * ∑ d ∈ Icc t m, (beta L m d : ℝ) := by
    exact_mod_cast card_boxes_le L m t (by omega) ht
  exact hc.trans (mul_le_mul_of_nonneg_left (sum_beta_le t hL) (by positivity))

/-- All tiles share the same geometry but each computes its own retained values.
This counts all those values against the actual padded outer dimension. -/
theorem total_boxes_le {L m t N : ℕ} (hL : 10 * m ≤ L) (ht : t ≤ m) :
    ((tiles L m N).card : ℝ) * ((boxes L m t).card : ℝ) ≤
      4 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (padN L m N : ℝ) ^ 2 := by
  have htiles : ((tiles L m N).card : ℝ) * (M L m : ℝ) ≤ 4 * (padN L m N : ℝ) ^ 2 := by
    exact_mod_cast card_tiles_mul_M_le L m N
  have hdecay : 0 ≤ rho L m ^ t / (1 - rho L m) :=
    div_nonneg (pow_nonneg (rho_nonneg (by omega)) _) (by linarith [rho_lt_one hL])
  calc ((tiles L m N).card : ℝ) * ((boxes L m t).card : ℝ)
      ≤ ((tiles L m N).card : ℝ) *
          (((m : ℝ) + 1) * ((M L m : ℝ) * (rho L m ^ t / (1 - rho L m)))) :=
        mul_le_mul_of_nonneg_left (card_boxes_le_geometric hL ht) (Nat.cast_nonneg _)
    _ = (((tiles L m N).card : ℝ) * (M L m : ℝ)) *
        (((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m))) := by ring
    _ ≤ (4 * (padN L m N : ℝ) ^ 2) *
        (((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m))) :=
      mul_le_mul_of_nonneg_right htiles (mul_nonneg (by positivity) hdecay)
    _ = _ := by ring

/-- If one band fits the original outer dimension, the retained-table count is bounded
by `N²` without using a source execution or asymptotic hypothesis. -/
theorem total_boxes_le_unpadded {L m t N : ℕ} (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : K0 L m * N0 L m ≤ N) :
    ((tiles L m N).card : ℝ) * ((boxes L m t).card : ℝ) ≤
      16 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2 := by
  have hpad : (padN L m N : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast padN_le_two_mul L m N hN
  have hdecay : 0 ≤ rho L m ^ t / (1 - rho L m) :=
    div_nonneg (pow_nonneg (rho_nonneg (by omega)) _) (by linarith [rho_lt_one hL])
  refine (total_boxes_le hL ht).trans ?_
  calc 4 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (padN L m N : ℝ) ^ 2
      ≤ 4 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (2 * (N : ℝ)) ^ 2 := by gcongr
    _ = 16 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2 := by ring

/-- Weighted binomial-prefix estimate from Section 4.4. With `x=8`, this gives
`Σ(d≤t) alpha(m,d) ≤ 72^t*(9/8)^m`; every wanted occurrence incurs this count. -/
theorem sum_alpha_le {x : ℝ} (hx : 0 < x) (h9x : 1 ≤ 9 * x) {m t : ℕ} (ht : t ≤ m) :
    ∑ d ∈ range (t + 1), (alpha m d : ℝ) ≤ (9 * x) ^ t * (1 + 1 / x) ^ m := by
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ ∑ d ∈ range (t + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum fun d hd => by
          have hα : (alpha m d : ℝ) =
              (9 * x) ^ d * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
            rw [alpha, one_pow, mul_one, ← mul_assoc, ← mul_pow,
              show 9 * x * (1 / x) = 9 by field_simp]
            push_cast
            ring
          rw [hα]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ h9x (Nat.lt_succ_iff.mp (mem_range.mp hd))) (by positivity)
    _ ≤ ∑ d ∈ range (m + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun _ _ _ => by positivity
    _ = (9 * x) ^ t * (1 + 1 / x) ^ m := by rw [← mul_sum, ← add_pow, add_comm]

/-- The Section 4.4 query-count estimate at the concrete rational weight `x=8`. -/
theorem sum_alpha_le_seventytwo {m t : ℕ} (ht : t ≤ m) :
    ∑ d ∈ range (t + 1), (alpha m d : ℝ) ≤ (72 : ℝ) ^ t * (9 / 8 : ℝ) ^ m := by
  exact (sum_alpha_le (x := 8) (by norm_num) (by norm_num) ht).trans_eq (by norm_num)

/-- At the source's `L=21m`, the ratio is strictly below `9/20` and its tail factor below `2`. -/
theorem rho_twentyone (m : ℕ) :
    rho (21 * m) m < 9 / 20 ∧ 1 / (1 - rho (21 * m) m) < 2 := by
  have hlt : rho (21 * m) m < 9 / 20 := by
    rw [rho, Nat.cast_mul, Nat.cast_ofNat,
      show (21 : ℝ) * m - m + 1 = 20 * m + 1 by ring,
      div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  exact ⟨hlt, (div_lt_iff₀ (by linarith)).mpr (by linarith)⟩

/-- Concrete rational-base preprocessing decay at `L=21m`. The threshold remains
explicit so an actual native parameter calculation can choose it independently. -/
theorem sum_beta_twentyone (m t : ℕ) :
    ∑ d ∈ Icc t m, (beta (21 * m) m d : ℝ) ≤
      2 * (M (21 * m) m : ℝ) * (9 / 20 : ℝ) ^ t := by
  obtain ⟨hrho, hfactor⟩ := rho_twentyone m
  refine (sum_beta_le t (by omega)).trans ?_
  rw [div_eq_mul_one_div, show 2 * (M (21 * m) m : ℝ) * (9 / 20 : ℝ) ^ t =
    (M (21 * m) m : ℝ) * ((9 / 20 : ℝ) ^ t * 2) by ring]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (pow_le_pow_left₀ (rho_nonneg (by omega)) hrho.le _) hfactor.le
      (one_div_nonneg.mpr (by linarith)) (by positivity))
    (Nat.cast_nonneg _)

end Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff
