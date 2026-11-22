/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily.Polynomial
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.IID.FunctionCollision
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Sqrt

/-!
# Birthday collisions in the two-block polynomial hash

Even with the key fixed, the probability of a collision between distinct messages is bounded
away from zero at the birthday scale. The proof uses the birthday lower bound for any function
on uniform samples, subtracting the chance of sampling the same message twice.

## Main results

* `Cslib.Probability.one_eighth_le_polyHash_twoBlock_collision`: the lower bound with exactly
  `⌊√|F|⌋` independent uniform two-block messages.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 7.26(a), printed p. 284.
-/

public section

namespace Cslib.Probability

/-- **Boneh–Shoup Exercise 7.26(a).** For any fixed key `k`, exactly `⌊√|F|⌋` independent
uniform two-block messages contain two distinct messages with equal `Hpoly` digest with
probability at least `1/8` once `|F| ≥ 16`. This applies to finite semirings, including the
book's prime field `ZMod p`. -/
theorem one_eighth_le_polyHash_twoBlock_collision {F : Type} [Semiring F] [Fintype F]
    (k : F) (hcard : 16 ≤ Fintype.card F) :
    (1 / 8 : ℝ) ≤
      ((PMF.iid (PMF.uniformOfFintype (F × F)) (Nat.sqrt (Fintype.card F))).toOuterMeasure
        {ms | ∃ i j, polyHash k [(ms i).1, (ms i).2] = polyHash k [(ms j).1, (ms j).2] ∧
          ms i ≠ ms j}).toReal := by
  classical
  let N := Fintype.card F
  let s := Nat.sqrt N
  refine le_trans ?_ (PMF.one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision
    (fun m : F × F => polyHash k [m.1, m.2]) Finset.univ (fun _ => Finset.mem_univ _) s)
  rw [Finset.card_univ, Fintype.card_prod]
  change (1 / 8 : ℝ) ≤
    1 - Real.exp (-(s * (s - 1) / (2 * N))) - s.choose 2 * ((N * N : ℕ) : ℝ)⁻¹
  have hs : 4 ≤ s := Nat.le_sqrt'.mpr hcard
  have hs' : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hN : (16 : ℝ) ≤ N := by exact_mod_cast hcard
  have hNpos : (0 : ℝ) < N := by linarith
  have hslo : (s : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hshi : (N : ℝ) < (s + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' N
  have hexponent : (1 / 5 : ℝ) ≤ s * (s - 1) / (2 * N) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((s : ℝ) - 4)]
  have hexp : Real.exp (-(s * (s - 1) / (2 * N))) ≤ (5 / 6 : ℝ) := by
    calc
      _ ≤ Real.exp (-(1 / 5 : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hexponent)
      _ ≤ 5 / 6 := by
        rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
        linarith [Real.add_one_le_exp (1 / 5 : ℝ)]
  have hrepeat : (s.choose 2 : ℝ) * ((N * N : ℕ) : ℝ)⁻¹ ≤ 1 / 32 := by
    rw [Nat.cast_mul, Nat.cast_choose_two, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hNpos.le]
  linarith

end Cslib.Probability
