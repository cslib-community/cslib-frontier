/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BinPacking.Harmonic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Harmonic_k as `k` grows: `T∞ ≤ T_k ≤ T∞ + 1 / (k * (k - 1))`

Lee and Lee's constant `T_k` (`harmonicRatio k`) bounds the asymptotic competitive ratio of
Harmonic_k (`length_run_harmonicPacker_le`). As `k` grows it tends to
`T∞ = ∑ 1 / (t_j - 1) = 1 + 1/2 + 1/6 + 1/42 + ⋯ ≈ 1.69103` over Sylvester's numbers `t_j`
(`harmonicLimit`), the constant of [Lee and Lee][LeeLee1985]:
`T∞ ≤ T_k ≤ T∞ + 1 / (k * (k - 1))` (`harmonicLimit_le_harmonicRatio`,
`harmonicRatio_le_harmonicLimit_add`). With `m` the least index with `k ≤ t_m - 1`, `T_k` and
`T∞` share the terms before `m`, and the last term of `T_k` is
`k / ((k - 1) * (t_m - 1)) = 1 / (t_m - 1) + 1 / ((k - 1) * (t_m - 1))`, while the rest of `T∞` is
`1 / (t_m - 1) + 1 / (t_{m+1} - 1) + ⋯`. So Harmonic_k uses at most
`(T∞ + 1 / (k * (k - 1))) * OPT + k` bins (`length_run_harmonicPacker_le_harmonicLimit`).

Bounding the rest of the series by `∑_{i ≥ j} 1 / (t_i - 1) ≤ 2 / (t_j - 1)` gives
`1.69102 < T∞ < 1.69104` (`harmonicLimit_mem_Ioo`).

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.harmonicLimit`: Lee and Lee's constant `T∞`.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.harmonicLimit_mem_Ioo`: `1.69102 < T∞ < 1.69104`.
* `Cslib.Algorithms.Lean.BinPacking.harmonicLimit_le_harmonicRatio`: `T∞ ≤ T_k`.
* `Cslib.Algorithms.Lean.BinPacking.harmonicRatio_le_harmonicLimit_add`:
  `T_k ≤ T∞ + 1 / (k * (k - 1))`.
* `Cslib.Algorithms.Lean.BinPacking.length_run_harmonicPacker_le_harmonicLimit`: Harmonic_k uses
  at most `(T∞ + 1 / (k * (k - 1))) * OPT + k` bins.

## References

* [C. C. Lee, D. T. Lee, *A simple on-line bin-packing algorithm*][LeeLee1985]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

/-- **Lee and Lee's constant** `T∞ = ∑ 1 / (t_j - 1) = 1 + 1/2 + 1/6 + 1/42 + ⋯ ≈ 1.69103` over
Sylvester's numbers `t_j`. -/
noncomputable def harmonicLimit : ℝ := ∑' j, 1 / ((sylvester j : ℝ) - 1)

private theorem two_pow_le_sylvester_sub_one : ∀ j, 2 ^ j ≤ sylvester j - 1
  | 0 => le_rfl
  | j + 1 => by
    have h1 := two_pow_le_sylvester_sub_one j
    have h2 := two_le_sylvester j
    rw [sylvester_succ_sub_one, pow_succ]
    exact Nat.mul_le_mul h1 (by omega)

private theorem cast_sylvester_sub_one (j : ℕ) :
    ((sylvester j : ℝ) - 1) = ((sylvester j - 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub (by have := two_le_sylvester j; omega), Nat.cast_one]

/-- The tail `∑_{i ≥ j} 1 / (t_i - 1)`. -/
private noncomputable def tail (j : ℕ) : ℝ := ∑' i, 1 / ((sylvester (i + j) : ℝ) - 1)

private theorem summable_tail (j : ℕ) : Summable fun i => 1 / ((sylvester (i + j) : ℝ) - 1) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) summable_geometric_two
  · rw [cast_sylvester_sub_one]
    positivity
  · rw [cast_sylvester_sub_one, div_pow, one_pow]
    have h := (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right i j)).trans
      (two_pow_le_sylvester_sub_one (i + j))
    have h' : ((2 : ℝ) ^ i) ≤ ((sylvester (i + j) - 1 : ℕ) : ℝ) := by exact_mod_cast h
    exact one_div_le_one_div_of_le (by positivity) h'

private theorem tail_eq (j : ℕ) : tail j = 1 / ((sylvester j : ℝ) - 1) + tail (j + 1) := by
  rw [tail, (summable_tail j).tsum_eq_zero_add, tail, Nat.zero_add]
  simp only [Nat.add_right_comm _ 1 j, Nat.add_assoc]

private theorem tail_nonneg (j : ℕ) : 0 ≤ tail j :=
  tsum_nonneg fun i => by rw [cast_sylvester_sub_one]; positivity

private theorem two_pow_mul_le (j : ℕ) :
    ∀ i, 2 ^ i * (sylvester j - 1) ≤ sylvester (i + j) - 1
  | 0 => by simp
  | i + 1 => by
    have ih := two_pow_mul_le j i
    have h2 := two_le_sylvester (i + j)
    rw [Nat.add_right_comm, sylvester_succ_sub_one, pow_succ, Nat.mul_right_comm]
    exact Nat.mul_le_mul ih (by omega)

/-- The tail from `t_j` is at most `2 / (t_j - 1)`. -/
private theorem tail_le (j : ℕ) : tail j ≤ 2 / ((sylvester j : ℝ) - 1) := by
  have hu : (0 : ℝ) < ((sylvester j - 1 : ℕ) : ℝ) := by
    have := two_le_sylvester j
    exact_mod_cast (show 0 < sylvester j - 1 by omega)
  have hle : ∀ i, 1 / ((sylvester (i + j) : ℝ) - 1) ≤
      ((1 : ℝ) / 2) ^ i * (1 / ((sylvester j - 1 : ℕ) : ℝ)) := fun i => by
    have h := two_pow_mul_le j i
    have h' : (2 : ℝ) ^ i * ((sylvester j - 1 : ℕ) : ℝ) ≤ ((sylvester (i + j) - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [cast_sylvester_sub_one, div_pow, one_pow, div_mul_div_comm, one_mul]
    exact one_div_le_one_div_of_le (by positivity) h'
  calc tail j ≤ ∑' i, ((1 : ℝ) / 2) ^ i * (1 / ((sylvester j - 1 : ℕ) : ℝ)) :=
        (summable_tail j).tsum_le_tsum hle (summable_geometric_two.mul_right _)
    _ = 2 / ((sylvester j : ℝ) - 1) := by
        rw [tsum_mul_right, tsum_geometric_two, cast_sylvester_sub_one, mul_one_div]

/-- **`T∞ ≈ 1.69103`**: `1.69102 < T∞ < 1.69104`, from the first five terms
`1 + 1/2 + 1/6 + 1/42 + 1/1806` and the tail bound `∑_{i ≥ j} 1 / (t_i - 1) ≤ 2 / (t_j - 1)`. -/
theorem harmonicLimit_mem_Ioo : harmonicLimit ∈ Set.Ioo (1.69102 : ℝ) 1.69104 := by
  have h : harmonicLimit = tail 0 := by simp [harmonicLimit, tail]
  have h5 := tail_le 5
  have h0 := tail_nonneg 5
  rw [h, tail_eq 0, tail_eq 1, tail_eq 2, tail_eq 3, tail_eq 4]
  simp only [sylvester, Nat.cast_ofNat] at h5 ⊢
  norm_num at h5 ⊢
  constructor <;> linarith

variable {k : ℕ}

private theorem harmonicTail_le (hk : 2 ≤ k) : ∀ (n j : ℕ), k ≤ sylvester j - 1 + n →
    (harmonicTail k n j : ℝ) ≤ tail j + 1 / (k * (k - 1))
  | n, j, hn => by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hu1 : 1 ≤ sylvester j - 1 := by have := two_le_sylvester j; omega
    have htail := tail_eq j
    have hnn := tail_nonneg (j + 1)
    rw [cast_sylvester_sub_one] at htail
    by_cases hku : k ≤ sylvester j - 1
    · -- `harmonicTail` is `k / ((k - 1) * u) = 1 / u + 1 / ((k - 1) * u)`
      have hval : harmonicTail k n j = k / ((k - 1) * ((sylvester j - 1 : ℕ) : ℚ)) := by
        cases n with
        | zero => rfl
        | succ n => rw [harmonicTail, ite_eq_left hku]
      rw [hval, htail]
      generalize sylvester j - 1 = U at hku hu1 ⊢
      have hU : (1 : ℝ) ≤ U := by exact_mod_cast hu1
      have hkU : (k : ℝ) ≤ U := by exact_mod_cast hku
      have hk1 : (k : ℝ) - 1 ≠ 0 := by intro h; linarith
      have e : (k : ℝ) / ((k - 1) * U) = 1 / U + 1 / ((k - 1) * U) := by
        field_simp
        ring
      have h2 : 1 / (((k : ℝ) - 1) * U) ≤ 1 / (k * (k - 1)) := by
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      push_cast
      linarith
    · push Not at hku
      match n, hn with
      | 0, hn => omega
      | n + 1, hn =>
        have ih := harmonicTail_le hk n (j + 1) (by
          rw [sylvester_succ_sub_one]; nlinarith)
        rw [harmonicTail, ite_eq_right (by omega)]
        push_cast
        linarith

private theorem tail_le_harmonicTail (hk : 2 ≤ k) : ∀ (n j : ℕ), k ≤ sylvester j - 1 + n →
    tail j ≤ (harmonicTail k n j : ℝ)
  | n, j, hn => by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    by_cases hku : k ≤ sylvester j - 1
    · -- `T∞`'s tail from `t_j` is at most `1 / u + 1 / (u * (u + 1)) + 2 / (t_{j+2} - 1)`
      have hval : harmonicTail k n j = k / ((k - 1) * ((sylvester j - 1 : ℕ) : ℚ)) := by
        cases n with
        | zero => rfl
        | succ n => rw [harmonicTail, ite_eq_left hku]
      have h2 := tail_le (j + 1 + 1)
      rw [hval, tail_eq j, tail_eq (j + 1)]
      simp only [cast_sylvester_sub_one] at h2 ⊢
      rw [sylvester_succ_sub_one (j + 1), sylvester_succ_sub_one j] at h2
      rw [sylvester_succ_sub_one j]
      generalize sylvester j - 1 = U at hku h2 ⊢
      have hkU : (k : ℝ) ≤ U := by exact_mod_cast hku
      push_cast at h2 ⊢
      have hk1 : (k : ℝ) - 1 ≠ 0 := by intro h; linarith
      have hU1 : (0 : ℝ) < U - 1 := by linarith
      have hP : (0 : ℝ) < U * (U + 1) := by nlinarith
      have e1 : (k : ℝ) / ((k - 1) * U) = 1 / U + 1 / ((k - 1) * U) := by
        field_simp
        ring
      have e2 : 1 / ((U : ℝ) * (U + 1)) + 2 / ((U - 1) * U * (U + 1)) = 1 / ((U - 1) * U) := by
        field_simp
        ring
      have i1 : 1 / (((U : ℝ) - 1) * U) ≤ 1 / ((k - 1) * U) :=
        one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
      have i2 : 2 / ((U : ℝ) * (U + 1) * (U * (U + 1) + 1)) ≤ 2 / ((U - 1) * U * (U + 1)) := by
        refine div_le_div_of_nonneg_left (by norm_num)
          (mul_pos (mul_pos hU1 (by linarith)) (by linarith)) ?_
        calc ((U : ℝ) - 1) * U * (U + 1) = (U - 1) * (U * (U + 1)) := by ring
          _ ≤ (U * (U + 1) + 1) * (U * (U + 1)) :=
            mul_le_mul_of_nonneg_right (by nlinarith) hP.le
          _ = U * (U + 1) * (U * (U + 1) + 1) := by ring
      linarith
    · push Not at hku
      match n, hn with
      | 0, hn => omega
      | n + 1, hn =>
        have hu1 : 1 ≤ sylvester j - 1 := by have := two_le_sylvester j; omega
        have ih := tail_le_harmonicTail hk n (j + 1) (by
          rw [sylvester_succ_sub_one]; nlinarith)
        rw [harmonicTail, ite_eq_right (by omega), tail_eq j, cast_sylvester_sub_one]
        push_cast
        linarith

/-- **`T∞ ≤ T_k`**: Lee and Lee's constant `T_k` is at least `T∞`, so together with
`harmonicRatio_le_harmonicLimit_add` it tends to `T∞` as `k` grows. -/
theorem harmonicLimit_le_harmonicRatio (hk : 2 ≤ k) : harmonicLimit ≤ (harmonicRatio k : ℝ) := by
  have h := tail_le_harmonicTail hk k 0 (by simp [sylvester])
  simpa [harmonicRatio, tail, harmonicLimit] using h

/-- **`T_k ≤ T∞ + 1 / (k * (k - 1))`**: Lee and Lee's constant `T_k` exceeds `T∞` by at most
`1 / (k * (k - 1))`. -/
theorem harmonicRatio_le_harmonicLimit_add (hk : 2 ≤ k) :
    (harmonicRatio k : ℝ) ≤ harmonicLimit + 1 / (k * (k - 1)) := by
  have h := harmonicTail_le hk k 0 (by simp [sylvester])
  simpa [harmonicRatio, tail, harmonicLimit] using h

/-- **Harmonic_k uses at most `(T∞ + 1 / (k * (k - 1))) * OPT + k` bins**: against every packing
`Q` of the same items, in particular an optimal one. So the asymptotic competitive ratio of
Harmonic_k tends to at most `T∞ ≈ 1.69103` as `k` grows. -/
theorem length_run_harmonicPacker_le_harmonicLimit (hk : 2 ≤ k) {C : ℕ} {l : List ℕ}
    {Q : List (List ℕ)} (hQ : IsPacking C l Q) :
    (((harmonicPacker k C).run l).length : ℝ) ≤
      (harmonicLimit + 1 / (k * (k - 1))) * Q.length + k := by
  have h1 : (((harmonicPacker k C).run l).length : ℝ) ≤ (harmonicRatio k : ℝ) * Q.length + k := by
    exact_mod_cast length_run_harmonicPacker_le hk hQ
  have h2 := harmonicRatio_le_harmonicLimit_add hk
  have h3 : (0 : ℝ) ≤ Q.length := Nat.cast_nonneg _
  nlinarith

end Cslib.Algorithms.Lean.BinPacking
