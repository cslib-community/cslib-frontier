/-
Copyright (c) 2026 Samuel Schlesinger, Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI, Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real bounds for partial binomial sums

The binomial generating function gives `∑ j ≤ e, q.choose j ≤ exp (q / T) * T ^ e`
for any real `T ≥ 1`. For `0 < e ≤ q`, choosing `T = q / e` gives `(exp 1 * q / e) ^ e`.
This bound remains valid above half the dimension. At radius zero the sum and bound are both one.

The generating-function proof is shared with the sparsification lemma. The logarithmic
consequences turn an exponential lower bound on the square of a partial binomial sum into
size-activity bounds; they include the zero-radius case using the usual total real operations.

An exact integer logarithm test also bounds the tail of dimension `C * N` and radius
`Γ * N / M` by `2 ^ (N / B)` for every `N`. This is an original specialization of the
generating-function bound, motivated by the geometric thresholds in Appendix A.3 of
[OpenAI2026ETH]; it does not construct the parameters or bound the cost of selecting them.

## Main results

* `Cslib.sum_choose_le_exp_mul_pow`: a real-parameter generating-function bound.
* `Cslib.sum_choose_le_exp_one_mul_div_pow`: the bound with parameter `q / e`.
* `Nat.choose_le_exp_mul_div_pow`: its single-binomial-coefficient consequence, for all `n, k`.
* `Cslib.sum_choose_le_two_rpow_div`: the geometric tail under an exact integer budget test.
* `Cslib.sum_choose_le_two_pow_div_add_one`: its natural-number rounded form.
* `Cslib.le_mul_logb_of_two_pow_le_sum_choose_sq`: the logarithmic consequence.
* `Cslib.mul_rpow_le_of_two_pow_le_sum_choose_sq`: the rearranged size lower bound.
* `Cslib.div_pow_le_choose`, `Cslib.mul_logb_div_le_logb_choose`,
  `Cslib.logb_choose_le_mul_logb_exp_mul_div`, `Cslib.logb_add_choose_le`,
  `Cslib.logb_choose_sub_logb_choose_sub_le`,
  `Cslib.logb_choose_sub_logb_sub_three_mul_choose_sub_le`: power and base-2 logarithm bounds for
  individual binomial coefficients and binomial differences.
* `Cslib.log_add_choose_le_two_mul_sqrt`: `log C(m + n, n) ≤ 2 √(m n)` in natural logarithms, a
  step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026], tracked in #8325 (the paper's
  Fact 2.1, §2, p. 11).
* `Real.exists_one_le_and_mul_pow_le_pow`: a polynomial is eventually below an exponential with base
  `r > 1`.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2]
  [ThresholdCircuitRepresentations2026]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.3, pp. 46–47][OpenAI2026ETH]
* [S. Khanna, A. Putterman, J. Song, *A Deterministic Linear Time Algorithm for Minimum Spanning
  Tree*, Fact 2.1][KhannaPuttermanSong2026]
-/

public section

namespace Cslib

open Finset

/-- A partial binomial sum is at most `exp (q / T) * T ^ e` for every real `T ≥ 1`.
The radius `e` may exceed `q`. -/
theorem sum_choose_le_exp_mul_pow (q e : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ Real.exp (q / T) * T ^ e := by
  have hT0 : 0 < T := by linarith
  set t : ℝ := 1 / T with ht
  have ht0 : 0 ≤ t := by positivity
  have hg : ∀ j, 0 ≤ (q.choose j : ℝ) * t ^ j := fun j => by positivity
  have hpartial : ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j ≤ (1 + t) ^ q := by
    set m := max (e + 1) (q + 1)
    calc ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j
        ≤ ∑ j ∈ range m, (q.choose j : ℝ) * t ^ j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (le_max_left _ _))
            fun j _ _ => hg j
      _ = ∑ j ∈ range (q + 1), (q.choose j : ℝ) * t ^ j := by
          refine (sum_subset (range_subset_range.mpr (le_max_right _ _)) fun j _ hj => ?_).symm
          rw [Nat.choose_eq_zero_of_lt (by simpa using hj), Nat.cast_zero, zero_mul]
      _ = (1 + t) ^ q := by
          rw [add_comm (1 : ℝ) t, add_pow]
          refine sum_congr rfl fun j _ => ?_
          rw [one_pow, mul_one, mul_comm]
  calc (∑ j ∈ range (e + 1), (q.choose j : ℝ))
      ≤ ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j * T ^ e := by
        refine sum_le_sum fun j hj => ?_
        have hje : j ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have : 1 ≤ t ^ j * T ^ e := by
          rw [← Nat.add_sub_cancel' hje, pow_add, ← mul_assoc, ht, ← mul_pow, one_div,
            inv_mul_cancel₀ hT0.ne', one_pow, one_mul]
          exact one_le_pow₀ hT
        calc (q.choose j : ℝ) = (q.choose j : ℝ) * 1 := (mul_one _).symm
          _ ≤ (q.choose j : ℝ) * (t ^ j * T ^ e) := by gcongr
          _ = (q.choose j : ℝ) * t ^ j * T ^ e := by ring
    _ = (∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j) * T ^ e := by rw [sum_mul]
    _ ≤ (1 + t) ^ q * T ^ e := by gcongr
    _ ≤ Real.exp t ^ q * T ^ e := by
        gcongr
        linarith [Real.add_one_le_exp t]
    _ = Real.exp (q / T) * T ^ e := by
        rw [← Real.exp_nat_mul, ht]
        ring_nf

/-- The standard bound `(exp 1 * q / e) ^ e` holds throughout `e ≤ q`, not just for
`e ≤ q / 2`. At `e = 0` both sides are one. -/
theorem sum_choose_le_exp_one_mul_div_pow {q e : ℕ} (heq : e ≤ q) :
    (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ (Real.exp 1 * q / e) ^ e := by
  by_cases he : e = 0
  · simp [he]
  have he0 : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le he0 (by exact_mod_cast heq)
  have hT : (1 : ℝ) ≤ q / e :=
    (le_div_iff₀ he0).mpr (by simpa only [one_mul] using (Nat.cast_le.mpr heq : (e : ℝ) ≤ q))
  have hqe : (q : ℝ) / (q / e) = e := by field_simp
  calc (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ Real.exp e * ((q : ℝ) / e) ^ e := by
        simpa only [hqe] using sum_choose_le_exp_mul_pow q e ((q : ℝ) / e) hT
    _ = (Real.exp 1 * q / e) ^ e := by
        rw [mul_div_assoc, mul_pow, ← Real.exp_nat_mul]
        simp

end Cslib

namespace Nat

/-- A single binomial coefficient is at most `(exp 1 * n / k)^k`, including `k = 0`.
This follows from `Cslib.sum_choose_le_exp_one_mul_div_pow` when `k ≤ n`; otherwise the
coefficient vanishes. The statement is also present in
[Anthropic's formal source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Choose.lean#L52-L53);
this proof reuses the partial-sum bound. -/
theorem choose_le_exp_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  by_cases hkn : k ≤ n
  · calc
      (n.choose k : ℝ) ≤ ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) :=
        Finset.single_le_sum (fun j _ => Nat.cast_nonneg (n.choose j))
          (Finset.mem_range.mpr (by omega))
      _ ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k :=
        Cslib.sum_choose_le_exp_one_mul_div_pow hkn
  · rw [choose_eq_zero_of_lt (by omega), cast_zero]
    positivity

end Nat

namespace Cslib

open Finset

/-- For any input size `N`, the tail with dimension `C * N` and radius `Γ * N / M` is at most
`2 ^ (N / B)` when the exact integer test `B * Γ * ⌈log₂ (4 * C * M)⌉ ≤ M` holds.
This is an original corollary of `sum_choose_le_exp_mul_pow`, motivated by Appendix A.3 of
[OpenAI2026ETH], rather than a verbatim result from that source. Zero input and zero radius are
included. The parameters are supplied; no parameter-selection or complexity bound is asserted. -/
theorem sum_choose_le_two_rpow_div {C Γ M B : ℕ} (hC : 4 ≤ C) (hΓ : 4 ≤ Γ)
    (hM : Γ ≤ M) (hB : 1 ≤ B) (hbudget : B * Γ * Nat.clog 2 (4 * C * M) ≤ M)
    (N : ℕ) :
    (∑ j ∈ range (Γ * N / M + 1), ((C * N).choose j : ℝ)) ≤ (2 : ℝ) ^ ((N : ℝ) / B) := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hΓ0 : (0 : ℝ) < Γ := by exact_mod_cast (show 0 < Γ by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  let T : ℝ := C * M / Γ
  let a : ℝ := Γ * N / M
  let h := Nat.clog 2 (4 * C * M)
  have hT : 1 ≤ T := by
    apply (le_div_iff₀ hΓ0).mpr
    have hCM : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
    have hΓM : (Γ : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hradius : ((Γ * N / M : ℕ) : ℝ) ≤ a := by
    apply (le_div_iff₀ hM0).mpr
    exact_mod_cast Nat.div_mul_le_self (Γ * N) M
  have hratio : ((C * N : ℕ) : ℝ) / T = a := by
    dsimp only [T, a]
    push_cast
    field_simp
  have hexp : Real.exp 1 ≤ (Γ : ℝ) :=
    Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ Γ by omega))
  have hbase : Real.exp 1 * T ≤ (4 * C * M : ℕ) := by
    calc Real.exp 1 * T ≤ Γ * T := mul_le_mul_of_nonneg_right hexp hT0.le
      _ = C * M := by dsimp only [T]; field_simp
      _ ≤ (4 * C * M : ℕ) := by push_cast; nlinarith
  have hpow : ((4 * C * M : ℕ) : ℝ) ≤ (2 : ℝ) ^ h := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (4 * C * M)
  have hexponent : (h : ℝ) * a ≤ (N : ℝ) / B := by
    have hb : (B : ℝ) * Γ * h ≤ M := by exact_mod_cast hbudget
    dsimp only [a]
    rw [← mul_div_assoc, div_le_div_iff₀ hM0 hB0]
    nlinarith [mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)]
  calc (∑ j ∈ range (Γ * N / M + 1), ((C * N).choose j : ℝ))
      ≤ Real.exp (((C * N : ℕ) : ℝ) / T) * T ^ (Γ * N / M) :=
        sum_choose_le_exp_mul_pow (C * N) (Γ * N / M) T hT
    _ = Real.exp a * T ^ (Γ * N / M) := by rw [hratio]
    _ ≤ Real.exp a * T ^ a := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos a).le
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hT hradius
    _ = (Real.exp 1 * T) ^ a := by
      rw [Real.mul_rpow (Real.exp_pos 1).le hT0.le, ← Real.exp_mul, one_mul]
    _ ≤ ((4 * C * M : ℕ) : ℝ) ^ a :=
      Real.rpow_le_rpow (by positivity) hbase ha
    _ ≤ ((2 : ℝ) ^ h) ^ a := Real.rpow_le_rpow (by positivity) hpow ha
    _ = (2 : ℝ) ^ ((h : ℝ) * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ (2 : ℝ) ^ ((N : ℝ) / B) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- The natural-number rounding of `sum_choose_le_two_rpow_div`, suitable for a discrete
leaf-count or round budget. The division in the conclusion is natural-number division. -/
theorem sum_choose_le_two_pow_div_add_one {C Γ M B : ℕ} (hC : 4 ≤ C) (hΓ : 4 ≤ Γ)
    (hM : Γ ≤ M) (hB : 1 ≤ B) (hbudget : B * Γ * Nat.clog 2 (4 * C * M) ≤ M)
    (N : ℕ) :
    ∑ j ∈ range (Γ * N / M + 1), (C * N).choose j ≤ 2 ^ (N / B + 1) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hround : (N : ℝ) / B ≤ ((N / B + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ hB0).mpr
    have hn : N < B * (N / B + 1) := by
      have := Nat.mod_lt N (show 0 < B by omega)
      have := Nat.div_add_mod N B
      nlinarith
    exact_mod_cast (show N ≤ (N / B + 1) * B by simpa only [Nat.mul_comm] using hn.le)
  have h := (sum_choose_le_two_rpow_div hC hΓ hM hB hbudget N).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hround)
  rw [Real.rpow_natCast] at h
  exact_mod_cast h

/-- If the square of the radius-`e` binomial sum is at least `2 ^ m`, then
`m / 2 ≤ e * log₂ (exp 1 * q / e)`. The statement includes `e = 0`, which forces `m = 0`. -/
theorem le_mul_logb_of_two_pow_le_sum_choose_sq {m q e : ℕ} (heq : e ≤ q)
    (h : 2 ^ m ≤ (∑ j ∈ range (e + 1), q.choose j) ^ 2) :
    (m : ℝ) / 2 ≤ e * Real.logb 2 (Real.exp 1 * q / e) := by
  have hreal : (2 : ℝ) ^ m ≤ (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ^ 2 := by
    exact_mod_cast h
  have hs : 0 ≤ ∑ j ∈ range (e + 1), (q.choose j : ℝ) := sum_nonneg fun _ _ => by positivity
  have hpow := hreal.trans (pow_le_pow_left₀ hs
    (sum_choose_le_exp_one_mul_div_pow heq) 2)
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by positivity : (0 : ℝ) < 2 ^ m) hpow
  rw [Real.logb_two_pow, Real.logb_pow, Real.logb_pow, Nat.cast_ofNat] at hlog
  linarith

/-- The logarithmic partial-binomial-sum bound rearranged as a lower bound on `q`.
At radius zero the lower bound is zero. -/
theorem mul_rpow_le_of_two_pow_le_sum_choose_sq {m q e : ℕ} (heq : e ≤ q)
    (h : 2 ^ m ≤ (∑ j ∈ range (e + 1), q.choose j) ^ 2) :
    e / Real.exp 1 * (2 : ℝ) ^ ((m : ℝ) / (2 * e)) ≤ q := by
  by_cases he : e = 0
  · simp [he]
  have he0 : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le he0 (by exact_mod_cast heq)
  have hlog := le_mul_logb_of_two_pow_le_sum_choose_sq heq h
  have hx : (m : ℝ) / (2 * e) ≤ Real.logb 2 (Real.exp 1 * q / e) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * e)).mpr
    linarith
  have hp := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).mp hx
  calc e / Real.exp 1 * (2 : ℝ) ^ ((m : ℝ) / (2 * e))
      ≤ e / Real.exp 1 * (Real.exp 1 * q / e) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = q := by field_simp

/-- Real-division form of `Nat.choose_mul_pow_le` at `a = k`: `((N : ℝ) / k) ^ k ≤ N.choose k`. -/
theorem div_pow_le_choose {N k : ℕ} (hk : k ≤ N) : ((N : ℝ) / (k : ℝ)) ^ k ≤ (N.choose k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp
  · rw [div_pow, div_le_iff₀ (pow_pos (by exact_mod_cast hpos) k)]
    exact_mod_cast (by simpa [Nat.choose_self] using Nat.choose_mul_pow_le hk k)

/-- Base-2 logarithmic form of `div_pow_le_choose` for `1 ≤ k ≤ N`. -/
theorem mul_logb_div_le_logb_choose {N k : ℕ} (hk₀ : 1 ≤ k) (hk : k ≤ N) :
    (k : ℝ) * Real.logb 2 ((N : ℝ) / (k : ℝ)) ≤ Real.logb 2 (N.choose k) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk₀
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hk_pos (by exact_mod_cast hk)
  simpa [Real.logb_pow] using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (div_pos hN_pos hk_pos) k) (div_pow_le_choose hk)

/-- Base-2 logarithmic form of `Nat.choose_le_exp_mul_div_pow` for `k ≤ N`. -/
theorem logb_choose_le_mul_logb_exp_mul_div {N k : ℕ} (hk : k ≤ N) :
    Real.logb 2 (N.choose k) ≤ (k : ℝ) * Real.logb 2 (Real.exp 1 * (N : ℝ) / (k : ℝ)) := by
  simpa [Real.logb_pow] using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast Nat.choose_pos hk) (Nat.choose_le_exp_mul_div_pow N k)

/-- Base-2 logarithm of `(n + m).choose m` for `1 ≤ m ≤ n` ([LiLiangYuZhou2023], Section 5.2,
p. 25 / PDF p. 26): `log₂ C(n + m, m) ≤ 3 * m + m * log₂ (n / m)`. -/
theorem logb_add_choose_le {n m : ℕ} (hm₀ : 1 ≤ m) (hmn : m ≤ n) :
    Real.logb 2 ((n + m).choose m) ≤ 3 * (m : ℝ) + (m : ℝ) * Real.logb 2 ((n : ℝ) / (m : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm₀
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hm_pos (by exact_mod_cast hmn)
  have h1 := logb_choose_le_mul_logb_exp_mul_div (Nat.le_add_left m n)
  have hnm : ((n + m : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast; linarith [show (m : ℝ) ≤ n by exact_mod_cast hmn]
  have h2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
    (show Real.exp 1 * ((n + m : ℕ) : ℝ) / (m : ℝ) ≤ 8 * ((n : ℝ) / (m : ℝ)) by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right
        (by nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]) hm_pos.le)
  rw [show (8 : ℝ) * ((n : ℝ) / (m : ℝ)) = (2 : ℝ) ^ (3 : ℕ) * ((n : ℝ) / (m : ℝ)) by ring,
    Real.logb_mul (by positivity) (div_pos hn_pos hm_pos).ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h2; nlinarith

/-- **The logarithm of a binomial coefficient is at most `2 √(m n)`**, a step in the proof of
Theorem 4.1 of [KhannaPuttermanSong2026] (the paper's Fact 2.1, §2, p. 11):
`log C(m + n, n) ≤ 2 √(m n)`, with the natural logarithm. The source states it for positive `m, n`;
it also holds when either is zero, where both sides vanish. The term `C(m + n, n) mᵐ nⁿ` of the
binomial expansion of `(m + n) ^ (m + n)` gives
`log C(m + n, n) ≤ m log (n / m + 1) + n log (m / n + 1)`, and `log (x + 1) ≤ √x`
(`Real.log_add_one_le_sqrt`) bounds each term by `√(m n)`. -/
theorem log_add_choose_le_two_mul_sqrt (m n : ℕ) :
    Real.log ((m + n).choose n) ≤ 2 * √(m * n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have ha : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ((m + n).choose n : ℝ) * ((m : ℝ) ^ m * (n : ℝ) ^ n) ≤
      ((m : ℝ) + n) ^ m * ((m : ℝ) + n) ^ n := by
    rw [← pow_add, add_pow]
    refine le_trans (le_of_eq ?_) (single_le_sum (f := fun k =>
      (m : ℝ) ^ k * (n : ℝ) ^ (m + n - k) * ((m + n).choose k)) (fun k _ => by positivity)
      (mem_range.2 (by omega : m < m + n + 1)))
    rw [Nat.add_sub_cancel_left, Nat.choose_symm_add]
    ring
  have hC : ((m + n).choose n : ℝ) ≤ ((n : ℝ) / m + 1) ^ m * ((m : ℝ) / n + 1) ^ n := by
    rw [div_add_one ha.ne', div_add_one hb.ne', div_pow, div_pow, div_mul_div_comm,
      le_div_iff₀ (by positivity), add_comm (n : ℝ)]
    exact hterm
  have hpos : (0 : ℝ) < (m + n).choose n := by exact_mod_cast Nat.choose_pos (by omega)
  have h1 := Real.log_le_log hpos hC
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
  have h2 := Real.log_add_one_le_sqrt (div_nonneg hb.le ha.le)
  have h3 := Real.log_add_one_le_sqrt (div_nonneg ha.le hb.le)
  have e2 : (m : ℝ) * √((n : ℝ) / m) = √(m * n) := by
    rw [Real.sqrt_div' _ ha.le, Real.sqrt_mul ha.le, mul_div_assoc',
      div_eq_iff (Real.sqrt_pos.2 ha).ne']
    linear_combination (-√(n : ℝ)) * Real.mul_self_sqrt ha.le
  have e3 : (n : ℝ) * √((m : ℝ) / n) = √(m * n) := by
    rw [Real.sqrt_div' _ hb.le, Real.sqrt_mul ha.le, mul_div_assoc',
      div_eq_iff (Real.sqrt_pos.2 hb).ne']
    linear_combination (-√(m : ℝ)) * Real.mul_self_sqrt hb.le
  nlinarith [mul_le_mul_of_nonneg_left h2 ha.le, mul_le_mul_of_nonneg_left h3 hb.le]

/-- Logarithmic form of `choose_le_two_pow_mul_choose_sub` ([LiLiangYuZhou2023], Section 5.2,
pp. 24–25 / PDF pp. 25–26): `log₂ C(U, k) - log₂ C(U - d, k) ≤ k`. -/
theorem logb_choose_sub_logb_choose_sub_le {U d k : ℕ} (hk : k ≤ U - d) (h : 2 * d + k ≤ U + 1) :
    Real.logb 2 (U.choose k) - Real.logb 2 ((U - d).choose k) ≤ (k : ℝ) := by
  have hp1 : (0 : ℝ) < (U.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (hk.trans (Nat.sub_le U d))
  have hp2 : (0 : ℝ) < ((U - d).choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp1
    (show (U.choose k : ℝ) ≤ (2 : ℝ) ^ k * ((U - d).choose k : ℝ) by
      exact_mod_cast Nat.choose_le_two_pow_mul_choose_sub hk h)
  rw [Real.logb_mul (by positivity) hp2.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog; linarith

/-- Binomial difference estimate for simultaneously shrinking ground set by `3 * m` and subset size
by `m` ([LiLiangYuZhou2023], Section 8, p. 30 / PDF p. 31): for `3 * n ≤ U` and `1 ≤ m ≤ n`,
`log₂ C(U, n) - log₂ C(U - 3 * m, n - m) ≤ m * log₂ (U / n) + 5 * m`. -/
theorem logb_choose_sub_logb_sub_three_mul_choose_sub_le {U n m : ℕ}
    (hU : 3 * n ≤ U) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    Real.logb 2 (U.choose n) - Real.logb 2 ((U - 3 * m).choose (n - m)) ≤
      (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)) + 5 * (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hm_pos (by exact_mod_cast hmn)
  have hU_pos : (0 : ℝ) < (U : ℝ) := lt_of_lt_of_le hn_pos (by exact_mod_cast (by omega : n ≤ U))
  have h1_nat := Nat.choose_le_two_pow_mul_choose_sub_of_two_mul_le
    (N := U) (d := 3 * m) (k := n - m) (by omega) (by omega)
  have hc_sub_pos : (0 : ℝ) < ((U - 3 * m).choose (n - m) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hc_Unm_pos : (0 : ℝ) < (U.choose (n - m) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hstep1 : Real.logb 2 (U.choose (n - m)) - Real.logb 2 ((U - 3 * m).choose (n - m)) ≤
      3 * (m : ℝ) := by
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hc_Unm_pos
      (show (U.choose (n - m) : ℝ) ≤ (2 : ℝ) ^ (3 * m) * ((U - 3 * m).choose (n - m) : ℝ) by
        exact_mod_cast h1_nat)
    rw [Real.logb_mul (by positivity) hc_sub_pos.ne', Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_mul,
      Nat.cast_ofNat] at hlog
    linarith
  have habs_nat : U.choose n * n.choose (n - m) =
      U.choose (n - m) * (U - (n - m)).choose (n - (n - m)) :=
    @Nat.choose_mul U n (n - m) (by omega)
  rw [← Nat.choose_symm (Nat.sub_le n m), Nat.sub_sub_self hmn] at habs_nat
  have hc_nm_ge : ((n : ℝ) / (m : ℝ)) ^ m ≤ (n.choose m : ℝ) := div_pow_le_choose hmn
  have hc_Um_le : (((U - (n - m)).choose m : ℕ) : ℝ) ≤ (4 * (U : ℝ) / (m : ℝ)) ^ m := by
    have hle1 : ((U - (n - m)).choose m : ℝ) ≤ (U.choose m : ℝ) := by
      exact_mod_cast Nat.choose_le_choose m (Nat.sub_le U _)
    have hle2 := Nat.choose_le_exp_mul_div_pow U m
    have he4 : Real.exp 1 * (U : ℝ) / (m : ℝ) ≤ 4 * (U : ℝ) / (m : ℝ) := by
      apply div_le_div_of_nonneg_right _ hm_pos.le
      nlinarith [Real.exp_one_lt_d9]
    exact hle1.trans (hle2.trans (pow_le_pow_left₀ (by positivity) he4 m))
  have hratio : (U.choose n : ℝ) ≤ (4 * ((U : ℝ) / (n : ℝ))) ^ m * (U.choose (n - m) : ℝ) := by
    have hpow_pos : 0 < ((n : ℝ) / (m : ℝ)) ^ m := pow_pos (div_pos hn_pos hm_pos) m
    have habs_real : (U.choose n : ℝ) * (n.choose m : ℝ) =
        (U.choose (n - m) : ℝ) * (((U - (n - m)).choose m : ℕ) : ℝ) := by exact_mod_cast habs_nat
    have hmul_ineq : (U.choose n : ℝ) * ((n : ℝ) / (m : ℝ)) ^ m ≤
        ((4 * ((U : ℝ) / (n : ℝ))) ^ m * (U.choose (n - m) : ℝ)) *
          ((n : ℝ) / (m : ℝ)) ^ m := by
      calc (U.choose n : ℝ) * ((n : ℝ) / (m : ℝ)) ^ m
          ≤ (U.choose n : ℝ) * (n.choose m : ℝ) :=
            mul_le_mul_of_nonneg_left hc_nm_ge (Nat.cast_nonneg _)
        _ = (U.choose (n - m) : ℝ) * (((U - (n - m)).choose m : ℕ) : ℝ) := habs_real
        _ ≤ (U.choose (n - m) : ℝ) * (4 * (U : ℝ) / (m : ℝ)) ^ m :=
            mul_le_mul_of_nonneg_left hc_Um_le (Nat.cast_nonneg _)
        _ = ((4 * ((U : ℝ) / (n : ℝ))) ^ m * (U.choose (n - m) : ℝ)) *
              ((n : ℝ) / (m : ℝ)) ^ m := by
            rw [mul_comm _ (U.choose (n - m) : ℝ), mul_assoc]
            congr 1
            rw [← mul_pow]
            congr 1
            field_simp
    exact le_of_mul_le_mul_right hmul_ineq hpow_pos
  have hc_Un_pos : (0 : ℝ) < (U.choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hstep2 : Real.logb 2 (U.choose n) - Real.logb 2 (U.choose (n - m)) ≤
      (m : ℝ) * Real.logb 2 ((U : ℝ) / (n : ℝ)) + 2 * (m : ℝ) := by
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hc_Un_pos hratio
    rw [Real.logb_mul (by positivity) hc_Unm_pos.ne', Real.logb_pow,
      show (4 : ℝ) * ((U : ℝ) / (n : ℝ)) = (2 : ℝ) ^ (2 : ℕ) * ((U : ℝ) / (n : ℝ)) by ring,
      Real.logb_mul (by positivity) (div_pos hU_pos hn_pos).ne', Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
    push_cast at hlog
    nlinarith
  linarith

end Cslib

namespace Real

open Filter

/-- A polynomial is eventually below an exponential with base `r > 1`. -/
theorem exists_one_le_and_mul_pow_le_pow (C : ℝ) (d : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ α : ℕ, 1 ≤ α ∧ C * (α : ℝ) ^ d ≤ r ^ α := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt d hr
  have hC : 0 < |C| + 1 := by positivity
  have hev := (hlim.eventually (gt_mem_nhds (inv_pos.mpr hC))).and (eventually_ge_atTop 1)
  obtain ⟨α, hα, hα1⟩ := hev.exists
  refine ⟨α, hα1, ?_⟩
  have hrα : 0 < r ^ α := pow_pos (by linarith) α
  rw [div_lt_iff₀ hrα] at hα
  have hpow : 0 ≤ (α : ℝ) ^ d := by positivity
  calc C * (α : ℝ) ^ d ≤ (|C| + 1) * (α : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hpow
    _ ≤ (|C| + 1) * ((|C| + 1)⁻¹ * r ^ α) := mul_le_mul_of_nonneg_left hα.le hC.le
    _ = r ^ α := by field_simp

end Real
