/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The price of compiling an expensive replicated computation

Let `x j` be the minimum cost per input bit of `j` copies of a computation. The profile may
drop at different replication factors at different batch sizes. Starting from an upper bound,
choose a scale where no admissible replication factor halves the cost. If the whole window
is expensive, a compiler with an interior gain and a fixed boundary charge then forces a
lower bound on the price it pays for its routing tests.

This numerical argument gives an alternative to the repeated compilation in
[OpenAI2026MatrixExponentNineFourths, “Finite fields with ports”]. The workload and compiler
inequalities are separate hypotheses in the transfer lemmas.
-/

namespace Cslib.Circuits.Frontier.BatchPrice

/-- A positive cost bounded below by one has a scale where multiplying the batch
size by any `d ≤ D` saves at most a factor of two. The length of the search
window depends only on the initial cost. -/
public theorem exists_le_two_mul {x : ℕ → ℝ} {D start rounds : ℕ}
    (floor : ∀ j, start ≤ j → j ≤ start * D ^ rounds → 1 ≤ x j)
    (budget : x start < 2 ^ rounds) :
    ∃ j, start ≤ j ∧ j * D ≤ start * D ^ rounds ∧ x j ≤ x start ∧
      ∀ d, 1 ≤ d → d ≤ D → x j ≤ 2 * x (j * d) := by
  induction rounds generalizing start with
  | zero =>
    exact ((not_lt_of_ge (floor start le_rfl (by simp))) (by simpa using budget)).elim
  | succ rounds ih =>
    by_cases stable : ∀ d, 1 ≤ d → d ≤ D → x start ≤ 2 * x (start * d)
    · exact ⟨start, le_rfl, Nat.mul_le_mul_left _ (Nat.le_self_pow (Nat.succ_ne_zero _) D),
        le_rfl, stable⟩
    · push Not at stable
      obtain ⟨d, hd, hdD, hdrop⟩ := stable
      have hstart := Nat.le_mul_of_pos_right start hd
      have hs : start * d * D ^ rounds ≤ start * D ^ (rounds + 1) := by
        rw [pow_succ', ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdD)
      have hbudget : x (start * d) < 2 ^ rounds := by
        rw [pow_succ] at budget
        linarith
      obtain ⟨j, hsj, hjD, hxj, hstable⟩ := ih
        (fun j lower upper => floor j (hstart.trans lower) (upper.trans hs)) hbudget
      have hupper := Nat.mul_le_mul_left start
        (hdD.trans (Nat.le_self_pow (Nat.succ_ne_zero rounds) D))
      exact ⟨j, hstart.trans hsj, hjD.trans hs, hxj.trans (by linarith [floor _ hstart hupper]),
        hstable⟩

/-- If a compiler divides the interior cost by `gain` and incurs an additive boundary
charge before paying `price`, a workload whose per-bit cost throughout the batch window
is at least `gain * boundary` forces the price to be at least `gain / 4`. -/
public theorem gain_le_four_mul_price_of_compiler {x : ℕ → ℝ} {D start rounds : ℕ}
    {gain boundary price : ℝ} (hgain : 0 < gain) (hprice : 0 ≤ price)
    (floor : ∀ j, start ≤ j → j ≤ start * D ^ rounds → max 1 (gain * boundary) ≤ x j)
    (budget : x start < 2 ^ rounds)
    (compile : ∀ j, start ≤ j → j * D ≤ start * D ^ rounds → x j ≤ x start →
      ∃ d, 1 ≤ d ∧ d ≤ D ∧ x (j * d) ≤ price * (x j / gain + boundary)) :
    gain ≤ 4 * price := by
  obtain ⟨j, lower, upper, hcost, stable⟩ := exists_le_two_mul
    (fun j lo hi => (le_max_left _ _).trans (floor j lo hi)) budget
  obtain ⟨d, hd, hdD, hcompiled⟩ := compile j lower upper hcost
  have hf := floor j lower ((Nat.le_mul_of_pos_right _ (hd.trans hdD)).trans upper)
  have hx : 0 < x j := zero_lt_one.trans_le ((le_max_left _ _).trans hf)
  have hb : boundary ≤ x j / gain := (le_div_iff₀ hgain).2
    (by simpa only [mul_comm boundary] using (le_max_right _ _).trans hf)
  have hpricebound : x j ≤ (4 * price * x j) / gain := calc
    x j ≤ 2 * x (j * d) := stable d hd hdD
    _ ≤ 2 * (price * (x j / gain + x j / gain)) := mul_le_mul_of_nonneg_left
      (hcompiled.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hb) hprice)) zero_le_two
    _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hx).mp
    ((mul_comm gain (x j)).le.trans ((le_div_iff₀ hgain).mp hpricebound))

/-- Transfer a compiler saving `gain` to the volume of `t` routing tests, with `3 * n * h`
ports per test. The workload is expensive between `n²` and `n³` copies. An unfinished batch of
up to `2 * n` tests charges at most `6 * h / ℓ` per bit of the replicated workload. In the
dyadic routing application, `n = 2 ^ h` and `ℓ` is the workload's number of exterior bits. -/
public theorem gain_mul_ports_le_four_mul_volume_of_compiler
    {n h t ℓ volume D rounds : ℕ} {x : ℕ → ℝ} {gain boundary K : ℝ}
    (hn : 0 < n) (hh : 0 < h) (ht : 0 < t) (htn : t ≤ 2 * n) (hℓ : 0 < ℓ)
    (hgain : 0 < gain) (hK : 0 ≤ K)
    (window : n ^ 2 * D ^ rounds ≤ n ^ 3) (budget : x (n ^ 2) < 2 ^ rounds)
    (floor : ∀ j, n ^ 2 ≤ j → j ≤ n ^ 3 → max 1 (gain * (boundary + 6 * h / ℓ)) ≤ x j)
    (compile : ∀ j, n ^ 2 ≤ j → j * D ≤ n ^ 3 → x j ≤ x (n ^ 2) →
      ∃ d, 1 ≤ d ∧ d ≤ D ∧ x (j * d) ≤
        K * volume / (t * (3 * n * h) : ℕ) *
          (x j / gain + boundary + (t * (3 * n * h) : ℕ) / (d * j * ℓ : ℕ))) :
    gain * (t * (3 * n * h) : ℕ) ≤ 4 * K * volume := by
  let price := K * volume / (t * (3 * n * h) : ℕ)
  have hp : 0 ≤ price := by dsimp [price]; positivity
  have hports : 0 < ((t * (3 * n * h) : ℕ) : ℝ) := by positivity
  suffices hbound : gain ≤ 4 * price by
    apply (le_div_iff₀ hports).mp
    simpa only [price, ← mul_div_assoc, ← mul_assoc] using hbound
  apply gain_le_four_mul_price_of_compiler hgain hp
    (fun j lo hi => floor j lo (hi.trans window)) budget
  intro j lower upper hx
  obtain ⟨d, hd, hdD, hc⟩ := compile j lower (upper.trans window) hx
  refine ⟨d, hd, hdD, hc.trans (mul_le_mul_of_nonneg_left ?_ hp)⟩
  rw [add_assoc]
  refine add_le_add le_rfl (add_le_add le_rfl ?_)
  have hj : 0 < j := (Nat.pow_pos hn).trans_le lower
  apply (div_le_div_iff₀ (by positivity : 0 < ((d * j * ℓ : ℕ) : ℝ))
    (by exact_mod_cast hℓ : 0 < (ℓ : ℝ))).mpr
  have hnum : t * (3 * n * h) ≤ 6 * h * (d * j) := calc
    t * (3 * n * h) ≤ (2 * n) * (3 * n * h) := Nat.mul_le_mul_right _ htn
    _ = 6 * h * n ^ 2 := by ring
    _ ≤ 6 * h * (d * j) := Nat.mul_le_mul_left _ (lower.trans (Nat.le_mul_of_pos_left _ hd))
  exact_mod_cast (Nat.mul_le_mul_right ℓ hnum).trans_eq (Nat.mul_assoc _ _ _)

end Cslib.Circuits.Frontier.BatchPrice
