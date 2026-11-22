/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.MainCorrect
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Polylog

/-!
# The budget is sublinear

`L_sublinear`: for every `c'`, eventually `c' · L(n) + c' ≤ n`. The support
budget, the measurement tuples and the group sizes are `O(N·k/s) = o(N)`
(`ParameterAsymptotics`), the polylogarithmic part is `o(N)`, the schedule
part is `O(t / log t)`, and `N ≤ K·(n + 1)`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Budget

open Cslib.Complexity.CountingSimulation ProgTerm Filter

/-- The block length is at most `log₂ N + 2`. -/
theorem blockLength_le (k s t : ℕ) (ht : 2 ≤ t) :
    blockLength t ≤ (edgesN k s t).log2 + 2 := by
  have hN : t ≤ edgesN k s t := (le_paddedTime t).trans (ProgTerm.paddedTime_le_edgesN k s t)
  unfold blockLength
  have hpos : edgesN k s t ≠ 0 := by omega
  have h2 : t + 2 ≤ 2 ^ ((edgesN k s t).log2 + 2) := by
    have := Nat.lt_log2_self (n := edgesN k s t)
    rw [pow_succ]; omega
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr h2

theorem blockLength_le_self (t : ℕ) (ht : 2 ≤ t) : blockLength t ≤ t := by
  unfold blockLength
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem numBlocks_mul_le (t : ℕ) : numBlocks t * blockLength t ≤ t + blockLength t := by
  unfold numBlocks
  rw [Nat.ceilDiv_eq_add_pred_div]
  have := Nat.div_mul_le_self (t + blockLength t - 1) (blockLength t)
  omega

/-- `N ≤ K·(n + 1)` with `K = 4(3k+1)(s+k+4)c`. -/
theorem edgesN_le (k s c n : ℕ) (hc : 2 ≤ c) :
    edgesN k s (clk c n) ≤ 4 * (3 * k + 1) * (s + k + 4) * c * (n + 1) := by
  have ht : 2 ≤ clk c n := by unfold clk; nlinarith
  have h1 := numBlocks_mul_le (clk c n)
  have h2 := blockLength_le_self (clk c n) ht
  have h3 : numBlocks (clk c n) * blockLength (clk c n) ≤ 2 * clk c n := by omega
  unfold edgesN Turing.MultiTapePTM.letterBits
  have e : 2 * (numBlocks (clk c n) * (3 * k + 1) * ((s + k + 4) * blockLength (clk c n))) =
      2 * (3 * k + 1) * (s + k + 4) * (numBlocks (clk c n) * blockLength (clk c n)) := by ring
  rw [e]
  have e2 : 4 * (3 * k + 1) * (s + k + 4) * c * (n + 1) = 2 * (3 * k + 1) * (s + k + 4) *
      (2 * clk c n) := by
    unfold clk; ring
  rw [e2]
  exact Nat.mul_le_mul_left _ h3

theorem poly_eventually (A m : ℕ) : ∀ᶠ N : ℕ in atTop, m * (A * (N.log2 + 1) ^ 3) ≤ N := by
  filter_upwards [Polylog.eventually_polylog_le (m * A + 1) 3] with N hN
  calc m * (A * (N.log2 + 1) ^ 3) = (m * A) * (N.log2 + 1) ^ 3 := by ring
    _ ≤ (m * A + 1) ^ 3 * (N.log2 + 1) ^ 3 := by
        gcongr
        calc m * A ≤ m * A + 1 := by omega
          _ = (m * A + 1) ^ 1 := by ring
          _ ≤ (m * A + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ((m * A + 1) * (N.log2 + 1)) ^ 3 := by ring
    _ ≤ N := hN

/-- The schedule part is `o(n)`. -/
theorem schedule_eventually (k c m : ℕ) (hc : 2 ≤ c) :
    ∀ᶠ n : ℕ in atTop, 8 * m * (2 * (k + 1) * numBlocks (clk c n)) ≤ n + 1 + 16 * m * (k + 1) := by
  set B := 32 * m * (k + 1) * c + 1
  filter_upwards [eventually_ge_atTop (2 ^ B)] with n hn
  set t := clk c n
  have hbB : B ≤ blockLength t := by
    unfold blockLength
    have h : B - 1 < Nat.clog 2 (t + 2) := by
      rw [← ProgTerm.lt_clog_iff]
      have : 2 ^ (B - 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : n ≤ t := by unfold t clk; nlinarith
      omega
    omega
  have hnb : numBlocks t ≤ t / B + 1 := by
    unfold numBlocks
    rw [Nat.ceilDiv_eq_add_pred_div]
    calc (t + blockLength t - 1) / blockLength t ≤ (t + blockLength t) / blockLength t :=
          Nat.div_le_div_right (by omega)
      _ = t / blockLength t + 1 := Nat.add_div_right t (by omega)
      _ ≤ t / B + 1 := by gcongr
  have hdiv : t / B * B ≤ t := Nat.div_mul_le_self t B
  have hkey : 8 * m * (2 * (k + 1)) * (t / B) * (2 * c) ≤ t := by
    calc 8 * m * (2 * (k + 1)) * (t / B) * (2 * c) = (t / B) * (32 * m * (k + 1) * c) := by ring
      _ ≤ (t / B) * B := Nat.mul_le_mul_left _ (by omega)
      _ ≤ t := hdiv
  have ht : t = c * (n + 1) := by unfold t clk; ring
  have hkey' : 8 * m * (2 * (k + 1)) * (t / B) * 2 ≤ n + 1 := by
    have h2 : (8 * m * (2 * (k + 1)) * (t / B) * 2) * c ≤ (n + 1) * c := by
      calc (8 * m * (2 * (k + 1)) * (t / B) * 2) * c
            = 8 * m * (2 * (k + 1)) * (t / B) * (2 * c) := by ring
        _ ≤ t := hkey
        _ = (n + 1) * c := by rw [ht]; ring
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  calc 8 * m * (2 * (k + 1) * numBlocks t) ≤ 8 * m * (2 * (k + 1) * (t / B + 1)) := by gcongr
    _ = 8 * m * (2 * (k + 1)) * (t / B) + 16 * m * (k + 1) := by ring
    _ ≤ n + 1 + 16 * m * (k + 1) := by omega

end Cslib.Complexity.NtimeDspace.Budget
