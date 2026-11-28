/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Real.GoldenRatio
-- `import all`: reads private index-shifting and diagonal-sum recurrence helpers
-- (`sum_Ico_one_succ_shift`, `diagSum_recurrence`) from `ConsistentTree`.
import all CslibFrontier.Computability.Circuit.Prefix.ConsistentTree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real two-parameter segment-width recurrence `V_k(d, h)` and diagonal sum `V_k*(D)`

Auxiliary real-valued recurrence `V_k(d, h)`, root-budgeted variant `W_k(r, d, h)`, and diagonal sum
`V_k*(D)` used to upper-bound generalized prefix distribution trees for fanout `k ≥ 3` in the proof
of Sergeev's theorem [Sergeev2025PrefixDepth].

## Main definitions

* `Cslib.Circuits.Prefix.V`, `Cslib.Circuits.Prefix.W`, `Cslib.Circuits.Prefix.vStar`: real
  segment-width bound `V_k(d, h)`, root-budgeted bound `W_k(r, d, h)`, and diagonal sum `V_k*(D)`.

## Main results

* `Cslib.Circuits.Prefix.W_split_depth_one`, `Cslib.Circuits.Prefix.W_split_depth_two`: subadditive
  splitting laws for direct (`depth + 1`) and deeper (`depth + 2`) `mul`-subtree extractions.
* `Cslib.Circuits.Prefix.vStar_recurrence`: inhomogeneous order-`k` linear recurrence for
  `vStar k D`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

/-- Real segment-width upper bound `V_k(d, h)` with base `(3 / 2) ^ d` at `h = 0`. -/
@[expose] noncomputable def V (k : ℕ) : ℕ → ℕ → ℝ
  | d, 0 => (3 / 2 : ℝ) ^ d
  | 0, _ + 1 => 1
  | d + 1, h + 1 =>
      let l := min (d + 1) (k - 1)
      (∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) h) + 2 * V k (d + 1 - l) h

/-- At output budget `h = 0`, `V k d 0 = (3 / 2) ^ d`. -/
theorem V_zero_right (k d : ℕ) : V k d 0 = (3 / 2 : ℝ) ^ d := by
  cases d <;> rfl

private theorem V_zero_left (k h : ℕ) : V k 0 h = 1 := by
  cases h <;> simp only [V, pow_zero]

/-- Unfolds `V k d (h + 1)` for `d ≠ 0` once its window `min d (k - 1)` is known. -/
private theorem V_succ_eq {k d l : ℕ} (hd : d ≠ 0) (hl : min d (k - 1) = l) (h : ℕ) :
    V k d (h + 1) = (∑ i ∈ Finset.Ico 1 l, V k (d - i) h) + 2 * V k (d - l) h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  subst hl
  rfl

private theorem V_one_le (k d h : ℕ) : (1 : ℝ) ≤ V k d h := by
  induction h generalizing d with
  | zero => exact V_zero_right k d ▸ one_le_pow₀ (by norm_num)
  | succ h ih =>
    cases d with
    | zero => rw [V_zero_left]
    | succ d =>
      rw [V_succ_eq d.add_one_ne_zero rfl]
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.Ico 1 (min (d + 1) (k - 1))) =>
        zero_le_one.trans (ih (d + 1 - i)), ih (d + 1 - min (d + 1) (k - 1))]

/-- `V k d h` is nonnegative for all `k, d, h`. -/
theorem V_nonneg (k d h : ℕ) : (0 : ℝ) ≤ V k d h :=
  zero_le_one.trans (V_one_le k d h)

private theorem V_one_left {k : ℕ} (hk : 2 ≤ k) (h : ℕ) : V k 1 (h + 1) = 2 := by
  rw [V_succ_eq one_ne_zero (Nat.min_eq_left (by omega)), Finset.Ico_self, Finset.sum_empty,
    zero_add, Nat.sub_self, V_zero_left, mul_one]

private theorem V_succ_sub_self_small {k d : ℕ} (hd : d + 1 ≤ k - 1) (h : ℕ) :
    V k (d + 1) (h + 1) - V k d (h + 1) =
      if d = 0 then 1 else V k d h := by
  cases d with
  | zero =>
    have hk2 : 2 ≤ k := by omega
    rw [V_one_left hk2, V_zero_left]
    norm_num
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [V_succ_eq (by omega) (Nat.min_eq_left hd),
      V_succ_eq (by omega) (Nat.min_eq_left (by omega : m + 1 ≤ k - 1)), Nat.sub_self, Nat.sub_self,
      V_zero_left, sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 1) (fun x => V k x h)]
    ring

private theorem V_step_le_mul {k a b h : ℕ} {c : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : k - 1 ≤ a) (hb : k - 1 ≤ b)
    (hstep : ∀ i ≤ k - 1, V k (a - i) h ≤ c * V k (b - i) h) :
    V k a (h + 1) ≤ c * V k b (h + 1) := by
  rw [V_succ_eq ha0 (Nat.min_eq_right ha), V_succ_eq hb0 (Nat.min_eq_right hb), mul_add,
    Finset.mul_sum, mul_left_comm c 2]
  exact add_le_add (Finset.sum_le_sum fun i hi => hstep i (Finset.mem_Ico.mp hi).2.le)
    (mul_le_mul_of_nonneg_left (hstep (k - 1) le_rfl) (by norm_num))

private theorem V_mono_left (k : ℕ) :
    ∀ d h : ℕ, V k d h ≤ V k (d + 1) h := by
  intro d h
  induction h generalizing d with
  | zero => simpa only [V_zero_right] using pow_le_pow_right₀ (by norm_num) d.le_succ
  | succ h ih =>
    cases d with
    | zero => exact (V_zero_left k (h + 1)).trans_le (V_one_le k 1 (h + 1))
    | succ d =>
      by_cases hle : d + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hle h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        linarith [V_nonneg k (d + 1) h]
      · simpa only [one_mul] using
          V_step_le_mul (c := 1) (by omega) (by omega) (by omega) (by omega) fun i hi => by
            simpa only [Nat.succ_sub (m := d + 1) (n := i) (by omega), one_mul] using ih _

private theorem V_one_mul_three_halves {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    V k (n + 1) 1 = (3 / 2 : ℝ) * V k n 1 := by
  have hstep (i : ℕ) (hi : i ≤ k - 1) : V k (n + 1 - i) 0 = 3 / 2 * V k (n - i) 0 := by
    rw [show n + 1 - i = n - i + 1 by omega, V_zero_right, V_zero_right, pow_succ, mul_comm]
  rw [V_succ_eq n.add_one_ne_zero (Nat.min_eq_right (by omega)) 0,
    V_succ_eq (by omega) (Nat.min_eq_right hn) 0, hstep _ le_rfl,
    Finset.sum_congr rfl fun i hi => hstep i (Finset.mem_Ico.1 hi).2.le, ← Finset.mul_sum]
  ring

private theorem pow_le_V_one {k : ℕ} (hk : 3 ≤ k) :
    ∀ n : ℕ, 2 ≤ n → (3 / 2 : ℝ) ^ (n + 1) ≤ V k n 1 := by
  intro n hn
  induction hn with
  | refl =>
    rw [V_succ_eq two_ne_zero (Nat.min_eq_left (by omega)) 0,
      show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, V_zero_right, V_zero_right]
    norm_num
  | @step m hm ih =>
    change (3 / 2 : ℝ) ^ (m + 2) ≤ V k (m + 1) 1
    by_cases hsmall : m + 1 ≤ k - 1
    · have hdiff := V_succ_sub_self_small hsmall 0
      simp only [Nat.zero_add, (by lia : m ≠ 0), ↓reduceIte, V_zero_right] at hdiff
      simp only [pow_succ' (3 / 2 : ℝ) m, pow_succ' (3 / 2 : ℝ) (m + 1)] at ih ⊢
      linarith only [ih, hdiff, pow_nonneg (by norm_num : 0 ≤ (3 / 2 : ℝ)) m]
    · rw [pow_succ', V_one_mul_three_halves hk (by lia : k - 1 ≤ m)]
      exact mul_le_mul_of_nonneg_left ih (by norm_num)

private theorem V_mono_right {k : ℕ} (hk : 3 ≤ k) :
    ∀ d h : ℕ, V k d h ≤ V k d (h + 1) := by
  intro d h
  induction h generalizing d with
  | zero =>
    rcases d with _ | _ | n
    · simp only [V_zero_left, le_rfl]
    · norm_num [V_zero_right, V_one_left (by omega : 2 ≤ k)]
    · exact (V_zero_right k _).trans_le ((pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)).trans
        (pow_le_V_one hk _ (by omega)))
  | succ h ih =>
    cases d with
    | zero => simp only [V_zero_left, le_rfl]
    | succ d =>
      rw [V_succ_eq d.add_one_ne_zero rfl h, V_succ_eq d.add_one_ne_zero rfl (h + 1)]
      gcongr <;> apply ih

private theorem V_le_two_mul {k : ℕ} (hk : 3 ≤ k) :
    ∀ d h : ℕ, V k (d + 1) h ≤ 2 * V k d h := by
  have hk2 : 2 ≤ k := by omega
  intro d h
  induction h generalizing d with
  | zero =>
    have hp0 : (0 : ℝ) ≤ (3 / 2) ^ d := by positivity
    simp only [V_zero_right, pow_succ]; linarith
  | succ h ih =>
    cases d with
    | zero => norm_num [V_one_left hk2, V_zero_left]
    | succ m =>
      by_cases hle : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hle h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        linarith [V_mono_right hk (m + 1) h]
      · exact V_step_le_mul (c := 2) (by omega) (by omega) (by omega) (by omega) fun i hi =>
          Nat.succ_sub (m := m + 1) (n := i) (by omega) ▸ ih _

private theorem V_three_term {k : ℕ} (hk : 3 ≤ k) :
    ∀ n h : ℕ, 2 * V k n h + V k (n + 2) h ≤ 3 * V k (n + 1) h := by
  intro n h
  induction h generalizing n with
  | zero =>
    simp only [V_zero_right, pow_succ' (3 / 2 : ℝ) n, pow_succ' (3 / 2 : ℝ) (n + 1)]
    linarith only [pow_nonneg (by norm_num : 0 ≤ (3 / 2 : ℝ)) n]
  | succ h ih =>
    cases n with
    | zero =>
      have h2 := V_le_two_mul hk 1 (h + 1)
      simp only [V_zero_left, V_one_left (show 2 ≤ k by omega)] at h2 ⊢
      linarith
    | succ m =>
      by_cases h1 : m + 3 ≤ k - 1
      · have hd1 := V_succ_sub_self_small (by omega : m + 2 ≤ k - 1) h
        have hd2 := V_succ_sub_self_small h1 h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hd1 hd2
        linarith [V_le_two_mul hk (m + 1) h]
      · by_cases h2 : m + 2 = k - 1
        · have hd1 := V_succ_sub_self_small (by omega : m + 2 ≤ k - 1) h
          simp only [Nat.succ_ne_zero, ↓reduceIte] at hd1
          have hd2 : V k (m + 3) (h + 1) - V k (m + 2) (h + 1) =
              V k (m + 2) h + V k 1 h - 2 * V k 0 h := by
            rw [V_succ_eq (by omega) (by omega : min (m + 3) (k - 1) = m + 2),
              V_succ_eq (by omega) (Nat.min_eq_left (by omega : m + 2 ≤ k - 1)),
              show m + 3 - (m + 2) = 1 by omega, Nat.sub_self,
              sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 2) (fun x => V k x h),
              Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1) (fun i => V k (m + 2 - i) h),
              show m + 2 - (m + 1) = 1 by omega]
            ring
          linarith [V_le_two_mul hk 0 h, V_le_two_mul hk (m + 1) h]
        · rw [V_succ_eq (by omega) (Nat.min_eq_right (by omega : k - 1 ≤ m + 1)),
            V_succ_eq (by omega) (Nat.min_eq_right (by omega : k - 1 ≤ m + 1 + 2)),
            V_succ_eq (by omega) (Nat.min_eq_right (by omega : k - 1 ≤ m + 1 + 1)), mul_add,
            mul_add, Finset.mul_sum, Finset.mul_sum]
          have hstep (i : ℕ) (hi : i ≤ k - 1) :
              2 * V k (m + 1 - i) h + V k (m + 3 - i) h ≤ 3 * V k (m + 2 - i) h := by
            rw [show m + 3 - i = (m + 1 - i) + 2 by lia,
              show m + 2 - i = (m + 1 - i) + 1 by lia]
            exact ih (m + 1 - i)
          have hsum := Finset.sum_le_sum (s := Finset.Ico 1 (k - 1)) fun i hi =>
            hstep i (Finset.mem_Ico.mp hi).2.le
          rw [Finset.sum_add_distrib] at hsum
          linarith only [hsum, hstep (k - 1) le_rfl]

private theorem V_step_ineq {k : ℕ} (hk : 3 ≤ k) :
    ∀ n h : ℕ, V k (n + 1) h + 2 * V k n (h + 1) ≤ 2 * V k (n + 1) (h + 1) := by
  intro n h
  induction h generalizing n with
  | zero =>
    cases n with
    | zero => norm_num [V_zero_right, V_zero_left, V_one_left (by omega : 2 ≤ k)]
    | succ m =>
      change V k (m + 2) 0 + 2 * V k (m + 1) 1 ≤ 2 * V k (m + 2) 1
      rw [V_zero_right]
      by_cases hsmall : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hsmall 0
        simp only [Nat.zero_add, Nat.succ_ne_zero, ↓reduceIte, V_zero_right, pow_succ'] at hdiff ⊢
        linarith [pow_nonneg (div_nonneg (zero_le_three : (0 : ℝ) ≤ 3) zero_le_two) m]
      · linarith [V_one_mul_three_halves hk (by omega : k - 1 ≤ m + 1),
          pow_le_V_one hk (m + 1) (by omega)]
  | succ h ih =>
    cases n with
    | zero => norm_num [V_one_left (by omega : 2 ≤ k), V_zero_left]
    | succ m =>
      by_cases hsmall : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hsmall (h + 1)
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        linarith [V_le_two_mul hk (m + 1) (h + 1)]
      · rw [V_succ_eq (by omega) (Nat.min_eq_right (by omega : k - 1 ≤ m + 1 + 1)) h,
          V_succ_eq (by omega) (Nat.min_eq_right (by omega : k - 1 ≤ m + 1 + 1)) (h + 1),
          V_succ_eq (by omega) (Nat.min_eq_right (by omega : k - 1 ≤ m + 1)) (h + 1), mul_add,
          mul_add, Finset.mul_sum, Finset.mul_sum]
        have hstep (i : ℕ) (hi : i ≤ k - 1) :
            V k (m + 2 - i) h + 2 * V k (m + 1 - i) (h + 1) ≤
              2 * V k (m + 2 - i) (h + 1) := by
          rw [show m + 2 - i = (m + 1 - i) + 1 by lia]
          exact ih (m + 1 - i)
        have hsum := Finset.sum_le_sum (s := Finset.Ico 1 (k - 1)) fun i hi =>
          hstep i (Finset.mem_Ico.mp hi).2.le
        rw [Finset.sum_add_distrib] at hsum
        linarith only [hsum, hstep (k - 1) le_rfl]

/-- Root-budgeted segment bound `W k r d h` for a root with fanout budget `r`. -/
@[expose] noncomputable def W (k r d : ℕ) : ℕ → ℝ
  | 0 => (3 / 2 : ℝ) ^ d
  | h + 1 =>
      if r = 0 then 0
      else if r = 1 then V k d h
      else if d = 0 then 1
      else
        let l := min d (r - 1)
        (∑ i ∈ Finset.Ico 1 l, V k (d - i) h) + 2 * V k (d - l) h

/-- Unfolds `W k r d (h + 1)` for `2 ≤ r` and `d ≠ 0` once its window `min d (r - 1)` is known. -/
private theorem W_succ_eq {k r d l : ℕ} (hr : 2 ≤ r) (hd : d ≠ 0) (hl : min d (r - 1) = l)
    (h : ℕ) : W k r d (h + 1) = (∑ i ∈ Finset.Ico 1 l, V k (d - i) h) + 2 * V k (d - l) h := by
  subst hl
  simp only [W, (Nat.zero_lt_of_lt hr).ne', (show 1 < r from hr).ne', hd, ↓reduceIte]

/-- At full root budget `r = k ≥ 2`, `W k k d h` coincides with `V k d h`. -/
theorem W_eq_V {k : ℕ} (hk : 2 ≤ k) (d h : ℕ) : W k k d h = V k d h := by
  cases h with
  | zero => rw [W, V_zero_right]
  | succ h =>
    cases d with
    | zero => simp only [W, (Nat.zero_lt_of_lt hk).ne', (show 1 < k from hk).ne', ↓reduceIte,
        V_zero_left]
    | succ d => rw [W_succ_eq hk d.add_one_ne_zero rfl, V_succ_eq d.add_one_ne_zero rfl]

/-- For positive root budget `r ≥ 1`, `1 ≤ W k r d h`. -/
theorem W_one_le {k r : ℕ} (hr : 1 ≤ r) (d h : ℕ) : (1 : ℝ) ≤ W k r d h := by
  cases h with
  | zero => exact one_le_pow₀ (by norm_num)
  | succ h =>
    obtain rfl | hr2 := hr.eq_or_lt
    · simpa only [W, one_ne_zero, ↓reduceIte] using V_one_le k d h
    obtain rfl | hd := Nat.eq_zero_or_pos d
    · simp only [W, (Nat.zero_lt_of_lt hr2).ne', hr2.ne', ↓reduceIte, le_rfl]
    rw [W_succ_eq hr2 hd.ne' rfl]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.Ico 1 (min d (r - 1))) =>
      V_nonneg k (d - i) h, V_one_le k (d - min d (r - 1)) h]

/-- `W k r d h` is monotone in the interval-tree depth `d`. -/
theorem W_mono_left (k : ℕ) :
    ∀ r d h : ℕ, W k r d h ≤ W k r (d + 1) h := by
  intro r d h
  cases h with
  | zero => simpa only [W] using pow_le_pow_right₀ (by norm_num) d.le_succ
  | succ h =>
    by_cases hr0 : r = 0
    · simp only [W, hr0, ↓reduceIte, le_rfl]
    by_cases hr1 : r = 1
    · simpa only [W, hr1, one_ne_zero, ↓reduceIte] using V_mono_left k d h
    have hr : 2 ≤ r := by omega
    obtain rfl | hd0 := Nat.eq_zero_or_pos d
    · rw [zero_add, W_succ_eq hr one_ne_zero (Nat.min_eq_left (by omega)), Finset.Ico_self,
        Finset.sum_empty, zero_add, Nat.sub_self, V_zero_left]
      simp only [W, hr0, hr1, ↓reduceIte]; norm_num
    by_cases hsmall : d + 1 ≤ r - 1
    · rw [W_succ_eq hr hd0.ne' (Nat.min_eq_left (by omega)),
        W_succ_eq hr d.add_one_ne_zero (Nat.min_eq_left hsmall), Nat.sub_self, Nat.sub_self,
        V_zero_left, sum_Ico_one_succ_shift (l := d) (by omega) d (fun x => V k x h)]
      linarith [V_nonneg k d h]
    · have hmono (x : ℕ) (hx : x ≤ d) : V k (d - x) h ≤ V k (d + 1 - x) h :=
        (Nat.succ_sub hx).symm ▸ V_mono_left k (d - x) h
      rw [W_succ_eq hr hd0.ne' (Nat.min_eq_right (by omega)),
        W_succ_eq hr d.add_one_ne_zero (Nat.min_eq_right (by omega))]
      gcongr with i hi
      exacts [hmono i (by have := (Finset.mem_Ico.1 hi).2; omega), hmono _ (by omega)]

/-- Splitting off a direct child subtree at depth `1` satisfies
`W k (r - 1) d (h + 1) + V k d h = W k r (d + 1) (h + 1)`. -/
theorem W_split_depth_one {k r d h : ℕ} (hr : 2 ≤ r) :
    W k (r - 1) d (h + 1) + V k d h = W k r (d + 1) (h + 1) := by
  obtain ⟨hr0, hr1⟩ : r ≠ 0 ∧ r ≠ 1 := by omega
  obtain rfl | hr3 : r = 2 ∨ 3 ≤ r := by omega
  · simp only [W, Nat.add_sub_cancel, ↓reduceIte, hr0, hr1, Nat.succ_ne_zero,
      Nat.min_eq_right (Nat.succ_pos d), Finset.Ico_self, Finset.sum_empty, zero_add]
    ring
  · obtain ⟨u, rfl⟩ : ∃ u, r = u + 3 := ⟨r - 3, by omega⟩
    cases d with
    | zero => norm_num [W, Nat.succ_ne_zero, V_zero_left]
    | succ m =>
      set l := min (m + 1) (u + 1)
      have hl : 1 ≤ l := by omega
      rw [W_succ_eq (r := u + 3 - 1) (Nat.le_add_left 2 u) m.add_one_ne_zero (rfl : _ = l),
        W_succ_eq hr m.succ.add_one_ne_zero (Nat.add_min_add_right (m + 1) (u + 1) 1),
        Nat.succ_sub_succ_eq_sub (m + 1) l, sum_Ico_one_succ_shift hl (m + 1) (fun x => V k x h)]
      ring

/-- Splitting off a proper descendant subtree at depth `≥ 2` satisfies
`W k r d (h + 2) + V k d h ≤ W k r (d + 1) (h + 2)` for `k ≥ 3` and `2 ≤ r ≤ k`. -/
theorem W_split_depth_two {k r d h : ℕ} (hk : 3 ≤ k) (hr : 2 ≤ r) (_hrk : r ≤ k) :
    W k r d (h + 2) + V k d h ≤ W k r (d + 1) (h + 2) := by
  obtain ⟨hr0, hr1⟩ : r ≠ 0 ∧ r ≠ 1 := by omega
  cases d with
  | zero =>
    norm_num [W, hr0, hr1, Nat.succ_ne_zero, Nat.min_eq_left (Nat.sub_pos_of_lt hr), V_zero_left]
  | succ m =>
    by_cases hsmall : m + 2 ≤ r - 1
    · rw [W_succ_eq hr m.add_one_ne_zero (Nat.min_eq_left (by omega : m + 1 ≤ r - 1)),
        W_succ_eq hr (by omega) (Nat.min_eq_left hsmall), Nat.sub_self, Nat.sub_self, V_zero_left,
        sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 1) (fun x => V k x (h + 1))]
      linarith [V_mono_right hk (m + 1) h]
    · obtain ⟨u, hu_eq⟩ : ∃ u, r - 1 = u + 1 := ⟨r - 2, by omega⟩
      rw [W_succ_eq hr m.add_one_ne_zero (by omega : min (m + 1) (r - 1) = u + 1),
        W_succ_eq hr (by omega) (by omega : min (m + 2) (r - 1) = u + 1)]
      have htel_sum : (∑ i ∈ Finset.Ico 1 (u + 1), V k (m + 2 - i) (h + 1)) +
          2 * V k (m + 2 - (u + 1)) (h + 1) -
          ((∑ i ∈ Finset.Ico 1 (u + 1), V k (m + 1 - i) (h + 1)) +
            2 * V k (m + 1 - (u + 1)) (h + 1)) =
          V k (m + 1) (h + 1) + V k (m + 2 - (u + 1)) (h + 1) -
            2 * V k (m + 1 - (u + 1)) (h + 1) := by
        cases u with
        | zero =>
          rw [Finset.Ico_self, Finset.sum_empty, Finset.sum_empty, Nat.add_sub_cancel (m + 1) 1]
          ring
        | succ u' =>
          have hsub : m + 1 - (u' + 1) = m + 2 - (u' + 1 + 1) := by omega
          rw [sum_Ico_one_succ_shift (l := u' + 1) (by omega) (m + 1) (fun x => V k x (h + 1)),
            Finset.sum_Ico_succ_top (Nat.le_add_left 1 u') (fun i => V k (m + 1 - i) (h + 1)),
            hsub]
          ring
      obtain ⟨a, rfl⟩ : ∃ a, m = a + u := ⟨m - u, by omega⟩
      have hchain (w : ℕ) :
          2 * (V k (a + w + 1) (h + 1) - V k (a + w) (h + 1)) ≤
            V k (a + w + 1) (h + 1) + V k (a + 1) (h + 1) - 2 * V k a (h + 1) := by
        induction w with
        | zero => simp only [Nat.add_zero]; linarith
        | succ w ih =>
          rw [← Nat.add_assoc a w 1]
          linarith [V_three_term hk (a + w) (h + 1)]
      obtain ⟨ha1, ha0⟩ : a + u + 2 - (u + 1) = a + 1 ∧ a + u + 1 - (u + 1) = a := by omega
      rw [ha1, ha0] at htel_sum ⊢
      linarith [hchain u, V_step_ineq hk (a + u) h]


/-- Diagonal sum `V_k*(D) = ∑_{d=0}^D V_k(d, D - d)` bounding circuit width for `k ≥ 3`. -/
@[expose] noncomputable def vStar (k D : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (D + 1), V k d (D - d)

/-- Inhomogeneous order-`k` linear recurrence for `vStar k D` when `3 ≤ k ≤ D`. -/
theorem vStar_recurrence {k D : ℕ} (hk : 3 ≤ k) (hD : k ≤ D) :
    vStar k D =
      (∑ i ∈ Finset.Ico 2 k, vStar k (D - i)) +
        2 * vStar k (D - k) + (3 / 2 : ℝ) ^ D + ((k - 1 : ℕ) : ℝ) := by
  unfold vStar
  rw [diagSum_recurrence (by omega) hD (V k) (V_zero_left k) (fun _ _ => rfl), V_zero_right]


end Cslib.Circuits.Prefix
