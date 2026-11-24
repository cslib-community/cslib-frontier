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

private theorem V_one_le (k d h : ℕ) : (1 : ℝ) ≤ V k d h := by
  induction h generalizing d with
  | zero =>
    rw [V_zero_right]
    exact one_le_pow₀ (by norm_num)
  | succ h ih =>
    cases d with
    | zero => rw [V_zero_left]
    | succ d =>
      change (1 : ℝ) ≤
        (∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), V k (d + 1 - i) h) +
          2 * V k (d + 1 - min (d + 1) (k - 1)) h
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), V k (d + 1 - i) h :=
        Finset.sum_nonneg fun i _ => ( zero_le_one.trans (ih _) )
      have hlast := ih (d + 1 - min (d + 1) (k - 1))
      linarith

/-- `V k d h` is nonnegative for all `k, d, h`. -/
theorem V_nonneg (k d h : ℕ) : (0 : ℝ) ≤ V k d h :=
  zero_le_one.trans (V_one_le k d h)

private theorem V_one_left {k : ℕ} (hk : 2 ≤ k) (h : ℕ) : V k 1 (h + 1) = 2 := by
  have hl : min 1 (k - 1) = 1 := Nat.min_eq_left (by omega)
  change (∑ i ∈ Finset.Ico 1 (min 1 (k - 1)), V k (1 - i) h) +
      2 * V k (1 - min 1 (k - 1)) h = 2
  rw [hl, Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self, V_zero_left, mul_one]

private theorem V_succ_sub_self_small {k d : ℕ} (hd : d + 1 ≤ k - 1) (h : ℕ) :
    V k (d + 1) (h + 1) - V k d (h + 1) =
      if d = 0 then 1 else V k d h := by
  cases d with
  | zero =>
    have hk2 : 2 ≤ k := by omega
    rw [V_one_left hk2, V_zero_left]
    norm_num
  | succ m =>
    have hl1 : min (m + 1) (k - 1) = m + 1 := Nat.min_eq_left (by omega)
    have hl2 : min (m + 2) (k - 1) = m + 2 := Nat.min_eq_left hd
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    change ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
        2 * V k (m + 2 - min (m + 2) (k - 1)) h) -
      ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) h) +
        2 * V k (m + 1 - min (m + 1) (k - 1)) h) = V k (m + 1) h
    rw [hl1, hl2, Nat.sub_self, Nat.sub_self, V_zero_left,
      sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 1) (fun x => V k x h)]
    ring

private theorem V_step_le_mul {k a b h : ℕ} {c : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : k - 1 ≤ a) (hb : k - 1 ≤ b)
    (hstep : ∀ i ≤ k - 1, V k (a - i) h ≤ c * V k (b - i) h) :
    V k a (h + 1) ≤ c * V k b (h + 1) := by
  have hrec (n : ℕ) (hn : n ≠ 0) : V k n (h + 1) =
      (∑ i ∈ Finset.Ico 1 (min n (k - 1)), V k (n - i) h) + 2 * V k (n - min n (k - 1)) h := by
    cases n with
    | zero => exact (hn rfl).elim
    | succ m => rfl
  rw [hrec a ha0, hrec b hb0, Nat.min_eq_right ha, Nat.min_eq_right hb,
    mul_add, Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.Ico 1 (k - 1), V k (a - i) h ≤
      ∑ i ∈ Finset.Ico 1 (k - 1), c * V k (b - i) h := by
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    exact hstep i (by omega)
  have hlast := hstep (k - 1) le_rfl
  linarith

private theorem V_mono_left (k : ℕ) :
    ∀ d h : ℕ, V k d h ≤ V k (d + 1) h := by
  intro d h
  induction h generalizing d with
  | zero =>
    simp only [V_zero_right, pow_succ]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by positivity
    linarith
  | succ h ih =>
    cases d with
    | zero =>
      rw [V_zero_left]
      exact V_one_le k 1 (h + 1)
    | succ d =>
      by_cases hle : d + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hle h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        have hpos := V_nonneg k (d + 1) h
        linarith
      · simpa only [one_mul] using
          V_step_le_mul (c := 1) (by omega) (by omega) (by omega) (by omega) fun i hi => by
            rw [show d + 2 - i = (d + 1 - i) + 1 by omega, one_mul]
            exact ih _

private theorem V_mono_right {k : ℕ} (hk : 3 ≤ k) :
    ∀ d h : ℕ, V k d h ≤ V k d (h + 1) := by
  intro d h
  induction h generalizing d with
  | zero =>
    cases d with
    | zero => simp only [V_zero_left, le_rfl]
    | succ m =>
      cases m with
      | zero =>
        rw [V_zero_right, pow_one, V_one_left (by omega)]
        norm_num
      | succ n =>
        set l := min (n + 2) (k - 1)
        have hl_ge2 : 2 ≤ l := by dsimp only [l]; omega
        change (3 / 2 : ℝ) ^ (n + 2) ≤
          (∑ i ∈ Finset.Ico 1 l, V k (n + 2 - i) 0) + 2 * V k (n + 2 - l) 0
        have hp_base : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by positivity
        by_cases hl2 : l = 2
        · rw [hl2]
          have h1 : Finset.Ico 1 2 = {1} := by decide
          rw [h1, Finset.sum_singleton, show n + 2 - 1 = n + 1 by omega,
            show n + 2 - 2 = n by omega, V_zero_right, V_zero_right]
          have hpow1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) * (3 / 2 : ℝ) ^ n := by ring
          have hpow2 : (3 / 2 : ℝ) ^ (n + 2) = (9 / 4) * (3 / 2 : ℝ) ^ n := by ring
          linarith
        · have hl3 : 3 ≤ l := by omega
          have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Ico 1 l := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_Ico]
            omega
          have hpair : ∑ i ∈ ({1, 2} : Finset ℕ), V k (n + 2 - i) 0 ≤
              ∑ i ∈ Finset.Ico 1 l, V k (n + 2 - i) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => V_nonneg k _ 0
          rw [Finset.sum_pair (by decide), show n + 2 - 1 = n + 1 by omega,
            show n + 2 - 2 = n by omega, V_zero_right, V_zero_right] at hpair
          have hlast := V_nonneg k (n + 2 - l) 0
          have hpow1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) * (3 / 2 : ℝ) ^ n := by ring
          have hpow2 : (3 / 2 : ℝ) ^ (n + 2) = (9 / 4) * (3 / 2 : ℝ) ^ n := by ring
          linarith
  | succ h ih =>
    cases d with
    | zero => simp only [V_zero_left, le_rfl]
    | succ d =>
      set l := min (d + 1) (k - 1)
      change (∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) h) + 2 * V k (d + 1 - l) h ≤
        (∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) (h + 1)) + 2 * V k (d + 1 - l) (h + 1)
      have hsum : ∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) h ≤
          ∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) (h + 1) :=
        Finset.sum_le_sum fun i _ => ih _
      have hlast := ih (d + 1 - l)
      linarith

private theorem V_le_two_mul {k : ℕ} (hk : 3 ≤ k) :
    ∀ d h : ℕ, V k (d + 1) h ≤ 2 * V k d h := by
  intro d h
  induction h generalizing d with
  | zero =>
    simp only [V_zero_right, pow_succ]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by positivity
    linarith
  | succ h ih =>
    cases d with
    | zero =>
      rw [V_one_left (by omega), V_zero_left]
      norm_num
    | succ m =>
      by_cases hle : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hle h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        have hmr := V_mono_right hk (m + 1) h
        linarith
      · exact V_step_le_mul (c := 2) (by omega) (by omega) (by omega) (by omega) fun i hi => by
          rw [show m + 2 - i = (m + 1 - i) + 1 by omega]
          exact ih _

private theorem V_three_term {k : ℕ} (hk : 3 ≤ k) :
    ∀ n h : ℕ, 2 * V k n h + V k (n + 2) h ≤ 3 * V k (n + 1) h := by
  intro n h
  induction h generalizing n with
  | zero =>
    simp only [V_zero_right]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by positivity
    have hp1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) * (3 / 2 : ℝ) ^ n := by ring
    have hp2 : (3 / 2 : ℝ) ^ (n + 2) = (9 / 4) * (3 / 2 : ℝ) ^ n := by ring
    linarith
  | succ h ih =>
    cases n with
    | zero =>
      rw [V_zero_left, V_one_left (by omega)]
      have h2 := V_le_two_mul hk 1 (h + 1)
      rw [V_one_left (by omega)] at h2
      linarith
    | succ m =>
      by_cases h1 : m + 3 ≤ k - 1
      · have hd1 := V_succ_sub_self_small (by omega : m + 2 ≤ k - 1) h
        have hd2 := V_succ_sub_self_small h1 h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hd1 hd2
        have htwo := V_le_two_mul hk (m + 1) h
        linarith
      · by_cases h2 : m + 2 = k - 1
        · have hd1 := V_succ_sub_self_small (by omega : m + 2 ≤ k - 1) h
          simp only [Nat.succ_ne_zero, ↓reduceIte] at hd1
          have hl2 : min (m + 2) (k - 1) = m + 2 := Nat.min_eq_left (by omega)
          have hl3 : min (m + 3) (k - 1) = m + 2 := by rw [← h2]; exact Nat.min_eq_right (by omega)
          have hd2 : V k (m + 3) (h + 1) - V k (m + 2) (h + 1) =
              V k (m + 2) h + V k 1 h - 2 * V k 0 h := by
            change ((∑ i ∈ Finset.Ico 1 (min (m + 3) (k - 1)), V k (m + 3 - i) h) +
                2 * V k (m + 3 - min (m + 3) (k - 1)) h) -
              ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
                2 * V k (m + 2 - min (m + 2) (k - 1)) h) = _
            rw [hl2, hl3, show m + 3 - (m + 2) = 1 by omega, Nat.sub_self]
            have hsum_tel : (∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 3 - i) h) -
                (∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 2 - i) h) =
                V k (m + 2) h - V k 1 h := by
              have hleft : ∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 3 - i) h =
                  V k (m + 2) h + ∑ j ∈ Finset.Ico 1 (m + 1), V k (m + 2 - j) h :=
                sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 2) (fun x => V k x h)
              have hright : ∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 2 - i) h =
                  (∑ j ∈ Finset.Ico 1 (m + 1), V k (m + 2 - j) h) + V k 1 h := by
                rw [Finset.sum_Ico_succ_top (by omega) (fun i => V k (m + 2 - i) h),
                  show m + 2 - (m + 1) = 1 by omega]
              rw [hleft, hright]
              ring
            linarith
          have hv1 : V k 1 h ≤ 2 * V k 0 h := V_le_two_mul hk 0 h
          have htwo := V_le_two_mul hk (m + 1) h
          linarith
        · have hl1 : min (m + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
          have hl2 : min (m + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
          have hl3 : min (m + 3) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
          change 2 * ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) h) +
              2 * V k (m + 1 - min (m + 1) (k - 1)) h) +
            ((∑ i ∈ Finset.Ico 1 (min (m + 3) (k - 1)), V k (m + 3 - i) h) +
              2 * V k (m + 3 - min (m + 3) (k - 1)) h) ≤
            3 * ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
              2 * V k (m + 2 - min (m + 2) (k - 1)) h)
          rw [hl1, hl2, hl3, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
          have hsum : (∑ i ∈ Finset.Ico 1 (k - 1), 2 * V k (m + 1 - i) h) +
              (∑ i ∈ Finset.Ico 1 (k - 1), V k (m + 3 - i) h) ≤
              ∑ i ∈ Finset.Ico 1 (k - 1), 3 * V k (m + 2 - i) h := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun i hi => ?_
            simp only [Finset.mem_Ico] at hi
            rw [show m + 3 - i = (m + 1 - i) + 2 by omega,
              show m + 2 - i = (m + 1 - i) + 1 by omega]
            exact ih (m + 1 - i)
          have hlast : 2 * V k (m + 1 - (k - 1)) h + V k (m + 3 - (k - 1)) h ≤
              3 * V k (m + 2 - (k - 1)) h := by
            rw [show m + 3 - (k - 1) = (m + 1 - (k - 1)) + 2 by omega,
              show m + 2 - (k - 1) = (m + 1 - (k - 1)) + 1 by omega]
            exact ih _
          linarith

private theorem V_one_mul_three_halves {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    V k (n + 1) 1 = (3 / 2 : ℝ) * V k n 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hl1 : min (m + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
  have hl2 : min (m + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
  change (∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) 0) +
      2 * V k (m + 2 - min (m + 2) (k - 1)) 0 =
    (3 / 2 : ℝ) * ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) 0) +
      2 * V k (m + 1 - min (m + 1) (k - 1)) 0)
  rw [hl1, hl2, mul_add, Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.Ico 1 (k - 1), V k (m + 2 - i) 0 =
      ∑ i ∈ Finset.Ico 1 (k - 1), (3 / 2 : ℝ) * V k (m + 1 - i) 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    rw [show m + 2 - i = (m + 1 - i) + 1 by omega, V_zero_right, V_zero_right, pow_succ]
    ring
  have hlast : V k (m + 2 - (k - 1)) 0 = (3 / 2 : ℝ) * V k (m + 1 - (k - 1)) 0 := by
    rw [show m + 2 - (k - 1) = (m + 1 - (k - 1)) + 1 by omega, V_zero_right, V_zero_right,
      pow_succ]
    ring
  rw [hsum, hlast]
  ring

private theorem pow_le_V_one {k : ℕ} (hk : 3 ≤ k) :
    ∀ n : ℕ, 2 ≤ n → (3 / 2 : ℝ) ^ (n + 1) ≤ V k n 1 := by
  intro n hn
  induction hn with
  | refl =>
    have hl : min 2 (k - 1) = 2 := Nat.min_eq_left (by omega)
    change (3 / 2 : ℝ) ^ 3 ≤
      (∑ i ∈ Finset.Ico 1 (min 2 (k - 1)), V k (2 - i) 0) + 2 * V k (2 - min 2 (k - 1)) 0
    rw [hl, show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, V_zero_right, V_zero_right]
    norm_num
  | @step m hm ih =>
    change (3 / 2 : ℝ) ^ (m + 2) ≤ V k (m + 1) 1
    have hm_ge2 : 2 ≤ m := hm
    by_cases hsmall : m + 1 ≤ k - 1
    · have hm0 : m ≠ 0 := by omega
      have hdiff := V_succ_sub_self_small hsmall 0
      simp only [Nat.zero_add, hm0, ↓reduceIte, V_zero_right] at hdiff
      have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ m := by positivity
      have hp1 : (3 / 2 : ℝ) ^ (m + 1) = (3 / 2) * (3 / 2 : ℝ) ^ m := by ring
      have hp2 : (3 / 2 : ℝ) ^ (m + 2) = (9 / 4) * (3 / 2 : ℝ) ^ m := by ring
      linarith
    · have hmul := V_one_mul_three_halves hk (by omega : k - 1 ≤ m)
      have hp2 : (3 / 2 : ℝ) ^ (m + 2) = (3 / 2) * (3 / 2 : ℝ) ^ (m + 1) := by ring
      linarith

private theorem V_step_ineq {k : ℕ} (hk : 3 ≤ k) :
    ∀ n h : ℕ, V k (n + 1) h + 2 * V k n (h + 1) ≤ 2 * V k (n + 1) (h + 1) := by
  intro n h
  induction h generalizing n with
  | zero =>
    cases n with
    | zero =>
      rw [V_zero_right, pow_one, V_zero_left, V_one_left (by omega)]
      norm_num
    | succ m =>
      change V k (m + 2) 0 + 2 * V k (m + 1) 1 ≤ 2 * V k (m + 2) 1
      rw [V_zero_right]
      by_cases hsmall : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hsmall 0
        simp only [Nat.zero_add, Nat.succ_ne_zero, ↓reduceIte, V_zero_right] at hdiff
        have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ (m + 1) := by positivity
        have hp1 : (3 / 2 : ℝ) ^ (m + 2) = (3 / 2) * (3 / 2 : ℝ) ^ (m + 1) := by ring
        linarith
      · have hm_ge : k - 1 ≤ m + 1 := by omega
        have hmul := V_one_mul_three_halves hk hm_ge
        have hpow := pow_le_V_one hk (m + 1) (by omega)
        linarith
  | succ h ih =>
    cases n with
    | zero =>
      rw [V_one_left (by omega), V_zero_left, V_one_left (by omega)]
      norm_num
    | succ m =>
      by_cases hsmall : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hsmall (h + 1)
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        have htwo := V_le_two_mul hk (m + 1) (h + 1)
        linarith
      · have hl1 : min (m + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        have hl2 : min (m + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        change ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
            2 * V k (m + 2 - min (m + 2) (k - 1)) h) +
          2 * ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) (h + 1)) +
            2 * V k (m + 1 - min (m + 1) (k - 1)) (h + 1)) ≤
          2 * ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) (h + 1)) +
            2 * V k (m + 2 - min (m + 2) (k - 1)) (h + 1))
        rw [hl1, hl2, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
        have hsum : (∑ i ∈ Finset.Ico 1 (k - 1), V k (m + 2 - i) h) +
            (∑ i ∈ Finset.Ico 1 (k - 1), 2 * V k (m + 1 - i) (h + 1)) ≤
            ∑ i ∈ Finset.Ico 1 (k - 1), 2 * V k (m + 2 - i) (h + 1) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [Finset.mem_Ico] at hi
          rw [show m + 2 - i = (m + 1 - i) + 1 by omega]
          exact ih (m + 1 - i)
        have hlast : V k (m + 2 - (k - 1)) h + 2 * V k (m + 1 - (k - 1)) (h + 1) ≤
            2 * V k (m + 2 - (k - 1)) (h + 1) := by
          rw [show m + 2 - (k - 1) = (m + 1 - (k - 1)) + 1 by omega]
          exact ih _
        linarith

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

/-- At full root budget `r = k ≥ 2`, `W k k d h` coincides with `V k d h`. -/
theorem W_eq_V {k : ℕ} (hk : 2 ≤ k) (d h : ℕ) : W k k d h = V k d h := by
  cases h with
  | zero => rw [W, V_zero_right]
  | succ h =>
    unfold W
    have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp only [hk0, hk1, ↓reduceIte]
    cases d with
    | zero => simp only [↓reduceIte, V_zero_left]
    | succ d => simp only [Nat.succ_ne_zero, ↓reduceIte]; rfl

/-- For positive root budget `r ≥ 1`, `1 ≤ W k r d h`. -/
theorem W_one_le {k r : ℕ} (hr : 1 ≤ r) (d h : ℕ) : (1 : ℝ) ≤ W k r d h := by
  cases h with
  | zero =>
    unfold W
    exact one_le_pow₀ (by norm_num)
  | succ h =>
    unfold W
    have hr0 : r ≠ 0 := by omega
    simp only [hr0, ↓reduceIte]
    by_cases hr1 : r = 1
    · simp only [hr1, ↓reduceIte]; exact V_one_le k d h
    · simp only [hr1, ↓reduceIte]
      by_cases hd0 : d = 0
      · simp only [hd0, ↓reduceIte, le_rfl]
      · simp only [hd0, ↓reduceIte]
        have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico 1 (min d (r - 1)), V k (d - i) h :=
          Finset.sum_nonneg fun i _ => V_nonneg k _ h
        have hlast := V_one_le k (d - min d (r - 1)) h
        linarith


/-- `W k r d h` is monotone in the interval-tree depth `d`. -/
theorem W_mono_left (k : ℕ) :
    ∀ r d h : ℕ, W k r d h ≤ W k r (d + 1) h := by
  intro r d h
  cases h with
  | zero =>
    simp only [W, pow_succ]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by positivity
    linarith
  | succ h =>
    by_cases hr0 : r = 0
    · simp only [W, hr0, ↓reduceIte, le_rfl]
    · by_cases hr1 : r = 1
      · simp only [W, hr1, ↓reduceIte]
        exact V_mono_left k d h
      · simp only [W, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero]
        by_cases hd0 : d = 0
        · subst hd0
          have hl : min 1 (r - 1) = 1 := Nat.min_eq_left (by omega)
          simp only [↓reduceIte, hl, Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self,
            V_zero_left]
          norm_num
        · simp only [hd0, ↓reduceIte]
          by_cases hsmall : d + 1 ≤ r - 1
          · have hl1 : min d (r - 1) = d := Nat.min_eq_left (by omega)
            have hl2 : min (d + 1) (r - 1) = d + 1 := Nat.min_eq_left hsmall
            rw [hl1, hl2, Nat.sub_self, Nat.sub_self, V_zero_left,
              sum_Ico_one_succ_shift (l := d) (by omega) d (fun x => V k x h)]
            have hp := V_nonneg k d h
            linarith
          · have hl1 : min d (r - 1) = r - 1 := Nat.min_eq_right (by omega)
            have hl2 : min (d + 1) (r - 1) = r - 1 := Nat.min_eq_right (by omega)
            rw [hl1, hl2]
            have hsum : ∑ i ∈ Finset.Ico 1 (r - 1), V k (d - i) h ≤
                ∑ i ∈ Finset.Ico 1 (r - 1), V k (d + 1 - i) h := by
              refine Finset.sum_le_sum fun i hi => ?_
              simp only [Finset.mem_Ico] at hi
              rw [show d + 1 - i = (d - i) + 1 by omega]
              exact V_mono_left k _ h
            have hlast : V k (d - (r - 1)) h ≤ V k (d + 1 - (r - 1)) h := by
              rw [show d + 1 - (r - 1) = (d - (r - 1)) + 1 by omega]
              exact V_mono_left k _ h
            linarith

/-- Splitting off a direct child subtree at depth `1` satisfies
`W k (r - 1) d (h + 1) + V k d h = W k r (d + 1) (h + 1)`. -/
theorem W_split_depth_one {k r d h : ℕ} (hr : 2 ≤ r) :
    W k (r - 1) d (h + 1) + V k d h = W k r (d + 1) (h + 1) := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  by_cases hr2 : r = 2
  · subst hr2
    have hl : min (d + 1) (2 - 1) = 1 := Nat.min_eq_right (by omega)
    simp only [W, Nat.add_sub_cancel, ↓reduceIte, hr0, hr1, Nat.succ_ne_zero, hl,
      Finset.Ico_self, Finset.sum_empty, zero_add]
    ring
  · have hr_m1_0 : r - 1 ≠ 0 := by omega
    have hr_m1_1 : r - 1 ≠ 1 := by omega
    cases d with
    | zero =>
      have hl : min 1 (r - 1) = 1 := Nat.min_eq_left (by omega)
      simp only [W, hr_m1_0, hr_m1_1, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero, hl,
        Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self, V_zero_left]
      norm_num
    | succ m =>
      change W k (r - 1) (m + 1) (h + 1) + V k (m + 1) h = W k r (m + 2) (h + 1)
      simp only [W, hr_m1_0, hr_m1_1, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero]
      rw [show r - 1 - 1 = r - 2 by omega]
      set l' := min (m + 1) (r - 2)
      have hl : min (m + 2) (r - 1) = l' + 1 := by
        rw [show r - 1 = (r - 2) + 1 by omega]
        exact Nat.succ_min_succ (m + 1) (r - 2)
      have hl'_pos : 1 ≤ l' := by dsimp only [l']; omega
      rw [hl, show m + 2 - (l' + 1) = m + 1 - l' by omega,
        sum_Ico_one_succ_shift hl'_pos (m + 1) (fun x => V k x h)]
      ring

/-- Splitting off a proper descendant subtree at depth `≥ 2` satisfies
`W k r d (h + 2) + V k d h ≤ W k r (d + 1) (h + 2)` for `k ≥ 3` and `2 ≤ r ≤ k`. -/
theorem W_split_depth_two {k r d h : ℕ} (hk : 3 ≤ k) (hr : 2 ≤ r) (_hrk : r ≤ k) :
    W k r d (h + 2) + V k d h ≤ W k r (d + 1) (h + 2) := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  cases d with
  | zero =>
    have hl : min 1 (r - 1) = 1 := Nat.min_eq_left (by omega)
    simp only [W, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero, hl, Finset.Ico_self, Finset.sum_empty,
      zero_add, Nat.sub_self, V_zero_left]
    norm_num
  | succ m =>
    change W k r (m + 1) (h + 2) + V k (m + 1) h ≤ W k r (m + 2) (h + 2)
    simp only [W, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero]
    by_cases hsmall : m + 2 ≤ r - 1
    · have hl1 : min (m + 1) (r - 1) = m + 1 := Nat.min_eq_left (by omega)
      have hl2 : min (m + 2) (r - 1) = m + 2 := Nat.min_eq_left hsmall
      rw [hl1, hl2, Nat.sub_self, Nat.sub_self, V_zero_left,
        sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 1) (fun x => V k x (h + 1))]
      have hmr := V_mono_right hk (m + 1) h
      linarith
    · obtain ⟨u, hu_eq⟩ : ∃ u, r - 1 = u + 1 := ⟨r - 2, by omega⟩
      have hu_le : u + 1 ≤ m + 1 := by omega
      have hl1 : min (m + 1) (r - 1) = u + 1 := by rw [hu_eq]; exact Nat.min_eq_right hu_le
      have hl2 : min (m + 2) (r - 1) = u + 1 := by rw [hu_eq]; exact Nat.min_eq_right (by omega)
      rw [hl1, hl2]
      have htel_sum : (∑ i ∈ Finset.Ico 1 (u + 1), V k (m + 2 - i) (h + 1)) +
          2 * V k (m + 2 - (u + 1)) (h + 1) -
          ((∑ i ∈ Finset.Ico 1 (u + 1), V k (m + 1 - i) (h + 1)) +
            2 * V k (m + 1 - (u + 1)) (h + 1)) =
          V k (m + 1) (h + 1) + V k (m + 2 - (u + 1)) (h + 1) -
            2 * V k (m + 1 - (u + 1)) (h + 1) := by
        cases u with
        | zero =>
          rw [Finset.Ico_self, Finset.sum_empty, Finset.sum_empty, show m + 2 - 1 = m + 1 by omega]
          ring
        | succ u' =>
          have hleft :=
            sum_Ico_one_succ_shift (l := u' + 1) (by omega) (m + 1) (fun x => V k x (h + 1))
          have hright : ∑ i ∈ Finset.Ico 1 (u' + 2), V k (m + 1 - i) (h + 1) =
              (∑ j ∈ Finset.Ico 1 (u' + 1), V k (m + 1 - j) (h + 1)) +
                V k (m + 2 - (u' + 2)) (h + 1) := by
            rw [Finset.sum_Ico_succ_top (by omega) (fun i => V k (m + 1 - i) (h + 1)),
              show m + 1 - (u' + 1) = m + 2 - (u' + 2) by omega]
          rw [hleft, hright]
          ring
      set a := m - u
      have ha_eq1 : m + 2 - (u + 1) = a + 1 := by omega
      have ha_eq2 : m + 1 - (u + 1) = a := by omega
      have ha_eq3 : m + 1 = a + u + 1 := by omega
      have hchain : ∀ w : ℕ,
          2 * (V k (a + w + 1) (h + 1) - V k (a + w) (h + 1)) ≤
            V k (a + w + 1) (h + 1) + V k (a + 1) (h + 1) - 2 * V k a (h + 1) := by
        intro w
        induction w with
        | zero =>
          simp only [Nat.add_zero]
          linarith
        | succ w ih =>
          have h3 := V_three_term hk (a + w) (h + 1)
          rw [show a + w + 2 = a + w + 1 + 1 by omega] at h3
          rw [← Nat.add_assoc a w 1]
          linarith
      have hchain_u := hchain u
      have hstep_last := V_step_ineq hk (a + u) h
      rw [ha_eq1, ha_eq2, ha_eq3] at htel_sum ⊢
      linarith


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
