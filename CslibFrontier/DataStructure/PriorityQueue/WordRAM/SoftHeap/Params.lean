/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Soft-Heap Rank Parameters, Corruption Bound, and Item Potential

Single-heap Word-RAM parameter and potential step toward #8624, after [Chazelle2000],
Theorem 1.1 and Section 5.1, Lemmas 5.1–5.2 (NECI TR 99-097 preprint, pp. 2, 12–13), and
[PettieRamachandran2002], Section 2.4, p. 19, Lemma 2.2. Supports `insert`, `extractMin`, and
`collectCorrupted` without `meld` or arbitrary-handle `delete`. The dismantling-free
binary-tree `defill` parameterization (`targetSize r k = 2 ^ ((k - r + 1) / 2)`), the
`12 / 2 ^ r` `sizeCap` recurrence, `rankThresholdForEps ε` for arbitrary `0 < ε : ℚ` (extending
Chazelle Theorem 1.1's `0 < ε ≤ 1 / 2` and PR02 Lemma 2.2's `0 < ε < 1 / 2`), and the `+(r : ℚ)`
baseline credit in `itemPhi` are this module's self-contained Word-RAM adaptation.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.rankThresholdForEps`: rank threshold
  sufficient to guarantee corruption fraction at most `ε : ℚ`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shFuelBound`: sufficient Word-RAM `defill`
  loop fuel `(50 * r + 100) * (maxItems + 1)`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.targetSize`, `sizeCap`: target item-list
  lower bound and capacity cap at rank `k` under threshold `r`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.itemPhi`: closed-form rational potential
  assigned to each item by threshold `r` and rank `k`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.corrupt_sum_bound`:
  `2 ^ r * ∑ k ∈ Finset.Icc (r + 1) K, C k * sizeCap r k ≤ 12 * C 0`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.rat_le_eps_mul_of_pow_mul_le`,
  `corrupt_sum_bound_eps`: rational corruption bound at threshold `rankThresholdForEps ε`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.itemPhi_sub_succ`: exact telescoping rank
  potential drop `itemPhi r k - itemPhi r (k + 1) = 1 / targetSize r k`.

## References

* [B. Chazelle, *The Soft Heap: An Approximate Priority Queue with Optimal Error Rate*,
  Journal of the ACM 47(6), 2000][Chazelle2000], Theorem 1.1 and Section 5.1, Lemmas 5.1–5.2
  (NECI TR 99-097 preprint, pp. 2, 12–13).
* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002], Section 2.4, p. 19, Lemma 2.2.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-- Rank threshold achieving error rate at most `ε : ℚ` (using `12 / 2 ^ r ≤ ε`). -/
@[expose] def rankThresholdForEps (ε : ℚ) : ℕ :=
  Nat.log 2 (Nat.ceil (12 / ε)) + 1

/-- Sufficient Word-RAM loop fuel for soft-heap operations with threshold `r` and capacity
`maxItems`. -/
@[expose] def shFuelBound (r maxItems : ℕ) : ℕ :=
  (50 * r + 100) * (maxItems + 1)

/-- Lower-bound exponent check for `rankThresholdForEps`: `12 / ε ≤ 2 ^ rankThresholdForEps ε`. -/
theorem twelve_div_le_two_pow_rankThresholdForEps (ε : ℚ) :
    12 / ε ≤ (2 ^ rankThresholdForEps ε : ℚ) := by
  have h1 : 12 / ε ≤ (Nat.ceil (12 / ε) : ℚ) := Nat.le_ceil _
  have h2q : (Nat.ceil (12 / ε) : ℚ) < (2 ^ rankThresholdForEps ε : ℚ) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide) (Nat.ceil (12 / ε))
  linarith

/-- Minimum target item-list length `targetSize r k` of a non-leaf soft-heap node of rank `k`
under corruption threshold `r`. -/
@[expose] def targetSize (r k : ℕ) : ℕ :=
  if k ≤ r then 1 else 2 ^ ((k - r + 1) / 2)

/-- Target size is always positive. -/
theorem targetSize_pos (r k : ℕ) : 0 < targetSize r k := by
  dsimp only [targetSize]
  split_ifs <;> positivity

/-- Target size equals `1` for all ranks at most `r`. -/
@[simp] theorem targetSize_le_threshold {r k : ℕ} (hk : k ≤ r) : targetSize r k = 1 := by
  simp [targetSize, hk]

/-- Recurrence for `targetSize r (k + 1)`. -/
theorem targetSize_succ (r k : ℕ) :
    targetSize r (k + 1) =
      if k + 1 ≤ r then 1
      else if (k + 1 - r) % 2 = 1 then targetSize r k + targetSize r k
      else targetSize r k := by
  by_cases hk : k + 1 ≤ r
  · simp [targetSize, hk]
  · by_cases hkr : k = r
    · subst hkr
      simp only [targetSize, le_rfl, ↓reduceIte, hk, Nat.add_sub_cancel_left]
      norm_num
    · have hne : ¬ (k ≤ r) := by omega
      by_cases hmod : (k + 1 - r) % 2 = 1 <;>
        simp only [targetSize, hk, hne, hmod, ↓reduceIte]
      · have hq : (k + 1 - r + 1) / 2 = (k - r + 1) / 2 + 1 := by omega
        rw [hq, Nat.pow_succ, Nat.mul_two]
      · have hq : (k + 1 - r + 1) / 2 = (k - r + 1) / 2 := by omega
        rw [hq]

/-- `targetSize r k` is even whenever `r < k`. -/
theorem targetSize_even_of_gt {r k : ℕ} (hk : r < k) : 2 ∣ targetSize r k := by
  simp only [targetSize, Nat.not_le.mpr hk, ↓reduceIte]
  exact dvd_pow_self 2 (by omega)

private theorem targetSize_even_step (r t : ℕ) : targetSize r (r + 2 * t) = 2 ^ t := by
  dsimp only [targetSize]
  split_ifs with hle
  · have : t = 0 := by omega
    subst this; rfl
  · have hq : (r + 2 * t - r + 1) / 2 = t := by omega
    rw [hq]

private theorem targetSize_odd_step (r t : ℕ) : targetSize r (r + 2 * t + 1) = 2 * 2 ^ t := by
  have hne : ¬ (r + 2 * t + 1 ≤ r) := by omega
  have hq : (r + 2 * t + 1 - r + 1) / 2 = t + 1 := by omega
  simp only [targetSize, hne, ↓reduceIte]
  rw [hq, Nat.pow_succ, Nat.mul_comm]

/-- Every rank `k` satisfies `k ≤ targetSize r k + r`. -/
theorem rank_le_targetSize_add (r k : ℕ) : k ≤ targetSize r k + r := by
  have hpow : ∀ t : ℕ, 2 * t ≤ 2 ^ t := fun t => by
    induction t with
    | zero => omega
    | succ t ih =>
      rw [Nat.pow_succ]
      have := Nat.two_pow_pos t
      omega
  by_cases hk : k ≤ r
  · omega
  · rcases Nat.even_or_odd (k - r) with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hk' : k = r + 2 * t := by omega
      have := hpow t
      rw [hk', targetSize_even_step]; omega
    · have hk' : k = r + 2 * t + 1 := by omega
      have := hpow t
      have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
      rw [hk', targetSize_odd_step]; omega

/-- Maximum number of items stored at a single soft-heap node of rank `k` under threshold `r`. -/
@[expose] def sizeCap (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => targetSize r (k + 1) - 1 + sizeCap r k

/-- `sizeCap r k = 1` for all `k ≤ r`. -/
@[simp] theorem sizeCap_eq_one_of_le {r k : ℕ} (hk : k ≤ r) : sizeCap r k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sizeCap, targetSize_le_threshold hk, ih (by omega)]

private theorem sizeCap_even_odd_le (r t : ℕ) :
    sizeCap r (r + 2 * t) ≤ 4 * 2 ^ t ∧ sizeCap r (r + 2 * t + 1) ≤ 6 * 2 ^ t := by
  induction t with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.mul_one, sizeCap,
      targetSize_odd_step r 0, sizeCap_eq_one_of_le le_rfl]
    omega
  | succ t ih =>
    have h1 : r + 2 * (t + 1) = (r + 2 * t + 1) + 1 := by omega
    have hts1 : targetSize r (r + 2 * (t + 1)) = 2 * 2 ^ t := by
      rw [targetSize_even_step, Nat.pow_succ, Nat.mul_comm]
    have hts2 : targetSize r (r + 2 * (t + 1) + 1) = 4 * 2 ^ t := by
      rw [targetSize_odd_step, Nat.pow_succ]; ring
    have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
    have heven : sizeCap r (r + 2 * (t + 1)) ≤ 4 * 2 ^ (t + 1) := by
      rw [h1, sizeCap, ← h1, hts1, Nat.pow_succ]; omega
    refine ⟨heven, ?_⟩
    rw [sizeCap, hts2, Nat.pow_succ]; omega

private theorem sizeCap_le_four_mul_targetSize (r k : ℕ) : sizeCap r k ≤ 4 * targetSize r k := by
  by_cases hk : k ≤ r
  · rw [sizeCap_eq_one_of_le hk, targetSize_le_threshold hk]; omega
  · let d := k - r
    rcases Nat.even_or_odd d with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hk' : k = r + 2 * t := by omega
      rw [hk', targetSize_even_step]
      exact (sizeCap_even_odd_le r t).1
    · have hk' : k = r + 2 * t + 1 := by omega
      rw [hk', targetSize_odd_step]
      have hsc := (sizeCap_even_odd_le r t).2
      omega

private def corruptPot (r k : ℕ) : ℕ :=
  if (k - r) % 2 = 0 then 3 * targetSize r k else 2 * targetSize r k

private theorem targetSize_add_corruptPot_le {r k : ℕ} (hk : r ≤ k) :
    targetSize r (k + 1) + corruptPot r (k + 1) = 2 * corruptPot r k := by
  rcases Nat.even_or_odd (k - r) with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hk' : k = r + 2 * t := by omega
    rw [hk']
    have hmod0 : (r + 2 * t - r) % 2 = 0 := by omega
    have hmod1 : (r + 2 * t + 1 - r) % 2 ≠ 0 := by omega
    simp only [corruptPot, hmod0, hmod1, ↓reduceIte, targetSize_even_step, targetSize_odd_step]
    omega
  · have hk' : k = r + 2 * t + 1 := by omega
    rw [hk']
    have hts1 : targetSize r (r + 2 * t + 1 + 1) = 2 * 2 ^ t := by
      have hsum : r + 2 * t + 1 + 1 = r + 2 * (t + 1) := by omega
      rw [hsum, targetSize_even_step, Nat.pow_succ, Nat.mul_comm]
    have hmod0 : (r + 2 * t + 1 - r) % 2 ≠ 0 := by omega
    have hmod1 : (r + 2 * t + 1 + 1 - r) % 2 = 0 := by omega
    simp only [corruptPot, hmod0, hmod1, ↓reduceIte, targetSize_odd_step, hts1]
    omega

/-- General geometric corruption bound: if `2 * C (k + 1) ≤ C k` for all `k`, then
`2 ^ r * ∑ k ∈ Finset.Icc (r + 1) K, C k * sizeCap r k ≤ 12 * C 0`. -/
theorem corrupt_sum_bound (r : ℕ) (C : ℕ → ℕ) (K : ℕ)
    (hstep : ∀ k, 2 * C (k + 1) ≤ C k) :
    2 ^ r * (∑ k ∈ Finset.Icc (r + 1) K, C k * sizeCap r k) ≤ 12 * C 0 := by
  have hts_bound (j : ℕ) (hj : r ≤ j) :
      (∑ k ∈ Finset.Icc (r + 1) j, C k * targetSize r k) + C j * corruptPot r j ≤ 3 * C r := by
    induction j with
    | zero =>
      have hr0 : r = 0 := by omega
      subst hr0
      simp [corruptPot, targetSize, Nat.mul_comm]
    | succ j ih =>
      by_cases hjr : j + 1 = r
      · subst hjr
        simp [corruptPot, targetSize, Nat.mul_comm]
      · have hj' : r ≤ j := by omega
        have hih := ih hj'
        have hsplit : Finset.Icc (r + 1) (j + 1) = insert (j + 1) (Finset.Icc (r + 1) j) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hsplit, Finset.sum_insert (by simp)]
        have hmul : C (j + 1) * (targetSize r (j + 1) + corruptPot r (j + 1)) ≤
            C j * corruptPot r j := by
          rw [targetSize_add_corruptPot_le hj']
          calc C (j + 1) * (2 * corruptPot r j)
              = (2 * C (j + 1)) * corruptPot r j := by ring
            _ ≤ C j * corruptPot r j := Nat.mul_le_mul_right _ (hstep j)
        rw [Nat.mul_add] at hmul
        omega
  have hpow : 2 ^ r * C r ≤ C 0 := Nat.pow_mul_le_of_step hstep r
  by_cases hK : K ≤ r
  · simp [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_of_le hK)]
  · have hsum_ts : ∑ k ∈ Finset.Icc (r + 1) K, C k * targetSize r k ≤ 3 * C r :=
      le_trans (Nat.le_add_right _ _) (hts_bound K (by omega))
    have hsum_sc : ∑ k ∈ Finset.Icc (r + 1) K, C k * sizeCap r k ≤ 12 * C r := by
      calc ∑ k ∈ Finset.Icc (r + 1) K, C k * sizeCap r k
          ≤ ∑ k ∈ Finset.Icc (r + 1) K, C k * (4 * targetSize r k) :=
            Finset.sum_le_sum fun k _ =>
              Nat.mul_le_mul_left _ (sizeCap_le_four_mul_targetSize r k)
        _ = 4 * ∑ k ∈ Finset.Icc (r + 1) K, C k * targetSize r k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring
        _ ≤ 4 * (3 * C r) := Nat.mul_le_mul_left 4 hsum_ts
        _ = 12 * C r := by ring
    calc 2 ^ r * (∑ k ∈ Finset.Icc (r + 1) K, C k * sizeCap r k)
        ≤ 2 ^ r * (12 * C r) := Nat.mul_le_mul_left _ hsum_sc
      _ = 12 * (2 ^ r * C r) := by ring
      _ ≤ 12 * C 0 := Nat.mul_le_mul_left 12 hpow

/-- Converts an integer corruption bound `2 ^ rankThresholdForEps ε * c ≤ 12 * n` into
`(c : ℚ) ≤ ε * (n : ℚ)` for any `0 < ε`. -/
theorem rat_le_eps_mul_of_pow_mul_le {ε : ℚ} (hε : 0 < ε) {c n : ℕ}
    (h : 2 ^ rankThresholdForEps ε * c ≤ 12 * n) : (c : ℚ) ≤ ε * (n : ℚ) := by
  have hb_q : (2 ^ rankThresholdForEps ε : ℚ) * (c : ℚ) ≤ 12 * (n : ℚ) := by
    exact_mod_cast h
  have hpow_pos : (0 : ℚ) < (2 ^ rankThresholdForEps ε : ℚ) := by positivity
  have h12 : 12 ≤ (2 ^ rankThresholdForEps ε : ℚ) * ε :=
    (div_le_iff₀ hε).mp (twelve_div_le_two_pow_rankThresholdForEps ε)
  have hmul : (2 ^ rankThresholdForEps ε : ℚ) * (c : ℚ) ≤
      (2 ^ rankThresholdForEps ε : ℚ) * (ε * (n : ℚ)) := by
    calc (2 ^ rankThresholdForEps ε : ℚ) * (c : ℚ) ≤ 12 * (n : ℚ) := hb_q
      _ ≤ ((2 ^ rankThresholdForEps ε : ℚ) * ε) * (n : ℚ) :=
          mul_le_mul_of_nonneg_right h12 (Nat.cast_nonneg _)
      _ = (2 ^ rankThresholdForEps ε : ℚ) * (ε * (n : ℚ)) := by ring
  exact (mul_le_mul_iff_right₀ hpow_pos).mp hmul

/-- Rational error-rate specialization: setting `r = rankThresholdForEps ε` for any `0 < ε` yields
total capacity above rank `r` at most `ε * C 0`. -/
theorem corrupt_sum_bound_eps {ε : ℚ} (hε : 0 < ε) (C : ℕ → ℕ) (K : ℕ)
    (hstep : ∀ k, 2 * C (k + 1) ≤ C k) :
    ((∑ k ∈ Finset.Icc (rankThresholdForEps ε + 1) K,
        C k * sizeCap (rankThresholdForEps ε) k : ℕ) : ℚ) ≤ ε * (C 0 : ℚ) :=
  rat_le_eps_mul_of_pow_mul_le hε (corrupt_sum_bound (rankThresholdForEps ε) C K hstep)

/-- Closed-form amortized item rank potential `itemPhi r k`, including an `(r : ℚ)` credit baseline
that pays for root-list suffix-min repairs so `shExtractMin` stays `O(1)` independently of `r`. -/
@[expose] def itemPhi (r k : ℕ) : ℚ :=
  (r : ℚ) +
    if k ≤ r then ((r + 3 : ℕ) : ℚ) - (k : ℚ)
    else if (k - r) % 2 = 1 then 4 / (targetSize r k : ℚ)
    else 3 / (targetSize r k : ℚ)

/-- Item potential is always at least the baseline credit `(r : ℚ)`. -/
theorem itemPhi_ge_threshold (r k : ℕ) : (r : ℚ) ≤ itemPhi r k := by
  dsimp only [itemPhi]
  split_ifs with h1 h2
  · have : (k : ℚ) ≤ r := by exact_mod_cast h1
    push_cast; linarith
  all_goals exact le_add_of_nonneg_right (by positivity)

/-- Item potential is always non-negative. -/
theorem itemPhi_nonneg (r k : ℕ) : 0 ≤ itemPhi r k :=
  le_trans (Nat.cast_nonneg r) (itemPhi_ge_threshold r k)

/-- Initial item potential at rank `0` equals `2 * r + 3`. -/
@[simp] theorem itemPhi_zero (r : ℕ) : itemPhi r 0 = 2 * (r : ℚ) + 3 := by
  simp only [itemPhi, Nat.zero_le, ↓reduceIte, Nat.cast_zero, sub_zero, Nat.cast_add,
    Nat.cast_ofNat]
  ring

/-- Every item potential at threshold `r` is bounded above by `2 * r + 3`. -/
theorem itemPhi_le_zero (r k : ℕ) : itemPhi r k ≤ 2 * (r : ℚ) + 3 := by
  dsimp only [itemPhi]
  split_ifs with h1 h2
  · have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    push_cast; linarith
  · have hpos := targetSize_pos r k
    have heven := targetSize_even_of_gt (by omega : r < k)
    have h2ts : (2 : ℚ) ≤ targetSize r k := by exact_mod_cast (by omega : 2 ≤ targetSize r k)
    have hdiv2 : 4 / (targetSize r k : ℚ) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  · have h1q : (1 : ℚ) ≤ targetSize r k := by exact_mod_cast targetSize_pos r k
    have hdiv : 3 / (targetSize r k : ℚ) ≤ 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith

/-- Exact telescoping drop `itemPhi r k - itemPhi r (k + 1) = 1 / targetSize r k`. -/
theorem itemPhi_sub_succ (r k : ℕ) :
    itemPhi r k - itemPhi r (k + 1) = 1 / (targetSize r k : ℚ) := by
  by_cases hlt : k < r
  · have hk : k ≤ r := by omega
    have hk1 : k + 1 ≤ r := by omega
    simp only [itemPhi, hk, hk1, ↓reduceIte, targetSize_le_threshold hk, Nat.cast_one]
    push_cast
    ring
  · by_cases hkr : k = r
    · subst hkr
      have hts0 : (targetSize k k : ℚ) = 1 := by simp
      have hts1 : targetSize k (k + 1) = 2 := by simpa using targetSize_odd_step k 0
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      have hm : (k + 1 - k) % 2 = 1 := by omega
      simp only [itemPhi, le_rfl, ↓reduceIte, hk1, hm, hts0, hts1]
      push_cast
      norm_num
    · have hne : ¬ (k ≤ r) := by omega
      have hne1 : ¬ (k + 1 ≤ r) := by omega
      rcases Nat.even_or_odd (k - r) with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hk' : k = r + 2 * t := by omega
        have hmod : (k - r) % 2 ≠ 1 := by omega
        have hmod1 : (k + 1 - r) % 2 = 1 := by omega
        simp only [itemPhi, hne, hne1, hmod, hmod1, ↓reduceIte]
        rw [hk', targetSize_even_step, targetSize_odd_step]
        push_cast
        field_simp
        ring
      · have hk' : k = r + 2 * t + 1 := by omega
        have hmod : (k - r) % 2 = 1 := by omega
        have hmod1 : (k + 1 - r) % 2 ≠ 1 := by omega
        have hts1 : targetSize r (k + 1) = 2 * 2 ^ t := by
          have hsum : r + 2 * t + 1 + 1 = r + 2 * (t + 1) := by omega
          rw [hk', hsum, targetSize_even_step, Nat.pow_succ, Nat.mul_comm]
        simp only [itemPhi, hne, hne1, hmod, hmod1, ↓reduceIte, hts1]
        rw [hk', targetSize_odd_step]
        push_cast
        field_simp
        ring

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
