/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# The knapsack FPTAS

An instance of the knapsack problem is a list of items `(weight, value)` and a capacity `B`; a
feasible solution is a subsequence of the items of total weight at most `B`, the notion of
`Cslib.Complexity.Knapsack` (`Cslib.Complexity.mem_Knapsack_iff_sublist`). The FPTAS with
accuracy `1 / k` (`Cslib.Algorithms.Lean.Knapsack.fptas`) discards the items heavier than `B`,
rounds the value `v` of each of the `n` remaining items to `⌊v * n * k / P⌋`, where `P` is their
largest value, and solves the rounded instance exactly with the dynamic program by profit
(`Cslib.Algorithms.Lean.Knapsack.profitDP`). The rounded values are at most `n * k`, so the
dynamic program runs in time polynomial in `n` and `k`
(`Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_fptas`).

Rounding loses less than `P / (n * k)` per item, so less than `P / k` in total, and the most
valuable fitting item alone is feasible, so the returned value is at least `(1 - 1 / k)` times
the value of every feasible solution (`Cslib.Algorithms.Lean.Knapsack.sub_one_mul_value_le_fptas`)
[Williamson and Shmoys, Algorithm 3.2 and Theorem 3.5][WilliamsonShmoys2011], [Ibarra and
Kim][IbarraKim1975]. Williamson and Shmoys round with `μ = ε P / n` and assume that every item
fits; discarding the items that do not fit removes that assumption.

## Main definitions

* `Cslib.Algorithms.Lean.Knapsack.fptas`: the FPTAS with accuracy `1 / k`.

## Main results

* `Cslib.Algorithms.Lean.Knapsack.fptas_sublist`,
  `Cslib.Algorithms.Lean.Knapsack.sum_map_fst_fptas_le`: the FPTAS returns a feasible solution.
* `Cslib.Algorithms.Lean.Knapsack.sub_one_mul_value_le_fptas`: its value is at least `1 - 1 / k`
  times that of every feasible solution.
* `Cslib.Algorithms.Lean.Knapsack.one_sub_mul_value_le_fptas`: for every real `ε > 0`, with
  `k = ⌈1 / ε⌉`, its value is at least `1 - ε` times that of every feasible solution.

## References

* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
* [O. H. Ibarra, C. E. Kim, *Fast approximation algorithms for the knapsack and sum of subset
  problems*][IbarraKim1975]
-/

public section

namespace Cslib.Algorithms.Lean.Knapsack

open scoped List

/-- The largest value of an item, `0` for no items. -/
@[expose] def maxValue (l : List (ℕ × ℕ)) : ℕ := l.foldl (fun m a => max m a.2) 0

private theorem foldl_max_spec (l : List (ℕ × ℕ)) (m : ℕ) :
    m ≤ l.foldl (fun m a => max m a.2) m ∧ ∀ a ∈ l, a.2 ≤ l.foldl (fun m a => max m a.2) m := by
  induction l generalizing m with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2⟩ := ih (max m b.2)
    exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1, h2⟩

/-- The running maximum is its start or the value of an item. -/
theorem foldl_max_eq (l : List (ℕ × ℕ)) (m : ℕ) :
    l.foldl (fun m a => max m a.2) m = m ∨ ∃ a ∈ l, a.2 = l.foldl (fun m a => max m a.2) m := by
  induction l generalizing m with
  | nil => exact .inl rfl
  | cons b l ih =>
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    rcases ih (max m b.2) with h | h
    · rw [h]
      exact (le_total m b.2).elim
        (fun hm => .inr (.inl (max_eq_right hm).symm)) (.inl ∘ max_eq_left)
    · exact .inr (.inr h)

/-- Every value is at most the largest value. -/
theorem le_maxValue {l : List (ℕ × ℕ)} {a : ℕ × ℕ} (ha : a ∈ l) : a.2 ≤ maxValue l :=
  (foldl_max_spec l 0).2 a ha

/-- The largest value of a nonempty list is attained. -/
theorem exists_maxValue_eq {l : List (ℕ × ℕ)} (hl : l ≠ []) :
    ∃ a ∈ l, a.2 = maxValue l := by
  rcases foldl_max_eq l 0 with h | h
  · obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hl
    refine ⟨b, List.mem_cons_self, le_antisymm (le_maxValue List.mem_cons_self) ?_⟩
    rw [maxValue, h]; exact Nat.zero_le _
  · exact h

/-- The items that fit into a knapsack of capacity `B` by themselves. -/
@[expose] def fits (B : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.filter fun a => a.1 ≤ B

/-- Pair the items with their values rounded to `min N ⌊v * N / P⌋`, which is `⌊v * N / P⌋`
whenever `v ≤ P`. -/
@[expose] def roundValues (N P : ℕ) (l : List (ℕ × ℕ)) : List ((ℕ × ℕ) × ℕ) :=
  l.map fun a => (a, min N (a.2 * N / P))

/-- **The knapsack FPTAS** with accuracy `1 / k`, on the items `x.1` and the capacity `x.2`:
discard the items heavier than the capacity, round the values of the `n` others to
`⌊v * n * k / P⌋` with `P` their largest value, and solve the rounded instance exactly with the
dynamic program by profit. -/
@[expose] def fptas (k : ℕ) (x : List (ℕ × ℕ) × ℕ) : List (ℕ × ℕ) :=
  (profitDP (fun a : (ℕ × ℕ) × ℕ => a.1.1) Prod.snd x.2
    (roundValues ((fits x.2 x.1).length * k) (maxValue (fits x.2 x.1)) (fits x.2 x.1))).map
    Prod.fst

/-- The FPTAS returns a subsequence of the items. -/
theorem fptas_sublist (k : ℕ) (x : List (ℕ × ℕ) × ℕ) : fptas k x <+ x.1 := by
  refine ((profitDP_sublist (w := fun a : (ℕ × ℕ) × ℕ => a.1.1) (p := Prod.snd) x.2
    (roundValues ((fits x.2 x.1).length * k) (maxValue (fits x.2 x.1)) (fits x.2 x.1))).map
    Prod.fst).trans ?_
  simp [fits, roundValues, List.map_map, Function.comp_def]

/-- The FPTAS respects the capacity. -/
theorem sum_map_fst_fptas_le (k : ℕ) (x : List (ℕ × ℕ) × ℕ) :
    ((fptas k x).map Prod.fst).sum ≤ x.2 := by
  have h := sum_map_profitDP_le (w := fun a : (ℕ × ℕ) × ℕ => a.1.1) (p := Prod.snd) x.2
    (roundValues ((fits x.2 x.1).length * k) (maxValue (fits x.2 x.1)) (fits x.2 x.1))
  simpa [fptas, List.map_map, Function.comp_def] using h

/-- A subsequence within the capacity consists of items that fit by themselves. -/
theorem sublist_fits {B : ℕ} {l s : List (ℕ × ℕ)} (hs : s <+ l) (hsw : (s.map Prod.fst).sum ≤ B) :
    s <+ fits B l := by
  have h := hs.filter (fun a : ℕ × ℕ => decide (a.1 ≤ B))
  rwa [List.filter_eq_self.mpr fun a ha => decide_eq_true
    ((List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.fst) ha)).trans hsw)] at h

/-- The rounding error of the FPTAS: `k` times the value of a feasible solution is at most `k`
times the value returned plus the largest value of a fitting item. -/
theorem mul_value_le_mul_value_fptas_add (k : ℕ) {x : List (ℕ × ℕ) × ℕ} {s : List (ℕ × ℕ)}
    (hs : s <+ x.1) (hsw : (s.map Prod.fst).sum ≤ x.2) :
    k * (s.map Prod.snd).sum ≤ k * ((fptas k x).map Prod.snd).sum + maxValue (fits x.2 x.1) := by
  set F := fits x.2 x.1
  set n := F.length
  set P := maxValue F
  set r : ℕ × ℕ → ℕ := fun a => min (n * k) (a.2 * (n * k) / P)
  have hsF : s <+ F := sublist_fits hs hsw
  set D := roundValues (n * k) P F
  set S' := profitDP (fun a : (ℕ × ℕ) × ℕ => a.1.1) Prod.snd x.2 D
  have hopt : (s.map r).sum ≤ (S'.map Prod.snd).sum := by
    simpa only [List.map_map, Function.comp_def] using
      sum_map_le_profitDP (w := fun a : (ℕ × ℕ) × ℕ => a.1.1) (p := Prod.snd) (B := x.2) (l := D)
        (hsF.map fun a => (a, r a)) (by simpa [List.map_map, Function.comp_def] using hsw)
  have hhigh {a : ℕ × ℕ} (ha : a ∈ F) : a.2 * (n * k) ≤ r a * P + P := by
    have haP : a.2 ≤ P := le_maxValue ha
    rcases Nat.eq_zero_or_pos P with hP | hP
    · simp [show a.2 = 0 by omega]
    · rw [show r a = a.2 * (n * k) / P from min_eq_right <|
        (Nat.div_le_div_right (Nat.mul_le_mul_right _ haP)).trans
          (Nat.mul_div_cancel_left _ hP).le]
      exact (Nat.lt_div_mul_add hP).le
  have hS : (S'.map Prod.snd).sum * P ≤ ((fptas k x).map Prod.snd).sum * (n * k) := by
    rw [show fptas k x = S'.map Prod.fst from rfl, List.map_map, ← List.sum_map_mul_right,
      ← List.sum_map_mul_right]
    refine List.sum_le_sum fun b hb => ?_
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ((profitDP_sublist _ _).subset hb)
    exact (Nat.mul_le_mul_right P (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  have hs' : (s.map Prod.snd).sum * (n * k) ≤ (s.map r).sum * P + n * P :=
    calc (s.map Prod.snd).sum * (n * k)
        = (s.map fun a => a.2 * (n * k)).sum := (List.sum_map_mul_right _ _ _).symm
      _ ≤ (s.map fun a => r a * P + P).sum := List.sum_le_sum fun a ha => hhigh (hsF.subset ha)
      _ = (s.map r).sum * P + s.length * P := by
          rw [List.sum_map_add, List.sum_map_mul_right, List.map_const', List.sum_const_nat]
      _ ≤ (s.map r).sum * P + n * P := Nat.add_le_add_left (Nat.mul_le_mul_right _ hsF.length_le) _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : s = [] := List.eq_nil_of_length_eq_zero (by have := hsF.length_le; omega)
    simp [this]
  · refine Nat.le_of_mul_le_mul_left (c := n) ?_ hn
    have hchain := hs'.trans (Nat.add_le_add_right ((Nat.mul_le_mul_right P hopt).trans hS) _)
    simpa only [show n * (k * (s.map Prod.snd).sum) = (s.map Prod.snd).sum * (n * k) by ring,
      show n * (k * ((fptas k x).map Prod.snd).sum + P) =
        ((fptas k x).map Prod.snd).sum * (n * k) + n * P by ring] using hchain

/-- **The FPTAS guarantee** [Williamson and Shmoys, Theorem 3.5][WilliamsonShmoys2011]: with
accuracy `1 / k`, the FPTAS returns at least `1 - 1 / k` times the value of every feasible
solution. -/
theorem sub_one_mul_value_le_fptas (k : ℕ) {x : List (ℕ × ℕ) × ℕ} {s : List (ℕ × ℕ)}
    (hs : s <+ x.1) (hsw : (s.map Prod.fst).sum ≤ x.2) :
    (k - 1) * (s.map Prod.snd).sum ≤ k * ((fptas k x).map Prod.snd).sum := by
  have hmain := mul_value_le_mul_value_fptas_add k hs hsw
  generalize hP : maxValue (fits x.2 x.1) = P at hmain
  have hP' : (k - 1) * P ≤ k * ((fptas k x).map Prod.snd).sum := by
    by_cases hF : fits x.2 x.1 = []
    · simp [show P = 0 by rw [← hP, hF]; rfl]
    · obtain ⟨a, ha, haP⟩ := exists_maxValue_eq hF
      obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
      have h := mul_value_le_mul_value_fptas_add k (List.singleton_sublist.mpr ha1)
        (by simpa using ha2)
      simp only [List.map_singleton, List.sum_singleton, haP, hP] at h
      rw [Nat.sub_one_mul]; omega
  rcases le_total (s.map Prod.snd).sum P with h | h
  · exact (Nat.mul_le_mul_left _ h).trans hP'
  · rw [Nat.sub_one_mul]; have := Nat.mul_le_mul_left k h; omega

/-- **The knapsack FPTAS** [Williamson and Shmoys, Theorem 3.5][WilliamsonShmoys2011],
[Ibarra and Kim][IbarraKim1975]: for every real `ε > 0`, with `k = ⌈1 / ε⌉`, the FPTAS returns
a feasible solution whose value is at least `1 - ε` times that of every feasible solution. -/
theorem one_sub_mul_value_le_fptas {ε : ℝ} (hε : 0 < ε) {x : List (ℕ × ℕ) × ℕ}
    {s : List (ℕ × ℕ)} (hs : s <+ x.1) (hsw : (s.map Prod.fst).sum ≤ x.2) :
    (1 - ε) * (s.map Prod.snd).sum ≤ ((fptas ⌈ε⁻¹⌉₊ x).map Prod.snd).sum := by
  set k := ⌈ε⁻¹⌉₊
  have hk : ε⁻¹ ≤ k := Nat.le_ceil _
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h =>
    not_le.mpr (inv_pos.mpr hε) (by simpa [h] using hk)
  have hreal : ((k : ℝ) - 1) * (s.map Prod.snd).sum ≤ k * ((fptas k x).map Prod.snd).sum := by
    simpa [Nat.cast_sub hk1] using
      (Nat.cast_le (α := ℝ)).mpr (sub_one_mul_value_le_fptas k hs hsw)
  have hεk : 1 ≤ ε * k :=
    (mul_inv_cancel₀ hε.ne').symm.trans_le (mul_le_mul_of_nonneg_left hk hε.le)
  rw [← mul_le_mul_iff_of_pos_left (by exact_mod_cast hk1 : (0 : ℝ) < k)]
  nlinarith [show (0 : ℝ) ≤ (s.map Prod.snd).sum from Nat.cast_nonneg _]

end Cslib.Algorithms.Lean.Knapsack
