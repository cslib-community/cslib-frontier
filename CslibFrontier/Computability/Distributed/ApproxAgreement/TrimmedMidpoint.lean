/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic.Linarith

/-!
# Trimmed-extremes midpoint operator for approximate Byzantine agreement

This module defines the computable trimmed-extremes midpoint operator `midTrim` over any linearly
ordered field `K` and proves the convex-hull validity and factor-`1/2` contraction properties used
by the unit-interval, fixed-horizon synchronous (`n > 3t`) and single-hop asynchronous (`n > 5t`)
protocols in `CslibFrontier.Computability.Distributed.ApproxAgreement.Protocol` (milestone steps
toward `#7116` and `#3261`, after Section 2 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]):

1. **Convex-hull validity (`midTrim_mem_Icc`):** given a list `xs` of length `m > 2t` in which at
   least `m - t` entries lie in `[lo, hi]` (so at most `t` entries come from Byzantine processes
   outside `[lo, hi]`), sorting `xs` and dropping its `t` smallest and `t` largest entries
   (`trimmed t xs`, corresponding to `reduce^t` in Section 2.1, Lemmas 3–4 of
   [DolevLynchPinterStarkWeihl1986]) leaves only values in `[lo, hi]`, and their extreme-value
   midpoint `midTrim t xs` also lies in `[lo, hi]`.
2. **Factor-`1/2` contraction (`abs_midTrim_sub_le`):** given two lists `xs` and `ys` (not
   necessarily of equal length) each having at most `t` entries outside `[lo, hi]` and sharing
   strictly more than `2t` entries with multiplicity (`2 * t < (xs ∩ ys).card` as multisets),
   `|midTrim t xs - midTrim t ys| ≤ (hi - lo) / 2`.

Both regimes of `CslibFrontier.Computability.Distributed.ApproxAgreement.Protocol` instantiate the
same Finset-indexed multiset corollaries (`multisetMidTrim_map_mem_Icc` and
`abs_multisetMidTrim_map_sub_le`):

* **Synchronous (`m = n`, `3 * t < n`):** two recipients collect values from `S₁ = S₂ = Finset.univ`
  and share all `n - |F| ≥ n - t > 2t` honest entries.
* **Single-hop asynchronous (`m ≥ n - t`, `5 * t < n`):** two recipients collect values from sender
  sets `S₁, S₂` of size at least `n - t`, whose intersection contains at least `n - 2t` senders and
  therefore at least `n - 3t > 2t` shared honest entries.

## Comparison with multi-step representative averaging

Section 2.2 (p. 503, Lemma 5) of [DolevLynchPinterStarkWeihl1986] defines the parameterized family
of approximation functions `f_{k, t}(V) = mean(select_k(reduce^t(V)))` that sort the received
multiset, discard `t` extremes on each end (`reduce^t`), select every `k`-th surviving point
(`select_k`), and take the arithmetic mean of those `c(m - 2t, k) = ⌊(m - 2t - 1) / k⌋ + 1`
representatives, achieving per-round contraction `1 / c(m - 2t, k)` (with `k = t` synchronously and
`k = 2t` asynchronously). Taking the midpoint `(min + max) / 2` of the trimmed multiset (`midTrim`)
averages just the two extreme surviving points: it agrees with `f_{t, t}` at `n = 3t + 1` and with
`f_{2t, t}` at `n = 5t + 1` (where `c = 2`), while trading sharper `1 / c` contraction at larger
`n / t` for one uniform formula across both `3t < n` and `5t < n` with no variable-arity division
and a uniform contraction factor of `1 / 2` per round.

To ensure kernel reduction (`decide +kernel`) works inside `module` clients (where Lean's
well-founded `List.mergeSort` and Mathlib's unexposed `List.insertionSort` do not unfold), sorting
is implemented structurally by `sortLE` (`@[expose]`) and equated to `List.mergeSort (· ≤ ·)` in
`sortLE_eq_mergeSort`.

## Main definitions

* `Cslib.Distributed.ApproxAgreement.trimmed`: sort a list in nondecreasing order and drop the `t`
  smallest and `t` largest entries.
* `Cslib.Distributed.ApproxAgreement.midTrim`: midpoint `(head + last) / 2` of `trimmed t xs`.
* `Cslib.Distributed.ApproxAgreement.multisetMidTrim`: permutation-invariant lift of `midTrim` to
  `Multiset K`, preserving kernel computability via `Quot.liftOn`.

## Main results

* `Cslib.Distributed.ApproxAgreement.mem_Icc_of_mem_trimmed`: every surviving entry of
  `trimmed t xs` lies in `[lo, hi]` when at least `xs.length - t` entries of `xs` lie in `[lo, hi]`.
* `Cslib.Distributed.ApproxAgreement.midTrim_mem_Icc`: convex-hull validity of `midTrim`.
* `Cslib.Distributed.ApproxAgreement.abs_midTrim_sub_le`: factor-`1/2` contraction of `midTrim`
  whenever two lists share strictly more than `2t` multiset entries.
* `Cslib.Distributed.ApproxAgreement.multisetMidTrim_map_mem_Icc`,
  `Cslib.Distributed.ApproxAgreement.abs_multisetMidTrim_map_sub_le`: unified `Finset`-indexed
  validity and contraction for synchronous (`3t < n`) and asynchronous (`5t < n`) rounds.

## References

* [D. Dolev, N. A. Lynch, S. S. Pinter, E. W. Stark, W. E. Weihl, *Reaching approximate agreement
  in the presence of faults*][DolevLynchPinterStarkWeihl1986]
-/

public section

namespace Cslib.Distributed.ApproxAgreement

/-! ### Kernel-reducible sorting and trimming -/

section LinearOrder

variable {K : Type*} [LinearOrder K]

/-- Insert `a` into a sorted list `l` in nondecreasing order. Marked `@[expose]` so kernel
evaluation (`decide +kernel`) unfolds `trimmed` and `midTrim` in downstream `module` clients. -/
@[expose] def insertSorted (a : K) : List K → List K
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insertSorted a l

/-- Structural insertion sort on `List K`, equal to `List.mergeSort (· ≤ ·)` (`sortLE_eq_mergeSort`)
and marked `@[expose]` for kernel reduction. -/
@[expose] def sortLE (xs : List K) : List K :=
  xs.foldr insertSorted []

private theorem sortLE_eq_insertionSort (xs : List K) : sortLE xs = xs.insertionSort (· ≤ ·) := by
  induction xs with
  | nil => simp only [sortLE, List.foldr_nil, List.insertionSort_nil]
  | cons a xs ih =>
    simp only [sortLE, List.foldr_cons] at ih ⊢
    rw [List.insertionSort_cons, ← ih]
    clear ih
    induction xs.foldr insertSorted [] with
    | nil => simp only [insertSorted, List.orderedInsert_nil]
    | cons b l ihl => simp only [insertSorted, List.orderedInsert_cons, ihl]

theorem sortLE_eq_mergeSort (xs : List K) : sortLE xs = xs.mergeSort (· ≤ ·) := by
  rw [sortLE_eq_insertionSort, ← List.mergeSort_eq_insertionSort]

private theorem sortedLE_sortLE (xs : List K) : (sortLE xs).SortedLE := by
  rw [sortLE_eq_mergeSort]
  exact List.sortedLE_mergeSort

private theorem perm_sortLE (xs : List K) : (sortLE xs).Perm xs := by
  rw [sortLE_eq_mergeSort]
  exact List.mergeSort_perm xs _

@[simp]
theorem length_sortLE (xs : List K) : (sortLE xs).length = xs.length :=
  (perm_sortLE xs).length_eq

private theorem sortLE_eq_of_perm {xs ys : List K} (h : xs.Perm ys) : sortLE xs = sortLE ys :=
  ((perm_sortLE xs).trans (h.trans (perm_sortLE ys).symm)).eq_of_sortedLE
    (sortedLE_sortLE xs) (sortedLE_sortLE ys)

/-- Sort `xs` in nondecreasing order and discard the `t` smallest and `t` largest entries. -/
@[expose] def trimmed (t : ℕ) (xs : List K) : List K :=
  ((sortLE xs).drop t).take (xs.length - 2 * t)

theorem trimmed_eq_mergeSort (t : ℕ) (xs : List K) :
    trimmed t xs = ((xs.mergeSort (· ≤ ·)).drop t).take (xs.length - 2 * t) := by
  rw [trimmed, sortLE_eq_mergeSort]

@[simp]
theorem length_trimmed (t : ℕ) (xs : List K) : (trimmed t xs).length = xs.length - 2 * t := by
  simp only [trimmed, List.length_take, List.length_drop, length_sortLE]
  omega

theorem trimmed_ne_nil {t : ℕ} {xs : List K} (h : 2 * t < xs.length) : trimmed t xs ≠ [] := by
  intro hemp
  have hlen := congrArg List.length hemp
  rw [length_trimmed, List.length_nil] at hlen
  omega

theorem trimmed_eq_of_perm {xs ys : List K} (h : xs.Perm ys) (t : ℕ) :
    trimmed t xs = trimmed t ys := by
  simp only [trimmed, sortLE_eq_of_perm h, h.length_eq]

/-! ### Order-statistic bounds on `sortLE` -/

/-- If at least `xs.length - k` entries of `xs` are `≥ v`, then `(sortLE xs)[k] ≥ v`. -/
private lemma le_sortLE_getElem {xs : List K} {k : ℕ} {v : K}
    (hk : k < (sortLE xs).length)
    (hcnt : xs.length - k ≤ xs.countP (fun x => decide (v ≤ x))) :
    v ≤ (sortLE xs)[k] := by
  by_contra! hlt
  have htake_lt : ∀ x ∈ (sortLE xs).take (k + 1), decide (v ≤ x) = false := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take]
    have hik : i ≤ k := by
      rw [List.length_take] at hi
      omega
    have hi_len : i < (sortLE xs).length := Nat.lt_of_le_of_lt hik hk
    have hle : (sortLE xs)[i] ≤ (sortLE xs)[k] :=
      (sortedLE_sortLE xs).getElem_le_getElem_of_le hik
    simp only [decide_eq_false_iff_not, not_le]
    exact lt_of_le_of_lt hle hlt
  have hsplit : sortLE xs = (sortLE xs).take (k + 1) ++ (sortLE xs).drop (k + 1) :=
    (List.take_append_drop (k + 1) (sortLE xs)).symm
  have hperm_cnt : xs.countP (fun x => decide (v ≤ x)) =
      (sortLE xs).countP (fun x => decide (v ≤ x)) :=
    (perm_sortLE xs).symm.countP_eq _
  have htake_zero : ((sortLE xs).take (k + 1)).countP (fun x => decide (v ≤ x)) = 0 :=
    List.countP_eq_zero.mpr fun x hx => by
      simp only [htake_lt x hx, Bool.false_eq_true, not_false_eq_true]
  have hdrop_le : ((sortLE xs).drop (k + 1)).countP (fun x => decide (v ≤ x)) ≤
      xs.length - (k + 1) := by
    refine List.countP_le_length.trans ?_
    simp only [List.length_drop, length_sortLE, le_rfl]
  rw [hperm_cnt, hsplit, List.countP_append, htake_zero, zero_add] at hcnt
  have hk_lt : k < xs.length := by simpa only [length_sortLE] using hk
  omega

/-- If at least `k + 1` entries of `xs` are `≤ v`, then `(sortLE xs)[k] ≤ v`. -/
private lemma sortLE_getElem_le {xs : List K} {k : ℕ} {v : K}
    (hk : k < (sortLE xs).length)
    (hcnt : k + 1 ≤ xs.countP (fun x => decide (x ≤ v))) :
    (sortLE xs)[k] ≤ v := by
  by_contra! hgt
  have hdrop_gt : ∀ x ∈ (sortLE xs).drop k, decide (x ≤ v) = false := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    have hkj : k + j < (sortLE xs).length := by
      rw [List.length_drop] at hj
      omega
    have hle : (sortLE xs)[k] ≤ (sortLE xs)[k + j] :=
      (sortedLE_sortLE xs).getElem_le_getElem_of_le (Nat.le_add_right k j)
    simp only [decide_eq_false_iff_not, not_le]
    exact lt_of_lt_of_le hgt hle
  have hsplit : sortLE xs = (sortLE xs).take k ++ (sortLE xs).drop k :=
    (List.take_append_drop k (sortLE xs)).symm
  have hperm_cnt : xs.countP (fun x => decide (x ≤ v)) =
      (sortLE xs).countP (fun x => decide (x ≤ v)) :=
    (perm_sortLE xs).symm.countP_eq _
  have hdrop_zero : ((sortLE xs).drop k).countP (fun x => decide (x ≤ v)) = 0 :=
    List.countP_eq_zero.mpr fun x hx => by
      simp only [hdrop_gt x hx, Bool.false_eq_true, not_false_eq_true]
  have htake_le : ((sortLE xs).take k).countP (fun x => decide (x ≤ v)) ≤ k := by
    refine List.countP_le_length.trans ?_
    simp only [List.length_take, min_le_iff, le_rfl, true_or]
  rw [hperm_cnt, hsplit, List.countP_append, hdrop_zero, add_zero] at hcnt
  omega

/-- Every surviving entry of `trimmed t xs` lies between `(sortLE xs)[t]` and
`(sortLE xs)[xs.length - 1 - t]`. -/
private lemma mem_trimmed_bounds {t : ℕ} {xs : List K} (h2t : 2 * t < xs.length)
    {z : K} (hz : z ∈ trimmed t xs) :
    (sortLE xs)[t]'(by rw [length_sortLE]; omega) ≤ z ∧
    z ≤ (sortLE xs)[xs.length - 1 - t]'(by rw [length_sortLE]; omega) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  have hj_bound : j < xs.length - 2 * t := by simpa only [length_trimmed] using hj
  have heq : (trimmed t xs)[j] = (sortLE xs)[t + j]'(by rw [length_sortLE]; omega) := by
    simp only [trimmed, List.getElem_take, List.getElem_drop]
  rw [heq]
  exact ⟨(sortedLE_sortLE xs).getElem_le_getElem_of_le (Nat.le_add_right t j),
    (sortedLE_sortLE xs).getElem_le_getElem_of_le (by omega)⟩

/-- If at least `xs.length - t` entries of `xs` lie in `[lo, hi]`, then `(sortLE xs)[t]` and
`(sortLE xs)[xs.length - 1 - t]` both lie in `[lo, hi]`. -/
private lemma sortLE_trim_endpoints_mem_Icc {t : ℕ} {xs : List K} {lo hi : K}
    (h2t : 2 * t < xs.length)
    (hcnt : xs.length - t ≤ xs.countP (fun x => decide (lo ≤ x ∧ x ≤ hi))) :
    lo ≤ (sortLE xs)[t]'(by rw [length_sortLE]; omega) ∧
    (sortLE xs)[xs.length - 1 - t]'(by rw [length_sortLE]; omega) ≤ hi := by
  have hlo_cnt : xs.length - t ≤ xs.countP (fun x => decide (lo ≤ x)) :=
    hcnt.trans (List.countP_mono_left fun x _ hx => by
      simp only [decide_eq_true_eq] at hx ⊢; exact hx.1)
  have hhi_cnt : (xs.length - 1 - t) + 1 ≤ xs.countP (fun x => decide (x ≤ hi)) := by
    have h1 : xs.length - t ≤ xs.countP (fun x => decide (x ≤ hi)) :=
      hcnt.trans (List.countP_mono_left fun x _ hx => by
        simp only [decide_eq_true_eq] at hx ⊢; exact hx.2)
    omega
  exact ⟨le_sortLE_getElem (by rw [length_sortLE]; omega) hlo_cnt,
    sortLE_getElem_le (by rw [length_sortLE]; omega) hhi_cnt⟩

/-- **Trimmed-range validity:** if at least `xs.length - t` entries of `xs` lie in `[lo, hi]`, then
every entry of `trimmed t xs` lies in `[lo, hi]`. -/
theorem mem_Icc_of_mem_trimmed {t : ℕ} {xs : List K} {lo hi z : K}
    (hcnt : xs.length - t ≤ xs.countP (fun x => decide (lo ≤ x ∧ x ≤ hi)))
    (hz : z ∈ trimmed t xs) : z ∈ Set.Icc lo hi := by
  have hpos : 0 < (trimmed t xs).length := List.length_pos_of_mem hz
  rw [length_trimmed] at hpos
  have h2t : 2 * t < xs.length := by omega
  obtain ⟨hlo, hhi⟩ := sortLE_trim_endpoints_mem_Icc h2t hcnt
  obtain ⟨h1, h2⟩ := mem_trimmed_bounds h2t hz
  exact ⟨hlo.trans h1, h2.trans hhi⟩

end LinearOrder

/-! ### Midpoint operator `midTrim` and contraction lemmas -/

section MidTrim

/-- The trimmed-extremes midpoint operator: sort `xs`, discard the `t` smallest and `t` largest
entries (`trimmed t xs`), and return `(head + last) / 2` (or `0` when `xs.length ≤ 2 * t`). -/
@[expose] def midTrim {K : Type*} [Field K] [LinearOrder K] (t : ℕ) (xs : List K) : K :=
  match trimmed t xs with
  | [] => 0
  | y :: ys => (y + ys.getLastD y) / 2

theorem midTrim_eq_of_perm {K : Type*} [Field K] [LinearOrder K] {xs ys : List K}
    (h : xs.Perm ys) (t : ℕ) : midTrim t xs = midTrim t ys := by
  simp only [midTrim, trimmed_eq_of_perm h t]

/-- Permutation-invariant lift of `midTrim t` to `Multiset K`. Because `Quot.liftOn` reduces
directly on quotient constructors, `decide +kernel` evaluates `multisetMidTrim` on concrete
multisets and `Finset.val.map` images in `module` clients. -/
@[expose] def multisetMidTrim {K : Type*} [Field K] [LinearOrder K] (t : ℕ) (s : Multiset K) : K :=
  Quot.liftOn s (midTrim t) fun _ _ h => midTrim_eq_of_perm h t

@[simp]
theorem multisetMidTrim_coe {K : Type*} [Field K] [LinearOrder K] (t : ℕ) (xs : List K) :
    multisetMidTrim t (Multiset.ofList xs) = midTrim t xs := rfl

private lemma getLastD_eq_getElem_last {α : Type*} (y : α) :
    ∀ ys : List α, ys.getLastD y = (y :: ys)[(y :: ys).length - 1]
  | [] => rfl
  | z :: zs => by
    simp only [List.getLastD_cons, List.length_cons, Nat.add_sub_cancel]
    exact getLastD_eq_getElem_last z zs

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- Explicit endpoint formula for `midTrim t xs` when `2 * t < xs.length`. -/
theorem midTrim_eq_endpoints {t : ℕ} {xs : List K} (h2t : 2 * t < xs.length) :
    midTrim t xs =
      ((sortLE xs)[t]'(by rw [length_sortLE]; omega) +
        (sortLE xs)[xs.length - 1 - t]'(by rw [length_sortLE]; omega)) / 2 := by
  have hne : trimmed t xs ≠ [] := trimmed_ne_nil h2t
  cases htr : trimmed t xs with
  | nil => exact absurd htr hne
  | cons y ys =>
    simp only [midTrim, htr]
    have hhead : y = (sortLE xs)[t]'(by rw [length_sortLE]; omega) := by
      have h0 : (trimmed t xs)[0]'(by rw [htr]; exact Nat.zero_lt_succ _) = y := by simp [htr]
      rw [← h0]
      simp only [trimmed, List.getElem_take, List.getElem_drop, Nat.add_zero]
    have hlast : ys.getLastD y =
        (sortLE xs)[xs.length - 1 - t]'(by rw [length_sortLE]; omega) := by
      rw [getLastD_eq_getElem_last y ys]
      have hlen : (y :: ys).length = xs.length - 2 * t := by
        rw [← htr, length_trimmed]
      have hidx : (trimmed t xs)[(y :: ys).length - 1]'(by
          rw [htr]; exact Nat.sub_lt (Nat.succ_pos _) Nat.one_pos) =
          (y :: ys)[(y :: ys).length - 1] := by
        simp only [htr]
      rw [← hidx]
      simp only [trimmed, List.getElem_take, List.getElem_drop]
      congr 1
      omega
    rw [hlast, hhead]

/-- **Convex-hull validity (`midTrim_mem_Icc`):** if `2 * t < xs.length` and at least
`xs.length - t` entries of `xs` lie in `[lo, hi]`, then `midTrim t xs ∈ [lo, hi]`. -/
theorem midTrim_mem_Icc {t : ℕ} {xs : List K} {lo hi : K}
    (h2t : 2 * t < xs.length)
    (hcnt : xs.length - t ≤ xs.countP (fun x => decide (lo ≤ x ∧ x ≤ hi))) :
    midTrim t xs ∈ Set.Icc lo hi := by
  rw [midTrim_eq_endpoints h2t]
  obtain ⟨hlo, hhi⟩ := sortLE_trim_endpoints_mem_Icc h2t hcnt
  have hmid : (sortLE xs)[t]'(by rw [length_sortLE]; omega) ≤
      (sortLE xs)[xs.length - 1 - t]'(by rw [length_sortLE]; omega) :=
    (sortedLE_sortLE xs).getElem_le_getElem_of_le (by omega)
  constructor <;> linarith

omit [Field K] [IsStrictOrderedRing K] in
/-- Cross-endpoint bound: if `xs` and `ys` share strictly more than `2 * t` multiset entries, then
the minimum of `trimmed t xs` is at most the maximum of `trimmed t ys`. -/
private lemma sortLE_min_le_max_of_inter {t : ℕ} {xs ys : List K}
    (hinter : 2 * t < (Multiset.ofList xs ∩ Multiset.ofList ys).card) :
    (sortLE xs)[t]'(by
      have hle := Multiset.card_le_card
        (Multiset.inter_le_left (s := Multiset.ofList xs) (t := Multiset.ofList ys))
      rw [Multiset.coe_card] at hle; rw [length_sortLE]; omega) ≤
    (sortLE ys)[ys.length - 1 - t]'(by
      have hle := Multiset.card_le_card
        (Multiset.inter_le_right (s := Multiset.ofList xs) (t := Multiset.ofList ys))
      rw [Multiset.coe_card] at hle; rw [length_sortLE]; omega) := by
  set M := Multiset.ofList xs ∩ Multiset.ofList ys
  have hx_len : 2 * t < xs.length := by
    have hle := Multiset.card_le_card
      (Multiset.inter_le_left (s := Multiset.ofList xs) (t := Multiset.ofList ys))
    simpa only [Multiset.coe_card] using lt_of_lt_of_le hinter hle
  have hy_len : 2 * t < ys.length := by
    have hle := Multiset.card_le_card
      (Multiset.inter_le_right (s := Multiset.ofList xs) (t := Multiset.ofList ys))
    simpa only [Multiset.coe_card] using lt_of_lt_of_le hinter hle
  set b₂ := (sortLE ys)[ys.length - 1 - t]'(by rw [length_sortLE]; omega)
  -- At most `t` elements of `ys` strictly exceed `b₂`.
  have hys_gt : (Multiset.ofList ys).countP (fun x => b₂ < x) ≤ t := by
    have hperm_eq : (Multiset.ofList ys).countP (fun x => b₂ < x) =
        (sortLE ys).countP (fun x => decide (b₂ < x)) := by
      rw [Multiset.coe_countP]
      exact (perm_sortLE ys).symm.countP_eq _
    rw [hperm_eq]
    have hsplit :
        sortLE ys = (sortLE ys).take (ys.length - t) ++ (sortLE ys).drop (ys.length - t) :=
      (List.take_append_drop (ys.length - t) (sortLE ys)).symm
    have htake_zero :
        ((sortLE ys).take (ys.length - t)).countP (fun x => decide (b₂ < x)) = 0 := by
      refine List.countP_eq_zero.mpr fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi_le : i ≤ ys.length - 1 - t := by
        rw [List.length_take, length_sortLE] at hi
        omega
      have hle : (sortLE ys)[i]'(by rw [length_sortLE]; omega) ≤ b₂ :=
        (sortedLE_sortLE ys).getElem_le_getElem_of_le hi_le
      simp only [List.getElem_take, decide_eq_true_eq, not_lt]
      exact hle
    have hdrop_le :
        ((sortLE ys).drop (ys.length - t)).countP (fun x => decide (b₂ < x)) ≤ t := by
      refine List.countP_le_length.trans ?_
      rw [List.length_drop, length_sortLE]
      omega
    rw [hsplit, List.countP_append, htake_zero, zero_add]
    exact hdrop_le
  -- Hence at most `t` elements of `M ≤ ys` exceed `b₂`, so at least `t + 1` elements of `M ≤ xs`
  -- satisfy `x ≤ b₂`.
  have hM_gt : M.countP (fun x => b₂ < x) ≤ t :=
    (Multiset.countP_le_of_le _ Multiset.inter_le_right).trans hys_gt
  have hM_part : M.card = M.countP (fun x => x ≤ b₂) + M.countP (fun x => b₂ < x) := by
    have hpart := Multiset.card_eq_countP_add_countP (fun x => x ≤ b₂) M
    simpa only [not_le] using hpart
  have hM_le : t + 1 ≤ M.countP (fun x => x ≤ b₂) := by omega
  have hxs_le : t + 1 ≤ xs.countP (fun x => decide (x ≤ b₂)) := by
    have hle := hM_le.trans (Multiset.countP_le_of_le _ Multiset.inter_le_left)
    simpa only [Multiset.coe_countP] using hle
  exact sortLE_getElem_le (by rw [length_sortLE]; omega) hxs_le

/-- **Trimmed-midpoint contraction (`abs_midTrim_sub_le`):** extreme-endpoint specialization after
Section 2.2, Lemma 5 of [Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]
(using `(min + max) / 2` in place of `f_{k, t}`'s `c`-point `select_k` mean): if `xs` and `ys`
each have at most `t` entries outside `[lo, hi]` and share strictly more than `2 * t` multiset
entries, then `|midTrim t xs - midTrim t ys| ≤ (hi - lo) / 2`. -/
theorem abs_midTrim_sub_le {t : ℕ} {xs ys : List K} {lo hi : K}
    (hinter : 2 * t < (Multiset.ofList xs ∩ Multiset.ofList ys).card)
    (hxs : xs.length - t ≤ xs.countP (fun x => decide (lo ≤ x ∧ x ≤ hi)))
    (hys : ys.length - t ≤ ys.countP (fun x => decide (lo ≤ x ∧ x ≤ hi))) :
    |midTrim t xs - midTrim t ys| ≤ (hi - lo) / 2 := by
  have hx_len : 2 * t < xs.length := by
    have hle := Multiset.card_le_card
      (Multiset.inter_le_left (s := Multiset.ofList xs) (t := Multiset.ofList ys))
    simpa only [Multiset.coe_card] using lt_of_lt_of_le hinter hle
  have hy_len : 2 * t < ys.length := by
    have hle := Multiset.card_le_card
      (Multiset.inter_le_right (s := Multiset.ofList xs) (t := Multiset.ofList ys))
    simpa only [Multiset.coe_card] using lt_of_lt_of_le hinter hle
  rw [midTrim_eq_endpoints hx_len, midTrim_eq_endpoints hy_len]
  obtain ⟨ha₁, hb₁⟩ := sortLE_trim_endpoints_mem_Icc hx_len hxs
  obtain ⟨ha₂, hb₂⟩ := sortLE_trim_endpoints_mem_Icc hy_len hys
  have hcross₁ : (sortLE xs)[t]'(by rw [length_sortLE]; omega) ≤
      (sortLE ys)[ys.length - 1 - t]'(by rw [length_sortLE]; omega) :=
    sortLE_min_le_max_of_inter hinter
  have hinter_symm : 2 * t < (Multiset.ofList ys ∩ Multiset.ofList xs).card := by
    rwa [Multiset.inter_comm]
  have hcross₂ : (sortLE ys)[t]'(by rw [length_sortLE]; omega) ≤
      (sortLE xs)[xs.length - 1 - t]'(by rw [length_sortLE]; omega) :=
    sortLE_min_le_max_of_inter hinter_symm
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### Unified `Finset`-sender multiset validity and contraction -/

omit [Field K] [IsStrictOrderedRing K] in
/-- Helper: in a sender set `S` with `F.card ≤ t`, if every non-faulty `p ∈ S \ F` maps into
`[lo, hi]`, then at least `S.card - t` entries of `S.val.map f` lie in `[lo, hi]`. -/
private lemma card_sub_le_countP_map {P : Type*}
    {F S : Finset P} {t : ℕ} (hF : F.card ≤ t) {f : P → K} {lo hi : K}
    (hval : ∀ p ∈ S, p ∉ F → f p ∈ Set.Icc lo hi) :
    (S.val.map f).card - t ≤ (S.val.map f).countP (fun x => lo ≤ x ∧ x ≤ hi) := by
  classical
  have hsub : (S \ F).val.map f ≤ S.val.map f :=
    Multiset.map_le_map (Finset.val_le_iff.mpr Finset.sdiff_subset)
  have hall : ∀ x ∈ (S \ F).val.map f, lo ≤ x ∧ x ≤ hi := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    have hp' := Finset.mem_sdiff.mp hp
    exact hval p hp'.1 hp'.2
  have hcnt_hon : ((S \ F).val.map f).countP (fun x => lo ≤ x ∧ x ≤ hi) = (S \ F).card := by
    rw [Multiset.countP_eq_card_filter, Multiset.filter_eq_self.mpr hall, Multiset.card_map]
    rfl
  have hle_cnt : (S \ F).card ≤ (S.val.map f).countP (fun x => lo ≤ x ∧ x ≤ hi) := by
    rw [← hcnt_hon]
    exact Multiset.countP_le_of_le _ hsub
  have hsdiff : S.card - F.card ≤ (S \ F).card := Finset.le_card_sdiff F S
  rw [Multiset.card_map, ← Finset.card_def]
  omega

/-- **Sender-multiset validity:** if `2 * t < S.card`, `F.card ≤ t`, and every correct sender
`p ∈ S \ F` reports a value `f p ∈ [lo, hi]`, then `multisetMidTrim t (S.val.map f) ∈ [lo, hi]`. -/
theorem multisetMidTrim_map_mem_Icc {P : Type*}
    {F S : Finset P} {t : ℕ} (hF : F.card ≤ t) (hS : 2 * t < S.card)
    {f : P → K} {lo hi : K} (hval : ∀ p ∈ S, p ∉ F → f p ∈ Set.Icc lo hi) :
    multisetMidTrim t (S.val.map f) ∈ Set.Icc lo hi := by
  have hcnt := card_sub_le_countP_map hF hval
  obtain ⟨xs, hxs⟩ := Quot.exists_rep (S.val.map f)
  have hxs' : Multiset.ofList xs = S.val.map f := hxs
  rw [← hxs', multisetMidTrim_coe]
  apply midTrim_mem_Icc
  · have hlen : xs.length = S.card := by
      have h := congrArg Multiset.card hxs'
      simpa only [Multiset.coe_card, Multiset.card_map, Finset.card_def] using h
    omega
  · rw [← hxs'] at hcnt
    simpa only [Multiset.coe_card, Multiset.coe_countP, decide_eq_true_eq] using hcnt

/-- **Sender-multiset contraction:** suppose `F.card ≤ t`, two recipients collect values `f₁`, `f₂`
from sender sets `S₁`, `S₂` with `Fintype.card P + 3 * t < S₁.card + S₂.card` (which holds both
synchronously when `S₁ = S₂ = univ` and `3 * t < |P|`, and asynchronously when
`|S₁|, |S₂| ≥ |P| - t` and `5 * t < |P|`), and every correct sender `p ∉ F` sends a common value
`val p ∈ [lo, hi]` to whichever recipient hears from it. Then
`|multisetMidTrim t (S₁.val.map f₁) - multisetMidTrim t (S₂.val.map f₂)| ≤ (hi - lo) / 2`. -/
theorem abs_multisetMidTrim_map_sub_le {P : Type*} [Fintype P]
    {F S₁ S₂ : Finset P} {t : ℕ} (hF : F.card ≤ t)
    (hcard : Fintype.card P + 3 * t < S₁.card + S₂.card)
    {val f₁ f₂ : P → K} {lo hi : K}
    (hval : ∀ p ∉ F, val p ∈ Set.Icc lo hi)
    (hf₁ : ∀ p ∈ S₁, p ∉ F → f₁ p = val p)
    (hf₂ : ∀ p ∈ S₂, p ∉ F → f₂ p = val p) :
    |multisetMidTrim t (S₁.val.map f₁) - multisetMidTrim t (S₂.val.map f₂)| ≤ (hi - lo) / 2 := by
  classical
  set H : Finset P := (S₁ ∩ S₂) \ F
  have hH_card : 2 * t < H.card := by
    have hiu := Finset.card_union_add_card_inter S₁ S₂
    have hu : (S₁ ∪ S₂).card ≤ Fintype.card P := Finset.card_le_univ _
    have hsdiff : (S₁ ∩ S₂).card - F.card ≤ H.card := Finset.le_card_sdiff F (S₁ ∩ S₂)
    omega
  have hmap_le : ∀ {S : Finset P} {f : P → K},
      H ⊆ S → (∀ p ∈ S, p ∉ F → f p = val p) → H.val.map val ≤ S.val.map f := by
    intro S f hHS hf
    have heq : H.val.map val = H.val.map f :=
      Multiset.map_congr rfl fun p hp =>
        (hf p (hHS hp) (Finset.mem_sdiff.mp hp).2).symm
    exact heq ▸ Multiset.map_le_map (Finset.val_le_iff.mpr hHS)
  have hH₁ : H.val.map val ≤ S₁.val.map f₁ :=
    hmap_le (Finset.sdiff_subset.trans Finset.inter_subset_left) hf₁
  have hH₂ : H.val.map val ≤ S₂.val.map f₂ :=
    hmap_le (Finset.sdiff_subset.trans Finset.inter_subset_right) hf₂
  have hinter : 2 * t < (S₁.val.map f₁ ∩ S₂.val.map f₂).card := by
    have hle := Multiset.card_le_card (Multiset.le_inter hH₁ hH₂)
    rw [Multiset.card_map, ← Finset.card_def] at hle
    exact lt_of_lt_of_le hH_card hle
  have hcnt₁ := card_sub_le_countP_map hF (S := S₁) (f := f₁) (lo := lo) (hi := hi)
    fun p hp hpF => hf₁ p hp hpF ▸ hval p hpF
  have hcnt₂ := card_sub_le_countP_map hF (S := S₂) (f := f₂) (lo := lo) (hi := hi)
    fun p hp hpF => hf₂ p hp hpF ▸ hval p hpF
  obtain ⟨xs, hxs⟩ := Quot.exists_rep (S₁.val.map f₁)
  obtain ⟨ys, hys⟩ := Quot.exists_rep (S₂.val.map f₂)
  have hxs' : Multiset.ofList xs = S₁.val.map f₁ := hxs
  have hys' : Multiset.ofList ys = S₂.val.map f₂ := hys
  rw [← hxs', ← hys', multisetMidTrim_coe, multisetMidTrim_coe]
  apply abs_midTrim_sub_le
  · rwa [hxs', hys']
  · rw [← hxs'] at hcnt₁
    simpa only [Multiset.coe_card, Multiset.coe_countP, decide_eq_true_eq] using hcnt₁
  · rw [← hys'] at hcnt₂
    simpa only [Multiset.coe_card, Multiset.coe_countP, decide_eq_true_eq] using hcnt₂

end OrderedField

end MidTrim

end Cslib.Distributed.ApproxAgreement
