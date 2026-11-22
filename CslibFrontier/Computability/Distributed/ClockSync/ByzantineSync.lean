/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ClockSync.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Byzantine fault-tolerant midpoint clock resynchronization

When up to `t` processes with `3 * t < Fintype.card P` suffer Byzantine clock faults—reporting
arbitrary, recipient-dependent timestamps to different honest processes—averaging all offset
estimates (`lundeliusLynchAvg`) can be skewed arbitrarily by a single faulty clock. Adapting the
fault-tolerant midpoint convergence step of [Welch and Lynch][WelchLynch1988] to separated
synchronous resynchronization rounds on drift-free clocks (`hardwareClock c p t = t + c p`, zero
clock drift; whereas `[WelchLynch1988]` analyzes local-timer-triggered asynchronous periodic
resynchronization under nonzero bounded hardware clock drift), each process sorts its
`n = Fintype.card P` midpoint-delay offset estimates (`estDiff`), discards the `t` smallest and `t`
largest values, and adjusts its clock by the midpoint `(s[t] + s[n - 1 - t]) / 2` of the remaining
range (`trimmedMidpoint`, `byzantineClockStep`).

This module proves, in this synchronous drift-free resynchronization setting:

* **Kernel-reducible sorting and permutation invariance (`sortLE_eq_mergeSort`,
  `trimmedMidpoint_eq_of_perm`, `multisetTrimmedMidpoint_coe`):** `sortLE` is `@[expose]` and
  agrees identically with `List.mergeSort (· ≤ ·)`, so `multisetTrimmedMidpoint` and
  `byzantineClockStep` evaluate in the kernel under `decide +kernel` in `module` clients without
  choosing an ordering on `P`.
* **Honest-interval accuracy (`byzantineSyncOffset_mem_Icc`):** In one synchronous drift-free
  resynchronization round, if all honest initial offsets lie in `[lo, hi]` and honest message
  delays lie in `[d_min, d_max]`, every honest process's updated offset lies in
  `[lo - (d_max - d_min) / 2, hi + (d_max - d_min) / 2]`.
* **Per-round skew halving (`byzantineSyncOffset_abs_sub_le`):** In one synchronous drift-free
  resynchronization round, if honest initial offsets have skew at most `δ₀`
  (`∀ p ∉ F, ∀ q ∉ F, |c p - c q| ≤ δ₀`) and honest message delays lie in `[d_min, d_max]`, every
  pair of honest processes satisfies `|syncOffset p - syncOffset q| ≤ δ₀ / 2 + (d_max - d_min)`.
* **Multi-round convergence to the `2 * (d_max - d_min)` envelope
  (`byzantineSyncOffsetIter_abs_sub_le`):** Iterating `R` separated synchronous drift-free
  resynchronization rounds against round-dependent equivocating Byzantine adversaries contracts
  initial honest skew `δ₀` to `δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min)`.

## Main definitions

* `Cslib.Distributed.ClockSync.insertSorted`, `sortLE`: kernel-reducible nondecreasing insertion
  sort agreeing with `List.mergeSort (· ≤ ·)`.
* `Cslib.Distributed.ClockSync.trimmedMidpoint`, `multisetTrimmedMidpoint`: trimmed-extremes
  midpoint convergence operator.
* `Cslib.Distributed.ClockSync.byzantineClockStep`: 1-round local Byzantine-resilient clock
  adjustment computed solely from observed arrival timestamps.
* `Cslib.Distributed.ClockSync.byzantineArrival`, `byzantineSyncOffset`,
  `byzantineSyncOffsetIter`: 1-round and `R`-round synchronized clock offsets under equivocating
  Byzantine faults `F`.

## Main results

* `Cslib.Distributed.ClockSync.trimmedMidpoint_eq_of_perm`: permutation invariance of
  `trimmedMidpoint`.
* `Cslib.Distributed.ClockSync.byzantineSyncOffset_mem_Icc`: honest interval preservation up to
  half the delay uncertainty `(d_max - d_min) / 2`.
* `Cslib.Distributed.ClockSync.byzantineSyncOffset_abs_sub_le`: 1-round skew contraction to
  `δ₀ / 2 + (d_max - d_min)` when `3 * t < Fintype.card P` and `F.card ≤ t`.
* `Cslib.Distributed.ClockSync.byzantineSyncOffsetIter_abs_sub_le`: `R`-round geometric
  contraction `δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min)`.

## References

* [J. L. Welch, N. Lynch,
  *A new fault-tolerant algorithm for clock synchronization*][WelchLynch1988]
-/

public section

namespace Cslib.Distributed.ClockSync

universe u v

/-! ### Trimmed-midpoint convergence operator via `List.mergeSort` -/

section TrimmedMidpoint

variable {K : Type v}

private theorem pairwise_le_mergeSort [LinearOrder K] (xs : List K) :
    List.Pairwise (· ≤ ·) (xs.mergeSort (· ≤ ·)) := by
  have htrans : ∀ a b c : K, decide (a ≤ b) = true → decide (b ≤ c) = true →
      decide (a ≤ c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htot : ∀ a b : K, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total a b
  exact (List.pairwise_mergeSort htrans htot xs).imp of_decide_eq_true

private theorem mergeSort_eq_of_perm [LinearOrder K] {xs ys : List K} (h : xs.Perm ys) :
    xs.mergeSort (· ≤ ·) = ys.mergeSort (· ≤ ·) :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (pairwise_le_mergeSort xs) (pairwise_le_mergeSort ys)
    ((List.mergeSort_perm xs _).trans (h.trans (List.mergeSort_perm ys _).symm))

/-- Insert `x` into a nondecreasing list at the first position with `x ≤ y`. Marked `@[expose]` so
that `sortLE` and `trimmedMidpoint` reduce in the kernel inside importing `module` clients. -/
@[expose] def insertSorted [LinearOrder K] (x : K) : List K → List K
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Kernel-reducible nondecreasing insertion sort, equal to `List.mergeSort (· ≤ ·)`
(`sortLE_eq_mergeSort`). -/
@[expose] def sortLE [LinearOrder K] : List K → List K
  | [] => []
  | x :: xs => insertSorted x (sortLE xs)

private theorem perm_insertSorted [LinearOrder K] (x : K) :
    ∀ xs : List K, (insertSorted x xs).Perm (x :: xs)
  | [] => List.Perm.refl _
  | y :: ys => by
    dsimp only [insertSorted]
    split_ifs
    · exact List.Perm.refl _
    · exact ((perm_insertSorted x ys).cons y).trans (List.Perm.swap x y ys)

private theorem perm_sortLE [LinearOrder K] : ∀ xs : List K, (sortLE xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => (perm_insertSorted x (sortLE xs)).trans ((perm_sortLE xs).cons x)

private theorem pairwise_insertSorted [LinearOrder K] (x : K) :
    ∀ {xs : List K}, xs.Pairwise (· ≤ ·) → (insertSorted x xs).Pairwise (· ≤ ·)
  | [], _ => List.pairwise_singleton _ _
  | y :: ys, h => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp h
    dsimp only [insertSorted]
    split_ifs with hxy
    · exact List.pairwise_cons.mpr ⟨fun z hz => by
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hxy
        · exact hxy.trans (hy z hz'), h⟩
    · have hyx : y ≤ x := le_of_not_ge hxy
      exact List.pairwise_cons.mpr ⟨fun z hz => by
        rcases List.mem_cons.mp ((perm_insertSorted x ys).subset hz) with rfl | hz'
        · exact hyx
        · exact hy z hz', pairwise_insertSorted x hys⟩

private theorem pairwise_sortLE [LinearOrder K] : ∀ xs : List K, (sortLE xs).Pairwise (· ≤ ·)
  | [] => List.Pairwise.nil
  | x :: xs => pairwise_insertSorted x (pairwise_sortLE xs)

/-- `sortLE` produces the exact same nondecreasing list as `List.mergeSort (· ≤ ·)`. -/
theorem sortLE_eq_mergeSort [LinearOrder K] (xs : List K) :
    sortLE xs = xs.mergeSort (· ≤ ·) :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (pairwise_sortLE xs) (pairwise_le_mergeSort xs)
    ((perm_sortLE xs).trans (List.mergeSort_perm xs _).symm)

/-- Sort `xs` in nondecreasing order (`sortLE`, equal to `List.mergeSort (· ≤ ·)`), discard the
`t` smallest and `t` largest entries, and return the midpoint `(s[t] + s[s.length - 1 - t]) / 2`
of the surviving extremes (or `0` when `xs.length ≤ 2 * t`) [Welch and Lynch][WelchLynch1988]. -/
@[expose] def trimmedMidpoint [Field K] [LinearOrder K] (t : ℕ) (xs : List K) : K :=
  let s := sortLE xs
  if h : 2 * t < s.length then
    (s[t] + s[s.length - 1 - t]) / 2
  else
    0

private theorem trimmedMidpoint_eq_mergeSort [Field K] [LinearOrder K] (t : ℕ) (xs : List K) :
    trimmedMidpoint t xs =
      let s := xs.mergeSort (· ≤ ·)
      if h : 2 * t < s.length then (s[t] + s[s.length - 1 - t]) / 2 else 0 := by
  simp only [trimmedMidpoint, sortLE_eq_mergeSort]

/-- `trimmedMidpoint` depends only on the multiset of entries in `xs`, not their list order. -/
theorem trimmedMidpoint_eq_of_perm [Field K] [LinearOrder K] (t : ℕ) {xs ys : List K}
    (h : xs.Perm ys) : trimmedMidpoint t xs = trimmedMidpoint t ys := by
  simp only [trimmedMidpoint_eq_mergeSort, mergeSort_eq_of_perm h]

/-- Permutation-invariant lift of `trimmedMidpoint` to `Multiset K`. Because `Quot.liftOn` reduces
definitionally on `Quot.mk`, this definition evaluates in the kernel under `decide`. -/
@[expose] def multisetTrimmedMidpoint [Field K] [LinearOrder K] (t : ℕ) (m : Multiset K) : K :=
  Quot.liftOn m (trimmedMidpoint t) (fun _ _ h => trimmedMidpoint_eq_of_perm t h)

/-- Evaluating `multisetTrimmedMidpoint` on a coerced list equals `trimmedMidpoint`. -/
@[simp] theorem multisetTrimmedMidpoint_coe [Field K] [LinearOrder K] (t : ℕ) (xs : List K) :
    multisetTrimmedMidpoint t (xs : Multiset K) = trimmedMidpoint t xs :=
  rfl

private theorem mergeSort_map_add [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
    (a : K) (xs : List K) :
    (xs.map (a + ·)).mergeSort (· ≤ ·) = (xs.mergeSort (· ≤ ·)).map (a + ·) := by
  have hpair : List.Pairwise (· ≤ ·) ((xs.mergeSort (· ≤ ·)).map (a + ·)) :=
    (pairwise_le_mergeSort xs).map (a + ·) (fun _ _ h => add_le_add_right h a)
  have hperm : ((xs.map (a + ·)).mergeSort (· ≤ ·)).Perm ((xs.mergeSort (· ≤ ·)).map (a + ·)) :=
    (List.mergeSort_perm _ _).trans ((List.mergeSort_perm xs _).symm.map (a + ·))
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba)
    (pairwise_le_mergeSort _) hpair hperm

private theorem add_trimmedMidpoint [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : K) (t : ℕ) {xs : List K} (hlen : 2 * t < xs.length) :
    a + trimmedMidpoint t xs = trimmedMidpoint t (xs.map (a + ·)) := by
  have hs_len : (xs.mergeSort (· ≤ ·)).length = xs.length := List.length_mergeSort xs
  have hlen' : 2 * t < (xs.mergeSort (· ≤ ·)).length := by omega
  simp only [trimmedMidpoint_eq_mergeSort, hlen', ↓reduceDIte, mergeSort_map_add,
    List.length_map, List.getElem_map]
  ring

private theorem pairwise_rel_of_le [LinearOrder K] {s : List K} (hs : s.Pairwise (· ≤ ·))
    {i j : ℕ} (hi : i < s.length) (hj : j < s.length) (hij : i ≤ j) : s[i] ≤ s[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp hs i j hi hj hlt

private theorem getElem_le_of_lt_countP [LinearOrder K] {s : List K} (hs : s.Pairwise (· ≤ ·))
    {k : ℕ} (hk : k < s.length) {B : K} (hcnt : k < s.countP (· ≤ B)) : s[k] ≤ B := by
  by_contra hlt
  rw [not_le] at hlt
  have hdrop : (s.drop k).countP (· ≤ B) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    have hky : s[k] ≤ s[k + i] := pairwise_rel_of_le hs hk (by omega) (by omega)
    simp only [decide_eq_true_eq, not_le]
    exact hlt.trans_le hky
  have hsplit : s.countP (· ≤ B) = (s.take k).countP (· ≤ B) + (s.drop k).countP (· ≤ B) := by
    conv_lhs => rw [← List.take_append_drop k s, List.countP_append]
  have htake : (s.take k).countP (· ≤ B) ≤ k := by
    calc (s.take k).countP (· ≤ B)
        ≤ (s.take k).length := List.countP_le_length
      _ = min k s.length := List.length_take
      _ ≤ k := Nat.min_le_left _ _
  omega

private theorem le_getElem_of_sub_le_countP [LinearOrder K] {s : List K} (hs : s.Pairwise (· ≤ ·))
    {k : ℕ} (hk : k < s.length) {B : K} (hcnt : s.length - k ≤ s.countP (B ≤ ·)) :
    B ≤ s[k] := by
  by_contra hlt
  rw [not_le] at hlt
  have htake : (s.take (k + 1)).countP (B ≤ ·) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    have hyk : s[i] ≤ s[k] := pairwise_rel_of_le hs (by omega) hk (by omega)
    simp only [decide_eq_true_eq, not_le]
    exact hyk.trans_lt hlt
  have hsplit :
      s.countP (B ≤ ·) = (s.take (k + 1)).countP (B ≤ ·) + (s.drop (k + 1)).countP (B ≤ ·) := by
    conv_lhs => rw [← List.take_append_drop (k + 1) s, List.countP_append]
  have hdrop : (s.drop (k + 1)).countP (B ≤ ·) ≤ s.length - (k + 1) := by
    calc (s.drop (k + 1)).countP (B ≤ ·)
        ≤ (s.drop (k + 1)).length := List.countP_le_length
      _ = s.length - (k + 1) := List.length_drop
  omega

private theorem sub_le_countP_self [LinearOrder K] {s : List K} (hs : s.Pairwise (· ≤ ·))
    {k : ℕ} (hk : k < s.length) : k + 1 ≤ s.countP (· ≤ s[k]) := by
  set v := s[k]
  have htake_eq : (s.take (k + 1)).countP (· ≤ v) = (s.take (k + 1)).length := by
    rw [List.countP_eq_length]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    simp only [decide_eq_true_eq]
    exact pairwise_rel_of_le hs (by omega) hk (by omega)
  have hlen : (s.take (k + 1)).length = k + 1 := List.length_take_of_le (by omega)
  have hsplit :
      s.countP (· ≤ v) =
        (s.take (k + 1)).countP (· ≤ v) + (s.drop (k + 1)).countP (· ≤ v) := by
    conv_lhs => rw [← List.take_append_drop (k + 1) s, List.countP_append]
  omega

end TrimmedMidpoint

/-! ### 1-round and `R`-round Byzantine clock resynchronization -/

private theorem countP_mergeSort_map_eq_card_filter {P : Type u} [Fintype P]
    {K : Type v} [LinearOrder K] {xs : List P}
    (hxs : (xs : Multiset P) = Finset.univ.val) (f : P → K)
    (pred : K → Prop) [DecidablePred pred] :
    ((xs.map f).mergeSort (· ≤ ·)).countP (fun x => decide (pred x)) =
      (Finset.univ.filter (fun j => pred (f j))).card := by
  rw [(List.mergeSort_perm _ _).countP_eq, ← Multiset.coe_countP]
  have hmap : ((xs.map f : List K) : Multiset K) = Finset.univ.val.map f := by
    rw [← hxs]; rfl
  rw [hmap, Multiset.countP_map]
  simp only [Finset.card_def, Finset.filter_val]

section ByzantineProtocol

variable {P : Type u} [Fintype P] [DecidableEq P]
variable {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- 1-round Byzantine-resilient trimmed-midpoint clock adjustment step
[Welch and Lynch][WelchLynch1988]: process `p` forms `estDiff d_min d_max p recv j` from its
observed arrival readings `recv : P → K` across all senders `j : P`, discards the `t` smallest and
`t` largest estimates, and outputs the midpoint of the remaining range. -/
@[expose] def byzantineClockStep (t : ℕ) (d_min d_max : K) (p : P) (recv : P → K) : K :=
  multisetTrimmedMidpoint t (Finset.univ.val.map (estDiff d_min d_max p recv))

/-- Arrival reading observed at `p` from sender `j` in a 1-round synchronization broadcast with
faulty processes `F` and equivocating adversary `adv`: a faulty clock `j ∈ F` induces an arbitrary
recipient-dependent timestamp `adv j p`, whereas an honest clock `j ∉ F` sends at local reading
`0` and arrives at `arrivalReading c (fun _ => δ) 0 j p 0`. -/
@[expose] def byzantineArrival {P : Type u} [DecidableEq P] {K : Type v} [AddCommGroup K]
    (F : Finset P) (adv : P → P → K) (c : P → K) (δ : P → P → K) (j p : P) : K :=
  if j ∈ F then adv j p else arrivalReading c (fun _ => δ) 0 j p 0

/-- Process `p`'s updated synchronized clock offset after one round of `byzantineClockStep` under
faulty set `F`, equivocating adversary `adv`, initial offsets `c`, and transit delays `δ`. -/
@[expose] def byzantineSyncOffset (t : ℕ) (d_min d_max : K) (F : Finset P) (adv : P → P → K)
    (c : P → K) (δ : P → P → K) (p : P) : K :=
  c p + byzantineClockStep t d_min d_max p (fun j => byzantineArrival F adv c δ j p)

/-- Updated clock offsets after `R` sequential resynchronization rounds against round-indexed
equivocating adversaries `adv : ℕ → P → P → K` and round transit delays `δ : ℕ → P → P → K`. -/
@[expose] def byzantineSyncOffsetIter (t : ℕ) (d_min d_max : K) (F : Finset P)
    (adv : ℕ → P → P → K) (c : P → K) (δ : ℕ → P → P → K) : ℕ → P → K
  | 0 => c
  | r + 1 =>
    byzantineSyncOffset t d_min d_max F (adv r)
      (byzantineSyncOffsetIter t d_min d_max F adv c δ r) (δ r)

private theorem syncOffset_eq_trimmedMidpoint_list {xs : List P}
    (hxs : (xs : Multiset P) = Finset.univ.val) (t : ℕ) (ht : 2 * t < Fintype.card P)
    (d_min d_max : K) (F : Finset P) (adv : P → P → K) (c : P → K) (δ : P → P → K) (p : P) :
    byzantineSyncOffset t d_min d_max F adv c δ p =
      trimmedMidpoint t
        (xs.map (fun j =>
          c p + estDiff d_min d_max p (fun k => byzantineArrival F adv c δ k p) j)) := by
  have hlen : xs.length = Fintype.card P := by
    have hcard := congrArg Multiset.card hxs
    rw [Multiset.coe_card] at hcard
    exact hcard
  dsimp only [byzantineSyncOffset, byzantineClockStep]
  rw [← hxs]
  change c p + trimmedMidpoint t (xs.map _) = _
  rw [add_trimmedMidpoint (c p) t (by rw [List.length_map, hlen]; exact ht), List.map_map]
  rfl

private theorem sorted_endpoints_bounds {xs : List P} (hxs : (xs : Multiset P) = Finset.univ.val)
    {t : ℕ} (ht : 2 * t < Fintype.card P) {F : Finset P} (hF : F.card ≤ t)
    {d_min d_max lo hi : K} (hd : d_min ≤ d_max) (adv : P → P → K) (c : P → K) (δ : P → P → K)
    (hc : ∀ j ∉ F, lo ≤ c j ∧ c j ≤ hi)
    (hδ : ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ j p ∧ δ j p ≤ d_max)
    {p : P} (hp : p ∉ F) :
    let x := fun j => c p + estDiff d_min d_max p (fun k => byzantineArrival F adv c δ k p) j
    let s := (xs.map x).mergeSort (· ≤ ·)
    have hlt : 2 * t < s.length := by
      have hcard := congrArg Multiset.card hxs
      rw [Multiset.coe_card] at hcard
      rw [List.length_mergeSort, List.length_map, hcard]
      exact ht
    lo - (d_max - d_min) / 2 ≤ s[t]'(by omega) ∧
      s[s.length - 1 - t]'(by omega) ≤ hi + (d_max - d_min) / 2 := by
  intro x s hlt
  set n := Fintype.card P
  set e : K := (d_max - d_min) / 2
  have hlen : xs.length = n := by
    have hcard := congrArg Multiset.card hxs
    rw [Multiset.coe_card] at hcard
    exact hcard
  have hs_len : s.length = n := by rw [List.length_mergeSort, List.length_map, hlen]
  have hs_pair : s.Pairwise (· ≤ ·) := pairwise_le_mergeSort _
  have hx_honest : ∀ j ∉ F, lo - e ≤ x j ∧ x j ≤ hi + e := by
    intro j hj
    have herr := abs_add_estDiff_sub_le hd c p j (fun k => byzantineArrival F adv c δ k p)
      (d := δ j p)
      (fun _ => by simp only [byzantineArrival, hj, ↓reduceIte, arrivalReading, zero_add])
      (fun _ => (hδ j hj p hp).1) (fun _ => (hδ j hj p hp).2)
    rw [abs_le] at herr
    change -e ≤ x j - c j ∧ x j - c j ≤ e at herr
    have hcj := hc j hj
    exact ⟨by linarith, by linarith⟩
  have hhonest_card : n - t ≤ (Finset.univ \ F).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ]
    omega
  constructor
  · apply le_getElem_of_sub_le_countP hs_pair (by omega)
    rw [hs_len, countP_mergeSort_map_eq_card_filter hxs x (lo - e ≤ ·)]
    refine hhonest_card.trans (Finset.card_le_card fun j hj => ?_)
    rw [Finset.mem_sdiff] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hx_honest j hj.2).1
  · apply getElem_le_of_lt_countP hs_pair (by omega)
    rw [hs_len, countP_mergeSort_map_eq_card_filter hxs x (· ≤ hi + e)]
    have hcard : n - t ≤ (Finset.univ.filter (fun j => x j ≤ hi + e)).card := by
      refine hhonest_card.trans (Finset.card_le_card fun j hj => ?_)
      rw [Finset.mem_sdiff] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hx_honest j hj.2).2
    omega

/-- **Honest-interval accuracy of a synchronous drift-free `byzantineClockStep` round** (adapting
the midpoint convergence step of [Welch and Lynch][WelchLynch1988] to a separated synchronous
round on drift-free clocks): when `2 * t < Fintype.card P`, `F.card ≤ t`, every honest process's
initial offset lies in `[lo, hi]`, and honest-to-honest transit delays lie in `[d_min, d_max]`,
every honest process's updated offset lies in
`[lo - (d_max - d_min) / 2, hi + (d_max - d_min) / 2]`. -/
theorem byzantineSyncOffset_mem_Icc {t : ℕ} (ht : 2 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {d_min d_max lo hi : K}
    (adv : P → P → K) (c : P → K) (δ : P → P → K)
    (hc : ∀ j ∉ F, lo ≤ c j ∧ c j ≤ hi)
    (hδ : ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ j p ∧ δ j p ≤ d_max)
    {p : P} (hp : p ∉ F) :
    lo - (d_max - d_min) / 2 ≤ byzantineSyncOffset t d_min d_max F adv c δ p ∧
      byzantineSyncOffset t d_min d_max F adv c δ p ≤ hi + (d_max - d_min) / 2 := by
  have hd : d_min ≤ d_max := (hδ p hp p hp).1.trans (hδ p hp p hp).2
  obtain ⟨xs, hxs⟩ : ∃ xs : List P, (xs : Multiset P) = Finset.univ.val :=
    Quot.inductionOn Finset.univ.val fun xs => ⟨xs, rfl⟩
  let x : P → K :=
    fun j => c p + estDiff d_min d_max p (fun k => byzantineArrival F adv c δ k p) j
  set s := (xs.map x).mergeSort (· ≤ ·)
  have hlt : 2 * t < s.length := by
    have hcard := congrArg Multiset.card hxs
    rw [Multiset.coe_card] at hcard
    rw [List.length_mergeSort, List.length_map, hcard]
    exact ht
  obtain ⟨hlo, hhi⟩ := sorted_endpoints_bounds hxs ht hF hd adv c δ hc hδ hp
  have hs_pair : s.Pairwise (· ≤ ·) := pairwise_le_mergeSort (xs.map x)
  have hord : s[t]'(by omega) ≤ s[s.length - 1 - t]'(by omega) :=
    pairwise_rel_of_le hs_pair (by omega) (by omega) (by omega)
  have hsync : byzantineSyncOffset t d_min d_max F adv c δ p = trimmedMidpoint t (xs.map x) :=
    syncOffset_eq_trimmedMidpoint_list hxs t ht d_min d_max F adv c δ p
  have hmid : byzantineSyncOffset t d_min d_max F adv c δ p =
      (s[t]'(by omega) + s[s.length - 1 - t]'(by omega)) / 2 := by
    rw [hsync, trimmedMidpoint_eq_mergeSort]
    change (if h : 2 * t < s.length then (s[t] + s[s.length - 1 - t]) / 2 else 0) = _
    simp only [hlt, ↓reduceDIte]
  rw [hmid]
  exact ⟨by linarith, by linarith⟩

/-- **Synchronous drift-free Byzantine midpoint convergence step** (adapting the midpoint
convergence step of [Welch and Lynch][WelchLynch1988] to a separated synchronous resynchronization
round on drift-free clocks): when `3 * t < Fintype.card P`, `F.card ≤ t`, initial honest offsets
have skew at most `δ₀`, and honest message delays lie in `[d_min, d_max]`, one round of
`byzantineClockStep` contracts the skew between any two honest processes `p, q ∉ F` to at most
`δ₀ / 2 + (d_max - d_min)`. -/
theorem byzantineSyncOffset_abs_sub_le {t : ℕ} (ht : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {d_min d_max δ₀ : K}
    (adv : P → P → K) (c : P → K) (δ : P → P → K)
    (hc : ∀ p ∉ F, ∀ q ∉ F, |c p - c q| ≤ δ₀)
    (hδ : ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ j p ∧ δ j p ≤ d_max)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    |byzantineSyncOffset t d_min d_max F adv c δ p -
        byzantineSyncOffset t d_min d_max F adv c δ q| ≤
      δ₀ / 2 + (d_max - d_min) := by
  have hd : d_min ≤ d_max := (hδ p hp p hp).1.trans (hδ p hp p hp).2
  set n := Fintype.card P
  set u : K := d_max - d_min
  set e : K := u / 2
  let H : Finset P := Finset.univ \ F
  have hpH : p ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩
  have hH_ne : H.Nonempty := ⟨p, hpH⟩
  let lo : K := H.inf' hH_ne c
  let hi : K := H.sup' hH_ne c
  have hhi_lo : hi - lo ≤ δ₀ := by
    obtain ⟨j_hi, hj_hi, hhi_eq⟩ := Finset.exists_mem_eq_sup' hH_ne c
    obtain ⟨j_lo, hj_lo, hlo_eq⟩ := Finset.exists_mem_eq_inf' hH_ne c
    rw [Finset.mem_sdiff] at hj_hi hj_lo
    have hskew := hc j_hi hj_hi.2 j_lo hj_lo.2
    linarith [le_abs_self (c j_hi - c j_lo)]
  have hc_Icc : ∀ j ∉ F, lo ≤ c j ∧ c j ≤ hi := by
    intro j hj
    have hjH : j ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
    exact ⟨Finset.inf'_le c hjH, Finset.le_sup' c hjH⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : List P, (xs : Multiset P) = Finset.univ.val :=
    Quot.inductionOn Finset.univ.val fun xs => ⟨xs, rfl⟩
  have hlen : xs.length = n := by
    have hcard := congrArg Multiset.card hxs
    rw [Multiset.coe_card] at hcard
    exact hcard
  suffices hdir : ∀ {a b : P}, a ∉ F → b ∉ F →
      byzantineSyncOffset t d_min d_max F adv c δ a -
        byzantineSyncOffset t d_min d_max F adv c δ b ≤ δ₀ / 2 + u by
    exact abs_le.mpr ⟨by linarith [hdir hq hp], hdir hp hq⟩
  intro a b ha hb
  let xa : P → K :=
    fun j => c a + estDiff d_min d_max a (fun k => byzantineArrival F adv c δ k a) j
  let xb : P → K :=
    fun j => c b + estDiff d_min d_max b (fun k => byzantineArrival F adv c δ k b) j
  have hxa_honest : ∀ j ∉ F, |xa j - c j| ≤ e := fun j hj =>
    abs_add_estDiff_sub_le hd c a j _
      (fun _ => by simp only [byzantineArrival, hj, ↓reduceIte, arrivalReading, zero_add])
      (fun _ => (hδ j hj a ha).1) (fun _ => (hδ j hj a ha).2)
  have hxb_honest : ∀ j ∉ F, |xb j - c j| ≤ e := fun j hj =>
    abs_add_estDiff_sub_le hd c b j _
      (fun _ => by simp only [byzantineArrival, hj, ↓reduceIte, arrivalReading, zero_add])
      (fun _ => (hδ j hj b hb).1) (fun _ => (hδ j hj b hb).2)
  have hsync_a : byzantineSyncOffset t d_min d_max F adv c δ a = trimmedMidpoint t (xs.map xa) :=
    syncOffset_eq_trimmedMidpoint_list hxs t (by omega) d_min d_max F adv c δ a
  have hsync_b : byzantineSyncOffset t d_min d_max F adv c δ b = trimmedMidpoint t (xs.map xb) :=
    syncOffset_eq_trimmedMidpoint_list hxs t (by omega) d_min d_max F adv c δ b
  let sa := (xs.map xa).mergeSort (· ≤ ·)
  let sb := (xs.map xb).mergeSort (· ≤ ·)
  have hsa_len : sa.length = n := by rw [List.length_mergeSort, List.length_map, hlen]
  have hsb_len : sb.length = n := by rw [List.length_mergeSort, List.length_map, hlen]
  have hsa_pair : sa.Pairwise (· ≤ ·) := pairwise_le_mergeSort _
  have hsb_pair : sb.Pairwise (· ≤ ·) := pairwise_le_mergeSort _
  have hsb_lo : lo - e ≤ sb[t]'(by omega) :=
    (sorted_endpoints_bounds hxs (by omega) hF hd adv c δ hc_Icc hδ hb).1
  have hsa_hi : sa[sa.length - 1 - t]'(by omega) ≤ hi + e :=
    (sorted_endpoints_bounds hxs (by omega) hF hd adv c δ hc_Icc hδ ha).2
  let M : K := sb[sb.length - 1 - t]'(by omega)
  have hsa_cross : sa[t]'(by omega) ≤ M + u := by
    apply getElem_le_of_lt_countP hsa_pair (by omega)
    rw [countP_mergeSort_map_eq_card_filter hxs xa (· ≤ M + u)]
    set Sb : Finset P := Finset.univ.filter (fun j => xb j ≤ M)
    have hSb_card : n - t ≤ Sb.card := by
      have hcnt := sub_le_countP_self hsb_pair (k := sb.length - 1 - t) (by omega)
      rw [countP_mergeSort_map_eq_card_filter hxs xb (· ≤ M)] at hcnt
      change sb.length - 1 - t + 1 ≤ Sb.card at hcnt
      omega
    have hSb_honest : t < (Sb \ F).card := by
      have hsub : Sb.card - F.card ≤ (Sb \ F).card := Finset.le_card_sdiff F Sb
      omega
    refine hSb_honest.trans_le (Finset.card_le_card fun j hj => ?_)
    rw [Finset.mem_sdiff, Finset.mem_filter] at hj
    obtain ⟨⟨_, hjM⟩, hjF⟩ := hj
    have h1 := (abs_le.mp (hxa_honest j hjF)).2
    have h2 := (abs_le.mp (hxb_honest j hjF)).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have he : 2 * e = u := by dsimp only [e]; ring
    linarith
  have hlt_a : 2 * t < sa.length := by omega
  have hlt_b : 2 * t < sb.length := by omega
  have hmid_a : byzantineSyncOffset t d_min d_max F adv c δ a =
      (sa[t]'(by omega) + sa[sa.length - 1 - t]'(by omega)) / 2 := by
    rw [hsync_a, trimmedMidpoint_eq_mergeSort]
    change (if h : 2 * t < sa.length then (sa[t] + sa[sa.length - 1 - t]) / 2 else 0) = _
    simp only [hlt_a, ↓reduceDIte]
  have hmid_b : byzantineSyncOffset t d_min d_max F adv c δ b =
      (sb[t]'(by omega) + M) / 2 := by
    rw [hsync_b, trimmedMidpoint_eq_mergeSort]
    change (if h : 2 * t < sb.length then (sb[t] + M) / 2 else 0) = _
    simp only [hlt_b, ↓reduceDIte]
  rw [hmid_a, hmid_b]
  have he : 2 * e = u := by dsimp only [e]; ring
  linarith

/-- **Iterated `R`-round synchronous drift-free Byzantine resynchronization bound** (iterating `R`
separated synchronous drift-free rounds of the [Welch and Lynch][WelchLynch1988] midpoint
convergence step): with `3 * t < Fintype.card P` and `F.card ≤ t`, initial honest skew `δ₀`
contracts geometrically to `δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min)`. -/
theorem byzantineSyncOffsetIter_abs_sub_le {t : ℕ} (ht : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {d_min d_max δ₀ : K}
    (adv : ℕ → P → P → K) (c : P → K) (δ : ℕ → P → P → K)
    (hc : ∀ p ∉ F, ∀ q ∉ F, |c p - c q| ≤ δ₀)
    (hδ : ∀ r, ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ r j p ∧ δ r j p ≤ d_max) (R : ℕ) :
    ∀ {p q : P}, p ∉ F → q ∉ F →
      |byzantineSyncOffsetIter t d_min d_max F adv c δ R p -
          byzantineSyncOffsetIter t d_min d_max F adv c δ R q| ≤
        δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min) := by
  induction R with
  | zero =>
    intro p q hp hq
    simp only [byzantineSyncOffsetIter, pow_zero, div_one, sub_self, mul_zero, zero_mul, add_zero]
    exact hc p hp q hq
  | succ r ih =>
    intro p q hp hq
    have hstep := byzantineSyncOffset_abs_sub_le ht hF (adv r)
      (byzantineSyncOffsetIter t d_min d_max F adv c δ r) (δ r)
      (fun a ha b hb => ih ha hb) (hδ r) hp hq
    have halg : (δ₀ / 2 ^ r + 2 * (1 - 1 / 2 ^ r) * (d_max - d_min)) / 2 + (d_max - d_min) =
        δ₀ / 2 ^ (r + 1) + 2 * (1 - 1 / 2 ^ (r + 1)) * (d_max - d_min) := by
      rw [pow_succ]
      ring
    simpa only [byzantineSyncOffsetIter, halg] using hstep

end ByzantineProtocol

end Cslib.Distributed.ClockSync
