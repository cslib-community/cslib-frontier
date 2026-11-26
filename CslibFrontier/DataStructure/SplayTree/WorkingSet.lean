/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.SplayTree.AccessLemma
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Analysis.PSeries

/-!
# Splay-Tree Static Finger and Working-Set Theorems

This module proves two locality bounds of Sleator and Tarjan for sequences of accesses to keys
present in a splay tree, with explicit constants and the cost measure `splaySeqTime` (each access
costs `splayTime = max rotations 1`, [SleatorTarjan1985b], Section 2, p. 658). Both follow from the
Access Lemma with inverse-square weights. The static finger weights `1/(d + 1)²` total at most
`2 + 1 = 3`: the keys at or below `f` have distinct distances `d ≥ 0` and contribute at most
`∑_{k ≥ 1} 1/k² ≤ 2`, and the keys above `f` have distinct distances `d ≥ 1` and contribute at most
`∑_{k ≥ 2} 1/k² ≤ 1`. The working-set weights `1/(t + 1)²` total at most `∑_{k ≥ 1} 1/k² ≤ 2`.

## Main definitions

* `fingerDist s f y`: symmetric-order distance from the finger `f` to `y` among the keys `s`, the
  number of keys of `s` in the half-open interval from `f` (exclusive) to `y` (inclusive). For
  `s = {1, …, n}` and `f, y ∈ s` it is `|y - f|`.
* `recencyRank x l`: the number of distinct keys before the first occurrence of `x` in `l`.
* `workingSetNumbers xs`: the list of `t(j)` from [SleatorTarjan1985b], Section 2, p. 659: the
  number of different keys accessed before access `j` since the last access of the same key, or
  since the beginning of the sequence for a first access.

## Main results

* `splaySeqTime_le_static_finger`: **Static Finger Theorem** ([SleatorTarjan1985b], Section 2,
  Theorem 3, p. 659): for a fixed key `f ∈ t`, `m` accesses to present keys cost at most
  `7m + 6 ∑ⱼ log₂(d(xⱼ) + 1) + n (2 + 2 log₂ n)`.
* `splaySeqTime_le_working_set`: **Working Set Theorem** ([SleatorTarjan1985b], Section 2,
  Theorem 4, pp. 659–660): `m` accesses to present keys cost at most
  `4m + 6 ∑ⱼ log₂(t(j) + 1) + n (1 + 2 log₂ n)`. The proof reassigns the weights
  `1, 1/4, …, 1/n²` in move-to-front order after each access and charges the reassignment through
  `potential_reweight_root_le`.

Both theorems assume every access is to a key stored in the tree, as in the source's analysis of
item accesses; unsuccessful searches are not covered.

## References

* [SleatorTarjan1985b] Daniel Dominic Sleator and Robert Endre Tarjan,
  *Self-Adjusting Binary Search Trees*, Journal of the ACM 32(3), Section 2, pp. 658–660, 1985.
-/

public section

namespace Cslib.DataStructure.SplayTree

open Cslib.DataStructure.SearchTree (elements Ordered)

/-! ### Inverse-Square Sums and Binary-Logarithm Helper -/

/-- An injective `ℕ`-valued map with values at least `c` has `∑ 1/(g(y) + 1)² ≤ 2/(c + 1)`. -/
private theorem sum_inv_sq_le_of_injOn {β : Type*} {s : Finset β} {g : β → ℕ}
    (hg : Set.InjOn g s) (c : ℕ) (hc : ∀ y ∈ s, c ≤ g y) :
    ∑ y ∈ s, 1 / ((g y : ℝ) + 1) ^ 2 ≤ 2 / ((c : ℝ) + 1) := by
  classical
  let N := ∑ y ∈ s, (g y + 2)
  have hsub : s.image (fun y => g y + 1) ⊆ Finset.Ioo c N := by
    refine Finset.image_subset_iff.mpr fun y hy =>
      Finset.mem_Ioo.mpr ⟨by have := hc y hy; omega, ?_⟩
    have := Finset.single_le_sum (f := fun y => g y + 2) (fun _ _ => Nat.zero_le _) hy
    omega
  calc ∑ y ∈ s, 1 / ((g y : ℝ) + 1) ^ 2
      = ∑ k ∈ s.image (fun y => g y + 1), ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_image fun a ha b hb hab => hg ha hb (by omega)]
        refine Finset.sum_congr rfl fun y _ => by push_cast; rw [one_div]
    _ ≤ ∑ k ∈ Finset.Ioo c N, ((k : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 2 / ((c : ℝ) + 1) := sum_Ioo_inv_sq_le c N

private theorem logb_div_inv_sq {C : ℝ} (hC : 0 < C) (k : ℕ) :
    Real.logb 2 (C / (1 / ((k : ℝ) + 1) ^ 2)) =
      Real.logb 2 C + 2 * Real.logb 2 ((k : ℝ) + 1) := by
  rw [div_div_eq_mul_div, div_one, Real.logb_mul hC.ne' (by positivity), Real.logb_pow]
  push_cast
  ring

/-! ### Static Finger Theorem -/

section StaticFinger

variable {α : Type*} [LinearOrder α]

/-- Symmetric-order distance from the finger `f` to `y` among the keys `s`: the number of keys of
`s` in `[y, f)` when `y ≤ f`, and in `(f, y]` when `f < y`. For `s = {1, …, n}` and `f, y ∈ s` this
is `|y - f|`, the distance in [SleatorTarjan1985b], Section 2, Theorem 3, p. 659. -/
@[expose] def fingerDist (s : Finset α) (f y : α) : ℕ :=
  if y ≤ f then (s.filter fun z => y ≤ z ∧ z < f).card
  else (s.filter fun z => f < z ∧ z ≤ y).card

/-- Static finger weight `1/(d(y) + 1)²` ([SleatorTarjan1985b], Section 2, proof of Theorem 3,
p. 659). -/
private noncomputable def fingerWeight (s : Finset α) (f y : α) : ℝ :=
  1 / ((fingerDist s f y : ℝ) + 1) ^ 2

private theorem fingerWeight_pos (s : Finset α) (f y : α) : 0 < fingerWeight s f y := by
  unfold fingerWeight; positivity

/-- The finger distance between keys of `s` is less than `|s|`: the counted keys exclude `f`. -/
theorem fingerDist_lt_card {s : Finset α} {f : α} (hf : f ∈ s) (y : α) :
    fingerDist s f y < s.card := by
  unfold fingerDist
  split_ifs <;> exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨f, hf, by simp⟩)

private theorem fingerDist_strictAntiOn (s : Finset α) (f : α) :
    StrictAntiOn (fingerDist s f) ↑(s.filter (· ≤ f)) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
  simp only [fingerDist, ha.2, hb.2, ↓reduceIte]
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr
    ⟨a, by simp [ha.1, hab.trans_le hb.2], by simp [not_le.mpr hab]⟩)
  intro z hz; simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hab.le.trans hz.2.1, hz.2.2⟩

private theorem fingerDist_strictMonoOn (s : Finset α) (f : α) :
    StrictMonoOn (fingerDist s f) ↑(s.filter fun y => ¬ y ≤ f) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
  simp only [fingerDist, ha.2, hb.2, ↓reduceIte]
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.mpr
    ⟨b, by simp [hb.1, not_le.mp hb.2], by simp [hab]⟩)
  intro z hz; simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hz.2.1, hz.2.2.trans hab.le⟩

private theorem one_le_fingerDist {s : Finset α} {f y : α} (hy : y ∈ s) (hfy : f < y) :
    1 ≤ fingerDist s f y := by
  simp only [fingerDist, not_le.mpr hfy, ↓reduceIte]
  exact Finset.card_pos.mpr ⟨y, by simp [hy, hfy]⟩

/-- The static finger weights have total at most `2 + 1 = 3`: the distances of keys at most `f`
are distinct, and those of keys above `f` are distinct and positive. -/
private theorem sum_fingerWeight_le (s : Finset α) (f : α) :
    ∑ y ∈ s, fingerWeight s f y ≤ 3 := by
  unfold fingerWeight
  rw [← Finset.sum_filter_add_sum_filter_not s (· ≤ f)]
  have h₁ := sum_inv_sq_le_of_injOn (fingerDist_strictAntiOn s f).injOn 0 fun _ _ => Nat.zero_le _
  have h₂ := sum_inv_sq_le_of_injOn (fingerDist_strictMonoOn s f).injOn 1 fun y hy =>
    one_le_fingerDist (Finset.mem_filter.mp hy).1 (not_le.mp (Finset.mem_filter.mp hy).2)
  simp only [one_div, not_le] at h₁ h₂ ⊢
  norm_num at h₁ h₂
  linarith

private theorem logb_two_three_le_two : Real.logb 2 3 ≤ 2 := by
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_two_pow]; norm_num
  exact (Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)).trans_eq h4

/-- **Static Finger Theorem** ([SleatorTarjan1985b], Section 2, Theorem 3, p. 659): let `t` be an
`Ordered` splay tree with `n = |t|` keys and `f ∈ t` a fixed key. A sequence `xs` of `m` accesses to
keys of `t` has total splay time at most
`7m + 6 ∑ⱼ log₂(d(xⱼ) + 1) + n (2 + 2 log₂ n)`, where `d = fingerDist (elements t) f` is the
symmetric-order distance to `f`. The proof assigns static weights `1/(d(y) + 1)²`, with total
at most `3`. -/
theorem splaySeqTime_le_static_finger (xs : List α) {t : BinaryTree α} (ht : Ordered t)
    (hxs : ∀ x ∈ xs, x ∈ elements t) {f : α} (hf : f ∈ elements t) :
    (splaySeqTime xs t : ℝ) ≤ 7 * xs.length +
      6 * (xs.map fun x => Real.logb 2 ((fingerDist (elements t) f x : ℝ) + 1)).sum +
      (elements t).card * (2 + 2 * Real.logb 2 (elements t).card) := by
  set s := elements t
  have hW : subtreeWeight (fingerWeight s f) t ≤ 3 :=
    (subtreeWeight_eq_sum_elements _ ht).symm ▸ sum_fingerWeight_le s f
  have hmain := splaySeqTime_le_fixed_weights (fingerWeight_pos s f) xs ht hxs hW
  have hterm (y : α) : Real.logb 2 (3 / fingerWeight s f y) =
      Real.logb 2 3 + 2 * Real.logb 2 ((fingerDist s f y : ℝ) + 1) :=
    logb_div_inv_sq (by norm_num) (fingerDist s f y)
  have hlog3 := logb_two_three_le_two
  have hacc : (xs.map fun x => 3 * Real.logb 2 (3 / fingerWeight s f x) + 1).sum ≤
      7 * xs.length + 6 * (xs.map fun x => Real.logb 2 ((fingerDist s f x : ℝ) + 1)).sum := by
    clear hmain hxs
    induction xs with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith [hterm x]
  have hdrop : ∑ y ∈ s, Real.logb 2 (3 / fingerWeight s f y) ≤
      s.card * (2 + 2 * Real.logb 2 s.card) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun y _ => ?_
    have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
      (by exact_mod_cast fingerDist_lt_card hf y : (fingerDist s f y : ℝ) + 1 ≤ s.card)
    linarith [hterm y]
  linarith

end StaticFinger

/-! ### Working-Set Numbers and Move-to-Front Ranks -/

section WorkingSetNumbers

variable {α : Type*} [DecidableEq α]

/-- The number of distinct keys before the first occurrence of `x` in `l` (all distinct keys of `l`
when `x ∉ l`). For a duplicate-free `l` this is the position of `x` in `l`; for a reversed access
history it is the position of `x` in the move-to-front list ([SleatorTarjan1985b], Section 2,
p. 659). -/
@[expose] def recencyRank (x : α) (l : List α) : ℕ :=
  (l.takeWhile fun y => y ≠ x).toFinset.card

/-- Sleator–Tarjan working-set numbers ([SleatorTarjan1985b], Section 2, p. 659): entry `j` is
`t(j)`, the number of different keys accessed before access `j` since the last access of `xs[j]`,
or since the beginning of the sequence if access `j` is the first access of `xs[j]`. The reversed
prefix lists earlier accesses from the most recent; `recencyRank` counts the distinct keys before
the most recent earlier access of `xs[j]`. -/
@[expose] def workingSetNumbers (xs : List α) : List ℕ :=
  xs.mapIdx fun j x => recencyRank x (xs.take j).reverse

@[simp] theorem length_workingSetNumbers (xs : List α) :
    (workingSetNumbers xs).length = xs.length :=
  List.length_mapIdx

/-- Working-set numbers of a suffix `F` after the history `h` (most recent access first). -/
private def wsAux : List α → List α → List ℕ
  | _, [] => []
  | h, x :: F => recencyRank x h :: wsAux (x :: h) F

private theorem wsAux_eq (h F : List α) :
    wsAux h F = F.mapIdx fun j x => recencyRank x ((F.take j).reverse ++ h) := by
  induction F generalizing h with
  | nil => rfl
  | cons x F ih =>
    simp only [wsAux, ih, List.mapIdx_cons, List.take_zero, List.reverse_nil, List.nil_append,
      List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem wsAux_nil (xs : List α) : wsAux [] xs = workingSetNumbers xs := by
  simp only [wsAux_eq, List.append_nil, workingSetNumbers]

private theorem takeWhile_ne_cons_of_ne {a y : α} (h : a ≠ y) (l : List α) :
    (a :: l).takeWhile (fun z => z ≠ y) = a :: l.takeWhile (fun z => z ≠ y) :=
  List.takeWhile_cons_of_pos (p := fun z => decide (z ≠ y)) (decide_eq_true h)

private theorem takeWhile_ne_cons_self (y : α) (l : List α) :
    (y :: l).takeWhile (fun z => z ≠ y) = [] :=
  List.takeWhile_cons_of_neg (p := fun z => decide (z ≠ y)) (by simp)

private theorem not_mem_toFinset_takeWhile_ne (y : α) (l : List α) :
    y ∉ (l.takeWhile fun z => z ≠ y).toFinset := by
  intro hmem
  exact absurd (List.all_eq_true.mp List.all_takeWhile y (List.mem_toFinset.mp hmem)) (by simp)

private theorem takeWhile_ne_append_cons_self (x : α) (h l : List α) :
    (h ++ x :: l).takeWhile (fun y => y ≠ x) = h.takeWhile (fun y => y ≠ x) := by
  induction h with
  | nil => rw [List.nil_append, takeWhile_ne_cons_self, List.takeWhile_nil]
  | cons a h ih =>
    by_cases hax : a = x
    · subst a; rw [List.cons_append, takeWhile_ne_cons_self, takeWhile_ne_cons_self]
    · rw [List.cons_append, takeWhile_ne_cons_of_ne hax, takeWhile_ne_cons_of_ne hax, ih]

/-- The rank of `x` just before it is accessed depends only on the history. -/
private theorem recencyRank_append_cons_self (x : α) (h l : List α) :
    recencyRank x (h ++ x :: l) = recencyRank x h := by
  simp only [recencyRank, takeWhile_ne_append_cons_self]

private theorem toFinset_takeWhile_subset (x y : α) (hxy : x ≠ y) (h L : List α) :
    ((h ++ x :: L).takeWhile fun z => z ≠ y).toFinset ⊆
      ((x :: (h ++ L)).takeWhile fun z => z ≠ y).toFinset := by
  rw [takeWhile_ne_cons_of_ne hxy, List.toFinset_cons]
  induction h with
  | nil => rw [List.nil_append, List.nil_append, takeWhile_ne_cons_of_ne hxy, List.toFinset_cons]
  | cons a h ih =>
    by_cases hay : a = y
    · subst a; rw [List.cons_append, takeWhile_ne_cons_self, List.toFinset_nil]
      exact Finset.empty_subset _
    · rw [List.cons_append, List.cons_append, takeWhile_ne_cons_of_ne hay,
        takeWhile_ne_cons_of_ne hay, List.toFinset_cons, List.toFinset_cons]
      exact (Finset.insert_subset_insert a ih).trans (by rw [Finset.insert_comm])

/-- After an access to `x` moves it to the front, no other key's rank decreases
([SleatorTarjan1985b], Section 2, proof of Theorem 4, p. 660). -/
private theorem recencyRank_le_recencyRank_cons {x y : α} (hxy : x ≠ y) (h L : List α) :
    recencyRank y (h ++ x :: L) ≤ recencyRank y (x :: (h ++ L)) :=
  Finset.card_le_card (toFinset_takeWhile_subset x y hxy h L)

/-- Of two distinct keys of `l`, the one occurring first has the smaller prefix, and the other's
prefix contains it. -/
private theorem takeWhile_ne_subset_or (l : List α) {y y' : α} (hy : y ∈ l) (hy' : y' ∈ l)
    (hne : y ≠ y') :
    ((l.takeWhile fun z => z ≠ y).toFinset ⊆ (l.takeWhile fun z => z ≠ y').toFinset ∧
        y ∈ (l.takeWhile fun z => z ≠ y').toFinset) ∨
      ((l.takeWhile fun z => z ≠ y').toFinset ⊆ (l.takeWhile fun z => z ≠ y).toFinset ∧
        y' ∈ (l.takeWhile fun z => z ≠ y).toFinset) := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rcases eq_or_ne a y with rfl | hay
    · simp [hne]
    rcases eq_or_ne a y' with rfl | hay'
    · simp [hne.symm]
    simp only [takeWhile_ne_cons_of_ne hay, takeWhile_ne_cons_of_ne hay', List.toFinset_cons]
    exact (ih (List.mem_of_ne_of_mem hay.symm hy) (List.mem_of_ne_of_mem hay'.symm hy')).imp
      (fun h => ⟨Finset.insert_subset_insert a h.1, Finset.mem_insert_of_mem h.2⟩)
      (fun h => ⟨Finset.insert_subset_insert a h.1, Finset.mem_insert_of_mem h.2⟩)

private theorem recencyRank_injOn (l : List α) :
    Set.InjOn (recencyRank · l) ↑l.toFinset := by
  intro y hy y' hy' heq
  by_contra hne
  simp only [recencyRank] at heq
  rcases takeWhile_ne_subset_or l (List.mem_toFinset.mp (Finset.mem_coe.mp hy))
      (List.mem_toFinset.mp (Finset.mem_coe.mp hy')) hne with ⟨hsub, hmem⟩ | ⟨hsub, hmem⟩ <;>
    · have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
        ⟨_, hmem, not_mem_toFinset_takeWhile_ne _ l⟩)
      omega

private theorem recencyRank_lt_card {l : List α} {y : α} (hy : y ∈ l) :
    recencyRank y l < l.toFinset.card :=
  Finset.card_lt_card (Finset.ssubset_iff_of_subset
    (fun _ hz =>
      List.mem_toFinset.mpr ((List.takeWhile_sublist _).subset (List.mem_toFinset.mp hz)))
    |>.mpr ⟨y, List.mem_toFinset.mpr hy, not_mem_toFinset_takeWhile_ne y l⟩)

/-- The move-to-front ranks of the keys of `l` are exactly `0, …, |l| - 1`. -/
private theorem image_recencyRank (l : List α) :
    l.toFinset.image (recencyRank · l) = Finset.range l.toFinset.card := by
  refine Finset.eq_of_subset_of_card_le (fun k hk => ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (recencyRank_lt_card (List.mem_toFinset.mp hy))
  · rw [Finset.card_range, Finset.card_image_of_injOn (recencyRank_injOn l)]

/-- Move-to-front weights `1/(k + 1)²` for the key of rank `k` ([SleatorTarjan1985b], Section 2,
proof of Theorem 4, p. 660). -/
private noncomputable def mtfWeight (l : List α) (y : α) : ℝ :=
  1 / ((recencyRank y l : ℝ) + 1) ^ 2

private theorem mtfWeight_pos (l : List α) (y : α) : 0 < mtfWeight l y := by
  unfold mtfWeight; positivity

/-- The move-to-front weights permute `1, 1/4, …, 1/|l|²`, so their total depends only on the set
of keys. -/
private theorem sum_mtfWeight (l : List α) :
    ∑ y ∈ l.toFinset, mtfWeight l y =
      ∑ k ∈ Finset.range l.toFinset.card, 1 / ((k : ℝ) + 1) ^ 2 := by
  rw [← image_recencyRank, Finset.sum_image (recencyRank_injOn l)]
  rfl

private theorem sum_range_inv_sq_le_two (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  simpa using
    sum_inv_sq_le_of_injOn (s := Finset.range n) (Set.injOn_id _) 0 fun _ _ => Nat.zero_le _

end WorkingSetNumbers

/-! ### Working Set Theorem -/

section WorkingSet

variable {α : Type*} [LinearOrder α]

/-- Amortized per-access charge `6 log₂(k + 1) + 4` for working-set number `k`. -/
private noncomputable def wsCharge (k : ℕ) : ℝ :=
  6 * Real.logb 2 ((k : ℝ) + 1) + 4

private theorem sum_map_wsCharge (l : List ℕ) :
    (l.map wsCharge).sum =
      6 * (l.map fun k : ℕ => Real.logb 2 ((k : ℝ) + 1)).sum + 4 * l.length := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_add, Nat.cast_one,
      wsCharge]
    ring

private theorem sum_mtfWeight_congr {l l' : List α} (h : l'.toFinset = l.toFinset) :
    ∑ y ∈ l.toFinset, mtfWeight l' y = ∑ y ∈ l.toFinset, mtfWeight l y := by
  rw [← h, sum_mtfWeight, h, sum_mtfWeight]

/-- Telescoping invariant for the Working Set Theorem. After the reversed history `h` and before
the remaining accesses `F`, the weights are `mtfWeight (h ++ F ++ R)`: the move-to-front order
initialized in order of first access, with the never-accessed keys `R` last. Each access costs at
most `6 log₂(t(j) + 1) + 4` in amortized time, and the reassignment after it does not increase the
potential (`potential_reweight_root_le`). -/
private theorem splaySeqTime_mtf_telescoping (F : List α) {h R : List α} {t : BinaryTree α}
    (ht : Ordered t) (hset : (h ++ F ++ R).toFinset = elements t) :
    (splaySeqTime F t : ℝ) + potential (mtfWeight (F.reverse ++ h ++ R)) (splaySeq F t).1 -
        potential (mtfWeight (h ++ F ++ R)) t ≤ ((wsAux h F).map wsCharge).sum := by
  induction F generalizing h t with
  | nil => simp [wsAux]
  | cons x F ih =>
    have hx : x ∈ elements t := hset ▸ by simp
    have ho' : Ordered (splay x t).tree := ordered_splay ht x
    have he' : elements (splay x t).tree = elements t := elements_splay x t
    have hset₁ : (x :: h ++ F ++ R).toFinset = elements (splay x t).tree := by
      rw [he', ← hset]; ext z
      simp only [List.mem_toFinset, List.mem_append, List.mem_cons]; tauto
    -- Access step: the Access Lemma with the current weights `mtfWeight (h ++ x :: F ++ R)`.
    have hacc := splay_splayTime_amortized_le_of_mem (mtfWeight_pos (h ++ x :: F ++ R)) ht hx
    have hlog : Real.logb 2 (subtreeWeight (mtfWeight (h ++ x :: F ++ R)) t /
        mtfWeight (h ++ x :: F ++ R) x) ≤ 1 + 2 * Real.logb 2 ((recencyRank x h : ℝ) + 1) := by
      have hW₀ : subtreeWeight (mtfWeight (h ++ x :: F ++ R)) t ≤ 2 := by
        rw [subtreeWeight_eq_sum_elements _ ht, ← hset, sum_mtfWeight]
        exact sum_range_inv_sq_le_two _
      have hwx := mtfWeight_pos (h ++ x :: F ++ R) x
      have hWpos : 0 < subtreeWeight (mtfWeight (h ++ x :: F ++ R)) t :=
        subtreeWeight_pos (mtfWeight_pos _) (by rintro rfl; simp [elements] at hx)
      refine (Real.logb_le_logb_of_le (b := 2) (by norm_num) (div_pos hWpos hwx)
        (div_le_div_of_nonneg_right hW₀ hwx.le)).trans_eq ?_
      rw [mtfWeight, List.append_assoc, List.cons_append, recencyRank_append_cons_self,
        logb_div_inv_sq (by norm_num), Real.logb_self_eq_one (by norm_num)]
    -- Reassignment step: `x` is at the root and receives weight `1`; no other weight increases.
    have hre := potential_reweight_root_le (w := mtfWeight (h ++ x :: F ++ R))
      (w' := mtfWeight (x :: h ++ F ++ R)) (mtfWeight_pos _) ho' (rootKey_splay_of_mem ht hx)
      (by rw [subtreeWeight_eq_sum_elements _ ho', subtreeWeight_eq_sum_elements _ ho', ← hset₁]
          exact (sum_mtfWeight_congr (hset.trans (he'.symm.trans hset₁.symm))).symm)
      fun y _ hyx => by
        have hle : recencyRank y (h ++ x :: F ++ R) ≤ recencyRank y (x :: h ++ F ++ R) := by
          simpa only [List.append_assoc, List.cons_append] using
            recencyRank_le_recencyRank_cons (Ne.symm hyx) h (F ++ R)
        unfold mtfWeight; gcongr
    have hrest := ih (h := x :: h) ho' hset₁
    rw [show (x :: F).reverse ++ h ++ R = F.reverse ++ x :: h ++ R by simp,
      show splaySeqTime (x :: F) t = splayTime (splay x t) + splaySeqTime F (splay x t).tree
        from rfl,
      show (splaySeq (x :: F) t).1 = (splaySeq F (splay x t).tree).1 from rfl,
      show ((wsAux h (x :: F)).map wsCharge).sum =
        wsCharge (recencyRank x h) + ((wsAux (x :: h) F).map wsCharge).sum from rfl,
      Nat.cast_add]
    simp only [wsCharge]
    linarith

/-- **Working Set Theorem** ([SleatorTarjan1985b], Section 2, Theorem 4, pp. 659–660): let `t` be
an `Ordered` splay tree with `n = |t|` keys. A sequence `xs` of `m` accesses to keys of `t` has
total splay time at most `4m + 6 ∑ⱼ log₂(t(j) + 1) + n (1 + 2 log₂ n)`, where
`t(j) = (workingSetNumbers xs)[j]` is the number of different keys accessed before access `j`
since the last access of `xs[j]`, or since the beginning if access `j` is the first access of
`xs[j]`.

The proof follows Sleator and Tarjan: the weights `1, 1/4, …, 1/n²` are assigned in move-to-front
order (initially in order of first access, never-accessed keys last), so the key accessed at step
`j` has weight `1/(t(j) + 1)²` and the total weight is at most `2`. After each access the weights
are reassigned with the accessed key, now at the root, moved to the front; this reassignment keeps
the root size and decreases every other size, so it does not increase the potential. -/
theorem splaySeqTime_le_working_set (xs : List α) {t : BinaryTree α} (ht : Ordered t)
    (hxs : ∀ x ∈ xs, x ∈ elements t) :
    (splaySeqTime xs t : ℝ) ≤ 4 * xs.length +
      6 * ((workingSetNumbers xs).map fun k : ℕ => Real.logb 2 ((k : ℝ) + 1)).sum +
      (elements t).card * (1 + 2 * Real.logb 2 (elements t).card) := by
  let R := (elements t).toList
  have hset : ([] ++ xs ++ R).toFinset = elements t := by
    ext z
    simp only [List.nil_append, List.mem_toFinset, List.mem_append, Finset.mem_toList, R]
    exact ⟨fun hz => hz.elim (hxs z) id, Or.inr⟩
  have htel := splaySeqTime_mtf_telescoping xs ht hset
  rw [wsAux_nil, sum_map_wsCharge, length_workingSetNumbers] at htel
  obtain ⟨ho_end, he_end⟩ := splaySeq_ordered_and_elements xs ht
  have hW : subtreeWeight (mtfWeight ([] ++ xs ++ R)) t ≤ 2 := by
    rw [subtreeWeight_eq_sum_elements _ ht, ← hset, sum_mtfWeight]
    exact sum_range_inv_sq_le_two _
  -- Initial potential: total weight at most `2`, so every rank is at most `1`.
  have hΦ₀ := potential_le_sum_logb_of_le (mtfWeight_pos ([] ++ xs ++ R)) ht hW
  rw [Real.logb_self_eq_one (by norm_num), Finset.sum_const, nsmul_eq_mul, mul_one] at hΦ₀
  -- Final potential: every final weight is at least `1/n²`.
  have hsetₘ : (xs.reverse ++ [] ++ R).toFinset = elements t := by
    ext z
    simp [← hset]
  have hΦₘ : -((elements t).card * (2 * Real.logb 2 (elements t).card)) ≤
      potential (mtfWeight (xs.reverse ++ [] ++ R)) (splaySeq xs t).1 := by
    refine le_trans ?_ (he_end ▸ sum_logb_weight_le_potential
      (mtfWeight_pos (xs.reverse ++ [] ++ R)) ho_end)
    rw [← nsmul_eq_mul, ← neg_nsmul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun y hy => ?_
    have hy' : y ∈ xs.reverse ++ [] ++ R := List.mem_toFinset.mp (hsetₘ.symm ▸ hy)
    have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by positivity : (0 : ℝ) < (recencyRank y (xs.reverse ++ [] ++ R) : ℝ) + 1)
      (by exact_mod_cast hsetₘ ▸ recencyRank_lt_card hy' :
        (recencyRank y (xs.reverse ++ [] ++ R) : ℝ) + 1 ≤ (elements t).card)
    rw [mtfWeight, one_div, Real.logb_inv, Real.logb_pow]
    push_cast
    linarith
  linarith

end WorkingSet

end Cslib.DataStructure.SplayTree
