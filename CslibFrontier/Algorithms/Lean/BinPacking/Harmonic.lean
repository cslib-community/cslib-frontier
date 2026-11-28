/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BinPacking.Online
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Harmonic_k uses at most `T_k * OPT + k` bins

Harmonic_k of [Lee and Lee][LeeLee1985] is an online bin-packing algorithm that keeps at most `k`
bins open. With bin capacity `C`, an item of size `a` has class `i < k` if
`C / (i + 1) < a ≤ C / i`, and class `k` if `a ≤ C / k` (`harmonicClass`). Each class is packed
on its own: items of class `i < k` go `i` to a bin, and items of class `k` by Next Fit.
`harmonicPacker k C` is Harmonic_k as an `OnlinePacker C`: an item goes into the most recently
opened bin of its class if it fits there, and otherwise into a new bin. For `i < k`, an item of
class `i` fits into a bin of `j` items of class `i` exactly when `j < i`. Like every online
packer, it packs every list of items that fit into a bin (`OnlinePacker.isPacking_run`).

The analysis is Lee and Lee's weighting argument, with sizes in `ℕ` and weights in `ℚ`. An item
of class `i < k` weighs `1 / i`, and an item of class `k` and size `a` weighs
`k / (k - 1) * a / C` (`harmonicWeight`).

* **Harmonic_k's bins.** All bins but the last of each class weigh at least `1`
  (`length_run_harmonicPacker_le_sum`). A bin of class `i < k` was closed because it held `i`
  items of weight `1 / i`. A bin of class `k` was closed by an item of size at most `C / k` that
  did not fit, so it is more than `(k - 1) / k` full. So Harmonic_k uses at most the items' total
  weight plus `k` bins.
* **Every bin.** Items of total size at most `C` weigh at most Lee and Lee's constant
  `T_k = harmonicRatio k` (`sum_map_harmonicWeight_le`). With Sylvester's numbers
  `t₀ = 2, t₁ = 3, t₂ = 7, t₃ = 43, …` (`sylvester`) and `m` the least index with `k ≤ t_m - 1`,
  `T_k = 1 / (t₀ - 1) + ⋯ + 1 / (t_{m-1} - 1) + k / ((k - 1) * (t_m - 1))`; so `T₃ = 7/4`,
  `T₄ = 31/18`, `T₅ = 41/24`, `T₆ = 17/10` and `T₇ = 61/36`. The proof is by induction along
  the greedy bound (`harmonicTail`): items of total size at most `C / u` with `u = t_j - 1 < k`
  either include an item of class `u`, of weight `1 / u`, and then the others have total size at
  most `C / (u * (u + 1)) = C / (t_{j+1} - 1)`, or weigh at most `max ((u + 2) / (u + 1),
  k / (k - 1))` times their total size over `C`.
* **The bound** (`length_run_harmonicPacker_le`). Summing over the bins of any packing `Q` of the
  same items, in particular an optimal one, Harmonic_k uses at most `T_k * Q.length + k` bins. So
  its asymptotic competitive ratio is at most `T_k`, with additive constant `k`.

Lee and Lee also show that the ratio `T_k` is attained by Harmonic_k and prove lower bounds for
online algorithms that keep a bounded number of bins open; neither is formalized here.
`CslibFrontier.Algorithms.Lean.BinPacking.HarmonicLimit` compares `T_k` with `T∞ ≈ 1.69103`.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.harmonicClass`: the class of an item.
* `Cslib.Algorithms.Lean.BinPacking.harmonicPacker`: Harmonic_k as an online packer.
* `Cslib.Algorithms.Lean.BinPacking.harmonicWeight`: the weight of an item.
* `Cslib.Algorithms.Lean.BinPacking.sylvester`: Sylvester's sequence.
* `Cslib.Algorithms.Lean.BinPacking.harmonicRatio`: Lee and Lee's constant `T_k`.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.length_run_harmonicPacker_le_sum`: Harmonic_k uses at most
  the items' total weight plus `k` bins.
* `Cslib.Algorithms.Lean.BinPacking.sum_map_harmonicWeight_le`: a bin weighs at most `T_k`.
* `Cslib.Algorithms.Lean.BinPacking.length_run_harmonicPacker_le`: Harmonic_k uses at most
  `T_k * OPT + k` bins.

## References

* [C. C. Lee, D. T. Lee, *A simple on-line bin-packing algorithm*][LeeLee1985]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open scoped List

/-- The class of an item of size `a` for Harmonic_k with bin capacity `C`: `k` if `a ≤ C / k`,
and otherwise `⌊C / a⌋`, the `i` with `C / (i + 1) < a ≤ C / i`. An item that fits into a bin
and is larger than `C / k` has a class `i` with `1 ≤ i < k`. -/
@[expose] def harmonicClass (k C a : ℕ) : ℕ := if k * a ≤ C then k else C / a

/-- The class of a bin for Harmonic_k: the class of its first item (`0` for an empty bin). -/
@[expose] def harmonicBinClass (k C : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: _ => harmonicClass k C a

/-- The index of the last bin of class `c` for Harmonic_k, if any. -/
@[expose] def harmonicLastBin (k C c : ℕ) : List (List ℕ) → Option ℕ
  | [] => none
  | b :: bs =>
    match harmonicLastBin k C c bs with
    | some i => some (i + 1)
    | none => if harmonicBinClass k C b = c then some 0 else none

/-- **Harmonic_k** of [Lee and Lee][LeeLee1985] as an online packer: an item of class `c` goes
into the most recently opened bin of class `c` if it fits there, and otherwise into a new bin.
For `c < k` an item of class `c` fits into a bin of class `c` exactly when the bin holds fewer
than `c` items, so items of class `c` are packed `c` to a bin; items of class `k` are packed by
Next Fit. -/
@[expose] def harmonicPacker (k C : ℕ) : OnlinePacker C :=
  ⟨fun _ bins a => harmonicLastBin k C (harmonicClass k C a) bins⟩

/-- The weight of an item of size `a` for Harmonic_k, as a fraction of a bin: `1 / i` for an
item of class `i < k`, and `k / (k - 1) * a / C` for an item of class `k`. -/
def harmonicWeight (k C a : ℕ) : ℚ :=
  if k * a ≤ C then k / ((k - 1) * C) * a else 1 / (C / a : ℕ)

/-! ### Harmonic_k's packing -/

private theorem onlineInsert_none (C a : ℕ) :
    ∀ bins : List (List ℕ), onlineInsert C a none bins = bins ++ [[a]]
  | [] => rfl
  | b :: bs => by simp [onlineInsert, onlineInsert_none C a bs]

private theorem onlineInsert_some_length (C a : ℕ) (b : List ℕ) (B : List (List ℕ)) :
    ∀ A : List (List ℕ), onlineInsert C a (some A.length) (A ++ b :: B) =
      if b.sum + a ≤ C then A ++ (b ++ [a]) :: B else A ++ b :: B ++ [[a]]
  | [] => by
    simp only [List.length_nil, List.nil_append, onlineInsert]
    split_ifs <;> simp [onlineInsert_none]
  | x :: A => by
    simp only [List.length_cons, List.cons_append, onlineInsert, onlineInsert_some_length C a b B A]
    split_ifs <;> simp

private theorem harmonicLastBin_spec (k C c : ℕ) : ∀ bins : List (List ℕ),
    (harmonicLastBin k C c bins = none ∧ ∀ b ∈ bins, harmonicBinClass k C b ≠ c) ∨
      ∃ A b B, bins = A ++ b :: B ∧ harmonicLastBin k C c bins = some A.length ∧
        harmonicBinClass k C b = c ∧ ∀ y ∈ B, harmonicBinClass k C y ≠ c
  | [] => .inl ⟨rfl, by simp⟩
  | b :: bs => by
    rcases harmonicLastBin_spec k C c bs with ⟨h, hn⟩ | ⟨A, b', B, rfl, h, hc, hB⟩
    · by_cases hb : harmonicBinClass k C b = c
      · exact .inr ⟨[], b, bs, rfl, by simp [harmonicLastBin, h, hb], hb, hn⟩
      · exact .inl ⟨by simp [harmonicLastBin, h, hb], by simpa [hb] using hn⟩
    · exact .inr ⟨b :: A, b', B, rfl, by simp [harmonicLastBin, h], hc, hB⟩

variable {k C : ℕ}

private theorem harmonicWeight_of_le {a : ℕ} (h : k * a ≤ C) :
    harmonicWeight k C a = k / ((k - 1) * C) * a := by
  simp [harmonicWeight, h]

private theorem harmonicWeight_of_lt {a : ℕ} (h : C < k * a) :
    harmonicWeight k C a = 1 / (C / a : ℕ) := by
  simp [harmonicWeight, Nat.not_le.2 h]

private theorem harmonicWeight_nonneg (hk : 1 ≤ k) (a : ℕ) : 0 ≤ harmonicWeight k C a := by
  have : (1 : ℚ) ≤ k := by exact_mod_cast hk
  unfold harmonicWeight
  split_ifs
  · have : (0 : ℚ) ≤ k - 1 := by linarith
    positivity
  · positivity

/-- An item of class `k` is at most `C / k`. -/
private theorem mul_le_of_harmonicClass_eq {a : ℕ} (h : harmonicClass k C a = k) : k * a ≤ C := by
  by_contra hka
  simp only [harmonicClass, hka, ite_false] at h
  have : C / a < k := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (by rintro rfl; simp at hka))).2
    (by simpa [Nat.mul_comm] using Nat.lt_of_not_le hka)
  omega

/-- The weight of a bin. -/
private abbrev binWeight (k C : ℕ) (b : List ℕ) : ℚ := (b.map (harmonicWeight k C)).sum

/-- A bin of items of class `k` weighs `k / (k - 1)` times its load, as a fraction of `C`. -/
private theorem binWeight_of_small {b : List ℕ} (h : ∀ x ∈ b, k * x ≤ C) :
    binWeight k C b = k / ((k - 1) * C) * b.sum := by
  rw [binWeight, List.map_congr_left (g := fun x : ℕ => k / ((k - 1) * C) * (x : ℚ))
    fun x hx => harmonicWeight_of_le (h x hx), List.sum_map_mul_left, Nat.cast_list_sum]

/-- **A closed bin is full in the weight sense**: if an item `a` of the same class as all items
of a bin `b` does not fit into `b`, then `b` weighs at least `1`. -/
private theorem one_le_binWeight_of_overflow (hk : 2 ≤ k) {b : List ℕ} {a : ℕ}
    (hb : b.sum ≤ C) (ha : a ≤ C) (hcls : ∀ x ∈ b, harmonicClass k C x = harmonicClass k C a)
    (hover : C < b.sum + a) : 1 ≤ binWeight k C b := by
  by_cases hka : k * a ≤ C
  · have hcl : harmonicClass k C a = k := by simp [harmonicClass, hka]
    have hw := binWeight_of_small (k := k) (C := C) (b := b) fun x hx =>
      mul_le_of_harmonicClass_eq ((hcls x hx).trans hcl)
    have h1 : k * C < k * b.sum + C := by nlinarith
    have h1' : (k : ℚ) * C < k * b.sum + C := by exact_mod_cast h1
    have hC : (0 : ℚ) < C := by exact_mod_cast (show 0 < C by omega)
    have hk' : (1 : ℚ) < k := by exact_mod_cast (show 1 < k by omega)
    rw [hw, div_mul_eq_mul_div, le_div_iff₀ (by nlinarith)]
    nlinarith
  · push Not at hka
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hka)
    set i := C / a with hi
    have hcl : harmonicClass k C a = i := by simp [harmonicClass, Nat.not_le.2 hka, hi]
    have hik : i < k := (Nat.div_lt_iff_lt_mul ha0).2 (by simpa [Nat.mul_comm] using hka)
    have hi1 : 1 ≤ i := (Nat.le_div_iff_mul_le ha0).2 (by omega)
    -- every item of `b` has class `i < k`, so it is at most `C / i` and weighs `1 / i`
    have hx : ∀ x ∈ b, C < k * x ∧ C / x = i := by
      intro x hxb
      have hc := (hcls x hxb).trans hcl
      by_cases hkx : k * x ≤ C
      · simp [harmonicClass, hkx] at hc; omega
      · simp only [harmonicClass, hkx, ite_false] at hc
        exact ⟨Nat.not_le.1 hkx, hc⟩
    have hw : binWeight k C b = b.length * (1 / i) := by
      rw [binWeight, List.map_congr_left (g := fun _ => (1 : ℚ) / i) fun x hxb => by
        rw [harmonicWeight_of_lt (hx x hxb).1, (hx x hxb).2]]
      simp
    have hsum : i * b.sum ≤ b.length * C := by
      have : (b.map (i * ·)).sum ≤ b.length * C := by
        simpa using List.sum_le_length_nsmul (b.map (i * ·)) C (by
          simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          intro x hxb
          have := Nat.div_mul_le_self C x
          rw [(hx x hxb).2] at this
          linarith [Nat.mul_comm x i])
      rwa [List.sum_map_mul_left, List.map_id'] at this
    have hia : i * a ≤ C := by rw [hi]; exact Nat.div_mul_le_self C a
    have hlen : i ≤ b.length := by
      by_contra hlt
      push Not at hlt
      have : i * (b.sum + a) ≤ i * C := by
        rw [Nat.mul_add]
        nlinarith
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega
    have hi' : (0 : ℚ) < i := by exact_mod_cast hi1
    rw [hw, mul_one_div, le_div_iff₀ hi', one_mul]
    exact_mod_cast hlen

/-- The invariant of Harmonic_k's bins: every bin is nonempty, fits, and holds items of a single
class, and every bin with a later bin of the same class weighs at least `1`. -/
private structure Inv (k C : ℕ) (bins : List (List ℕ)) : Prop where
  bin : ∀ b ∈ bins, b ≠ [] ∧ b.sum ≤ C ∧ ∀ x ∈ b, harmonicClass k C x = harmonicBinClass k C b
  pairwise : bins.Pairwise fun b b' =>
    harmonicBinClass k C b = harmonicBinClass k C b' → 1 ≤ binWeight k C b

private theorem harmonicBinClass_append {b : List ℕ} (hb : b ≠ []) (a : ℕ) :
    harmonicBinClass k C (b ++ [a]) = harmonicBinClass k C b := by
  match b, hb with
  | x :: b, _ => rfl

private theorem inv_insert (hk : 2 ≤ k) {bins : List (List ℕ)} {a : ℕ} (h : Inv k C bins)
    (ha : a ≤ C) :
    Inv k C (onlineInsert C a (harmonicLastBin k C (harmonicClass k C a) bins) bins) := by
  have hR := h.pairwise
  rcases harmonicLastBin_spec k C (harmonicClass k C a) bins with
    ⟨hn, hcls⟩ | ⟨A, b, B, rfl, hs, hb, hB⟩
  · -- no bin of the item's class: open one
    rw [hn, onlineInsert_none]
    refine ⟨fun x hx => ?_, List.pairwise_append.2 ⟨hR, by simp, fun x hx y hy hxy => ?_⟩⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact h.bin x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        simp [harmonicBinClass, ha]
    · simp only [List.mem_singleton] at hy
      subst hy
      exact absurd hxy (hcls x hx)
  · have hbin := h.bin b (by simp)
    rw [hs, onlineInsert_some_length]
    split_ifs with hfit
    · -- the item fits into the last bin of its class
      have hba := harmonicBinClass_append (k := k) (C := C) hbin.1 a
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · exact h.bin x (by simp [hx])
        · refine ⟨by simp, by simpa using hfit, fun y hy => ?_⟩
          rw [hba]
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact hbin.2.2 y hy
          · exact hb.symm
        · exact h.bin x (by simp [hx])
      · rw [List.pairwise_append, List.pairwise_cons] at hR ⊢
        refine ⟨hR.1, ⟨fun y hy hxy => absurd (hxy.symm.trans (hba.trans hb)) (hB y hy),
          hR.2.1.2⟩, fun x hx y hy => ?_⟩
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · rw [hba]
          exact hR.2.2 x hx b List.mem_cons_self
        · exact hR.2.2 x hx y (List.mem_cons_of_mem _ hy)
    · -- the item does not fit: open a new bin
      refine ⟨fun x hx => ?_, List.pairwise_append.2 ⟨hR, by simp, fun x hx y hy hxy => ?_⟩⟩
      · rcases List.mem_append.1 hx with hx | hx
        · exact h.bin x (by simpa using hx)
        · simp only [List.mem_singleton] at hx
          subst hx
          simp [harmonicBinClass, ha]
      · simp only [List.mem_singleton] at hy
        subst hy
        simp only [harmonicBinClass] at hxy
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · exact List.Pairwise.rel_of_mem_append hR hx List.mem_cons_self (hxy.trans hb.symm)
        · exact one_le_binWeight_of_overflow hk hbin.2.1 ha
            (fun y hy => (hbin.2.2 y hy).trans hb) (by omega)
        · exact absurd hxy (hB x hx)

private theorem inv_runFrom (hk : 2 ≤ k) :
    ∀ {hist : List ℕ} {bins : List (List ℕ)} {l : List ℕ}, Inv k C bins → (∀ a ∈ l, a ≤ C) →
      Inv k C ((harmonicPacker k C).runFrom hist bins l)
  | _, _, [], h, _ => h
  | _, _, a :: l, h, hl => by
    rw [OnlinePacker.runFrom]
    exact inv_runFrom hk (inv_insert hk h (hl a List.mem_cons_self))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

/-- An item that fits into a bin has a class between `1` and `k`. -/
private theorem harmonicClass_mem (hk : 1 ≤ k) {a : ℕ} (ha : a ≤ C) :
    harmonicClass k C a ∈ Finset.Icc 1 k := by
  rw [Finset.mem_Icc, harmonicClass]
  split_ifs with hka
  · exact ⟨hk, le_rfl⟩
  · have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hka)
    exact ⟨(Nat.le_div_iff_mul_le ha0).2 (by omega),
      ((Nat.div_lt_iff_lt_mul ha0).2 (by simpa [Nat.mul_comm] using Nat.lt_of_not_le hka)).le⟩

/-- If every bin with a later bin of the same class weighs at least `1`, then the number of bins
is at most their total weight plus their number of classes. -/
private theorem length_le_of_pairwise {f : List ℕ → ℕ} {w : List ℕ → ℚ} :
    ∀ {L : List (List ℕ)}, (∀ b ∈ L, 0 ≤ w b) →
      L.Pairwise (fun b b' => f b = f b' → 1 ≤ w b) →
      (L.length : ℚ) ≤ (L.map w).sum + (L.map f).toFinset.card
  | [], _, _ => by simp
  | b :: L, hw, hp => by
    rw [List.pairwise_cons] at hp
    have ih := length_le_of_pairwise (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hp.2
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.toFinset_cons]
    by_cases hb : f b ∈ (L.map f).toFinset
    · rw [Finset.insert_eq_of_mem hb]
      obtain ⟨y, hy, hfy⟩ := List.mem_map.1 (List.mem_toFinset.1 hb)
      have := hp.1 y hy hfy.symm
      push_cast
      linarith
    · rw [Finset.card_insert_of_notMem hb]
      have := hw b List.mem_cons_self
      push_cast
      linarith

private theorem length_le_of_inv (hk : 2 ≤ k) {bins : List (List ℕ)} (h : Inv k C bins) :
    (bins.length : ℚ) ≤ (bins.map (binWeight k C)).sum + k := by
  have h1 := length_le_of_pairwise (fun b _ => List.sum_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact harmonicWeight_nonneg (by omega) y) h.pairwise
  have h2 : (bins.map (harmonicBinClass k C)).toFinset ⊆ Finset.Icc 1 k := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
    obtain ⟨hne, hsum, -⟩ := h.bin b hb
    match b, hne with
    | x :: b', _ =>
      exact harmonicClass_mem (by omega) ((List.le_sum_of_mem List.mem_cons_self).trans hsum)
  have h3 : ((bins.map (harmonicBinClass k C)).toFinset.card : ℚ) ≤ k := by
    exact_mod_cast (Finset.card_le_card h2).trans (by simp)
  linarith

/-- A weight summed over the items of bins that hold exactly `l` is its sum over `l`. -/
private theorem sum_map_eq_of_perm {f : ℕ → ℚ} {l : List ℕ} {F : List (List ℕ)}
    (h : F.flatten ~ l) : (l.map f).sum = (F.map fun b => (b.map f).sum).sum := by
  rw [← (h.map f).sum_eq, List.map_flatten, List.sum_flatten, List.map_map]
  rfl

/-- **Harmonic_k uses at most its total weight plus `k` bins**: all bins but at most one of
each class weigh at least `1`. -/
theorem length_run_harmonicPacker_le_sum (hk : 2 ≤ k) {l : List ℕ} (hl : ∀ a ∈ l, a ≤ C) :
    (((harmonicPacker k C).run l).length : ℚ) ≤ (l.map (harmonicWeight k C)).sum + k := by
  rw [sum_map_eq_of_perm ((harmonicPacker k C).isPacking_run hl).perm]
  exact length_le_of_inv hk (inv_runFrom hk ⟨by simp, List.Pairwise.nil⟩ hl)

/-! ### The weight of a bin -/

/-- **Sylvester's sequence** `2, 3, 7, 43, 1807, …`: `t₀ = 2` and `t_{j+1} = t_j * (t_j - 1) + 1`.
[Lee and Lee][LeeLee1985] index it from `1`. -/
@[expose] def sylvester : ℕ → ℕ
  | 0 => 2
  | j + 1 => sylvester j * (sylvester j - 1) + 1

/-- Sylvester's numbers are at least `2`. -/
theorem two_le_sylvester : ∀ j, 2 ≤ sylvester j
  | 0 => le_rfl
  | j + 1 => by
    have h := two_le_sylvester j
    have := Nat.mul_le_mul h (show 1 ≤ sylvester j - 1 by omega)
    simp only [sylvester]
    omega

/-- Sylvester's numbers minus one, `u_j = t_j - 1`, satisfy `u_{j+1} = u_j * (u_j + 1)`. -/
theorem sylvester_succ_sub_one (j : ℕ) :
    sylvester (j + 1) - 1 = (sylvester j - 1) * (sylvester j - 1 + 1) := by
  have := two_le_sylvester j
  rw [sylvester, Nat.sub_add_cancel (by omega), Nat.add_sub_cancel, Nat.mul_comm]

/-- The greedy bound from `t_j`: with `u = t_j - 1`, `harmonicTail k n j` bounds the weight of
items of total size at most `C / u`. If `u < k`, the largest item may be of class `u`, of weight
`1 / u`, leaving room `C / u - C / (u + 1) = C / (t_{j+1} - 1)`; if `u ≥ k`, every item is of
class `k`. So `harmonicTail k n j` is
`1 / (t_j - 1) + ⋯ + 1 / (t_{m-1} - 1) + k / ((k - 1) * (t_m - 1))` for the least `m ≥ j` with
`k ≤ t_m - 1`, provided `m ≤ j + n`; the fuel `n = k` suffices for `j = 0`. -/
@[expose] def harmonicTail (k : ℕ) : ℕ → ℕ → ℚ
  | 0, j => k / ((k - 1) * ((sylvester j - 1 : ℕ) : ℚ))
  | n + 1, j =>
    if k ≤ sylvester j - 1 then k / ((k - 1) * ((sylvester j - 1 : ℕ) : ℚ))
    else 1 / ((sylvester j - 1 : ℕ) : ℚ) + harmonicTail k n (j + 1)

/-- **Lee and Lee's constant**
`T_k = 1 / (t₀ - 1) + ⋯ + 1 / (t_{m-1} - 1) + k / ((k - 1) * (t_m - 1))` over Sylvester's
numbers `t_j`, for the least `m` with `k ≤ t_m - 1`: `T₃ = 7/4`, `T₄ = 31/18`, `T₅ = 41/24`,
`T₆ = 17/10`, `T₇ = 61/36`. -/
@[expose] def harmonicRatio (k : ℕ) : ℚ := harmonicTail k k 0

/-- `c / C * s ≤ c / u` for a load `s ≤ C / u`. -/
private theorem div_mul_le_div {c : ℚ} (hc : 0 ≤ c) {u s : ℕ} (hu : 1 ≤ u) (hs : u * s ≤ C) :
    c / C * s ≤ c / u := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    positivity
  · have hu' : (0 : ℚ) < u := by exact_mod_cast hu
    have hC' : (0 : ℚ) < C := by exact_mod_cast hC
    have hs' : (u : ℚ) * s ≤ C := by exact_mod_cast hs
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hC' hu']
    nlinarith

private theorem le_harmonicTail (hk : 2 ≤ k) : ∀ (n j : ℕ),
    (k : ℚ) / ((k - 1) * ((sylvester j - 1 : ℕ) : ℚ)) ≤ harmonicTail k n j
  | 0, _ => le_rfl
  | n + 1, j => by
    rw [harmonicTail]
    split_ifs with hku
    · exact le_rfl
    · have ih := le_harmonicTail hk n (j + 1)
      rw [sylvester_succ_sub_one] at ih
      have hu : 1 ≤ sylvester j - 1 := by have := two_le_sylvester j; omega
      generalize sylvester j - 1 = u at hku hu ih ⊢
      push Not at hku
      have hu' : (1 : ℚ) ≤ u := by exact_mod_cast hu
      have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
      have hku' : (u : ℚ) + 1 ≤ k := by exact_mod_cast hku
      have key : (k : ℚ) / ((k - 1) * u) ≤ 1 / u + k / ((k - 1) * ((u * (u + 1) : ℕ) : ℚ)) := by
        have ha : (0 : ℚ) < k - 1 := by linarith
        have e : 1 / (u : ℚ) + k / ((k - 1) * ((u * (u + 1) : ℕ) : ℚ)) - k / ((k - 1) * u) =
            (k - u - 1) / ((k - 1) * (u * (u + 1))) := by
          push_cast
          field_simp
          ring
        have : 0 ≤ ((k : ℚ) - u - 1) / ((k - 1) * (u * (u + 1))) :=
          div_nonneg (by linarith) (mul_nonneg ha.le (by positivity))
        linarith
      linarith

/-- Items of class `k` of total size at most `C / u` weigh at most `k / ((k - 1) * u)`. -/
private theorem binWeight_le_of_small (hk : 2 ≤ k) {u : ℕ} {b : List ℕ} (hu : 1 ≤ u)
    (hsmall : ∀ x ∈ b, k * x ≤ C) (hs : u * b.sum ≤ C) : binWeight k C b ≤ k / ((k - 1) * u) := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  rw [binWeight_of_small hsmall, ← div_div, ← div_div]
  exact div_mul_le_div (div_nonneg (by positivity) (by linarith)) hu hs

/-- An item of size at most `C / (u + 1)` with `u + 2 ≤ k` weighs at most `(u + 2) / (u + 1)`
times its size. -/
private theorem harmonicWeight_le (hk : 2 ≤ k) {u x : ℕ} (hu2 : u + 2 ≤ k)
    (hx : (u + 1) * x ≤ C) : harmonicWeight k C x ≤ (u + 2) / ((u + 1) * C) * x := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  by_cases hkx : k * x ≤ C
  · rw [harmonicWeight_of_le hkx]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rcases Nat.eq_zero_or_pos C with rfl | hC
    · simp
    · have hC' : (0 : ℚ) < C := by exact_mod_cast hC
      have hu2' : (u : ℚ) + 2 ≤ k := by exact_mod_cast hu2
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
  · push Not at hkx
    rw [harmonicWeight_of_lt hkx]
    have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hkx)
    have hi : u + 1 ≤ C / x := (Nat.le_div_iff_mul_le hx0).2 (by linarith [Nat.mul_comm x (u + 1)])
    have hlt := Nat.lt_mul_div_succ C hx0
    have key : (u + 1) * C ≤ (u + 2) * x * (C / x) := by nlinarith
    have key' : ((u : ℚ) + 1) * C ≤ (u + 2) * x * (C / x : ℕ) := by exact_mod_cast key
    have hC' : (0 : ℚ) < C := by exact_mod_cast (show 0 < C by nlinarith)
    have hi' : (0 : ℚ) < (C / x : ℕ) := by exact_mod_cast (show 0 < C / x by omega)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hi' (by positivity)]
    linarith

private theorem binWeight_le_harmonicTail (hk : 2 ≤ k) : ∀ (n j : ℕ) {b : List ℕ},
    k ≤ sylvester j - 1 + n → (sylvester j - 1) * b.sum ≤ C → binWeight k C b ≤ harmonicTail k n j
  | n, j, b, hn, hs => by
    have hu : 1 ≤ sylvester j - 1 := by have := two_le_sylvester j; omega
    by_cases hku : k ≤ sylvester j - 1
    · have hval : harmonicTail k n j = k / ((k - 1) * ((sylvester j - 1 : ℕ) : ℚ)) := by
        cases n with
        | zero => rfl
        | succ n => rw [harmonicTail, ite_eq_left hku]
      rw [hval]
      exact binWeight_le_of_small hk hu (fun x hx => by
        have := List.le_sum_of_mem hx; nlinarith) hs
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    push Not at hku
    have hT1 := le_harmonicTail hk (n + 1) j
    have hT := le_harmonicTail hk n (j + 1)
    rw [harmonicTail, ite_eq_right (by omega)] at hT1 ⊢
    have hrec : ∀ {b' : List ℕ}, (sylvester j - 1) * (sylvester j - 1 + 1) * b'.sum ≤ C →
        binWeight k C b' ≤ harmonicTail k n (j + 1) := fun h =>
      binWeight_le_harmonicTail hk n (j + 1) (by rw [sylvester_succ_sub_one]; nlinarith)
        (by rwa [sylvester_succ_sub_one])
    rw [sylvester_succ_sub_one] at hT
    generalize sylvester j - 1 = u at hku hu hs hT1 hT hrec ⊢
    have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hu' : (1 : ℚ) ≤ u := by exact_mod_cast hu
    by_cases hbig : ∃ x ∈ b, C < (u + 1) * x
    · -- the bin holds an item of class `u`, of weight `1 / u`
      obtain ⟨x, hx, hxC⟩ := hbig
      have hperm := List.perm_cons_erase hx
      have hsum : b.sum = x + (b.erase x).sum := by simpa using hperm.sum_eq
      have hW : binWeight k C b = harmonicWeight k C x + binWeight k C (b.erase x) := by
        simpa using (hperm.map (harmonicWeight k C)).sum_eq
      rw [hsum] at hs
      have hux : u * x ≤ C := (Nat.mul_le_mul_left u (Nat.le_add_right x _)).trans hs
      have hwx : harmonicWeight k C x = 1 / u := by
        rw [harmonicWeight_of_lt (lt_of_lt_of_le hxC (Nat.mul_le_mul_right x hku)),
          Nat.div_eq_of_lt_le hux hxC]
      have := hrec (b' := b.erase x) (by nlinarith)
      rw [hW, hwx]
      linarith
    · push Not at hbig
      rcases Nat.lt_or_ge (u + 1) k with hu2 | hu2
      · -- every item weighs at most `(u + 2) / (u + 1)` times its size
        have hle : binWeight k C b ≤ (u + 2) / ((u + 1) * C) * b.sum := by
          rw [binWeight, Nat.cast_list_sum, ← List.sum_map_mul_left]
          exact List.sum_le_sum fun x hx => harmonicWeight_le hk hu2 (hbig x hx)
        rw [← div_div] at hle
        have h2 := div_mul_le_div (c := ((u : ℚ) + 2) / (u + 1)) (by positivity) hu hs
        have e : ((u : ℚ) + 2) / (u + 1) / u = 1 / u + 1 / (u * (u + 1)) := by
          field_simp
          ring
        have h3 : 1 / ((u : ℚ) * (u + 1)) ≤ k / ((k - 1) * ((u * (u + 1) : ℕ) : ℚ)) := by
          push_cast
          rw [div_le_div_iff₀ (by positivity) (mul_pos (by linarith) (by positivity))]
          nlinarith
        linarith
      · -- every item is of class `k`
        have := binWeight_le_of_small hk hu (fun x hx => by have := hbig x hx; nlinarith) hs
        linarith

/-- **A bin weighs at most `T_k`**: items of total size at most `C` have total weight at most
`harmonicRatio k` under `harmonicWeight k C`. -/
theorem sum_map_harmonicWeight_le (hk : 2 ≤ k) {b : List ℕ} (hb : b.sum ≤ C) :
    (b.map (harmonicWeight k C)).sum ≤ harmonicRatio k :=
  binWeight_le_harmonicTail hk k 0 (by simp [sylvester]) (by simpa [sylvester] using hb)

/-- **Harmonic_k uses at most `T_k * OPT + k` bins** ([Lee and Lee][LeeLee1985]): against every
packing `Q` of the same items, in particular an optimal one, Harmonic_k uses at most
`harmonicRatio k * Q.length + k` bins. So its asymptotic competitive ratio is at most `T_k`. -/
theorem length_run_harmonicPacker_le (hk : 2 ≤ k) {l : List ℕ} {Q : List (List ℕ)}
    (hQ : IsPacking C l Q) :
    (((harmonicPacker k C).run l).length : ℚ) ≤ harmonicRatio k * Q.length + k := by
  have h1 := length_run_harmonicPacker_le_sum hk fun a ha => hQ.le_of_mem ha
  rw [sum_map_eq_of_perm hQ.perm] at h1
  have h2 := List.sum_le_length_nsmul (Q.map fun b => (b.map (harmonicWeight k C)).sum)
    (harmonicRatio k) (by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun b hb => sum_map_harmonicWeight_le hk (hQ.sum_le b hb))
  rw [List.length_map, nsmul_eq_mul] at h2
  linarith

end Cslib.Algorithms.Lean.BinPacking
