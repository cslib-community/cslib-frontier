/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SparseModeLength
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted mass as a sum of local products

In an occupied row, the weight of entry `j` is the sum of its positive position gaps up
through `j`. The total mass is therefore the sum of one gap times one multiplicity over ordered
pairs of occupied entries of the same row. Outside the sparse array the summand is zero.
Clipping each operand at the budget preserves the strict comparison and gives an explicit
width bound even on an overweight table.
-/

public section

namespace Cslib.SparseModeTuple

open Finset

/-- One positive position gap, and zero for a padded entry. -/
@[expose] def gapAt (es : List Entry) (i : ℕ) : ℕ := es[i]?.elim 0 (fun e => e.skip + 1)

/-- One positive multiplicity, and zero for a padded entry. -/
@[expose] def copiesAt (es : List Entry) (i : ℕ) : ℕ := es[i]?.elim 0 (fun e => e.extra + 1)

/-- Entries in a selected sparse row, with an empty row on padding. -/
@[expose] def entriesAt (rows : List Row) (c : ℕ) : List Entry :=
  rows[c]?.elim [] (fun r => r.first :: r.rest)

private def copies (es : List Entry) : ℕ := (es.map fun e => e.extra + 1).sum

private theorem mass_add (es : List Entry) (o t : ℕ) :
    entryMass (o + t) es = entryMass o es + t * copies es := by
  induction es generalizing o with
  | nil => simp [entryMass, copies]
  | cons e es ih =>
    simp only [entryMass, copies, List.map_cons, List.sum_cons]
    rw [show o + t + (e.skip + 1) = o + (e.skip + 1) + t by omega, ih, copies]
    ring

private theorem sum_copiesAt (es : List Entry) (L : ℕ) (h : es.length ≤ L) :
    ∑ i ∈ range L, copiesAt es i = copies es := by
  induction es generalizing L with
  | nil => simp [copiesAt, copies]
  | cons e es ih =>
    cases L with
    | zero => simp at h
    | succ L =>
      rw [sum_range_succ']
      have hr : ∀ i, copiesAt (e :: es) (i + 1) = copiesAt es i := by intro i; rfl
      simp only [hr, ih L (by simpa using h)]
      change copies es + (e.extra + 1) = (e.extra + 1) + copies es
      omega

/-- Product read from entries `i` and `j` of the same row. -/
@[expose] def rowTerm (es : List Entry) (i j : ℕ) : ℕ :=
  if i ≤ j then gapAt es i * copiesAt es j else 0

private theorem sum_rowTerm (es : List Entry) (L : ℕ) (h : es.length ≤ L) :
    ∑ i ∈ range L, ∑ j ∈ range L, rowTerm es i j = entryMass 0 es := by
  induction es generalizing L with
  | nil => simp [rowTerm, gapAt, copiesAt, entryMass]
  | cons e es ih =>
    cases L with
    | zero => simp at h
    | succ L =>
      have hL : es.length ≤ L := by simpa using h
      have htail (i : ℕ) :
          ∑ j ∈ range (L + 1), rowTerm (e :: es) (i + 1) j =
            ∑ j ∈ range L, rowTerm es i j := by
        rw [sum_range_succ']
        simp only [rowTerm, Nat.add_le_add_iff_right]
        rfl
      have hhead : ∑ j ∈ range (L + 1), rowTerm (e :: es) 0 j =
          (e.skip + 1) * copies (e :: es) := by
        simp only [rowTerm, Nat.zero_le, ite_true, ← mul_sum, sum_copiesAt _ _ h]
        rfl
      rw [sum_range_succ', hhead, sum_congr rfl (fun i _ => htail i), ih L hL, entryMass,
        Nat.zero_add, ← Nat.zero_add (e.skip + 1), mass_add]
      simp [copies]
      ring

/-- The padded rectangular sum reads at most one gap and one multiplicity per leaf. -/
theorem mass_eq_sum {rows : List Row} {L : ℕ} (hc : rows.length ≤ L)
    (he : ∀ r ∈ rows, (r.first :: r.rest).length ≤ L) :
    mass rows = ∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L,
      rowTerm (entriesAt rows c) i j := by
  have hrow (c) : (entriesAt rows c).length ≤ L := by
    cases hr : rows[c]? with
    | none => simp [entriesAt, hr]
    | some r => simpa [entriesAt, hr] using he r (List.mem_of_getElem? hr)
  simp_rw [sum_rowTerm _ _ (hrow _)]
  clear he hrow
  change (rows.map (fun r => entryMass 0 (r.first :: r.rest))).sum = _
  induction rows generalizing L with
  | nil => simp [entriesAt, entryMass]
  | cons r rows ih =>
    cases L with
    | zero => simp at hc
    | succ L =>
      rw [sum_range_succ']
      have hr (c) : entriesAt (r :: rows) (c + 1) = entriesAt rows c := rfl
      simp only [hr, ← ih (by simpa using hc), List.map_cons, List.sum_cons]
      change _ + _ = _ + entryMass 0 (r.first :: r.rest)
      omega

/-- Truncate both factors to the strict budget before multiplying. -/
@[expose] def clippedTerm (p : ℕ) (es : List Entry) (i j : ℕ) : ℕ :=
  if i ≤ j then min p (gapAt es i) * min p (copiesAt es j) else 0

private theorem min_mul_clip (p x y : ℕ) :
    min p (min p x * min p y) = min p (x * y) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  by_cases hxp : x < p <;> by_cases hyp : y < p
  · simp [Nat.min_eq_right hxp.le, Nat.min_eq_right hyp.le]
  · rw [Nat.min_eq_right hxp.le, Nat.min_eq_left (by omega : p ≤ y)]
    have h₁ : p ≤ x * p := Nat.le_mul_of_pos_left _ hx
    have h₂ : p ≤ x * y := (by omega : p ≤ y).trans (Nat.le_mul_of_pos_left _ hx)
    simp [Nat.min_eq_left h₁, Nat.min_eq_left h₂]
  · rw [Nat.min_eq_left (by omega : p ≤ x), Nat.min_eq_right hyp.le]
    have h₁ : p ≤ p * y := Nat.le_mul_of_pos_right _ hy
    have h₂ : p ≤ x * y := (by omega : p ≤ x).trans (Nat.le_mul_of_pos_right _ hy)
    simp [Nat.min_eq_left h₁, Nat.min_eq_left h₂]
  · by_cases hz : p = 0
    · simp [hz]
    have hp : 0 < p := by omega
    have h₁ : p ≤ p * p := Nat.le_mul_of_pos_left _ hp
    have h₂ : p ≤ x * y := (by omega : p ≤ x).trans (Nat.le_mul_of_pos_right _ hy)
    simp [Nat.min_eq_left (by omega : p ≤ x), Nat.min_eq_left (by omega : p ≤ y),
      Nat.min_eq_left h₁, Nat.min_eq_left h₂]

private theorem min_sum_congr {α : Type*} (p : ℕ) (s : Finset α) (f g : α → ℕ)
    (h : ∀ i ∈ s, min p (f i) = min p (g i)) :
    min p (∑ i ∈ s, f i) = min p (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    have hs := ih (fun i hi => h i (by simp [hi]))
    have h₁ := h a (by simp)
    omega

/-- The clipped rectangular test accepts precisely when the true weighted mass is below `p`. -/
theorem sum_clipped_lt_iff {rows : List Row} {L : ℕ} (p : ℕ) (hc : rows.length ≤ L)
    (he : ∀ r ∈ rows, (r.first :: r.rest).length ≤ L) :
    (∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L,
      clippedTerm p (entriesAt rows c) i j) < p ↔
      mass rows < p := by
  rw [mass_eq_sum hc he]
  suffices min p (∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L,
      clippedTerm p (entriesAt rows c) i j) = min p (∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L,
        rowTerm (entriesAt rows c) i j) by omega
  apply min_sum_congr
  intro c _
  apply min_sum_congr
  intro i _
  apply min_sum_congr
  intro j _
  by_cases hij : i ≤ j <;> simp [clippedTerm, rowTerm, hij, min_mul_clip]

private theorem length_entries_le (es : List Entry) :
    es.length ≤ (es.flatMap encodeEntry).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have := List.length_pos_iff.mpr (Cslib.BitString.eliasGamma_ne_nil (e.skip + 1))
    simp only [List.length_cons, List.flatMap_cons, List.length_append, encodeEntry]
    omega

private theorem length_row_pos (r : Row) : 0 < (encodeRow r).length := by
  have h := List.length_pos_iff.mpr (Cslib.BitString.eliasGamma_ne_nil (r.skip + 1))
  simp only [encodeRow, List.length_append]
  omega

private theorem bounds_flatMap (rows : List Row) :
    rows.length ≤ (rows.flatMap encodeRow).length ∧
      ∀ r ∈ rows, (encodeRow r).length ≤ (rows.flatMap encodeRow).length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append, List.mem_cons]
    constructor
    · have := length_row_pos r
      omega
    · intro t ht
      rcases ht with rfl | h
      · omega
      · have := ih.2 t h
        omega

/-- The encoded word length itself bounds both sparse row indices, so the test needs no
separately provided support-size certificates. -/
theorem sum_clipped_lt_iff_of_encode (p : ℕ) (rows : List Row) :
    let L := (encode rows).length
    (∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L,
      clippedTerm p (entriesAt rows c) i j) < p ↔
      mass rows < p := by
  have h := bounds_flatMap rows
  dsimp only
  apply sum_clipped_lt_iff
  · simp only [encode, List.length_append]
    omega
  · intro r hr
    have hrow := h.2 r hr
    have he := length_entries_le (r.first :: r.rest)
    simp only [encodeRow, List.length_append] at hrow
    simp only [encode, List.length_append]
    omega

/-- All clipped operands fit a common polynomial range, even on overweight sparse tables. -/
theorem sum_clipped_le (p L : ℕ) (rows : List Row) :
    (∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L,
      clippedTerm p (entriesAt rows c) i j) ≤ L ^ 3 * p ^ 2 := by
  calc
    _ ≤ ∑ _ ∈ range L, ∑ _ ∈ range L, ∑ _ ∈ range L, (p * p) := by
      gcongr with c _ i _ j _
      unfold clippedTerm
      split
      · exact Nat.mul_le_mul (min_le_left _ _) (min_le_left _ _)
      · omega
    _ = L ^ 3 * p ^ 2 := by simp [pow_succ]; ring

end Cslib.SparseModeTuple
