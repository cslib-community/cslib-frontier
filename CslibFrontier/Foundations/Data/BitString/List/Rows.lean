/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List

/-!
# Flattening and replacing fixed-width rows of bit lists

Splitting a bit list of length `count * width` into `count` rows of width `width` via
`Cslib.BitString.listRows` and concatenating the rows recovers the original list, and replacing a
row via `Cslib.BitString.replaceRow` with a `width`-bit word produces a `count * width`-bit list.
Reading `count` rows of width `width` uses only the first `count * width` bits of the word.

## Main results

* `Cslib.BitString.listRows_take`: `listRows count width (word.take (count * width)) =
  listRows count width word`.
* `Cslib.BitString.flatten_listRows_of_length`: `(listRows count width w).flatten = w` when
  `w.length = count * width`.
* `Cslib.BitString.listRows_append_aligned`: split a concatenation at a row boundary.
* `Cslib.BitString.prefix_of_flatten_prefix`: a prefix between flattened positive-width rows
  gives a prefix between their row lists.
* `Cslib.BitString.length_replaceRow`: `(replaceRow width count j x word).length = count * width`
  when `x.length = width`.
-/

public section

namespace Cslib.BitString

/-- Reading `count` rows of width `width` does not see bits beyond the first `count * width`. -/
theorem listRows_take (count width : ℕ) (word : List Bool) :
    listRows count width (word.take (count * width)) = listRows count width word := by
  rw [listRows_eq_ofFn, ofList_take, ← listRows_eq_ofFn]

/-- Splitting a list of length `count * width` into `count` rows of width `width` and flattening
the rows recovers the original list. -/
theorem flatten_listRows_of_length {count width : ℕ} {w : List Bool}
    (hw : w.length = count * width) :
    (listRows count width w).flatten = w := by
  have heq : w = List.ofFn (ofList (count * width) w) := (ofFn_ofList hw).symm
  conv_lhs => rw [heq, listRows_ofFn, ← ofFn_blocksEquiv_symm]
  simp [blocksEquiv_symm_block, ← heq]

/-- Splitting a concatenation of aligned bit lists into rows splits each list separately. -/
theorem listRows_append_aligned {width : ℕ} (hwidth : 0 < width) {left right : List Bool}
    (hleft : width ∣ left.length) (hright : width ∣ right.length) :
    listRows ((left ++ right).length / width) width (left ++ right) =
      listRows (left.length / width) width left ++ listRows (right.length / width) width right := by
  have hcount : (left ++ right).length / width =
      left.length / width + right.length / width := by
    calc
      _ = ((left.length / width + right.length / width) * width) / width := by
        rw [List.length_append, Nat.add_mul, Nat.div_mul_cancel hleft, Nat.div_mul_cancel hright]
      _ = _ := Nat.mul_div_cancel _ hwidth
  rw [hcount]
  have hrows := listRows_flatten
    (listRows (left.length / width) width left ++ listRows (right.length / width) width right)
    (fun row hrow => (List.mem_append.mp hrow).elim length_of_mem_listRows length_of_mem_listRows)
  simpa only [List.length_append, length_listRows, List.flatten_append,
    flatten_listRows_of_length (Nat.div_mul_cancel hleft).symm,
    flatten_listRows_of_length (Nat.div_mul_cancel hright).symm] using hrows

/-- For lists of rows of the same positive width, flattening reflects the prefix relation. -/
theorem prefix_of_flatten_prefix {width : ℕ} (hwidth : 0 < width)
    {us vs : List (List Bool)} (hu : ∀ row ∈ us, row.length = width)
    (hv : ∀ row ∈ vs, row.length = width) (h : us.flatten <+: vs.flatten) : us <+: vs := by
  induction us generalizing vs with
  | nil => exact List.nil_prefix
  | cons u us ih =>
    cases vs with
    | nil =>
      have hlen := h.length_le
      simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_nil,
        hu u List.mem_cons_self] at hlen
      omega
    | cons v vs =>
      obtain ⟨tail, htail⟩ := h
      simp only [List.flatten_cons, List.append_assoc] at htail
      have huv := (hu u List.mem_cons_self).trans (hv v List.mem_cons_self).symm
      obtain ⟨rfl, hrest⟩ := List.append_inj htail huv
      exact List.cons_prefix_cons.mpr ⟨rfl, ih (fun x hx => hu x (List.mem_cons_of_mem _ hx))
        (fun x hx => hv x (List.mem_cons_of_mem _ hx)) ⟨tail, hrest⟩⟩

/-- Replacing one fixed-width row with a `width`-bit word produces a `count * width`-bit list. -/
@[simp] theorem length_replaceRow {width count j : ℕ} {x : List Bool} (hx : x.length = width)
    (word : List Bool) :
    (replaceRow width count j x word).length = count * width := by
  unfold replaceRow
  induction count with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton]
    split_ifs <;> simp [hx, Nat.succ_mul]

end Cslib.BitString
