/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Crypto.Primitives.Hash.Keccak

/-!
# Extendable-output functions on raw bit strings

A request specifies an input and a byte count. Every request at the same input reads a
prefix of one stream, even if the counts or the roles of the callers differ.
-/

public section

namespace Cslib.Crypto

/-- A bit-input XOF with output lengths in bytes. -/
structure ExtendableOutput where
  /-- The requested number of bytes at this raw input. -/
  read : List Bool → ℕ → List Byte
  /-- Every request returns the specified number of bytes. -/
  length_read : ∀ x n, (read x n).length = n
  /-- Requesting more bytes preserves every byte already read. -/
  take_read : ∀ x {m n}, m ≤ n → (read x n).take m = read x m

/-- Byte input uses the FIPS 202 least-significant-bit-first convention. -/
@[expose] def ExtendableOutput.readBytes (H : ExtendableOutput) (input : List Byte) :=
  H.read (Keccak.bytesToBitsLE input)

private def ExtendableOutput.byte (H : ExtendableOutput) (x : List Bool) (i : ℕ) : Byte :=
  (H.read x (i + 1))[i]'(by rw [H.length_read]; omega)

private theorem ExtendableOutput.byte_eq (H : ExtendableOutput) (x : List Bool) {i n : ℕ}
    (hi : i < n) : H.byte x i = (H.read x n)[i]'(by rw [H.length_read]; exact hi) := by
  have h := H.take_read x (show i + 1 ≤ n by omega)
  unfold ExtendableOutput.byte
  simp only [← h, List.getElem_take]

/-- Fill a finite window of each selected raw row, starting after its previously read prefix.
All earlier bytes, other rows and bytes past the window come from the original XOF. -/
def ExtendableOutput.fill (H : ExtendableOutput) {rows : Finset (List Bool)} {width : ℕ}
    (seen : List Bool → ℕ) (tape : rows → FixedBytes width) : ExtendableOutput :=
  let byteAt (x : List Bool) (i : ℕ) :=
    if hx : x ∈ rows then
      if h : seen x ≤ i ∧ i - seen x < width then tape ⟨x, hx⟩ ⟨_, h.2⟩ else H.byte x i
    else H.byte x i
  { read := fun x n => (List.range n).map (byteAt x)
    length_read := by simp
    take_read := fun _ _ _ h => by rw [← List.map_take, List.take_range, Nat.min_eq_left h] }

/-- All previously read prefixes, including repeated reads at different lengths, survive. -/
theorem ExtendableOutput.read_fill_of_le (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) {x : List Bool} {n : ℕ}
    (hn : n ≤ seen x) : (H.fill seen tape).read x n = H.read x n := by
  apply List.ext_getElem
  · rw [ExtendableOutput.length_read, ExtendableOutput.length_read]
  · intro i hi _
    have lt : i < n := by simpa only [ExtendableOutput.length_read] using hi
    have outside : ¬(seen x ≤ i ∧ i - seen x < width) := by omega
    simp only [fill, List.getElem_map, List.getElem_range, outside, dite_false]
    split <;> exact H.byte_eq x lt

/-- An input outside the completed rows keeps its entire XOF output. -/
theorem ExtendableOutput.read_fill_of_notMem (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) {x : List Bool}
    (hx : x ∉ rows) (n : ℕ) : (H.fill seen tape).read x n = H.read x n := by
  apply List.ext_getElem
  · rw [ExtendableOutput.length_read, ExtendableOutput.length_read]
  · intro i hi _
    have lt : i < n := by simpa only [ExtendableOutput.length_read] using hi
    simp only [fill, List.getElem_map, List.getElem_range, hx, dite_false]
    exact H.byte_eq x lt

/-- The new window of a row is exactly its tape. The retained prefix may have any length. -/
theorem ExtendableOutput.drop_read_fill (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) (x : rows) :
    ((H.fill seen tape).read x (seen x + width)).drop (seen x) = List.ofFn (tape x) := by
  apply List.ext_getElem
  · simp only [List.length_drop, ExtendableOutput.length_read, Nat.add_sub_cancel_left,
      List.length_ofFn]
  · intro i _ hi
    have hs : i < width := by simpa only [List.length_ofFn] using hi
    simp only [List.getElem_drop, fill, List.getElem_map, List.getElem_range, x.property,
      dite_true, Nat.le_add_right, Nat.add_sub_cancel_left, hs, true_and,
      List.getElem_ofFn]

/-- Within the filled window a raw read consists of its old prefix followed by fresh bytes. -/
theorem ExtendableOutput.read_fill_window (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) (x : rows) {n : ℕ}
    (hn : n ≤ seen x + width) :
    (H.fill seen tape).read x n = (H.read x (seen x) ++ List.ofFn (tape x)).take n := by
  let K := H.fill seen tape
  have h := List.take_append_drop (seen x) (K.read x (seen x + width))
  rw [K.take_read x (Nat.le_add_right ..), H.read_fill_of_le seen tape le_rfl,
    H.drop_read_fill seen tape x] at h
  rw [← K.take_read x hn, ← h]

end Cslib.Crypto
