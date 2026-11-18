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

/-- Read an XOF with the first bytes of this stream replaced. Requests shorter than the
replacement are truncations. Longer requests continue with the original tail. -/
@[expose] def ExtendableOutput.readWithPrefix (H : ExtendableOutput) (x : List Bool) (n : ℕ)
    (head : List Byte) : List Byte :=
  head.take n ++ (H.read x n).drop head.length

/-- Overwriting each selected input's prefix gives a single prefix-consistent XOF on raw inputs.
Every role reading the same input sees the same bytes, including when their counts differ. -/
@[expose] def ExtendableOutput.withPrefixes (H : ExtendableOutput)
    (atInput : List Bool → Option (List Byte)) : ExtendableOutput where
  read x n := match atInput x with
    | none => H.read x n
    | some head => H.readWithPrefix x n head
  length_read x n := by
    cases h : atInput x with
    | none => exact H.length_read x n
    | some p =>
      simp only [readWithPrefix, List.length_append, List.length_take, List.length_drop,
        H.length_read]
      lia
  take_read x m n h := by
    cases e : atInput x with
    | none => exact H.take_read x h
    | some p =>
      simp only [readWithPrefix, List.take_append, List.take_take, Nat.min_eq_left h,
        List.length_take, ← H.take_read x h, List.drop_take]
      congr 2
      lia

/-- Replacing a stream prefix by its actual first bytes preserves every read. -/
theorem ExtendableOutput.readWithPrefix_self (H : ExtendableOutput) (x : List Bool) (n k : ℕ) :
    H.readWithPrefix x n (H.read x k) = H.read x n := by
  unfold readWithPrefix
  rw [H.length_read]
  by_cases h : n ≤ k
  · rw [H.take_read x h, List.drop_eq_nil_of_le (by rw [H.length_read]; exact h), List.append_nil]
  · rw [← H.take_read x (show k ≤ n by lia), List.take_take, Nat.min_eq_right (by lia)]
    exact List.take_append_drop k (H.read x n)

/-- Fill a finite window of each selected raw row, starting after its previously read prefix.
All earlier bytes, other rows and bytes past the window come from the original XOF. -/
def ExtendableOutput.fill (H : ExtendableOutput) {rows : Finset (List Bool)} {width : ℕ}
    (seen : List Bool → ℕ) (tape : rows → FixedBytes width) : ExtendableOutput :=
  H.withPrefixes fun x =>
    if hx : x ∈ rows then some (H.read x (seen x) ++ List.ofFn (tape ⟨x, hx⟩)) else none

/-- An input outside the completed rows keeps its entire XOF output. -/
theorem ExtendableOutput.read_fill_of_notMem (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) {x : List Bool}
    (hx : x ∉ rows) (n : ℕ) : (H.fill seen tape).read x n = H.read x n := by
  simp [fill, withPrefixes, hx]

/-- Within the filled window a raw read consists of its old prefix followed by fresh bytes. -/
theorem ExtendableOutput.read_fill_window (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) (x : rows) {n : ℕ}
    (hn : n ≤ seen x + width) :
    (H.fill seen tape).read x n = (H.read x (seen x) ++ List.ofFn (tape x)).take n := by
  simp [fill, withPrefixes, x.property, readWithPrefix, H.length_read,
    List.drop_eq_nil_of_le (show (H.read x n).length ≤ seen x + width by rwa [H.length_read])]

/-- All previously read prefixes, including repeated reads at different lengths, survive. -/
theorem ExtendableOutput.read_fill_of_le (H : ExtendableOutput) {rows : Finset (List Bool)}
    {width : ℕ} (seen : List Bool → ℕ) (tape : rows → FixedBytes width) {x : List Bool} {n : ℕ}
    (hn : n ≤ seen x) : (H.fill seen tape).read x n = H.read x n := by
  by_cases hx : x ∈ rows
  · rw [H.read_fill_window seen tape ⟨x, hx⟩ (hn.trans (Nat.le_add_right ..))]
    simp [List.take_append, H.length_read, Nat.sub_eq_zero_of_le hn, H.take_read x hn]
  · exact H.read_fill_of_notMem seen tape hx n

namespace ExtendableOutput

/-- The byte at a fixed offset of a raw XOF input stream. -/
def byteAt (H : ExtendableOutput) (x : List Bool) (i : ℕ) : Byte :=
  (H.read x (i + 1))[i]'(by rw [H.length_read]; exact Nat.lt_succ_self _)

/-- All reads long enough to contain an offset agree on its byte. -/
theorem getElem_read (H : ExtendableOutput) (x : List Bool) {i n : ℕ} (hi : i < n) :
    (H.read x n)[i]'(by rwa [H.length_read]) = byteAt H x i := by
  unfold byteAt
  have h := H.take_read x (show i + 1 ≤ n by lia)
  have hlen : i < ((H.read x n).take (i + 1)).length := by simp [H.length_read, hi]
  simpa only [List.getElem_take] using List.getElem_of_eq h hlen

/-- A prefix update affects exactly the byte offsets present in the replacement row. -/
theorem byteAt_withPrefixes (H : ExtendableOutput) (f : List Bool → Option (List Byte))
    (x : List Bool) (i : ℕ) :
    byteAt (H.withPrefixes f) x i = ((f x).bind (fun row => row[i]?)).getD (byteAt H x i) := by
  cases h : f x with
  | none => simp [byteAt, ExtendableOutput.withPrefixes, h]
  | some row =>
    by_cases hi : i < row.length
    · simp [byteAt, ExtendableOutput.withPrefixes, ExtendableOutput.readWithPrefix, h, hi,
        List.getElem_append_left, List.getElem_take]
    · have le : row.length ≤ i := Nat.le_of_not_gt hi
      simp [byteAt, ExtendableOutput.withPrefixes, ExtendableOutput.readWithPrefix, h, hi,
        List.take_of_length_le (by lia : row.length ≤ i + 1), List.getElem_append_right le,
        List.getElem_drop, Nat.add_sub_of_le le]

/-- The first `n` bytes at one input determine its `n`-byte read. -/
theorem read_eq_of_byteAt_eq {H G : ExtendableOutput} {x : List Bool} {n : ℕ}
    (same : ∀ i < n, H.byteAt x i = G.byteAt x i) : H.read x n = G.read x n := by
  apply List.ext_getElem
  · rw [H.length_read, G.length_read]
  · intro i hi _
    have h : i < n := hi.trans_le (H.length_read ..).le
    rw [getElem_read H x h, getElem_read G x h, same i h]

/-- Two XOFs agree on all finite reads if their individual bytes agree. -/
theorem ext_byteAt {H G : ExtendableOutput}
    (same : ∀ x i, byteAt H x i = byteAt G x i) : H = G := by
  have hr : H.read = G.read := by
    funext x n
    exact read_eq_of_byteAt_eq fun i _ => same x i
  cases H
  cases G
  congr

end ExtendableOutput

end Cslib.Crypto
