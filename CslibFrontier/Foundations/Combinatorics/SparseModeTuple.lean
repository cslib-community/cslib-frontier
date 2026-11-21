/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.WeightedGamma

/-!
# Sparse exponent tuples

In a row of mode exponents, only the nonzero multiplicities are stored. Each entry records
a run of zero weights followed by a positive multiplicity. The outer list uses the same
convention for empty rows. A row stores its first entry separately, so inserting an empty
row cannot give another description of the same tuple.

Natural-number fields use Elias gamma codes. The row and entry counts delimit the stream,
allowing a decoder to recover a tuple in the presence of trailing zero padding.
-/

public section

namespace Cslib.SparseModeTuple

open BitString

/-- Zero coordinates skipped, followed by a positive value represented by its predecessor. -/
structure Entry where
  /-- Number of zero coordinates preceding this one. -/
  skip : ℕ
  /-- Number of copies in addition to the first. -/
  extra : ℕ
  deriving DecidableEq, Repr

/-- A nonempty row with the number of empty rows preceding it. -/
structure Row where
  /-- Number of empty rows preceding this row. -/
  skip : ℕ
  /-- First nonzero entry. -/
  first : Entry
  /-- Remaining entries in increasing weight order. -/
  rest : List Entry
  deriving DecidableEq, Repr

/-- Look up a zero-based coordinate by walking successive gaps. -/
@[expose] def entryAt : List Entry → ℕ → ℕ
  | [], _ => 0
  | e :: es, i => if i < e.skip then 0 else if i = e.skip then e.extra + 1
      else entryAt es (i - (e.skip + 1))

/-- The exponent of the mode in colour `c` of weight `i + 1`. -/
@[expose] def coord : List Row → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | r :: rs, c, i => if c < r.skip then 0 else if c = r.skip then entryAt (r.first :: r.rest) i
      else coord rs (c - (r.skip + 1)) i

/-- Consecutive gamma words for a positive coordinate gap and a positive multiplicity. -/
@[expose] def encodeEntry (e : Entry) : List Bool :=
  eliasGamma (e.skip + 1) ++ eliasGamma (e.extra + 1)

/-- The colour gap and entry count, followed by one pair of gamma words per occupied weight. -/
@[expose] def encodeRow (r : Row) : List Bool :=
  eliasGamma (r.skip + 1) ++ eliasGamma (r.rest.length + 1) ++
    (r.first :: r.rest).flatMap encodeEntry

/-- The occupied colour count, followed by the nonempty rows. -/
@[expose] def encode (rows : List Row) : List Bool :=
  eliasGamma (rows.length + 1) ++ rows.flatMap encodeRow

/-- Pad an encoding on the right with zeroes up to the specified width. -/
@[expose] def padded (width : ℕ) (rows : List Row) : List Bool :=
  encode rows ++ List.replicate (width - (encode rows).length) false

/-- Padding at a width admitting the tuple has exactly that width. -/
theorem length_padded {width : ℕ} {rows : List Row} (h : (encode rows).length ≤ width) :
    (padded width rows).length = width := by simp [padded]; omega

private abbrev Reader (α : Type) := List Bool → Option (α × List Bool)

private def gammaTail (k : ℕ) : Reader ℕ
  | [] => none
  | false :: xs => gammaTail (k + 1) xs
  | true :: xs => if k ≤ xs.length then
      some (decodeEliasGamma (List.replicate k false ++ true :: xs.take k), xs.drop k)
    else none

private theorem gammaTail_replicate (n k : ℕ) (xs : List Bool) :
    gammaTail k (List.replicate n false ++ xs) = gammaTail (k + n) xs := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, gammaTail, ih]
    congr 1
    omega

private theorem read_gamma {n : ℕ} (h : 0 < n) (xs : List Bool) :
    gammaTail 0 (eliasGamma n ++ xs) = some (n, xs) := by
  set k := Nat.log 2 n
  rw [show eliasGamma n = List.replicate k false ++ true :: lowBits k n by rfl, List.append_assoc,
    gammaTail_replicate]
  have hlen : (lowBits k n).length = k := length_lowBits k n
  have htake : (lowBits k n ++ xs).take k = lowBits k n := by
    conv_lhs => arg 1; rw [← hlen]
    exact List.take_left
  have hdrop : (lowBits k n ++ xs).drop k = xs := by
    conv_lhs => arg 1; rw [← hlen]
    exact List.drop_left
  have hbound : k ≤ (lowBits k n ++ xs).length := by simp [hlen]
  simp only [Nat.zero_add, List.cons_append, gammaTail, hbound, ite_true, htake, hdrop]
  rw [show List.replicate k false ++ true :: lowBits k n = eliasGamma n by rfl,
    decodeEliasGamma_eliasGamma h]

private def many {α : Type} (read : Reader α) : ℕ → Reader (List α)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
    let (a, ys) ← read xs
    let (as, zs) ← many read n ys
    return (a :: as, zs)

private theorem read_many {α : Type} {read : Reader α} {code : α → List Bool}
    (h : ∀ a xs, read (code a ++ xs) = some (a, xs)) (as : List α) (xs : List Bool) :
    many read as.length (as.flatMap code ++ xs) = some (as, xs) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [many, List.append_assoc, h, ih]

private def readEntry : Reader Entry := fun xs => do
  let (a, ys) ← gammaTail 0 xs
  let (b, zs) ← gammaTail 0 ys
  return (⟨a - 1, b - 1⟩, zs)

private theorem read_entry (e : Entry) (xs : List Bool) :
    readEntry (encodeEntry e ++ xs) = some (e, xs) := by
  simp [readEntry, encodeEntry, List.append_assoc, read_gamma]

private def readRow : Reader Row := fun xs => do
  let (g, ys) ← gammaTail 0 xs
  let (n, zs) ← gammaTail 0 ys
  let (e, us) ← readEntry zs
  let (es, vs) ← many readEntry (n - 1) us
  return (⟨g - 1, e, es⟩, vs)

private theorem read_row (r : Row) (xs : List Bool) :
    readRow (encodeRow r ++ xs) = some (r, xs) := by
  simp [readRow, encodeRow, List.append_assoc, read_gamma, read_entry, read_many read_entry]

private def readTuple : Reader (List Row) := fun xs => do
  let (n, ys) ← gammaTail 0 xs
  many readRow (n - 1) ys

private theorem read_encode (rows : List Row) (xs : List Bool) :
    readTuple (encode rows ++ xs) = some (rows, xs) := by
  simp [readTuple, encode, List.append_assoc, read_gamma, read_many read_row]

/-- Decode a fixed-width word. The round trip checks all separators, counts and padding. -/
def decode (width : ℕ) (xs : List Bool) : Option (List Row) := do
  if xs.length ≠ width then none else
    let (rows, _) ← readTuple xs
    if (encode rows).length ≤ width ∧ padded width rows = xs then some rows else none

/-- A sufficiently wide canonical word returns the original sparse tuple. -/
theorem decode_padded {width : ℕ} {rows : List Row} (h : (encode rows).length ≤ width) :
    decode width (padded width rows) = some rows := by
  simp only [decode, length_padded h, ne_eq, not_true_eq_false, ite_false]
  simp [padded, read_encode, h]

/-- Decoding accepts exactly one fixed-width word for each tuple that fits. -/
theorem decode_eq_some_iff {width : ℕ} {xs : List Bool} {rows : List Row} :
    decode width xs = some rows ↔ (encode rows).length ≤ width ∧ xs = padded width rows := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · contradiction
    · cases hr : readTuple xs with
      | none => simp [hr] at h
      | some pair =>
        rcases pair with ⟨decoded, rest⟩
        have hd : ((encode decoded).length ≤ width ∧ padded width decoded = xs) ∧
            decoded = rows := by simpa [hr] using h
        rcases hd with ⟨⟨hle, heq⟩, rfl⟩
        exact ⟨hle, heq.symm⟩
  · rintro ⟨h, rfl⟩
    exact decode_padded h

private def queryRows : ℕ → List Bool → ℕ → ℕ → Option ℕ
  | 0, _, _, _ => some 0
  | n + 1, xs, c, i => do
    let (r, rest) ← readRow xs
    if c < r.skip then return 0
    if c = r.skip then return entryAt (r.first :: r.rest) i
    queryRows n rest (c - (r.skip + 1)) i

private theorem query_rows (rows : List Row) (suffix : List Bool) (c i : ℕ) :
    queryRows rows.length (rows.flatMap encodeRow ++ suffix) c i = some (coord rows c i) := by
  induction rows generalizing c with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, queryRows, read_row, coord]
    by_cases h₁ : c < r.skip <;> by_cases h₂ : c = r.skip <;> simp [h₁, h₂, ih]

/-- Read the requested exponent from a stream with the canonical format. The search stops once
the requested colour is passed and omits all unvisited rows. -/
def query (xs : List Bool) (c i : ℕ) : Option ℕ := do
  let (n, ys) ← gammaTail 0 xs
  queryRows (n - 1) ys c i

/-- Every valid padded code yields the requested exponent. -/
theorem query_padded (width : ℕ) (rows : List Row) (c i : ℕ) :
    query (padded width rows) c i = some (coord rows c i) := by
  simp [query, padded, encode, List.append_assoc, read_gamma, query_rows]

/-- Correctness of a coordinate query on every word accepted by the validating decoder. -/
theorem query_of_decode {width : ℕ} {xs : List Bool} {rows : List Row}
    (h : decode width xs = some rows) (c i : ℕ) : query xs c i = some (coord rows c i) := by
  rw [(decode_eq_some_iff.mp h).2, query_padded]

end Cslib.SparseModeTuple
