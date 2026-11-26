/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import CslibFrontier.Foundations.Data.Nat.Bitwise.SumTree
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Foundations.Data.BitString.Positions
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pure Metadata Layer for the `k`-Kick Tree Dynamic Dictionary

This module formalizes the pure metadata building blocks for the STOC 2022 `k`-kick tree dynamic
dictionary of Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul, and Liu
([BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`, Section 4, pp. 24–26, and
Section 5.1, pp. 27–28):
1. **Four-Russians Bit-Table Specifications (`FourRussians`)** (Section 4.1, p. 24): abstract
   specifications for bit-parallel operations on small bit-vectors of width `B` (`popcount`,
   `rank1`, `rank0`, `select1`, `select0`, `firstZeroBit`, `firstSetBit`), proving rank
   complementation, rank/select bounds, soundness theorems `select1_sound` and `select0_sound`,
   rank-select inversion `rank1_select1` and `rank0_select0`, and domain completeness
   `select1_isSome_iff` and `select0_isSome_iff`. The `Table` structure formalizes specification
   agreement; physical precomputed Word-RAM lookup tables are deferred to Stage A4.
2. **Mini-Array (`MiniArray`)** (Section 4.2, pp. 24–25): abstract array specification supporting
   point-update semantics and unary delimiter bitmap sizing with exact bit-length theorem
   `delimiters_length_eq_totalBits` matching total bits $K + \sum_i s_i$; physical bit-packed
   Word-RAM representation is deferred to Stage A4.
3. **Local Query Router (`LocalQueryRouter` / `PrefixTrie`)** (Section 4.3, pp. 25–26): binary
   prefix-trie router (adapting Lemma 15 for prefix-free key sets: callers supply prefix-free
   keys and `insert?` rejects collisions instead of extending stored prefixes via oracle $g$),
   with exact roundtrip decoding theorem `decode_encode`, collision-preventing insertion `insert?`,
   frame theorem `query_insert_of_diverge`, key preservation `query_insert_two_distinct`, and key
   extension routing `query_insert_prefix`.
4. **Free-Slot Tree (`FreeSlotTree`)** (Section 5.1, pp. 27–28): constant-depth $B$-ary bitmap tree
   over $[0, B^{h+1})$ for depth-0 free-slot allocation and deallocation, with full-tree soundness
   `findFree?_sound` and completeness `findFree?_complete` across all heights, semantic bridge
   `hasFree_iff_exists_isFree`, full-height update/frame theorems `isFree_setSlot_self` and
   `isFree_setSlot_of_ne`, and preservation of structural validity `Valid`.

## Source attribution

* [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`):
  - Section 4.1 (printed p. 24 / PDF p. 25): Method of Four Russians lookup tables on machine words.
  - Section 4.2 (printed pp. 24–25 / PDF pp. 25–26): mini-array of variable-size values in
    $O(K + \sum_i s_i)$ space with $O(1)$ updates and queries.
  - Section 4.3 (printed pp. 25–26 / PDF pp. 26–27): local query router over stored prefixes
    with DFS tree-shape encoding $E_1$ and leaf-value encoding $E_2$.
  - Section 5.1 (printed pp. 27–28 / PDF pp. 28–29): $O(1)$-depth free-slot tree with uniform fanout
    for depth-0 free-slot location.

## Main definitions

* `FourRussians.popcount`, `FourRussians.rank1`, `FourRussians.rank0`,
  `FourRussians.select1`, `FourRussians.select0`, `FourRussians.firstZeroBit`,
  `FourRussians.firstSetBit`: bit-parallel operations over small words `Fin (2 ^ B)`.
* `FourRussians.Table`: Four-Russians precomputed lookup table specification structure.
* `FourRussians.popcountTable`: table specification for population count.
* `MiniArray`: abstract sequence model supporting point updates and unary delimiter sizing.
* `PrefixTrie`: canonical binary prefix trie over prefix-free keys.
* `PrefixTrie.query`, `PrefixTrie.insert?`, `PrefixTrie.delete`, `PrefixTrie.pruneBranch`:
  prefix-free routing, collision-rejecting insertion, and branch contraction.
* `PrefixTrie.encodeE1`, `PrefixTrie.encodeE2`, `PrefixTrie.decode`: DFS serialization into
  binary tree shape and values.
* `FreeSlotTree`: $B$-ary constant-depth bitmap tree for free-slot management.
* `FreeSlotTree.hasFree`, `FreeSlotTree.isFree`, `FreeSlotTree.findFree?`,
  `FreeSlotTree.setSlot`, `FreeSlotTree.allocSlot`, `FreeSlotTree.freeSlot`,
  `FreeSlotTree.Valid`: operations and structural validity for free-slot trees.

## Main results

* `FourRussians.popcount_eq_length_bitIndices`, `FourRussians.popcount_eq_sum_testBit`,
  `FourRussians.popcount_eq_spec`: population count characterizations.
* `FourRussians.rank0_add_rank1`, `FourRussians.rank1_le`, `FourRussians.rank0_le`: rank
  complementation and bounds.
* `FourRussians.select1_sound`, `FourRussians.select0_sound`: selection soundness.
* `FourRussians.rank1_select1`, `FourRussians.rank0_select0`: rank-select inversion theorems.
* `FourRussians.select1_isSome_iff`, `FourRussians.select0_isSome_iff`: domain completeness.
* `MiniArray.delimiters_length_eq_totalBits`, `MiniArray.delimiters_count_delimiters`:
  exact bit length and delimiter count for mini-array packed representations.
* `PrefixTrie.query_insert_prefix`, `PrefixTrie.query_insert_of_diverge`,
  `PrefixTrie.query_insert_two_distinct`: prefix trie routing correctness and framing.
* `PrefixTrie.decode_encode`: roundtrip DFS trie deserialization.
* `FreeSlotTree.isFree_setSlot_self`, `FreeSlotTree.isFree_setSlot_of_ne`,
  `FreeSlotTree.allocSlot_self`, `FreeSlotTree.freeSlot_self`,
  `FreeSlotTree.allocSlot_of_ne`, `FreeSlotTree.freeSlot_of_ne`: full-height update and framing.
* `FreeSlotTree.setSlot_preserves_valid`, `FreeSlotTree.allocSlot_preserves_valid`,
  `FreeSlotTree.freeSlot_preserves_valid`: validity preservation across all levels.
* `FreeSlotTree.hasFree_iff_exists_isFree`: semantic bridge between summary and leaves.
* `FreeSlotTree.findFree?_sound`, `FreeSlotTree.findFree?_complete`: full-tree soundness
  and completeness across all tree heights.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, M. Liu,
  *Dynamic Dictionaries with Worst-Case Optimal Operations and Space*]
  [BenderFarachColtonKuszmaulKuszmaulLiu2022], arXiv:2111.00602.
-/

public section

namespace Cslib.DataStructure.Dictionary.KickTree

/-! ### 1. Four-Russians Bit-Table Specifications (`arXiv:2111.00602` §4.1, p. 24) -/

namespace FourRussians

/-- Population count: number of 1-bits in `w < 2 ^ B`. -/
@[expose] def popcount (B : ℕ) (w : Fin (2 ^ B)) : ℕ :=
  ((List.range B).filter (fun i => w.val.testBit i)).length

/-- Population count matches the length of the set-bit index list `w.val.bitIndices`. -/
theorem popcount_eq_length_bitIndices (B : ℕ) (w : Fin (2 ^ B)) :
    popcount B w = w.val.bitIndices.length := by
  rw [popcount, ← List.toFinset_card_of_nodup (List.nodup_range.filter _),
    ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Nat.mem_bitIndices,
    and_iff_right_iff_imp]
  exact fun hi => (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
    ((Nat.ge_two_pow_of_testBit hi).trans_lt w.isLt)

/-- Population count matches the sum of individual bits via
`Nat.sum_testBit_eq_length_bitIndices`. -/
theorem popcount_eq_sum_testBit (B : ℕ) (w : Fin (2 ^ B)) :
    popcount B w = ∑ i ∈ Finset.range B, (w.val.testBit i).toNat := by
  rw [popcount_eq_length_bitIndices, ← Nat.sum_testBit_eq_length_bitIndices w.isLt]

/-- Prefix rank: count of 1-bits among the first `k` bit positions `0, 1, …, k - 1`. -/
@[expose] def rank1 (B : ℕ) (w : Fin (2 ^ B)) (k : Fin (B + 1)) : ℕ :=
  ((List.range k.val).filter (fun i => w.val.testBit i)).length

/-- Prefix rank: count of 0-bits among the first `k` bit positions `0, 1, …, k - 1`. -/
@[expose] def rank0 (B : ℕ) (w : Fin (2 ^ B)) (k : Fin (B + 1)) : ℕ :=
  ((List.range k.val).filter (fun i => !w.val.testBit i)).length

/-- Complementation: `rank0 w k + rank1 w k = k`. -/
theorem rank0_add_rank1 (B : ℕ) (w : Fin (2 ^ B)) (k : Fin (B + 1)) :
    rank0 B w k + rank1 B w k = k.val := by
  rw [rank0, rank1, Nat.add_comm, ← List.length_eq_length_filter_add, List.length_range]

/-- Rank 1 is bounded by the prefix length `k`. -/
theorem rank1_le (B : ℕ) (w : Fin (2 ^ B)) (k : Fin (B + 1)) :
    rank1 B w k ≤ k.val :=
  (List.length_filter_le _ _).trans_eq List.length_range

/-- Rank 0 is bounded by the prefix length `k`. -/
theorem rank0_le (B : ℕ) (w : Fin (2 ^ B)) (k : Fin (B + 1)) :
    rank0 B w k ≤ k.val :=
  (List.length_filter_le _ _).trans_eq List.length_range

/-- Full-prefix rank matches the total population count. -/
theorem rank1_eq_popcount (B : ℕ) (w : Fin (2 ^ B)) :
    rank1 B w ⟨B, Nat.le_refl _⟩ = popcount B w := rfl

/-- Selection: find the 0-indexed position of the `k`-th 1-bit (`0`-based index in `Fin B`). -/
@[expose] def select1 (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) : Option (Fin B) :=
  (BitString.positions ((BitString.equivFin B).symm w))[k]?

/-- Selection: find the 0-indexed position of the `k`-th 0-bit (`0`-based index in `Fin B`). -/
@[expose] def select0 (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) : Option (Fin B) :=
  (BitString.positions (fun i => !((BitString.equivFin B).symm w i)))[k]?

/-- Soundness of `select1`: any returned position genuinely holds a 1-bit. -/
theorem select1_sound (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) (idx : Fin B)
    (h : select1 B w k = some idx) : w.val.testBit idx.val = true := by
  simpa only [BitString.mem_positions, BitString.equivFin_symm_apply] using List.mem_of_getElem? h

/-- Soundness of `select0`: any returned position genuinely holds a 0-bit. -/
theorem select0_sound (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) (idx : Fin B)
    (h : select0 B w k = some idx) : w.val.testBit idx.val = false := by
  simpa only [BitString.mem_positions, BitString.equivFin_symm_apply, Bool.not_eq_true'] using
    List.mem_of_getElem? h

/-- Find the least index of a 0-bit in `w < 2 ^ B` (`none` if all bits are 1). -/
@[expose] def firstZeroBit (B : ℕ) (w : Fin (2 ^ B)) : Option (Fin B) :=
  select0 B w 0

/-- Find the least index of a 1-bit in `w < 2 ^ B` (`none` if all bits are 0). -/
@[expose] def firstSetBit (B : ℕ) (w : Fin (2 ^ B)) : Option (Fin B) :=
  select1 B w 0

private theorem filter_lt_of_getElem {α : Type*} [LinearOrder α] {l : List α}
    (hl : l.Pairwise (· < ·)) {k : ℕ} {x : α} (hk : l[k]? = some x) :
    (l.filter (· < x)).length = k := by
  induction l generalizing k with
  | nil => cases hk
  | cons a as ih =>
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp hl
    cases k with
    | zero =>
      obtain rfl : a = x := by simpa using hk
      simpa [List.filter_eq_nil_iff] using fun y hy => (ha y hy).le
    | succ k =>
      rw [List.getElem?_cons_succ] at hk
      simp [ha x (List.mem_of_getElem? hk), ih has hk]

private theorem filter_range_length_eq_filter_positions_length {B : ℕ} (w : Fin (2 ^ B))
    (b : Bool) {n : ℕ} (hn : n ≤ B) :
    ((List.range n).filter (fun i => w.val.testBit i == b)).length =
      ((BitString.positions (fun i : Fin B => (BitString.equivFin B).symm w i == b)).filter
        (fun i => i.val < n)).length := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _),
    ← List.toFinset_card_of_nodup ((BitString.nodup_positions _).filter _),
    ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_map,
    BitString.mem_positions, BitString.equivFin_symm_apply, Function.Embedding.coeFn_mk,
    decide_eq_true_eq]
  exact ⟨fun ⟨hj, hb⟩ => ⟨⟨j, hj.trans_le hn⟩, ⟨hb, hj⟩, rfl⟩,
    fun ⟨_, ⟨hb, hi⟩, h⟩ => h ▸ ⟨hi, hb⟩⟩

private theorem rank1_eq_filter_positions_length {B : ℕ} (w : Fin (2 ^ B)) (idx : Fin B) :
    ((List.range idx.val).filter (fun i => w.val.testBit i)).length =
      ((BitString.positions ((BitString.equivFin B).symm w)).filter (· < idx)).length := by
  simpa only [beq_true, Fin.lt_def] using
    filter_range_length_eq_filter_positions_length w true idx.isLt.le

private theorem rank0_eq_filter_positions_length {B : ℕ} (w : Fin (2 ^ B)) (idx : Fin B) :
    ((List.range idx.val).filter (fun i => !w.val.testBit i)).length =
      ((BitString.positions (fun i => !((BitString.equivFin B).symm w i))).filter
        (· < idx)).length := by
  simpa only [beq_false, Fin.lt_def] using
    filter_range_length_eq_filter_positions_length w false idx.isLt.le

/-- Rank-select inversion: if `select1 B w k = some idx`, the rank of `idx` is `k`. -/
theorem rank1_select1 (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) (idx : Fin B)
    (h : select1 B w k = some idx) :
    rank1 B w ⟨idx.val, Nat.lt_succ_of_lt idx.isLt⟩ = k := by
  rw [rank1, rank1_eq_filter_positions_length w idx]
  exact filter_lt_of_getElem (BitString.pairwise_positions _) h

/-- Rank-select inversion: if `select0 B w k = some idx`, the 0-rank of `idx` is `k`. -/
theorem rank0_select0 (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) (idx : Fin B)
    (h : select0 B w k = some idx) :
    rank0 B w ⟨idx.val, Nat.lt_succ_of_lt idx.isLt⟩ = k := by
  rw [rank0, rank0_eq_filter_positions_length w idx]
  exact filter_lt_of_getElem (BitString.pairwise_positions _) h

/-- Population count matches the length of the set-bit positions list. -/
theorem popcount_eq_length_positions (B : ℕ) (w : Fin (2 ^ B)) :
    popcount B w = (BitString.positions ((BitString.equivFin B).symm w)).length := by
  simpa only [popcount, beq_true, Fin.is_lt, decide_true, List.filter_true] using
    filter_range_length_eq_filter_positions_length w true le_rfl

/-- Population count matches the `BitString.weight` semantic specification. -/
theorem popcount_eq_spec (B : ℕ) (w : Fin (2 ^ B)) :
    popcount B w = BitString.weight ((BitString.equivFin B).symm w) := by
  rw [popcount_eq_length_positions, BitString.length_positions]

/-- Domain completeness for `select1`: `select1 B w k` is defined if and only if
`k < popcount B w`. -/
theorem select1_isSome_iff (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) :
    (select1 B w k).isSome ↔ k < popcount B w := by
  simp [select1, popcount_eq_length_positions]

/-- Domain completeness for `select0`: `select0 B w k` is defined if and only if
`k < B - popcount B w`. -/
theorem select0_isSome_iff (B : ℕ) (w : Fin (2 ^ B)) (k : ℕ) :
    (select0 B w k).isSome ↔ k < B - popcount B w := by
  rw [select0, isSome_getElem?, BitString.length_positions, BitString.weight_not, Fintype.card_fin,
    ← BitString.length_positions, ← popcount_eq_length_positions]

/-- Specification of a Four-Russians bit-parallel lookup table of block size `B`. -/
structure Table (B : ℕ) (α : Type*) where
  /-- Direct table lookup function over `Fin (2 ^ B)`. -/
  lookup : Fin (2 ^ B) → α
  /-- High-level semantic specification over bit-vectors `Fin B → Bool`. -/
  spec : (Fin B → Bool) → α
  /-- Table correctness: the table evaluation matches the semantic specification. -/
  correct : ∀ w : Fin (2 ^ B), lookup w = spec ((BitString.equivFin B).symm w)

/-- Four-Russians lookup table for population count with verified specification equivalence. -/
@[expose] def popcountTable (B : ℕ) : Table B ℕ where
  lookup := popcount B
  spec := BitString.weight
  correct := popcount_eq_spec B

end FourRussians

/-! ### 2. Mini-Array (`arXiv:2111.00602` §4.2, pp. 24–25) -/

/-- Abstract mini-array sequence model (`arXiv:2111.00602` §4.2, pp. 24–25): sequence of `K`
items of type `α` supporting point updates and unary delimiter bitmap sizing for packed sequence
representations. This represents the functional specification of the $K$-item array; physical
bit-packing into machine words is addressed in Stage A4. -/
structure MiniArray (α : Type*) (K : ℕ) where
  /-- The `K` items stored in the mini-array. -/
  data : Fin K → α

namespace MiniArray

variable {α : Type*} {K : ℕ}

/-- Initialize a mini-array with a uniform default value. -/
@[expose] def init (defaultVal : α) : MiniArray α K where
  data := fun _ => defaultVal

/-- Read the item at index `i`. -/
@[expose] def read (A : MiniArray α K) (i : Fin K) : α :=
  A.data i

/-- Write a value at index `i`. -/
@[expose] def write (A : MiniArray α K) (i : Fin K) (val : α) : MiniArray α K where
  data := Function.update A.data i val

@[simp] theorem read_write_same (A : MiniArray α K) (i : Fin K) (val : α) :
    (A.write i val).read i = val := by
  simp [read, write]

theorem read_write_of_ne (A : MiniArray α K) {i j : Fin K} (h : j ≠ i) (val : α) :
    (A.write i val).read j = A.read j := by
  simp [read, write, Function.update_of_ne h]

private theorem sum_ofFn_add_one (f : Fin K → ℕ) :
    (List.ofFn (fun i => f i + 1)).sum = (List.ofFn f).sum + K := by
  simp only [List.sum_ofFn, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  rfl

@[simp] theorem write_write_same (A : MiniArray α K) (i : Fin K) (v₁ v₂ : α) :
    (A.write i v₂).write i v₁ = A.write i v₁ := by
  simp [write]

theorem write_comm (A : MiniArray α K) {i j : Fin K} (h : i ≠ j) (u v : α) :
    (A.write i u).write j v = (A.write j v).write i u := by
  simp [write, Function.update_comm h]

/-- Total packed bit length: one delimiter bit per item plus the sum of item sizes. -/
@[expose] def totalBits (A : MiniArray α K) (sizeOf : α → ℕ) : ℕ :=
  K + (List.ofFn (fun i => sizeOf (A.data i))).sum

/-- Starting bit-offset of item `i` within the packed sequence. -/
@[expose] def itemOffset (A : MiniArray α K) (sizeOf : α → ℕ) (i : Fin K) : ℕ :=
  ((List.ofFn (fun j : Fin K => sizeOf (A.data j))).take i.val).sum

/-- Unary delimiter bitmap: `sizeOf (A.data i)` 0-bits followed by a 1-bit delimiter per item. -/
@[expose] def delimiters (A : MiniArray α K) (sizeOf : α → ℕ) : List Bool :=
  let itemBits (i : Fin K) :=
    (List.replicate (sizeOf (A.data i)) false).concat true
  (List.ofFn itemBits).flatten

/-- The total bit length of the unary delimiters equals `totalBits`. -/
theorem delimiters_length_eq_totalBits (A : MiniArray α K) (sizeOf : α → ℕ) :
    (A.delimiters sizeOf).length = A.totalBits sizeOf := by
  have hlen : (List.length ∘ fun i : Fin K =>
      (List.replicate (sizeOf (A.data i)) false).concat true) = fun i => sizeOf (A.data i) + 1 :=
    funext fun _ => by simp
  rw [delimiters, totalBits, List.length_flatten, List.map_ofFn, hlen, sum_ofFn_add_one,
    Nat.add_comm]

private lemma filter_id_replicate_false_concat_true (s : ℕ) :
    ((List.replicate s false).concat true).filter id = [true] := by
  rw [List.concat_eq_append, List.filter_append, List.filter_replicate_of_neg (by decide)]
  rfl

/-- Delimiter count: the total number of delimiter 1-bits across all `K` items is exactly `K`. -/
theorem delimiters_count_delimiters (A : MiniArray α K) (sizeOf : α → ℕ) :
    ((A.delimiters sizeOf).filter id).length = K := by
  dsimp only [delimiters]
  simp only [List.filter_flatten, List.length_flatten, List.map_ofFn,
    Function.comp_def, filter_id_replicate_false_concat_true]
  simp

end MiniArray


/-! ### 3. Local Query Router (`arXiv:2111.00602` §4.3, Lemma 15, pp. 25–26) -/

/-- Binary prefix trie for local prefix routing (`arXiv:2111.00602` §4.3, Lemma 15).
In the terminology of Bender et al. (Lemma 15), this is an uncompressed binary trie where each
leaf stores its payload value and internal nodes branch on successive bits of the key.
Adaptation: in place of the paper's oracle $g$ dynamically extending prefixes during insertion,
the formal router operates on prefix-free key sets, where `insert?` rejects collisions and
returns `none` (zero silent drops or overwrites). Once a leaf is reached, its stored payload is
returned for any key extension. Bit-packed Four-Russians decoding subroutines on Word-RAM belong
to Stage A4. -/
inductive PrefixTrie (α : Type*) where
  /-- Empty trie. -/
  | empty : PrefixTrie α
  /-- Leaf storing routed payload value `val`. -/
  | leaf (val : α) : PrefixTrie α
  /-- Branch node with left (0-bit) and right (1-bit) subtrees. -/
  | branch (left : PrefixTrie α) (right : PrefixTrie α) : PrefixTrie α
  deriving DecidableEq, Repr

namespace PrefixTrie

variable {α : Type*}

/-- Total number of nodes in the prefix trie. -/
@[expose] def nodeCount : PrefixTrie α → ℕ
  | .empty => 1
  | .leaf _ => 1
  | .branch l r => nodeCount l + nodeCount r + 1

/-- Route a bit-sequence through the prefix trie.
Once a leaf is reached (corresponding to the stored prefix), its stored
payload is returned for any key extension (`arXiv:2111.00602` §4.3, p. 25). -/
@[expose] def query : PrefixTrie α → List Bool → Option α
  | .empty, _ => none
  | .leaf v, _ => some v
  | .branch l _, false :: bs => query l bs
  | .branch _ r, true :: bs => query r bs
  | .branch _ _, [] => none

/-- Insert a stored prefix and value into the prefix trie.
Returns `none` if a prefix collision occurs (a leaf already exists at or above `k`,
or branch subtrees already exist below `k`), ensuring zero silent drops or overwrites. -/
@[expose] def insert? (val : α) : PrefixTrie α → List Bool → Option (PrefixTrie α)
  | .empty, [] => some (.leaf val)
  | .empty, false :: bs => do
    let l' ← insert? val .empty bs
    some (.branch l' .empty)
  | .empty, true :: bs => do
    let r' ← insert? val .empty bs
    some (.branch .empty r')
  | .leaf _, _ => none
  | .branch _ _, [] => none
  | .branch l r, false :: bs => do
    let l' ← insert? val l bs
    some (.branch l' r)
  | .branch l r, true :: bs => do
    let r' ← insert? val r bs
    some (.branch l r')

/-- Inserting at or below an existing leaf returns `none` (zero silent drops). -/
theorem insert?_leaf (v1 v2 : α) (k : List Bool) :
    insert? v2 (.leaf v1) k = none := by
  cases k <;> rfl

private lemma insert?_cons (b : Bool) {val : α} {t t' : PrefixTrie α} {bs : List Bool}
    (hins : insert? val t (b :: bs) = some t') :
    ∃ l r sub', (t = .empty ∧ l = .empty ∧ r = .empty ∨ t = .branch l r) ∧
      insert? val (cond b r l) bs = some sub' ∧
      t' = cond b (.branch l sub') (.branch sub' r) := by
  cases t with
  | empty | branch l r =>
    cases b <;> dsimp [insert?] at hins <;>
    cases hrec : insert? val _ bs with
    | none => rw [hrec] at hins; contradiction
    | some s =>
      rw [hrec] at hins
      injection hins with heq
      first | exact ⟨.empty, .empty, s, Or.inl ⟨rfl, rfl, rfl⟩, hrec, heq.symm⟩
            | exact ⟨l, r, s, Or.inr rfl, hrec, heq.symm⟩
  | leaf _ => contradiction

/-- Prune an empty branch node `.branch .empty .empty` back to `.empty`. -/
@[expose] def pruneBranch : PrefixTrie α → PrefixTrie α → PrefixTrie α
  | .empty, .empty => .empty
  | l, r => .branch l r

/-- Routing a query through `pruneBranch l r` is semantically equivalent to routing
through `.branch l r`. -/
theorem query_pruneBranch (l r : PrefixTrie α) (k : List Bool) :
    query (pruneBranch l r) k = query (.branch l r) k := by
  cases l <;> cases r <;> try rfl
  rcases k with _ | ⟨⟨⟩, _⟩ <;> rfl

/-- Delete a prefix from the prefix trie, removing the target leaf and contracting
empty branches back to `.empty`. -/
@[expose] def delete : PrefixTrie α → List Bool → PrefixTrie α
  | .empty, _ => .empty
  | .leaf _, _ => .empty
  | .branch l r, [] => pruneBranch l r
  | .branch l r, false :: bs => pruneBranch (delete l bs) r
  | .branch l r, true :: bs => pruneBranch l (delete r bs)

/-- Routing any key extension of a stored unique prefix returns the stored payload. -/
theorem query_insert_prefix (val : α) (t t' : PrefixTrie α) (k ext : List Bool)
    (hins : insert? val t k = some t') :
    query t' (k ++ ext) = some val := by
  induction k generalizing t t' with
  | nil => cases t <;> cases hins; rfl
  | cons b bs ih =>
    obtain ⟨l, r, s, _, hrec, rfl⟩ := insert?_cons b hins
    cases b <;> exact ih _ _ hrec

/-- Querying the exact inserted prefix returns the inserted value. -/
theorem query_insert_same (val : α) (t t' : PrefixTrie α) (k : List Bool)
    (hins : insert? val t k = some t') :
    query t' k = some val := by
  simpa using query_insert_prefix val t t' k [] hins

/-- Querying a deleted prefix returns `none`. -/
theorem query_delete_same (k : List Bool) (t : PrefixTrie α) :
    query (delete t k) k = none := by
  induction k generalizing t with
  | nil => cases t <;> simp [delete, query_pruneBranch, query]
  | cons b bs ih => cases t <;> cases b <;> simp [delete, query_pruneBranch, query, ih]

/-- General frame theorem for insertion: inserting a key does not alter queries for any key
that diverges from it at some bit position. -/
theorem query_insert_of_diverge (val : α) (p : List Bool) (b1 b2 : Bool) (hb : b1 ≠ b2)
    (s1 s2 : List Bool) (t t' : PrefixTrie α)
    (hins : insert? val t (p ++ (b1 :: s1)) = some t') :
    query t' (p ++ (b2 :: s2)) = query t (p ++ (b2 :: s2)) := by
  induction p generalizing t t' with
  | nil =>
    obtain ⟨l, r, s, ht, -, rfl⟩ := insert?_cons b1 hins
    cases b1 <;> cases b2 <;> (try contradiction) <;> rcases ht with ⟨rfl, rfl, rfl⟩ | rfl <;> rfl
  | cons bit p ih =>
    obtain ⟨l, r, s, ht, hrec, rfl⟩ := insert?_cons bit hins
    cases bit <;> rcases ht with ⟨rfl, rfl, rfl⟩ | rfl <;> exact ih _ _ hrec

/-- Key-preservation for distinct prefix-incomparable keys: inserting two divergent keys
preserves the retrieval of both payloads. -/
theorem query_insert_two_distinct (v1 v2 : α) (p : List Bool) (b1 b2 : Bool) (hb : b1 ≠ b2)
    (s1 s2 : List Bool) (t1 t2 : PrefixTrie α)
    (hins1 : insert? v1 .empty (p ++ (b1 :: s1)) = some t1)
    (hins2 : insert? v2 t1 (p ++ (b2 :: s2)) = some t2) :
    query t2 (p ++ (b1 :: s1)) = some v1 ∧ query t2 (p ++ (b2 :: s2)) = some v2 := by
  exact ⟨(query_insert_of_diverge v2 p b2 b1 hb.symm s2 s1 t1 t2 hins2).trans
      (query_insert_same v1 .empty t1 _ hins1),
    query_insert_same v2 t1 t2 _ hins2⟩

/-- Deleting from the left branch does not alter queries routed to the right branch. -/
theorem query_delete_branch_other_dir_false (l r : PrefixTrie α) (bs bs' : List Bool) :
    query (delete (.branch l r) (false :: bs)) (true :: bs') =
      query (.branch l r) (true :: bs') := by
  rw [delete, query_pruneBranch]; rfl

/-- Deleting from the right branch does not alter queries routed to the left branch. -/
theorem query_delete_branch_other_dir_true (l r : PrefixTrie α) (bs bs' : List Bool) :
    query (delete (.branch l r) (true :: bs)) (false :: bs') =
      query (.branch l r) (false :: bs') := by
  rw [delete, query_pruneBranch]; rfl

/-- DFS tree-shape encoding $E_1$ (`arXiv:2111.00602` §4.3, p. 25): preorder sequence
encoding node types (`[false, false]` for empty, `[false, true]` for leaf,
`true :: (encodeE1 l ++ encodeE1 r)` for branch), adapting the binary tree shape for
unambiguous DFS reconstruction. -/
@[expose] def encodeE1 : PrefixTrie α → List Bool
  | .empty => [false, false]
  | .leaf _ => [false, true]
  | .branch l r => true :: (encodeE1 l ++ encodeE1 r)

/-- Leaf payload encoding $E_2$ (`arXiv:2111.00602` §4.3, p. 25): list of leaf values in
DFS traversal order (`List α`). -/
@[expose] def encodeE2 : PrefixTrie α → List α
  | .empty => []
  | .leaf v => [v]
  | .branch l r => encodeE2 l ++ encodeE2 r

/-- Helper for DFS decoding of $(E_1, E_2)$ using fuel for structural termination. -/
private def decodeHelper (fuel : ℕ) (e1 : List Bool) (e2 : List α) :
    Option (PrefixTrie α × List Bool × List α) :=
  match fuel, e1, e2 with
  | _, false :: false :: rest1, rest2 => some (.empty, rest1, rest2)
  | _, false :: true :: rest1, v :: rest2 => some (.leaf v, rest1, rest2)
  | fuel' + 1, true :: rest1, rest2 => do
    let (l, e1', e2') ← decodeHelper fuel' rest1 rest2
    let (r, e1'', e2'') ← decodeHelper fuel' e1' e2'
    some (.branch l r, e1'', e2'')
  | _, _, _ => none

/-- Reconstruct a prefix trie from its $(E_1, E_2)$ DFS encodings. -/
def decode (e1 : List Bool) (e2 : List α) : Option (PrefixTrie α) :=
  match decodeHelper (e1.length + 1) e1 e2 with
  | some (t, [], []) => some t
  | _ => none

theorem nodeCount_le_encodeE1_length (t : PrefixTrie α) :
    nodeCount t ≤ (encodeE1 t).length := by
  induction t with
  | empty | leaf _ => exact Nat.le_add_right 1 1
  | branch l r ihl ihr =>
    simp only [encodeE1, nodeCount, List.length_cons, List.length_append]; omega

private theorem decodeHelper_encode (t : PrefixTrie α) (fuel : ℕ)
    (hfuel : nodeCount t ≤ fuel) (rest1 : List Bool) (rest2 : List α) :
    decodeHelper fuel (encodeE1 t ++ rest1) (encodeE2 t ++ rest2) = some (t, rest1, rest2) := by
  induction t generalizing fuel rest1 rest2 with
  | empty | leaf _ => cases fuel <;> rfl
  | branch l r ihl ihr =>
    cases fuel with
    | zero => simp [nodeCount] at hfuel
    | succ fuel' =>
      simp only [nodeCount] at hfuel
      simp [encodeE1, encodeE2, decodeHelper, List.append_assoc,
        ihl fuel' (by omega), ihr fuel' (by omega)]

/-- Exact DFS roundtrip decoding theorem for prefix tries. -/
theorem decode_encode (t : PrefixTrie α) :
    decode (encodeE1 t) (encodeE2 t) = some t := by
  have h := decodeHelper_encode t ((encodeE1 t).length + 1)
    (Nat.le_succ_of_le (nodeCount_le_encodeE1_length t)) [] []
  simp_all [decode]

@[simp] theorem query_leaf_nil (v : α) : query (.leaf v) [] = some v := rfl

@[simp] theorem query_empty (bs : List Bool) : query (.empty : PrefixTrie α) bs = none := rfl

end PrefixTrie

/-- Local query router alias for the prefix trie. -/
abbrev LocalQueryRouter (α : Type*) := PrefixTrie α


/-! ### 4. Free-Slot Tree (`arXiv:2111.00602` §5.1, pp. 27–28) -/

/-- Constant-depth $B$-ary bitmap tree over $[0, B^{h+1})$ for depth-0 free-slot allocation. -/
inductive FreeSlotTree (B : ℕ) : ℕ → Type where
  /-- Leaf node (height 0) storing a bitmap over `B` slots. -/
  | leaf (freeBits : Fin B → Bool) : FreeSlotTree B 0
  /-- Internal node (height `h + 1`) storing a summary bitmap and `B` children. -/
  | node (h : ℕ) (summary : Fin B → Bool) (children : Fin B → FreeSlotTree B h) :
      FreeSlotTree B (h + 1)

namespace FreeSlotTree

variable {B : ℕ}

/-- Check whether the tree has at least one free slot. -/
@[expose] def hasFree : {h : ℕ} → FreeSlotTree B h → Bool
  | 0, .leaf freeBits => (List.ofFn freeBits).any id
  | _ + 1, .node _ summary _ => (List.ofFn summary).any id

/-- Test whether a slot is free in the tree. -/
@[expose] def isFree : {h : ℕ} → FreeSlotTree B h → ℕ → Bool
  | 0, .leaf freeBits, idx =>
    if h : idx < B then freeBits ⟨idx, h⟩ else false
  | h + 1, .node _ _ children, idx =>
    let stride := B ^ (h + 1)
    if stride = 0 then false else
      let childIdx := idx / stride
      let childRem := idx % stride
      if hc : childIdx < B then isFree (children ⟨childIdx, hc⟩) childRem else false

/-- Find the first free slot index in the tree, if one exists. -/
@[expose] def findFree? : {h : ℕ} → FreeSlotTree B h → Option ℕ
  | 0, .leaf freeBits =>
    match (BitString.positions freeBits).head? with
    | some i => some i.val
    | none => none
  | h + 1, .node _ summary children =>
    match (BitString.positions summary).head? with
    | some c =>
      match findFree? (children c) with
      | some off => some (c.val * B ^ (h + 1) + off)
      | none => none
    | none => none

/-- Set the occupancy of a slot in the tree (`b = true` for free, `b = false` for allocated). -/
@[expose] def setSlot (b : Bool) (idx : ℕ) : {h : ℕ} → FreeSlotTree B h → FreeSlotTree B h
  | 0, .leaf freeBits =>
    .leaf (fun i => if i.val == idx then b else freeBits i)
  | h + 1, .node _ summary children =>
    if _hstride : B ^ (h + 1) > 0 then
      if hc : idx / B ^ (h + 1) < B then
        let newChild := setSlot b (idx % B ^ (h + 1)) (children ⟨idx / B ^ (h + 1), hc⟩)
        let newChildren := Function.update children ⟨idx / B ^ (h + 1), hc⟩ newChild
        let newSummary := fun i =>
          if i.val == idx / B ^ (h + 1) then hasFree newChild else summary i
        .node h newSummary newChildren
      else .node h summary children
    else .node h summary children

/-- Mark a slot as occupied (allocated). -/
@[expose] def allocSlot {h : ℕ} (t : FreeSlotTree B h) (idx : ℕ) : FreeSlotTree B h :=
  setSlot false idx t

/-- Mark a slot as free (deallocated). -/
@[expose] def freeSlot {h : ℕ} (t : FreeSlotTree B h) (idx : ℕ) : FreeSlotTree B h :=
  setSlot true idx t

/-- Bitmap tree structural validity invariant: summary bits accurately reflect child occupancy. -/
@[expose] def Valid : {h : ℕ} → FreeSlotTree B h → Prop
  | 0, .leaf _ => True
  | _ + 1, .node _ summary children =>
    (∀ i : Fin B, Valid (children i)) ∧
    (∀ i : Fin B, summary i = hasFree (children i))

/-- Setting a slot preserves structural validity across all tree levels. -/
theorem setSlot_preserves_valid : {h : ℕ} → (t : FreeSlotTree B h) → (b : Bool) → (idx : ℕ) →
    Valid t → Valid (setSlot b idx t)
  | 0, .leaf _, _, _, _ => trivial
  | h + 1, .node _ summary children, b, idx, hval => by
    rw [setSlot]
    split_ifs with hstride hc
    · refine ⟨fun i => ?_, fun i => ?_⟩ <;>
        rcases eq_or_ne i ⟨idx / B ^ (h + 1), hc⟩ with rfl | heq
      · simpa only [Function.update_self] using setSlot_preserves_valid _ b _ (hval.1 _)
      · simpa only [Function.update_of_ne heq] using hval.1 i
      · simp
      · simp [Function.update_of_ne heq, Fin.val_ne_of_ne heq, hval.2 i]
    all_goals exact hval

/-- Allocating a slot preserves structural validity across all tree levels. -/
theorem allocSlot_preserves_valid {h : ℕ} (t : FreeSlotTree B h) (idx : ℕ) (hv : Valid t) :
    Valid (allocSlot t idx) :=
  setSlot_preserves_valid t false idx hv

/-- Freeing a slot preserves structural validity across all tree levels. -/
theorem freeSlot_preserves_valid {h : ℕ} (t : FreeSlotTree B h) (idx : ℕ) (hv : Valid t) :
    Valid (freeSlot t idx) :=
  setSlot_preserves_valid t true idx hv

theorem isFree_lt : ∀ {h : ℕ} (t : FreeSlotTree B h) (i : ℕ),
    isFree t i = true → i < B ^ (h + 1)
  | 0, .leaf freeBits, i, hfree => by
    dsimp [isFree] at hfree
    split_ifs at hfree with hlt
    · simpa using hlt
  | h + 1, .node _ _ children, i, hfree => by
    rw [isFree] at hfree
    dsimp only at hfree
    split_ifs at hfree with hstride hc
    rw [pow_succ']
    exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hstride)).mp hc

private theorem isFree_node_mul_add {h : ℕ} (summary : Fin B → Bool)
    (children : Fin B → FreeSlotTree B h) (c : Fin B) {off : ℕ}
    (hoff : off < B ^ (h + 1)) :
    isFree (.node h summary children) (c.val * B ^ (h + 1) + off) = isFree (children c) off := by
  have hdiv : (c.val * B ^ (h + 1) + off) / B ^ (h + 1) = c.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hoff, Nat.zero_add]
  have hmod : (c.val * B ^ (h + 1) + off) % B ^ (h + 1) = off := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hoff
  rw [isFree]
  dsimp only
  split_ifs with h0 hc'
  · omega
  · rw [show (⟨_, hc'⟩ : Fin B) = c from Fin.ext hdiv, hmod]
  · exact (hc' (by rw [hdiv]; exact c.isLt)).elim

/-- Full-tree soundness of free-slot lookup: any slot index returned by `findFree?`
is genuinely free. -/
theorem findFree?_sound : ∀ {h : ℕ} (t : FreeSlotTree B h), Valid t → ∀ {i : ℕ},
    findFree? t = some i → isFree t i = true
  | 0, .leaf freeBits => fun _ _ hfind => by
    cases hhd : (BitString.positions freeBits).head? <;>
      simp only [findFree?, hhd, Option.some.injEq, reduceCtorEq] at hfind
    subst hfind
    simpa [isFree] using BitString.mem_positions.mp (List.mem_of_mem_head? hhd)
  | h + 1, .node _ summary children => fun hv _ hfind => by
    rcases hcand : (BitString.positions summary).head? with _ | c <;>
      simp only [findFree?, hcand, reduceCtorEq] at hfind
    rcases hchild : findFree? (children c) with _ | off <;>
      simp only [hchild, Option.some.injEq, reduceCtorEq] at hfind
    subst hfind
    have hsound := findFree?_sound (children c) (hv.1 c) hchild
    rwa [isFree_node_mul_add summary children c (isFree_lt _ off hsound)]

private theorem ofFn_any_id_iff {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).any id = true ↔ ∃ i : Fin n, f i = true := by
  simp [List.any_eq_true, List.mem_ofFn]

private theorem positions_head?_isSome_of_mem {n : ℕ} (bits : Fin n → Bool)
    {i : Fin n} (hi : bits i = true) :
    ∃ idx : Fin n, (BitString.positions bits).head? = some idx :=
  Option.isSome_iff_exists.mp
    (List.isSome_head?.mpr (List.ne_nil_of_mem (BitString.mem_positions.mpr hi)))

/-- Full-tree completeness of free-slot lookup: if `hasFree t = true` and `Valid t`, `findFree?`
succeeds in finding a free slot. -/
theorem findFree?_complete : ∀ {h : ℕ} (t : FreeSlotTree B h), Valid t →
    hasFree t = true → ∃ i, findFree? t = some i
  | 0, .leaf freeBits => fun _ hfree => by
    obtain ⟨i, hi⟩ := (ofFn_any_id_iff _).mp hfree
    obtain ⟨idx, hhd⟩ := positions_head?_isSome_of_mem freeBits hi
    exact ⟨idx.val, by simp only [findFree?, hhd]⟩
  | h + 1, .node _ summary children => fun hv hfree => by
    obtain ⟨c, hc⟩ := (ofFn_any_id_iff _).mp hfree
    obtain ⟨c_idx, hhd⟩ := positions_head?_isSome_of_mem summary hc
    obtain ⟨off, hoff⟩ := findFree?_complete (children c_idx) (hv.1 c_idx)
      ((hv.2 c_idx).symm.trans (BitString.mem_positions.mp (List.mem_of_mem_head? hhd)))
    exact ⟨c_idx.val * B ^ (h + 1) + off, by simp only [findFree?, hhd, hoff]⟩

/-- Semantic completeness bridge: the summary bitmap reflects existence of free slots. -/
theorem hasFree_iff_exists_isFree : ∀ {h : ℕ} (t : FreeSlotTree B h), Valid t →
    (hasFree t = true ↔ ∃ i : ℕ, isFree t i = true)
  | 0, .leaf freeBits => fun _ => by
    rw [hasFree, ofFn_any_id_iff]
    refine ⟨fun ⟨i, hi⟩ => ⟨i.val, by simp [isFree, i.isLt, hi]⟩, fun ⟨idx, hfree⟩ => ?_⟩
    simp only [isFree] at hfree
    split_ifs at hfree with hlt
    exact ⟨⟨idx, hlt⟩, hfree⟩
  | h + 1, .node _ summary children => fun hv => by
    rw [hasFree, ofFn_any_id_iff]
    refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨idx, hfree⟩ => ?_⟩
    · obtain ⟨off, hoff⟩ :=
        (hasFree_iff_exists_isFree (children c) (hv.1 c)).mp ((hv.2 c).symm.trans hc)
      exact ⟨c.val * B ^ (h + 1) + off,
        by rwa [isFree_node_mul_add summary children c (isFree_lt _ off hoff)]⟩
    · simp only [isFree] at hfree
      split_ifs at hfree with h0 hc'
      exact ⟨⟨idx / B ^ (h + 1), hc'⟩,
        (hv.2 _).trans ((hasFree_iff_exists_isFree _ (hv.1 _)).mpr ⟨_, hfree⟩)⟩

/-- Full-tree semantic completeness: if any slot in the tree is free, `findFree?` succeeds. -/
theorem findFree?_complete_of_exists_isFree {h : ℕ} (t : FreeSlotTree B h) (hv : Valid t)
    (hfree : ∃ j, isFree t j = true) : ∃ i, findFree? t = some i :=
  findFree?_complete t hv ((hasFree_iff_exists_isFree t hv).mpr hfree)

/-- Updating a slot to `b` correctly sets the slot occupancy at `idx` across all tree heights. -/
theorem isFree_setSlot_self : ∀ {h : ℕ} (t : FreeSlotTree B h) (b : Bool) (idx : ℕ),
    idx < B ^ (h + 1) → isFree (setSlot b idx t) idx = b
  | 0, .leaf _, _, _, hlt => by simp_all [setSlot, isFree]
  | h + 1, .node _ summary children, b, idx, hlt => by
    rw [pow_succ] at hlt
    have hstride_pos : B ^ (h + 1) > 0 := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt
    have hc : idx / B ^ (h + 1) < B := Nat.div_lt_of_lt_mul hlt
    simp only [setSlot, isFree, hstride_pos, hstride_pos.ne', ↓reduceIte, hc, ↓reduceDIte,
      Function.update_self]
    exact isFree_setSlot_self _ b _ (Nat.mod_lt _ hstride_pos)

/-- Updating slot `idx` preserves the occupancy of any distinct slot `j ≠ idx`. -/
theorem isFree_setSlot_of_ne : ∀ {h : ℕ} (t : FreeSlotTree B h) (b : Bool) (idx j : ℕ),
    j ≠ idx → isFree (setSlot b idx t) j = isFree t j
  | 0, .leaf freeBits, b, idx, j, hne => by simp [setSlot, isFree, hne]
  | h + 1, .node _ summary children, b, idx, j, hne => by
    rw [setSlot]
    split_ifs with hstride hc
    · simp only [isFree, hstride.ne', ↓reduceIte]
      split_ifs with hc'
      · rcases eq_or_ne (⟨j / B ^ (h + 1), hc'⟩ : Fin B) ⟨idx / B ^ (h + 1), hc⟩ with heq | heq
        · rw [heq, Function.update_self]
          refine isFree_setSlot_of_ne _ b _ _ fun hmod => hne ?_
          rw [← Nat.div_add_mod j (B ^ (h + 1)), ← Nat.div_add_mod idx (B ^ (h + 1)), hmod,
            Fin.mk.inj heq]
        · rw [Function.update_of_ne heq]
      · rfl
    all_goals rfl

/-- Allocating slot `idx` marks it as occupied across all tree heights. -/
theorem allocSlot_self {h : ℕ} (t : FreeSlotTree B h) {idx : ℕ} (hidx : idx < B ^ (h + 1)) :
    isFree (allocSlot t idx) idx = false :=
  isFree_setSlot_self t false idx hidx

/-- Freeing slot `idx` marks it as free across all tree heights. -/
theorem freeSlot_self {h : ℕ} (t : FreeSlotTree B h) {idx : ℕ} (hidx : idx < B ^ (h + 1)) :
    isFree (freeSlot t idx) idx = true :=
  isFree_setSlot_self t true idx hidx

/-- Allocating slot `idx` preserves the status of any distinct slot `j ≠ idx`. -/
theorem allocSlot_of_ne {h : ℕ} (t : FreeSlotTree B h) {idx j : ℕ} (h : j ≠ idx) :
    isFree (allocSlot t idx) j = isFree t j :=
  isFree_setSlot_of_ne t false idx j h

/-- Freeing slot `idx` preserves the status of any distinct slot `j ≠ idx`. -/
theorem freeSlot_of_ne {h : ℕ} (t : FreeSlotTree B h) {idx j : ℕ} (h : j ≠ idx) :
    isFree (freeSlot t idx) j = isFree t j :=
  isFree_setSlot_of_ne t true idx j h

/-- Allocating leaf slot `i` marks it as occupied. -/
theorem allocSlot_leaf_self (freeBits : Fin B → Bool) (i : Fin B) :
    isFree (allocSlot (.leaf freeBits) i.val) i.val = false :=
  allocSlot_self (.leaf freeBits) (by simp [i.isLt])

/-- Freeing leaf slot `i` marks it as free. -/
theorem freeSlot_leaf_self (freeBits : Fin B → Bool) (i : Fin B) :
    isFree (freeSlot (.leaf freeBits) i.val) i.val = true :=
  freeSlot_self (.leaf freeBits) (by simp [i.isLt])

/-- Allocating leaf slot `i` preserves distinct leaf slot `j ≠ i`. -/
theorem allocSlot_leaf_of_ne (freeBits : Fin B → Bool) {i j : Fin B} (h : j ≠ i) :
    isFree (allocSlot (.leaf freeBits) i.val) j.val = isFree (.leaf freeBits) j.val :=
  allocSlot_of_ne (.leaf freeBits) (fun heq => h (Fin.ext heq))

/-- Freeing leaf slot `i` preserves distinct leaf slot `j ≠ i`. -/
theorem freeSlot_leaf_of_ne (freeBits : Fin B → Bool) {i j : Fin B} (h : j ≠ i) :
    isFree (freeSlot (.leaf freeBits) i.val) j.val = isFree (.leaf freeBits) j.val :=
  freeSlot_of_ne (.leaf freeBits) (fun heq => h (Fin.ext heq))

end FreeSlotTree

end KickTree
end Dictionary
end DataStructure
end Cslib
