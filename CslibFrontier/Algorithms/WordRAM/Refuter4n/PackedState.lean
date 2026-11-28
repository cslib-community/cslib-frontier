/-
Copyright (c) 2026 Christian Reitwiessner, Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.XORSATDense
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterSizes
import CslibFrontier.Foundations.Data.Nat.Bitwise.Sparse
import Mathlib.Data.List.GetD

/-!
# Packed state of the `4n - 9d` refuter and its invariant

A word-level representation of the gate-elimination states that the refuter `refute` visits
(`Cslib.Circuits.Boolean.AffineDisperser4n`), and the relation `Rep` saying that packed words
represent a state. This is the pure layer of the Word-RAM refuter of issue `#4322`
(Milestone 4); no program and no running time is claimed here.

Fix a bound `N` on the names of parameters, auxiliary variables and gates and a bound `E` on
equation names. The layout of a circuit `C` uses `N = nameBound C = n + C.size` (names along the
run, `nameSet_iterate`) and `E = eqnBound C = 5 n + 7 C.size` (equation names at the end of the
run, `eqns_refuterLoop`). The packed state `PackedState` consists of:

* **masks:** the parameters, auxiliary variables and gates as bitmasks `maskOf`, bit `i` set iff
  `i` is in the set;
* **gate table:** `N` rows of three words (`GateRow`), `rowOf g = ⟨ttOf g.op, argCode g.left,
  argCode g.right⟩`: the truth table of the operation (bit `idx a b = 2a + b` is `op a b`,
  `testBit_ttOf`) and the codes `const b ↦ b`, `node i ↦ i + 2` of the arguments; rows of
  non-gates are junk, but every row is within range (`RowLt`);
* **equation table:** `E` words, one per equation name. `eqnWord N e alive` has the terms below
  `N` at bits `0, …, N - 1`, the right-hand side at bit `N` (the packed row `rowWord` of the dense
  `XORSAT` elimination, `eqnWord_mod`) and an alive flag at bit `N + 1`. Equation names are array
  indices, never bits of a mask;
* **output:** one word `litCode`, `2 · argCode + neg`;
* **pairs:** a duplicate-free list of two-word records `pairCode`, `(2 fst + fstBias,
  2 snd + sndBias)`, one per pair;
* **parameter map:** `n` explicit affine rows. Row `i` is a word `r`, read as
  `rowEval N r val = r_N + ∑_{j < N, r_j} val j` (the same packed format), and `S.phi val i` is
  the value of row `i` (`PhiWords`). Restriction and the affine reparameterisation update every row
  by `substWord` (`PhiWords.restrict`, `PhiWords.swap`): these are the only operations of the
  refuter that change `phi`.

`Rep` records only the words; the bounds that also follow from validity (terms, output and pairs
named below `N`) are derived from `State.Valid` (`Rep.terms_lt`, `Rep.out_lt`, `Rep.pairs_lt`).

**Word width.** At `w ≥ N + 2` and `w ≥ 4`, every stored word of a valid represented state fits
(`Rep.fits`); with `N = n + C.size` this is the basis `w ≥ n + C.size + 2`, plus `w ≥ 4` for a
4-bit truth table, which binds only when `N < 2`. This layer fixes no memory layout: addresses,
counters, scratch cells and the separate instruction and workspace bounds come with the step
programs. Equation words are rows at the fixed width `N`, while `evaluateAux` builds its dense rows
at the width `varBound S`; the step layer relates the two.

Searches of the refuter run over sorted `Finset`s; on a mask they are the ascending bit scan over
`List.range N` (`find?_sort_eq_find?_range`, `findSome?_sort_eq_findSome?_range`). The first
client is the `(D1)` search: `pFindD1` scans the gate mask and reads only packed rows, and equals
`findD1` on every represented state (`Rep.pFindD1_eq`). The second client is the initial state:
`initialPacked C` represents `initialState C` (`rep_initialPacked`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.maskOf`, `argCode`, `idx`, `ttOf`, `GateRow`, `rowOf`,
  `RowLt`, `litCode`, `pairCode`, `eqnWord`: encodings.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowEval`, `substWord`, `litWord`,
  `Cslib.Algorithms.WordRAM.Refuter4n.PhiWords`: explicit rows of the parameter map.
* `Cslib.Algorithms.WordRAM.Refuter4n.PackedState`, `PackedState.Fits`, `Rep`: the packed state,
  its word-width condition and the representation relation.
* `Cslib.Algorithms.WordRAM.Refuter4n.nameBound`, `eqnBound`: the table sizes of the layout.
* `Cslib.Algorithms.WordRAM.Refuter4n.isDegenerateRow`, `pFindD1`: `(D1)` on the packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.initialPacked`: the packed initial state.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.testBit_maskOf`, `testBit_ttOf`,
  `testBit_rowWord_toDenseRow`, `eqnWord_mod`, `testBit_eqnWord_alive`: the encodings are
  faithful.
* `Cslib.Algorithms.WordRAM.Refuter4n.maskOf_lt`, `ttOf_lt`, `argCode_lt`, `litCode_lt`,
  `rowLt_rowOf`, `rowWord_toDenseRow_lt`, `eqnWord_lt`, `substWord_lt`, `litWord_lt`: the
  encodings fit in their bit ranges.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowEval_two_pow`, `rowEval_rowWord`, `rowEval_litWord`:
  values of coordinate, equation and literal rows.
* `Cslib.Algorithms.WordRAM.Refuter4n.rowEval_substWord`, `PhiWords.restrict`, `PhiWords.swap`:
  exact row updates of the parameter map, with no side conditions beyond names below `N`.
* `Cslib.Algorithms.WordRAM.Refuter4n.find?_sort_eq_find?_range`,
  `findSome?_sort_eq_findSome?_range`: sorted searches are ascending bit scans.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.terms_lt`, `Rep.out_lt`, `Rep.pairs_lt`: names read by a
  valid represented state are below `N`.
* `Cslib.Algorithms.WordRAM.Refuter4n.Rep.fits`, `Rep.length_pairs`, `Rep.length_pairs_le`:
  every word fits at `w ≥ N + 2`, `w ≥ 4`; the pair list has one record per pair and at most `N`
  records.
* `Cslib.Algorithms.WordRAM.Refuter4n.eqnBound_le`: the equation table has at most
  `7 · nameBound C` words.
* `Cslib.Algorithms.WordRAM.Refuter4n.isDegenerateRow_rowOf`, `Rep.pFindD1_eq`,
  `rep_initialPacked`: the two clients.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Finset
open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Algorithms.WordRAM.XORSATDense

variable {n : ℕ}

/-! ### Bitmasks and sorted searches -/

/-- The bitmask of a finite set of names: bit `i` is set iff `i ∈ s` (the inverse of
`Finset.equivBitIndices`). -/
@[expose] def maskOf (s : Finset ℕ) : ℕ :=
  ∑ i ∈ s, 2 ^ i

/-- Bit `i` of `maskOf s` is membership of `i` in `s`. -/
@[simp] theorem testBit_maskOf (s : Finset ℕ) (i : ℕ) : (maskOf s).testBit i = decide (i ∈ s) :=
  Bool.eq_iff_iff.2 ((Nat.testBit_sum_two_pow s i).trans decide_eq_true_iff.symm)

/-- A set of names below `N` has a mask below `2 ^ N`. -/
theorem maskOf_lt {s : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N) : maskOf s < 2 ^ N :=
  Nat.geomSum_lt Nat.one_lt_two hs

private theorem sort_eq_filter_range {s : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N) :
    s.sort (· ≤ ·) = (List.range N).filter fun i => decide (i ∈ s) :=
  (Finset.sortedLT_sort s).pairwise.eq_of_mem_iff ((List.pairwise_lt_range).filter _) fun i => by
    simp only [Finset.mem_sort, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => ⟨hs i h, h⟩, fun h => h.2⟩

/-- A search in a sorted set of names below `N` is the ascending scan of its mask. -/
theorem find?_sort_eq_find?_range {s : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N) (p : ℕ → Bool) :
    (s.sort (· ≤ ·)).find? p = (List.range N).find? fun i => (maskOf s).testBit i && p i := by
  rw [sort_eq_filter_range hs, List.find?_filter]
  exact List.find?_congr fun i _ => by simp

private theorem findSome?_filter {α β : Type*} (l : List α) (q : α → Bool) (g : α → Option β) :
    (l.filter q).findSome? g = l.findSome? fun a => if q a then g a else none := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : q a <;> simp [h, List.findSome?_cons, ih]

/-- `findSome?` in a sorted set of names below `N` is the ascending scan of its mask. -/
theorem findSome?_sort_eq_findSome?_range {α : Type*} {s : Finset ℕ} {N : ℕ}
    (hs : ∀ i ∈ s, i < N) (g : ℕ → Option α) :
    (s.sort (· ≤ ·)).findSome? g =
      (List.range N).findSome? fun i => if (maskOf s).testBit i then g i else none := by
  rw [sort_eq_filter_range hs, findSome?_filter]
  simp only [testBit_maskOf]

/-! ### Gate rows -/

/-- The word code of an argument: `const b ↦ b`, `node i ↦ i + 2`. -/
@[expose] def argCode : Arg → ℕ
  | .const b => b.toNat
  | .node i => i + 2

/-- The bit index `2a + b` of the input pair `(a, b)` in a truth table. -/
@[expose] def idx (a b : Bool) : ℕ :=
  2 * a.toNat + b.toNat

/-- The 4-bit truth table of a binary operation: bit `idx a b` is `op a b`. -/
@[expose] def ttOf (op : Bool → Bool → Bool) : ℕ :=
  (op false false).toNat + 2 * (op false true).toNat + 4 * (op true false).toNat +
    8 * (op true true).toNat

/-- The truth table records the operation. -/
theorem testBit_ttOf (op : Bool → Bool → Bool) (a b : Bool) :
    (ttOf op).testBit (idx a b) = op a b := by
  cases a <;> cases b <;> cases h1 : op false false <;> cases h2 : op false true <;>
    cases h3 : op true false <;> cases h4 : op true true <;>
    simp only [ttOf, idx, h1, h2, h3, h4] <;> decide

/-- A truth table is a 4-bit word. -/
theorem ttOf_lt (op : Bool → Bool → Bool) : ttOf op < 16 := by
  unfold ttOf
  have := Bool.toNat_le (op false false)
  have := Bool.toNat_le (op false true)
  have := Bool.toNat_le (op true false)
  have := Bool.toNat_le (op true true)
  omega

/-- The code of an argument that reads only names below `N` is below `N + 2`. -/
theorem argCode_lt {a : Arg} {N : ℕ} (h : ∀ i, a = .node i → i < N) :
    argCode a < N + 2 := by
  cases a with
  | const b => have := Bool.toNat_le b; simp only [argCode]; omega
  | node i => simpa [argCode] using h i rfl

/-- A gate row of three words. -/
structure GateRow where
  /-- The truth table of the operation. -/
  tt : ℕ
  /-- The code of the left argument. -/
  left : ℕ
  /-- The code of the right argument. -/
  right : ℕ
  deriving DecidableEq, Repr

/-- The row of a gate. -/
@[expose] def rowOf (g : Gate) : GateRow :=
  ⟨ttOf g.op, argCode g.left, argCode g.right⟩

/-- The fields of a gate row are within their ranges for names below `N`. -/
@[expose] def RowLt (N : ℕ) (r : GateRow) : Prop :=
  r.tt < 16 ∧ r.left < N + 2 ∧ r.right < N + 2

/-- The row of a gate reading only names below `N` is within range. -/
theorem rowLt_rowOf {g : Gate} {N : ℕ} (h : ∀ i, g.Reads i → i < N) : RowLt N (rowOf g) :=
  ⟨ttOf_lt _, argCode_lt fun i hi => h i (.inl hi), argCode_lt fun i hi => h i (.inr hi)⟩

/-! ### Output, pairs and equations -/

/-- The word code of a literal: `2 · argCode + neg`. -/
@[expose] def litCode (ℓ : Lit) : ℕ :=
  2 * argCode ℓ.arg + ℓ.neg.toNat

/-- The code of a literal that reads only names below `N` is below `2 N + 4`. -/
theorem litCode_lt {ℓ : Lit} {N : ℕ} (h : ∀ i, ℓ.Reads i → i < N) : litCode ℓ < 2 * N + 4 := by
  have := argCode_lt (a := ℓ.arg) h
  have := Bool.toNat_le ℓ.neg
  rw [litCode]
  omega

/-- The two-word record of a pair: `(2 fst + fstBias, 2 snd + sndBias)`. -/
@[expose] def pairCode (pr : ZeroPair) : ℕ × ℕ :=
  (2 * pr.fst + pr.fstBias.toNat, 2 * pr.snd + pr.sndBias.toNat)

/-- The word of an equation: terms below `N` at bits `0, …, N - 1`, the right-hand side at bit
`N` (the packed row `rowWord` of `toDenseRow`), and the alive flag at bit `N + 1`. -/
@[expose] def eqnWord (N : ℕ) (e : Equation) (alive : Bool) : ℕ :=
  rowWord (toDenseRow N e.terms e.rhs) ||| (if alive then 2 ^ (N + 1) else 0)

private theorem rowRel_toDenseRow (N : ℕ) (T : Finset ℕ) (c : Bool) :
    RowRel N 0 (rowWord (toDenseRow N T c)) (toDenseRow N T c) :=
  rowRel_rowWord (by simp [toDenseRow])

/-- The packed dense row of `∑ T = c` at width `N` fits in `N + 1` bits. -/
theorem rowWord_toDenseRow_lt (N : ℕ) (T : Finset ℕ) (c : Bool) :
    rowWord (toDenseRow N T c) < 2 ^ (N + 1) :=
  (rowRel_toDenseRow N T c).lt

/-- Bits of the packed dense row of `∑ T = c` at width `N`. -/
theorem testBit_rowWord_toDenseRow (N : ℕ) (T : Finset ℕ) (c : Bool) (i : ℕ) :
    (rowWord (toDenseRow N T c)).testBit i =
      if i < N then decide (i ∈ T) else (decide (i = N) && c) := by
  have h := rowRel_toDenseRow N T c
  rcases lt_trichotomy i N with hi | rfl | hi
  · have hc := h.coeff i (by omega)
    rw [zero_add, List.getD_eq_getElem _ _ (by simpa [toDenseRow] using hi)] at hc
    simpa [hi, toDenseRow] using hc
  · simpa [toDenseRow] using h.rhs
  · simp only [show ¬ i < N by omega, show i ≠ N by omega, ↓reduceIte, decide_false,
      Bool.false_and]
    exact Nat.testBit_lt_two_pow (h.lt.trans_le (Nat.pow_le_pow_right two_pos (by omega)))

/-- The alive flag of an equation word. -/
@[simp] theorem testBit_eqnWord_alive (N : ℕ) (e : Equation) (alive : Bool) :
    (eqnWord N e alive).testBit (N + 1) = alive := by
  rw [eqnWord, Nat.testBit_or, testBit_rowWord_toDenseRow]
  cases alive <;> simp [Nat.testBit_two_pow_self]

/-- Below the alive flag, an equation word is the dense `XORSAT` row of the equation, in the
packed format of `Cslib.Algorithms.WordRAM.XORSATDense`. -/
theorem eqnWord_mod (N : ℕ) (e : Equation) (alive : Bool) :
    eqnWord N e alive % 2 ^ (N + 1) = rowWord (toDenseRow N e.terms e.rhs) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, eqnWord, Nat.testBit_or]
  by_cases hi : i < N + 1
  · have : (if alive then 2 ^ (N + 1) else 0).testBit i = false := by
      split_ifs
      · rw [Nat.testBit_two_pow, decide_eq_false (by omega)]
      · simp
    simp [hi, this]
  · simp only [hi, decide_false, Bool.false_and]
    rw [Nat.testBit_lt_two_pow ((rowWord_toDenseRow_lt N _ _).trans_le
      (Nat.pow_le_pow_right two_pos (by omega)))]

/-- An equation word fits in `N + 2` bits. -/
theorem eqnWord_lt (N : ℕ) (e : Equation) (alive : Bool) : eqnWord N e alive < 2 ^ (N + 2) := by
  apply Nat.or_lt_two_pow ((rowWord_toDenseRow_lt N _ _).trans_le
    (Nat.pow_le_pow_right two_pos (by omega)))
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) (by omega)
  · exact Nat.two_pow_pos _

/-! ### Explicit rows of the parameter map -/

/-- The value of the affine row stored in the word `r`: `r_N + ∑_{j < N, r_j} val j`. -/
@[expose] def rowEval (N r : ℕ) (val : ℕ → Bool) : Bool :=
  r.testBit N + ∑ j ∈ (range N).filter fun j => r.testBit j, val j

/-- Substitute, in the row `r`, the name `x` by the row `u`: if `x` occurs, clear it and add `u`
(terms and constant at once). -/
@[expose] def substWord (x u r : ℕ) : ℕ :=
  if r.testBit x then r ^^^ 2 ^ x ^^^ u else r

private theorem sum_filter_xor (N a b : ℕ) (f : ℕ → Bool) :
    ∑ j ∈ (range N).filter (fun j => (a ^^^ b).testBit j), f j =
      (∑ j ∈ (range N).filter (fun j => a.testBit j), f j) +
        ∑ j ∈ (range N).filter (fun j => b.testBit j), f j := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> cases f j <;> rfl

private theorem filter_testBit_two_pow {N x : ℕ} (hx : x < N) :
    (range N).filter (fun j => (2 ^ x).testBit j) = {x} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_two_pow, decide_eq_true_eq,
    Finset.mem_singleton]
  exact ⟨fun h => h.2.symm, fun h => ⟨h ▸ hx, h.symm⟩⟩

/-- The row `2 ^ i` is the coordinate `val i`. -/
theorem rowEval_two_pow {N i : ℕ} (hi : i < N) (val : ℕ → Bool) :
    rowEval N (2 ^ i) val = val i := by
  rw [rowEval, filter_testBit_two_pow hi, Finset.sum_singleton, Nat.testBit_two_pow,
    decide_eq_false (by omega)]
  cases val i <;> rfl

/-- The packed dense row of `∑ T = c` is the row `c + ∑ T`. -/
theorem rowEval_rowWord {N : ℕ} {T : Finset ℕ} (hT : ∀ j ∈ T, j < N) (c : Bool)
    (val : ℕ → Bool) : rowEval N (rowWord (toDenseRow N T c)) val = c + ∑ j ∈ T, val j := by
  have hF : (range N).filter (fun j => (rowWord (toDenseRow N T c)).testBit j) = T := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, testBit_rowWord_toDenseRow]
    constructor
    · rintro ⟨hj, h⟩
      simpa [hj] using h
    · intro h
      exact ⟨hT j h, by simp [hT j h, h]⟩
  rw [rowEval, hF, testBit_rowWord_toDenseRow]
  simp

/-- **Row update.** Substituting `x` by the row `u` in the row `r` evaluates `r` at the assignment
giving `x` the value of `u`. -/
theorem rowEval_substWord {N x : ℕ} (hx : x < N) (u r : ℕ) (val : ℕ → Bool) :
    rowEval N (substWord x u r) val =
      rowEval N r (Function.update val x (rowEval N u val)) := by
  unfold substWord
  split_ifs with hr
  · have hxF : x ∈ (range N).filter fun j => r.testBit j := by simp [hx, hr]
    have hxN : (2 ^ x).testBit N = false := by rw [Nat.testBit_two_pow, decide_eq_false (by omega)]
    simp only [rowEval]
    rw [sum_filter_xor, sum_filter_xor, filter_testBit_two_pow hx, Finset.sum_singleton,
      Finset.sum_update_of_mem hxF, Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase _ _ hxF, Nat.testBit_xor, Nat.testBit_xor, hxN]
    generalize r.testBit N = a
    generalize u.testBit N = b
    generalize val x = c
    generalize ∑ j ∈ ((range N).filter fun j => r.testBit j).erase x, val j = d
    generalize ∑ j ∈ (range N).filter (fun j => u.testBit j), val j = e
    revert a b c d e
    decide
  · simp only [rowEval]
    congr 1
    refine Finset.sum_congr rfl fun j hj => (Function.update_of_ne ?_ _ _).symm
    rintro rfl
    exact hr (Finset.mem_filter.1 hj).2

/-- Substitution keeps a row in `N + 1` bits. -/
theorem substWord_lt {N x u r : ℕ} (hx : x < N) (hu : u < 2 ^ (N + 1)) (hr : r < 2 ^ (N + 1)) :
    substWord x u r < 2 ^ (N + 1) := by
  unfold substWord
  split_ifs
  · exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hr (Nat.pow_lt_pow_right (by omega) (by omega)))
      hu
  · exact hr

/-- The row of a literal: `b ^^ neg` for a constant `b`, `val y ^^ neg` for a node `y`. -/
@[expose] def litWord (N : ℕ) (ℓ : Lit) : ℕ :=
  match ℓ.arg with
  | .const b => rowWord (toDenseRow N ∅ (b ^^ ℓ.neg))
  | .node y => rowWord (toDenseRow N {y} ℓ.neg)

/-- The row of a literal reading a name below `N` evaluates to the literal. -/
theorem rowEval_litWord {N : ℕ} {ℓ : Lit} (h : ∀ y, ℓ.Reads y → y < N) (val : ℕ → Bool) :
    rowEval N (litWord N ℓ) val = ℓ.eval val := by
  obtain ⟨a, neg⟩ := ℓ
  cases a with
  | const b =>
    rw [litWord, rowEval_rowWord (by simp), Finset.sum_empty]
    cases b <;> cases neg <;> rfl
  | node y =>
    rw [litWord, rowEval_rowWord (by simpa using h y rfl), Finset.sum_singleton]
    change neg + val y = (val y ^^ neg)
    cases val y <;> cases neg <;> rfl

/-- The row of a literal fits in `N + 1` bits. -/
theorem litWord_lt (N : ℕ) (ℓ : Lit) : litWord N ℓ < 2 ^ (N + 1) := by
  unfold litWord
  split <;> exact rowWord_toDenseRow_lt _ _ _

/-- The words `W` are explicit affine rows of the parameter map of `S`: `S.phi val i` is the
value of row `i`, and every row has its terms below `N` and its constant at bit `N`. -/
structure PhiWords (N : ℕ) (W : List ℕ) (S : State n) : Prop where
  /-- One row per output bit. -/
  length : W.length = n
  /-- Every row fits in `N + 1` bits. -/
  lt : ∀ r ∈ W, r < 2 ^ (N + 1)
  /-- Output bit `i` is the value of row `i`. -/
  eval : ∀ (val : ℕ → Bool) (i : Fin n), S.phi val i = rowEval N (W.getD i 0) val

private theorem PhiWords.map_substWord {N : ℕ} {W : List ℕ} {S S' : State n} (h : PhiWords N W S)
    {x u : ℕ} (hx : x < N) (hu : u < 2 ^ (N + 1))
    (hphi : ∀ val, S'.phi val = S.phi (Function.update val x (rowEval N u val))) :
    PhiWords N (W.map (substWord x u)) S' where
  length := by rw [List.length_map, h.length]
  lt r hr := by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact substWord_lt hx hu (h.lt r' hr')
  eval val i := by
    have hi : (i : ℕ) < W.length := h.length ▸ i.isLt
    have hget : (W.map (substWord x u)).getD i 0 = substWord x u (W.getD i 0) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
    rw [hphi, h.eval, hget, rowEval_substWord hx]

/-- **Restriction** `x := ℓ` (`State.restrict`, hence `State.fixConst`) updates every row by
substituting the row of `ℓ`. -/
theorem PhiWords.restrict {N : ℕ} {W : List ℕ} {S : State n} (h : PhiWords N W S) {x : ℕ}
    (hx : x < N) {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y < N) (P : Finset ZeroPair) :
    PhiWords N (W.map (substWord x (litWord N ℓ))) (S.restrict x ℓ P) :=
  h.map_substWord hx (litWord_lt N ℓ) fun val => by rw [rowEval_litWord hℓ]; rfl

/-- **Affine reparameterisation** (`State.swap x Q c T`) updates every row by substituting
`x := c + val Q + ∑_{T \ {x}} val`, the packed row of `∑ ((T \ {x}) ∆ {Q}) = c`. -/
theorem PhiWords.swap {N : ℕ} {W : List ℕ} {S : State n} (h : PhiWords N W S) {x Q : ℕ}
    (hx : x < N) (hQ : Q < N) {T : Finset ℕ} (hT : ∀ j ∈ T, j < N) (c : Bool) :
    PhiWords N (W.map (substWord x (rowWord (toDenseRow N (symmDiff (T.erase x) {Q}) c))))
      (S.swap x Q c T) := by
  have hU : ∀ j ∈ symmDiff (T.erase x) {Q}, j < N := fun j hj => by
    rcases Finset.mem_symmDiff.1 hj with ⟨hj, -⟩ | ⟨hj, -⟩
    · exact hT j (Finset.mem_of_mem_erase hj)
    · exact (Finset.mem_singleton.1 hj) ▸ hQ
  refine h.map_substWord hx (rowWord_toDenseRow_lt _ _ _) fun val => ?_
  rw [rowEval_rowWord hU, sum_symmDiff_singleton]
  change S.phi _ = S.phi _
  congr 2
  generalize ∑ j ∈ T.erase x, val j = s
  cases val Q <;> cases c <;> cases s <;> rfl

/-! ### Packed states -/

/-- A packed refuter state (pure model of the Word-RAM memory image). -/
structure PackedState where
  /-- Bitmask of the parameters. -/
  params : ℕ
  /-- Bitmask of the auxiliary variables. -/
  aux : ℕ
  /-- Bitmask of the gates. -/
  gates : ℕ
  /-- The gate table, one row per name below `N`. -/
  gateRows : List GateRow
  /-- The equation table, one word per equation name below `E`. -/
  eqnRows : List ℕ
  /-- The code of the output literal. -/
  out : ℕ
  /-- The pair records. -/
  pairs : List (ℕ × ℕ)
  /-- The rows of the parameter map. -/
  phiRows : List ℕ
  deriving DecidableEq, Repr

/-- Every word of `P` is below `2 ^ w`. -/
@[expose] def PackedState.Fits (w : ℕ) (P : PackedState) : Prop :=
  P.params < 2 ^ w ∧ P.aux < 2 ^ w ∧ P.gates < 2 ^ w ∧ P.out < 2 ^ w ∧
    (∀ r ∈ P.gateRows, r.tt < 2 ^ w ∧ r.left < 2 ^ w ∧ r.right < 2 ^ w) ∧
    (∀ x ∈ P.eqnRows, x < 2 ^ w) ∧ (∀ c ∈ P.pairs, c.1 < 2 ^ w ∧ c.2 < 2 ^ w) ∧
    ∀ r ∈ P.phiRows, r < 2 ^ w

/-- `P` represents the state `S`, with names below `N` and equation names below `E`. -/
structure Rep (N E : ℕ) (P : PackedState) (S : State n) : Prop where
  /-- Parameters, auxiliary variables and gates are named below `N`. -/
  names : nameSet S ⊆ range N
  /-- Equations are named below `E`. -/
  eqns : S.eqns ⊆ range E
  /-- The parameter mask. -/
  params : P.params = maskOf S.params
  /-- The auxiliary mask. -/
  aux : P.aux = maskOf S.aux
  /-- The gate mask. -/
  gates : P.gates = maskOf S.gates
  /-- The gate table has `N` rows. -/
  gateRows_length : P.gateRows.length = N
  /-- The row of every gate is the row of its gate. -/
  gateRow : ∀ J ∈ S.gates, P.gateRows.getD J ⟨0, 0, 0⟩ = rowOf (S.gate J)
  /-- Every row, junk or not, is within range. -/
  gateRow_lt : ∀ r ∈ P.gateRows, RowLt N r
  /-- The equation table has `E` words. -/
  eqnRows_length : P.eqnRows.length = E
  /-- The word of every equation is its equation word. -/
  eqnRow : ∀ e ∈ S.eqns, P.eqnRows.getD e 0 = eqnWord N (S.eqn e) true
  /-- The alive flags are the equation names. -/
  eqnRow_alive : ∀ e < E, (P.eqnRows.getD e 0).testBit (N + 1) = decide (e ∈ S.eqns)
  /-- Every word of the table, junk or not, fits in `N + 2` bits. -/
  eqnRow_lt : ∀ x ∈ P.eqnRows, x < 2 ^ (N + 2)
  /-- The output word. -/
  out : P.out = litCode S.out
  /-- The pair records list the pairs, each once. -/
  pairs : ∃ l : List ZeroPair, l.Nodup ∧ l.toFinset = S.pairs ∧ P.pairs = l.map pairCode
  /-- The rows of the parameter map. -/
  phi : PhiWords N P.phiRows S

namespace Rep

variable {N E : ℕ} {P : PackedState} {S : State n}

private theorem lt_of_mem_nameSet (h : Rep N E P S) {i : ℕ} (hi : i ∈ nameSet S) : i < N :=
  Finset.mem_range.1 (h.names hi)

private theorem lt_of_mem_params (h : Rep N E P S) {i : ℕ} (hi : i ∈ S.params) : i < N :=
  h.lt_of_mem_nameSet (by simp [nameSet, hi])

private theorem lt_of_mem_aux (h : Rep N E P S) {i : ℕ} (hi : i ∈ S.aux) : i < N :=
  h.lt_of_mem_nameSet (by simp [nameSet, hi])

private theorem lt_of_mem_gates (h : Rep N E P S) {i : ℕ} (hi : i ∈ S.gates) : i < N :=
  h.lt_of_mem_nameSet (by simp [nameSet, hi])

/-- Terms of the equations of a valid represented state are named below `N`. -/
theorem terms_lt (h : Rep N E P S) {f : BooleanFunction n} (hS : S.Valid f) {e : ℕ}
    (he : e ∈ S.eqns) {j : ℕ} (hj : j ∈ (S.eqn e).terms) : j < N :=
  h.lt_of_mem_nameSet (Finset.mem_union_left _ (hS.wf.terms_subset e he hj))

/-- The output of a valid represented state reads a name below `N`. -/
theorem out_lt (h : Rep N E P S) {f : BooleanFunction n} (hS : S.Valid f) {i : ℕ}
    (hi : S.out.Reads i) : i < N :=
  h.lt_of_mem_nameSet (hS.wf.out_live i hi)

/-- The pairs of a valid represented state consist of names below `N`. -/
theorem pairs_lt (h : Rep N E P S) {f : BooleanFunction n} (hS : S.Valid f) {pr : ZeroPair}
    (hpr : pr ∈ S.pairs) : pr.fst < N ∧ pr.snd < N :=
  ⟨h.lt_of_mem_params (hS.pair_mem pr hpr).1, h.lt_of_mem_params (hS.pair_mem pr hpr).2.1⟩

/-- There is one pair record per pair. -/
theorem length_pairs (h : Rep N E P S) : P.pairs.length = S.pairs.card := by
  obtain ⟨l, hl, hS, hP⟩ := h.pairs
  rw [hP, List.length_map, ← hS, List.toFinset_card_of_nodup hl]

/-- For a valid state, there are at most `N` pair records. -/
theorem length_pairs_le (h : Rep N E P S) {f : BooleanFunction n} (hS : S.Valid f) :
    P.pairs.length ≤ N := by
  rw [h.length_pairs]
  calc S.pairs.card ≤ S.params.card :=
        Finset.card_le_card_of_injOn (fun pr : ZeroPair => pr.fst)
          (fun pr hpr => (hS.pair_mem pr hpr).1)
          fun a ha b hb hab => by
            by_contra hne
            exact (hS.pairs_disjoint a ha b hb hne).1 hab
    _ ≤ (range N).card := Finset.card_le_card fun i hi => h.names (by simp [nameSet, hi])
    _ = N := Finset.card_range N

/-- **Word width.** At `w ≥ N + 2` and `w ≥ 4`, every word of a valid represented state fits. -/
theorem fits (h : Rep N E P S) {f : BooleanFunction n} (hS : S.Valid f) {w : ℕ}
    (hw : N + 2 ≤ w) (h4 : 4 ≤ w) : P.Fits w := by
  have hNw : 2 ^ (N + 2) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw
  have hN1 : 2 ^ (N + 1) ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
  have hN0 : 2 ^ N ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
  have h16 : 16 ≤ 2 ^ w := (Nat.pow_le_pow_right two_pos h4 :)
  have hlt : N < 2 ^ N := Nat.lt_two_pow_self
  have hpow : 2 ^ (N + 2) = 4 * 2 ^ N := by rw [pow_add]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.params]; exact (maskOf_lt fun i => h.lt_of_mem_params).trans_le hN0
  · rw [h.aux]; exact (maskOf_lt fun i => h.lt_of_mem_aux).trans_le hN0
  · rw [h.gates]; exact (maskOf_lt fun i => h.lt_of_mem_gates).trans_le hN0
  · rw [h.out]
    have := litCode_lt (ℓ := S.out) fun i hi => h.out_lt hS hi
    omega
  · intro r hr
    obtain ⟨h1, h2, h3⟩ := h.gateRow_lt r hr
    exact ⟨by omega, by omega, by omega⟩
  · exact fun x hx => (h.eqnRow_lt x hx).trans_le hNw
  · intro c hc
    obtain ⟨l, -, hl, hP⟩ := h.pairs
    rw [hP] at hc
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2⟩ := h.pairs_lt hS (hl ▸ List.mem_toFinset.2 hpr)
    have := Bool.toNat_le pr.fstBias
    have := Bool.toNat_le pr.sndBias
    exact ⟨by simp only [pairCode]; omega, by simp only [pairCode]; omega⟩
  · exact fun r hr => (h.phi.lt r hr).trans_le hN1

end Rep

/-! ### The table sizes of the layout -/

/-- The name bound of the layout of `C`: the names along the run are below `n + C.size`
(`nameSet_iterate`). -/
@[expose] def nameBound (C : Circuit (fullSignature 2 Bool) n 1) : ℕ :=
  n + C.size

/-- The equation-name bound of the layout of `C`: the equation names at the end of the run are
below `5 n + 7 C.size` (`eqns_refuterLoop`). -/
@[expose] def eqnBound (C : Circuit (fullSignature 2 Bool) n 1) : ℕ :=
  5 * n + 7 * C.size

/-- The equation table has at most `7 · nameBound C` words. -/
theorem eqnBound_le (C : Circuit (fullSignature 2 Bool) n 1) : eqnBound C ≤ 7 * nameBound C := by
  unfold eqnBound nameBound
  omega

/-! ### First client: the `(D1)` search -/

/-- A gate row is degenerate: a constant argument (code below `2`) or two equal arguments. -/
@[expose] def isDegenerateRow (r : GateRow) : Bool :=
  decide (r.left < 2) || decide (r.right < 2) || r.left == r.right

/-- On the row of a gate, `isDegenerateRow` is `isDegenerate`. -/
theorem isDegenerateRow_rowOf (g : Gate) : isDegenerateRow (rowOf g) = isDegenerate g := by
  rcases g with ⟨op, l | l, r | r⟩ <;>
    simp [isDegenerateRow, rowOf, argCode, isDegenerate, Bool.toNat_le, Bool.beq_eq_decide_eq]

/-- `(D1)` on a packed state: the ascending scan of the gate mask for a degenerate row. -/
@[expose] def pFindD1 (P : PackedState) : Option ℕ :=
  (List.range P.gateRows.length).find? fun J =>
    P.gates.testBit J && isDegenerateRow (P.gateRows.getD J ⟨0, 0, 0⟩)

/-- The packed `(D1)` search returns the gate of `findD1`. -/
theorem Rep.pFindD1_eq {N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) :
    pFindD1 P = findD1 S := by
  rw [findD1, find?_sort_eq_find?_range fun i => h.lt_of_mem_gates, pFindD1,
    h.gateRows_length, h.gates]
  refine List.find?_congr fun J _ => ?_
  rw [testBit_maskOf]
  by_cases hJ : J ∈ S.gates
  · rw [h.gateRow J hJ, isDegenerateRow_rowOf]
  · simp [hJ]

/-! ### Second client: the initial state -/

/-- The packed initial state of `C`, with `nameBound C` gate rows and `eqnBound C` equation
words. -/
@[expose] def initialPacked (C : Circuit (fullSignature 2 Bool) n 1) : PackedState where
  params := maskOf (range n)
  aux := 0
  gates := maskOf (initialState C).gates
  gateRows := (List.range (nameBound C)).map fun J =>
    if J ∈ (initialState C).gates then rowOf ((initialState C).gate J) else ⟨0, 0, 0⟩
  eqnRows := List.replicate (eqnBound C) 0
  out := litCode (initialState C).out
  pairs := []
  phiRows := (List.range n).map (2 ^ ·)

/-- `initialPacked C` represents `initialState C`. -/
theorem rep_initialPacked (C : Circuit (fullSignature 2 Bool) n 1) :
    Rep (nameBound C) (eqnBound C) (initialPacked C) (initialState C) := by
  have hnames : nameSet (initialState C) ⊆ range (nameBound C) := nameSet_initialState C
  have hwf := wellFormed_ofCircuitBinary C
  have hlive : ∀ i ∈ (ofCircuitBinary C).live, i < nameBound C := fun i hi =>
    Finset.mem_range.1 (hnames hi)
  have heqns : (initialState C).eqns = ∅ := ofCircuitBinary_eqns C
  have hgates : ∀ J ∈ (initialState C).gates, J < nameBound C := fun J hJ =>
    Finset.mem_range.1 (hnames (by simp [nameSet, hJ]))
  refine
    { names := hnames
      eqns := by rw [heqns]; exact Finset.empty_subset _
      params := by
        change maskOf (range n) = maskOf (ofCircuitBinary C).params
        rw [ofCircuitBinary_params]
      aux := by
        change 0 = maskOf (ofCircuitBinary C).aux
        rw [ofCircuitBinary_aux, maskOf, Finset.sum_empty]
      gates := rfl
      gateRows_length := by simp [initialPacked]
      gateRow := fun J hJ => by
        have hJN := hgates J hJ
        rw [List.getD_eq_getElem _ _ (by simpa [initialPacked] using hJN)]
        simp [initialPacked, hJ]
      gateRow_lt := fun r hr => by
        simp only [initialPacked, List.mem_map, List.mem_range] at hr
        obtain ⟨J, -, rfl⟩ := hr
        split_ifs with hJ
        · exact rowLt_rowOf fun i hi => hlive i (hwf.reads_live J hJ i hi)
        · simp [RowLt]
      eqnRows_length := by simp [initialPacked]
      eqnRow := fun e he => by rw [heqns] at he; exact absurd he (Finset.notMem_empty e)
      eqnRow_alive := fun e he => by
        simp [initialPacked, heqns, he]
      eqnRow_lt := fun x hx => by
        rw [(List.eq_of_mem_replicate hx : x = 0)]
        exact Nat.two_pow_pos _
      out := rfl
      pairs := ⟨[], List.nodup_nil, rfl, rfl⟩
      phi :=
        { length := by simp [initialPacked]
          lt := fun r hr => by
            simp only [initialPacked, List.mem_map, List.mem_range] at hr
            obtain ⟨i, hi, rfl⟩ := hr
            exact Nat.pow_lt_pow_right (by omega) (by unfold nameBound; omega)
          eval := fun val i => by
            have hi : (i : ℕ) < nameBound C := by
              have := i.isLt; unfold nameBound; omega
            have hrow : ((List.range n).map (2 ^ ·)).getD i 0 = 2 ^ (i : ℕ) := by
              rw [List.getD_eq_getElem _ _ (by simp)]
              simp
            change val i = rowEval (nameBound C) (((List.range n).map (2 ^ ·)).getD i 0) val
            rw [hrow, rowEval_two_pow hi] } }

end Cslib.Algorithms.WordRAM.Refuter4n
