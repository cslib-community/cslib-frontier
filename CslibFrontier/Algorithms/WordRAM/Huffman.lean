/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Huffman.TwoQueue
public import CslibFrontier.Computability.WordRAM.ListOutput
public import Mathlib.Data.Nat.Log

import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.Sort

/-!
# Huffman Tree and Codeword-Length Construction on the Word RAM

This module implements van Leeuwen's two-queue Huffman construction ([VanLeeuwen1976]) and
unsorted Huffman coding ([Huffman1952]; [CLRS2009], Section 16.3) as deterministic structured and
compiled programs over `Cslib.WordRAM.Basis.standard`, charging every array load, store, address
calculation, weight addition, comparison, loop test, and final `halt`:

1. **Linear-time `O(n)` construction from pre-sorted weights (`fromSortedCode`,
   `fromSortedProgram`)**: given `n = ws.length` nondecreasing symbol weights `ws : List ℕ` in
   standard Word-RAM input layout (`State.init ws`), runs `n - 1` iterations of van Leeuwen's
   two-queue merge pass directly over the input leaf slice and an internal-node FIFO array, records
   explicit left/right child arrays in memory, propagates root-to-leaf depths in a single reverse
   pass of `n - 1` iterations, and halts within `58 * n + 26` instructions outputting the exact
   per-symbol Huffman codeword-length list via `ExecutesList`.
2. **`O(n log n)` construction from arbitrary unsorted weights (`huffmanCode`,
   `huffmanProgram`)**: sorts an index permutation `[0, …, n - 1]` by nondecreasing input weight
   using deterministic bottom-up iterative merge sort, gathers the sorted weight array, invokes the
   shared two-queue subroutine, and scatters the resulting leaf depths back to the original symbol
   indices within `50 * n * Nat.clog 2 n + 84 * n + 50` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Huffman.symWeight`: symbol weight lookup `i ↦ ws[i]` on `Fin ws.length`.
* `Cslib.Algorithms.WordRAM.Huffman.fromSortedCode`,
  `Cslib.Algorithms.WordRAM.Huffman.fromSortedProgram`: `O(n)` Word-RAM Huffman construction from
  pre-sorted weights.
* `Cslib.Algorithms.WordRAM.Huffman.huffmanCode`,
  `Cslib.Algorithms.WordRAM.Huffman.huffmanProgram`: `O(n log n)` Word-RAM Huffman construction
  from arbitrary unsorted weights.

## Main results

* `Cslib.Algorithms.WordRAM.Huffman.fromSortedProgram_spec`: `58 * n + 26` Word-RAM instruction
  bound, `ExecutesList` codeword-length output, `IsHuffmanBuild` certificate, and uniquely
  decodable optimality on pre-sorted weights.
* `Cslib.Algorithms.WordRAM.Huffman.huffmanProgram_spec`: `50 * n * Nat.clog 2 n + 84 * n + 50`
  Word-RAM instruction bound, `ExecutesList` codeword-length output, `IsHuffmanBuild` certificate,
  and uniquely decodable optimality on arbitrary weights.

## References

* [VanLeeuwen1976] Jan van Leeuwen, *On the Construction of Huffman Trees*, ICALP 1976, pp. 382–410.
* [Huffman1952] David A. Huffman, *A Method for the Construction of Minimum-Redundancy Codes*, 1952.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Section 16.3, 2009.
-/

public section

namespace Cslib.Algorithms.WordRAM.Huffman

open Cslib.WordRAM
open Cslib.Algorithms.Lean.Huffman

/-- Weight of symbol `i : Fin ws.length` in weight list `ws`. -/
@[expose] def symWeight (ws : List ℕ) (i : Fin ws.length) : ℕ := ws[i]

/-! ## Private `CodeTree`, `List`, and Memory Helpers -/

private theorem weight_map_eq {α₁ α₂ β : Type*} [Add β] {w₁ : α₁ → β} {w₂ : α₂ → β}
    {f : α₁ → α₂} (T : CodeTree α₁) (hw : ∀ a, w₂ (f a) = w₁ a) :
    (T.map f).weight w₂ = T.weight w₁ := by
  induction T with
  | leaf a => exact hw a
  | branch l r ihl ihr => simp [CodeTree.map, ihl, ihr]

private theorem encodeSym_map_of_injective {α₁ α₂ : Type*} [DecidableEq α₁] [DecidableEq α₂]
    {f : α₁ → α₂} (hf : Function.Injective f) (T : CodeTree α₁) (a : α₁) :
    (T.map f).encodeSym (f a) = T.encodeSym a := by
  induction T with
  | leaf b =>
    simp only [CodeTree.map, CodeTree.encodeSym, hf.eq_iff]
  | branch l r ihl ihr =>
    simp only [CodeTree.map, CodeTree.encodeSym, ihl, ihr]

private theorem isHuffmanBuild_map {α₁ α₂ β : Type*} [Add β] [LE β]
    {w₁ : α₁ → β} {w₂ : α₂ → β} {f : α₁ → α₂} (hw : ∀ a, w₂ (f a) = w₁ a)
    {F : List (CodeTree α₁)} {T : CodeTree α₁} (h : IsHuffmanBuild w₁ F T) :
    IsHuffmanBuild w₂ (F.map (CodeTree.map f)) (T.map f) := by
  induction h with
  | single t => exact .single (t.map f)
  | @step F F_rest t₁ t₂ T hmin _ ih =>
    refine .step ⟨?_, ?_⟩ ih
    · simpa [List.map_cons] using hmin.perm.map (CodeTree.map f)
    · intro t' ht'
      rcases List.mem_map.mp ht' with ⟨t, ht, rfl⟩
      rw [weight_map_eq t₁ hw, weight_map_eq t₂ hw, weight_map_eq t hw]
      exact hmin.weight_le t ht

private def slice {α : Type*} (L : List α) (a k : ℕ) : List α :=
  (L.drop a).take k

private theorem pairwise_of_length_le_one {α : Type*} {R : α → α → Prop} {xs : List α}
    (h : xs.length ≤ 1) : xs.Pairwise R := by
  rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact .nil
  · exact List.pairwise_singleton R x
  · simp at h

private theorem slice_zero {α : Type*} (L : List α) (a : ℕ) : slice L a 0 = [] := by
  simp [slice]

private theorem slice_eq_cons {α : Type*} (L : List α) {a b : ℕ} (hab : a < b)
    (hb : b ≤ L.length) :
    slice L a (b - a) = L[a]'(by omega) :: slice L (a + 1) (b - (a + 1)) := by
  have ha : a < L.length := by omega
  have hsub : b - a = (b - (a + 1)) + 1 := by omega
  rw [slice, List.drop_eq_getElem_cons ha, hsub, List.take_succ_cons]
  rfl

private theorem take_append_slice {α : Type*} (L : List α) {a b : ℕ} (hab : a ≤ b) :
    L.take a ++ slice L a (b - a) = L.take b := by
  rw [slice, ← List.take_add, Nat.add_sub_of_le hab]

private theorem slice_append_left {α : Type*} {xs ys : List α} {a k : ℕ}
    (h : a + k ≤ xs.length) : slice (xs ++ ys) a k = slice xs a k := by
  rw [slice, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]
  rfl

private theorem take_min_length {α : Type*} (xs : List α) (k : ℕ) :
    xs.take (min xs.length k) = xs.take k := by
  by_cases h : xs.length ≤ k
  · rw [Nat.min_eq_left h, List.take_length, List.take_of_length_le h]
  · rw [Nat.min_eq_right (by omega)]

private theorem pool_step_arith {n s i₀ h₀ i₁ h₁ i₂ h₂ : ℕ}
    (_hlt : s < n - 1) (h0 : (n - i₀) + (s - h₀) = n - s)
    (h1 : (n - i₁) + (s - h₁) + 1 = (n - i₀) + (s - h₀))
    (h2 : (n - i₂) + (s - h₂) + 1 = (n - i₁) + (s - h₁))
    (hh₂ : h₂ ≤ s) :
    (n - i₂) + (s + 1 - h₂) = n - (s + 1) := by
  omega

private theorem prefix_snoc_mem {bb lo_v idx_v : ℕ} {u_mem v_mem : ℕ → ℕ}
    {pref : List ℕ} {elem : ℕ}
    (hlen : pref.length = idx_v - lo_v) (hlo : lo_v ≤ idx_v)
    (hmod : Modifies (Block.mk (bb + lo_v) (idx_v - lo_v)).footprint u_mem v_mem)
    (hmem : ∀ d : ℕ, (hd : d < pref.length) → v_mem (bb + lo_v + d) = pref[d]) :
    Modifies (Block.mk (bb + lo_v) (idx_v + 1 - lo_v)).footprint u_mem
        (Function.update v_mem (bb + idx_v) elem) ∧
      ∀ d : ℕ, (hd : d < (pref ++ [elem]).length) →
        Function.update v_mem (bb + idx_v) elem (bb + lo_v + d) = (pref ++ [elem])[d] := by
  refine ⟨fun a ha => ?_, fun d hd => ?_⟩
  · rw [Block.mem_footprint, Block.Owns] at ha; dsimp only at ha
    rw [Function.update_of_ne (by omega)]
    exact hmod a (by rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  · by_cases hdeq : d = pref.length
    · subst hdeq
      rw [show bb + lo_v + pref.length = bb + idx_v by omega, Function.update_self]
      simp
    · have hd_lt : d < pref.length := by simp at hd; omega
      rw [Function.update_of_ne (by omega), List.getElem_append_left hd_lt]
      exact hmem d hd_lt

private theorem modifies_mono {base₁ n₁ base₂ n₂ : ℕ} {m₀ m₁ : ℕ → ℕ}
    (h : Modifies (Block.mk base₁ n₁).footprint m₀ m₁)
    (hlo : base₂ ≤ base₁) (hhi : base₁ + n₁ ≤ base₂ + n₂) :
    Modifies (Block.mk base₂ n₂).footprint m₀ m₁ := by
  rw [Modifies.block_iff] at h ⊢
  exact fun a ha => h a (by dsimp only at ha ⊢; omega)

private theorem modifies_write {base n a v : ℕ} {m₀ m₁ : ℕ → ℕ}
    (h : Modifies (Block.mk base n).footprint m₀ m₁) (ha : base ≤ a ∧ a < base + n) :
    Modifies (Block.mk base n).footprint m₀ (Function.update m₁ a v) := by
  rw [Modifies.block_iff] at h ⊢
  intro c hc
  dsimp only at hc
  rw [Function.update_of_ne (by omega)]
  exact h c (by dsimp only; omega)

private theorem holdsList_read_key {kb pb : ℕ} {ws L : List ℕ} {mem : ℕ → ℕ}
    (hws : Block.HoldsList kb ws mem) (hL : Block.HoldsList pb L mem)
    (hbound : ∀ v ∈ L, v < ws.length) {p : ℕ} (hp : p < L.length) :
    mem (pb + p) = L[p] ∧ L[p] < ws.length ∧ mem (kb + L[p]) = ws.getD L[p] 0 := by
  have hu : L[p] < ws.length := hbound _ (List.getElem_mem hp)
  refine ⟨hL.get p hp, hu, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
  exact hws.get _ hu

private theorem map_range_sub_eq_cons {α : Type*} (f : ℕ → α) {i n : ℕ} (hi : i < n) :
    (List.range (n - i)).map (fun d => f (i + d)) =
      f i :: (List.range (n - (i + 1))).map (fun d => f (i + 1 + d)) := by
  have hsub : n - i = (n - (i + 1)) + 1 := by omega
  rw [hsub, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Function.comp_def, List.cons.injEq, true_and]
  refine List.map_congr_left fun d _ => ?_
  rw [show i + (d + 1) = i + 1 + d by omega]

/-! ## Private Register File (`Fin 30`) -/

private abbrev zero : Fin 30 := 0
private abbrev one : Fin 30 := 1
private abbrev len : Fin 30 := 2
private abbrev wtBase : Fin 30 := 3
private abbrev workBase : Fin 30 := 4
private abbrev nSub1 : Fin 30 := 5
private abbrev i1 : Fin 30 := 6
private abbrev h2 : Fin 30 := 7
private abbrev step : Fin 30 := 8
private abbrev wpl : Fin 30 := 9
private abbrev outPtr : Fin 30 := 10
private abbrev uA : Fin 30 := 11
private abbrev wA : Fin 30 := 12
private abbrev uB : Fin 30 := 13
private abbrev wB : Fin 30 := 14
private abbrev keyBase : Fin 30 := 15
private abbrev permBase : Fin 30 := 16
private abbrev bufBase : Fin 30 := 17
private abbrev wRun : Fin 30 := 18
private abbrev lo : Fin 30 := 19
private abbrev mid : Fin 30 := 20
private abbrev hi : Fin 30 := 21
private abbrev pA : Fin 30 := 22
private abbrev pB : Fin 30 := 23
private abbrev outIdx : Fin 30 := 24
private abbrev finalOut : Fin 30 := 25
private abbrev addr : Fin 30 := 26
private abbrev tmp1 : Fin 30 := 27
private abbrev tmp2 : Fin 30 := 28
private abbrev tmp3 : Fin 30 := 29

/-! ## Two-Queue Huffman Core (`O(n)` on pre-sorted weights) -/

private def popOne : Code .standard 30 := ram[
  if i1 < len then [
    if h2 < step then [
      addr ← wtBase + i1; tmp1 ← *addr;
      addr ← workBase + h2; tmp2 ← *addr;
      if tmp2 < tmp1 then [
        uB ← len + h2; wB ← tmp2; h2 ← h2 + one
      ] else [
        uB ← i1; wB ← tmp1; i1 ← i1 + one
      ]
    ] else [
      addr ← wtBase + i1; tmp1 ← *addr;
      uB ← i1; wB ← tmp1; i1 ← i1 + one
    ]
  ] else [
    addr ← workBase + h2; tmp2 ← *addr;
    uB ← len + h2; wB ← tmp2; h2 ← h2 + one
  ] ]

private def mergeTail : Code .standard 30 := ram[
  tmp1 ← wA + wB;
  addr ← workBase + step; *addr ← tmp1;
  tmp2 ← workBase + len; addr ← tmp2 + step; *addr ← uA;
  tmp2 ← tmp2 + len; addr ← tmp2 + step; *addr ← uB;
  wpl ← wpl + tmp1;
  step ← step + one ]

private def mergePopTwo : Code .standard 30 :=
  .seq popOne (.seq (.op (.copy uA uB)) (.seq (.op (.copy wA wB)) popOne))

private def mergeBody : Code .standard 30 :=
  .seq mergePopTwo mergeTail

private def depthBody : Code .standard 30 := ram[
  tmp1 ← nSub1 - one;
  uA ← tmp1 - step;
  uB ← len + uA;
  tmp2 ← outPtr + one;
  addr ← tmp2 + uB; tmp3 ← *addr;
  tmp3 ← tmp3 + one;
  tmp1 ← workBase + len;
  addr ← tmp1 + uA; wA ← *addr;
  tmp1 ← tmp1 + len;
  addr ← tmp1 + uA; wB ← *addr;
  addr ← tmp2 + wA; *addr ← tmp3;
  addr ← tmp2 + wB; *addr ← tmp3;
  step ← step + one ]

private def twoQueueCore : Code .standard 30 := ram[
  if zero < len then [
    nSub1 ← len - one;
    i1 ← #0;
    h2 ← #0;
    step ← #0;
    wpl ← #0;
    while step < nSub1 do [ ⟪mergeBody⟫ ];
    tmp1 ← len + len;
    tmp1 ← tmp1 + len;
    outPtr ← workBase + tmp1;
    *outPtr ← len;
    tmp2 ← outPtr + one;
    tmp3 ← nSub1 + nSub1;
    addr ← tmp2 + tmp3;
    *addr ← zero;
    step ← #0;
    while step < nSub1 do [ ⟪depthBody⟫ ]
  ] else [
    wpl ← #0;
    outPtr ← workBase;
    *outPtr ← zero
  ] ]

private def Avail (n i₁ h₂ s u : ℕ) : Prop :=
  (i₁ ≤ u ∧ u < n) ∨ (n + h₂ ≤ u ∧ u < n + s)

private def mkQ1 {n : ℕ} (hn : 0 < n) (sws : List ℕ) (trees : List (CodeTree (Fin n))) (i₁ : ℕ) :
    List (WeightedTree (Fin n) ℕ) :=
  (List.range (n - i₁)).map fun d =>
    ⟨trees.getD (i₁ + d) (.leaf ⟨0, hn⟩), sws.getD (i₁ + d) 0⟩

private def mkQ2 {n : ℕ} (hn : 0 < n) (trees : List (CodeTree (Fin n))) (mem : ℕ → ℕ)
    (wb h₂ s : ℕ) : List (WeightedTree (Fin n) ℕ) :=
  (List.range (s - h₂)).map fun d =>
    ⟨trees.getD (n + (h₂ + d)) (.leaf ⟨0, hn⟩), mem (wb + (h₂ + d))⟩

private theorem mkQ1_eq_nil {n : ℕ} (hn : 0 < n) (sws : List ℕ)
    (trees : List (CodeTree (Fin n))) {i₁ : ℕ} (hi : n ≤ i₁) :
    mkQ1 hn sws trees i₁ = [] := by
  have h0 : n - i₁ = 0 := by omega
  simp [mkQ1, h0]

private theorem mkQ1_eq_cons {n : ℕ} (hn : 0 < n) (sws : List ℕ)
    (trees : List (CodeTree (Fin n))) {i₁ : ℕ} (hi : i₁ < n) :
    mkQ1 hn sws trees i₁ =
      ⟨trees.getD i₁ (.leaf ⟨0, hn⟩), sws.getD i₁ 0⟩ :: mkQ1 hn sws trees (i₁ + 1) :=
  map_range_sub_eq_cons (α := WeightedTree (Fin n) ℕ)
    (fun k => ⟨trees.getD k (.leaf ⟨0, hn⟩), sws.getD k 0⟩) hi

private theorem mkQ2_eq_nil {n : ℕ} (hn : 0 < n) (trees : List (CodeTree (Fin n)))
    (mem : ℕ → ℕ) (wb : ℕ) {h₂ s : ℕ} (hh : s ≤ h₂) :
    mkQ2 hn trees mem wb h₂ s = [] := by
  have h0 : s - h₂ = 0 := by omega
  simp [mkQ2, h0]

private theorem mkQ2_eq_cons {n : ℕ} (hn : 0 < n) (trees : List (CodeTree (Fin n)))
    (mem : ℕ → ℕ) (wb : ℕ) {h₂ s : ℕ} (hh : h₂ < s) :
    mkQ2 hn trees mem wb h₂ s =
      ⟨trees.getD (n + h₂) (.leaf ⟨0, hn⟩), mem (wb + h₂)⟩ ::
        mkQ2 hn trees mem wb (h₂ + 1) s :=
  map_range_sub_eq_cons (α := WeightedTree (Fin n) ℕ)
    (fun k => ⟨trees.getD (n + k) (.leaf ⟨0, hn⟩), mem (wb + k)⟩) hh

private theorem getD_append_left {α : Type*} (xs ys : List α) {i : ℕ} (hi : i < xs.length)
    (dflt : α) : (xs ++ ys).getD i dflt = xs.getD i dflt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_singleton_self {α : Type*} (xs : List α) (v dflt : α) :
    (xs ++ [v]).getD xs.length dflt = v := by
  simp [List.getD_eq_getElem?_getD]

private theorem mkQ1_append_tree {n : ℕ} (hn : 0 < n) (sws : List ℕ)
    (trees : List (CodeTree (Fin n))) (T : CodeTree (Fin n)) (htrees : n ≤ trees.length) (i₁ : ℕ) :
    mkQ1 hn sws (trees ++ [T]) i₁ = mkQ1 hn sws trees i₁ := by
  unfold mkQ1
  refine List.map_congr_left fun d hd => ?_
  rw [List.mem_range] at hd
  rw [getD_append_left trees [T] (by omega)]

private theorem mkQ2_snoc {n : ℕ} (hn : 0 < n) (trees : List (CodeTree (Fin n)))
    (T : CodeTree (Fin n)) (mem mem' : ℕ → ℕ) (wb h₂ s wt : ℕ)
    (hlen_t : trees.length = n + s) (h₂_le : h₂ ≤ s)
    (hmem_old : ∀ k < s, mem' (wb + k) = mem (wb + k))
    (hmem_new : mem' (wb + s) = wt) :
    mkQ2 hn (trees ++ [T]) mem' wb h₂ (s + 1) =
      mkQ2 hn trees mem wb h₂ s ++ [⟨T, wt⟩] := by
  have hsub : s + 1 - h₂ = (s - h₂) + 1 := by omega
  rw [mkQ2, hsub, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · unfold mkQ2
    refine List.map_congr_left fun d hd => ?_
    rw [List.mem_range] at hd
    rw [getD_append_left trees [T] (by omega), hmem_old (h₂ + d) (by omega)]
  · have h_eq : h₂ + (s - h₂) = s := by omega
    have h_len : n + s = trees.length := hlen_t.symm
    rw [h_eq, h_len, getD_append_singleton_self, hmem_new]

private theorem popOne_spec {w n wb wtb s : ℕ} (hn_pos : 0 < n)
    {sws : List ℕ} (hlen : sws.length = n)
    {trees : List (CodeTree (Fin n))}
    (x : Data 30)
    (ho : x.regs one = 1) (hn : x.regs len = n) (hwtb : x.regs wtBase = wtb)
    (hwb : x.regs workBase = wb) (hs : x.regs step = s)
    (hi1_le : x.regs i1 ≤ n) (hh2_le : x.regs h2 ≤ s) (hs_le : s ≤ n)
    (hne : 1 ≤ (n - x.regs i1) + (s - x.regs h2))
    (hsws : Block.HoldsList wtb sws x.mem)
    (hfit_wtb : Fits w (wtb + n)) (hfit_wb : Fits w (wb + 2 * n))
    {q₂ : FifoQueue (WeightedTree (Fin n) ℕ)} (hwf : q₂.WF)
    (hq₂ : q₂.toList = mkQ2 hn_pos trees x.mem wb (x.regs h2) s) :
    ∃ y : Data 30, ExecWithin w popOne x y 11 ∧
      ∃ (u : ℕ) (wt : ℕ) (q₂' : FifoQueue (WeightedTree (Fin n) ℕ)),
        y.mem = x.mem ∧
        (∀ r : Fin 30, r ≠ i1 → r ≠ h2 → r ≠ uB → r ≠ wB → r ≠ addr → r ≠ tmp1 → r ≠ tmp2 →
          y.regs r = x.regs r) ∧
        y.regs uB = u ∧ y.regs wB = wt ∧
        y.regs i1 ≤ n ∧ y.regs h2 ≤ s ∧
        (n - y.regs i1) + (s - y.regs h2) + 1 = (n - x.regs i1) + (s - x.regs h2) ∧
        u < n + s ∧ Avail n (x.regs i1) (x.regs h2) s u ∧
        (∀ v, Avail n (y.regs i1) (y.regs h2) s v ↔ Avail n (x.regs i1) (x.regs h2) s v ∧ v ≠ u) ∧
        q₂'.WF ∧
        q₂'.toList = mkQ2 hn_pos trees x.mem wb (y.regs h2) s ∧
        popMin (mkQ1 hn_pos sws trees (x.regs i1)) q₂ =
          some (⟨trees.getD u (.leaf ⟨0, hn_pos⟩), wt⟩,
            mkQ1 hn_pos sws trees (y.regs i1), q₂') := by
  have hpm := popMin_spec_toList (mkQ1 hn_pos sws trees (x.regs i1)) hwf
  refine WP.exists_execWithin ?_
  unfold popOne
  by_cases hi : x.regs i1 < n
  · have hq1_eq := mkQ1_eq_cons hn_pos sws trees hi
    have hsws_getD : sws.getD (x.regs i1) 0 = sws[x.regs i1]'(by omega) := by
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : x.regs i1 < sws.length)]
    have hread1 : x.mem (wtb + x.regs i1) = sws.getD (x.regs i1) 0 := by
      rw [hsws_getD]; exact hsws.get _ (by omega)
    by_cases hh : x.regs h2 < s
    · have hq2_eq := mkQ2_eq_cons hn_pos trees x.mem wb hh
      rw [hq1_eq, hq₂, hq2_eq] at hpm
      dsimp only at hpm
      by_cases hlt : x.mem (wb + x.regs h2) < sws.getD (x.regs i1) 0
      · have hnle : ¬ (sws.getD (x.regs i1) 0 ≤ x.mem (wb + x.regs h2)) := by omega
        simp only [hnle, ↓reduceIte] at hpm
        rcases hpm with ⟨q₂', hpop, hwf', hto'⟩
        wram_exec [hn, hs, hwtb, hwb, ho, hi, hh, hread1, hlt]
        refine ⟨n + x.regs h2, x.mem (wb + x.regs h2), q₂', rfl, ?_, ?_, ?_, ?_, ?_, ?_,
          by omega, Or.inr ⟨by omega, by omega⟩, ?_, hwf', ?_, ?_⟩
        · intro r _ h2 h3 h4 h5 h6 h7
          simp only [Data.set_regs, Function.update_of_ne h2, Function.update_of_ne h4,
            Function.update_of_ne h3, Function.update_of_ne h7, Function.update_of_ne h5,
            Function.update_of_ne h6]
        · wram_simp
        · wram_simp
        · wram_simp; omega
        · wram_simp; omega
        · wram_simp; omega
        · intro v; wram_simp [Avail]; omega
        · wram_simp [hto']
        · wram_simp; rwa [← hq1_eq] at hpop
      · have hle : sws.getD (x.regs i1) 0 ≤ x.mem (wb + x.regs h2) := by omega
        simp only [hle, ↓reduceIte] at hpm
        wram_exec [hn, hs, hwtb, hwb, ho, hi, hh, hread1, hlt]
        refine ⟨x.regs i1, sws.getD (x.regs i1) 0, q₂, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
          by omega, Or.inl ⟨le_rfl, hi⟩, ?_, hwf, ?_, ?_⟩
        · intro r h1 _ h3 h4 h5 h6 h7
          simp only [Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h4,
            Function.update_of_ne h3, Function.update_of_ne h7, Function.update_of_ne h5,
            Function.update_of_ne h6]
        · wram_simp
        · wram_simp
        · wram_simp; omega
        · wram_simp; omega
        · wram_simp; omega
        · intro v; wram_simp [Avail]; omega
        · wram_simp [hq₂]
        · wram_simp; rw [hq1_eq]; exact hpm
    · have hh_ge : s ≤ x.regs h2 := by omega
      have hq2_eq := mkQ2_eq_nil hn_pos trees x.mem wb hh_ge
      rw [hq1_eq, hq₂, hq2_eq] at hpm
      dsimp only at hpm
      wram_exec [hn, hs, hwtb, hwb, ho, hi, hh, hread1]
      refine ⟨x.regs i1, sws.getD (x.regs i1) 0, q₂, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
        by omega, Or.inl ⟨le_rfl, hi⟩, ?_, hwf, ?_, ?_⟩
      · intro r h1 _ h3 h4 h5 h6 _
        simp only [Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h4,
          Function.update_of_ne h3, Function.update_of_ne h6, Function.update_of_ne h5]
      · wram_simp
      · wram_simp
      · wram_simp; omega
      · wram_simp; omega
      · wram_simp; omega
      · intro v; wram_simp [Avail]; omega
      · wram_simp [hq₂]
      · wram_simp; rw [hq1_eq]; exact hpm
  · have hi_ge : n ≤ x.regs i1 := by omega
    have hh : x.regs h2 < s := by omega
    have hq1_eq := mkQ1_eq_nil hn_pos sws trees hi_ge
    have hq2_eq := mkQ2_eq_cons hn_pos trees x.mem wb hh
    rw [hq1_eq, hq₂, hq2_eq] at hpm
    dsimp only at hpm
    rcases hpm with ⟨q₂', hpop, hwf', hto'⟩
    wram_exec [hn, hs, hwtb, hwb, ho, hi, hh]
    refine ⟨n + x.regs h2, x.mem (wb + x.regs h2), q₂', rfl, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, Or.inr ⟨by omega, by omega⟩, ?_, hwf', ?_, ?_⟩
    · intro r _ h2 h3 h4 h5 _ h7
      simp only [Data.set_regs, Function.update_of_ne h2, Function.update_of_ne h4,
        Function.update_of_ne h3, Function.update_of_ne h7, Function.update_of_ne h5]
    · wram_simp
    · wram_simp
    · wram_simp; omega
    · wram_simp; omega
    · wram_simp; omega
    · intro v; wram_simp [Avail]; omega
    · wram_simp [hto']
    · wram_simp; rwa [← hq1_eq] at hpop

private structure MergeInv (sws : List ℕ) (hn_pos : 0 < sws.length)
    (wtb wb pb_init fo_init : ℕ) (x_mem : ℕ → ℕ) (s : ℕ) (y : Data 30) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  len_eq : y.regs len = sws.length
  wtBase_eq : y.regs wtBase = wtb
  workBase_eq : y.regs workBase = wb
  nSub1_eq : y.regs nSub1 = sws.length - 1
  permBase_eq : y.regs permBase = pb_init
  finalOut_eq : y.regs finalOut = fo_init
  i1_le : y.regs i1 ≤ sws.length
  h2_le : y.regs h2 ≤ s
  pool_sz : (sws.length - y.regs i1) + (s - y.regs h2) = sws.length - s
  mod : Modifies (Block.mk wb (3 * sws.length)).footprint x_mem y.mem
  state :
    ∃ (trees : List (CodeTree (Fin sws.length))) (i1_hist h2_hist : ℕ → ℕ)
      (q₂ : FifoQueue (WeightedTree (Fin sws.length) ℕ)),
      trees.length = sws.length + s ∧
      (∀ (i : ℕ) (hi : i < sws.length),
        trees.getD i (.leaf ⟨0, hn_pos⟩) = .leaf ⟨i, hi⟩) ∧
      i1_hist 0 = 0 ∧ h2_hist 0 = 0 ∧ i1_hist s = y.regs i1 ∧ h2_hist s = y.regs h2 ∧
      (∀ k < s,
        let u_l := y.mem (wb + sws.length + k)
        let u_r := y.mem (wb + 2 * sws.length + k)
        u_l < sws.length + k ∧ u_r < sws.length + k ∧ u_l ≠ u_r ∧
          trees.getD (sws.length + k) (.leaf ⟨0, hn_pos⟩) =
            .branch (trees.getD u_l (.leaf ⟨0, hn_pos⟩)) (trees.getD u_r (.leaf ⟨0, hn_pos⟩)) ∧
          Avail sws.length (i1_hist k) (h2_hist k) k u_l ∧
          Avail sws.length (i1_hist k) (h2_hist k) k u_r ∧
          (∀ v, Avail sws.length (i1_hist (k + 1)) (h2_hist (k + 1)) (k + 1) v ↔
            (Avail sws.length (i1_hist k) (h2_hist k) k v ∧ v ≠ u_l ∧ v ≠ u_r) ∨
              v = sws.length + k)) ∧
      q₂.WF ∧
      q₂.toList = mkQ2 hn_pos trees y.mem wb (y.regs h2) s ∧
      (∀ e ∈ mkQ1 hn_pos sws trees (y.regs i1) ++ q₂.toList,
        e.wt = e.tree.weight (symWeight sws)) ∧
      (((mkQ1 hn_pos sws trees (y.regs i1) ++ q₂.toList).map WeightedTree.wt).sum = sws.sum) ∧
      y.regs wpl =
        ((mkQ1 hn_pos sws trees (y.regs i1) ++ q₂.toList).map fun e =>
          e.tree.weightedPathLength (symWeight sws)).sum ∧
      y.regs wpl ≤ s * sws.sum ∧
      twoQueueLoop (mkQ1 hn_pos sws trees (y.regs i1)) q₂ =
        huffmanFromSorted (symWeight sws) (List.finRange sws.length)

private structure DepthInv (sws : List ℕ) (hn_pos : 0 < sws.length)
    (wb pb_init fo_init : ℕ) (x_mem yM_mem : ℕ → ℕ)
    (trees : List (CodeTree (Fin sws.length))) (i1_hist h2_hist : ℕ → ℕ)
    (T_root : CodeTree (Fin sws.length)) (j : ℕ) (y : Data 30) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  len_eq : y.regs len = sws.length
  workBase_eq : y.regs workBase = wb
  nSub1_eq : y.regs nSub1 = sws.length - 1
  permBase_eq : y.regs permBase = pb_init
  finalOut_eq : y.regs finalOut = fo_init
  wpl_eq : y.regs wpl = T_root.weightedPathLength (symWeight sws)
  outPtr_eq : y.regs outPtr = wb + 3 * sws.length
  mem_out : y.mem (wb + 3 * sws.length) = sws.length
  mem_child : ∀ a, wb + sws.length ≤ a → a < wb + 3 * sws.length → y.mem a = yM_mem a
  mod : Modifies (Block.mk wb (5 * sws.length + 1)).footprint x_mem y.mem
  depths :
    ∀ u, Avail sws.length (i1_hist (sws.length - 1 - j))
        (h2_hist (sws.length - 1 - j)) (sws.length - 1 - j) u →
      u < 2 * sws.length - 1 ∧
      y.mem (wb + 3 * sws.length + 1 + u) ≤ j ∧
      (T_root.leaves.Nodup →
        (trees.getD u (.leaf ⟨0, hn_pos⟩)).leaves.Nodup ∧
        ∀ (a : Fin sws.length) (c : List Bool),
          (trees.getD u (.leaf ⟨0, hn_pos⟩)).encodeSym a = some c →
          ∃ cr, T_root.encodeSym a = some cr ∧
            cr.length = y.mem (wb + 3 * sws.length + 1 + u) + c.length)

private theorem popMin_perm {α β : Type} [LinearOrder β]
    {l₁ l₁' : List (WeightedTree α β)}
    {qf qf' : FifoQueue (WeightedTree α β)} {e : WeightedTree α β}
    (hqwf : qf.WF) (hp : popMin l₁ qf = some (e, l₁', qf')) :
    (l₁ ++ qf.toList).Perm (e :: (l₁' ++ qf'.toList)) := by
  have hsp := popMin_spec_toList l₁ hqwf
  rcases l₁ with _ | ⟨x0, xs0⟩ <;> rcases hto : qf.toList with _ | ⟨y0, ys0⟩
  · rw [hto] at hsp; rw [hsp] at hp; cases hp
  · rw [hto] at hsp; rcases hsp with ⟨q', hp', _, hto'⟩
    rw [hp'] at hp; obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hp
    simp [hto']
  · rw [hto] at hsp; rw [hsp] at hp; obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hp
    simp [hto]
  · rw [hto] at hsp; dsimp only at hsp
    by_cases hc : x0.wt ≤ y0.wt
    · simp only [hc, ↓reduceIte] at hsp
      rw [hsp] at hp; obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hp
      simp [hto]
    · simp only [hc, ↓reduceIte] at hsp
      rcases hsp with ⟨q', hp', _, hto'⟩
      rw [hp'] at hp; obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hp
      rw [hto']
      exact List.perm_middle

private theorem popTwo_exec {w wtb wb pb_init fo_init s : ℕ}
    (sws : List ℕ) (hn_pos : 0 < sws.length)
    (trees : List (CodeTree (Fin sws.length)))
    (y : Data 30)
    (hyz : y.regs zero = 0) (hyo : y.regs one = 1) (hyn : y.regs len = sws.length)
    (hywtb : y.regs wtBase = wtb) (hywb : y.regs workBase = wb)
    (hyns : y.regs nSub1 = sws.length - 1)
    (hypb : y.regs permBase = pb_init) (hyfo : y.regs finalOut = fo_init)
    (hys : y.regs step = s)
    (hyi1 : y.regs i1 ≤ sws.length) (hyh2 : y.regs h2 ≤ s)
    (hlt : s < sws.length - 1)
    (hpool_sz : (sws.length - y.regs i1) + (s - y.regs h2) = sws.length - s)
    (hy_sws : Block.HoldsList wtb sws y.mem)
    (hfit_wtb : Fits w (wtb + sws.length)) (hfit_wb2 : Fits w (wb + 2 * sws.length))
    {q₂ : FifoQueue (WeightedTree (Fin sws.length) ℕ)} (hwf : q₂.WF)
    (hq₂ : q₂.toList = mkQ2 hn_pos trees y.mem wb (y.regs h2) s) :
    ∃ (y₂ : Data 30) (u_a wt_a u_b wt_b i1_mid : ℕ)
      (q₂' q₂'' : FifoQueue (WeightedTree (Fin sws.length) ℕ)),
      ExecWithin w mergePopTwo y y₂ 24 ∧
      y₂.mem = y.mem ∧
      y₂.regs zero = 0 ∧ y₂.regs one = 1 ∧ y₂.regs len = sws.length ∧
      y₂.regs wtBase = wtb ∧ y₂.regs workBase = wb ∧ y₂.regs nSub1 = sws.length - 1 ∧
      y₂.regs permBase = pb_init ∧ y₂.regs finalOut = fo_init ∧
      y₂.regs step = s ∧ y₂.regs wpl = y.regs wpl ∧
      y₂.regs uA = u_a ∧ y₂.regs wA = wt_a ∧ y₂.regs uB = u_b ∧ y₂.regs wB = wt_b ∧
      y₂.regs i1 ≤ sws.length ∧ y₂.regs h2 ≤ s ∧
      (sws.length - y₂.regs i1) + (s + 1 - y₂.regs h2) = sws.length - (s + 1) ∧
      u_a < sws.length + s ∧ u_b < sws.length + s ∧
      Avail sws.length (y.regs i1) (y.regs h2) s u_a ∧
      Avail sws.length (y.regs i1) (y.regs h2) s u_b ∧ u_b ≠ u_a ∧
      (∀ v, Avail sws.length (y₂.regs i1) (y₂.regs h2) s v ↔
        Avail sws.length (y.regs i1) (y.regs h2) s v ∧ v ≠ u_a ∧ v ≠ u_b) ∧
      q₂'.WF ∧ q₂''.WF ∧
      q₂''.toList = mkQ2 hn_pos trees y.mem wb (y₂.regs h2) s ∧
      popMin (mkQ1 hn_pos sws trees (y.regs i1)) q₂ =
        some (⟨trees.getD u_a (.leaf ⟨0, hn_pos⟩), wt_a⟩,
          mkQ1 hn_pos sws trees i1_mid, q₂') ∧
      popMin (mkQ1 hn_pos sws trees i1_mid) q₂' =
        some (⟨trees.getD u_b (.leaf ⟨0, hn_pos⟩), wt_b⟩,
          mkQ1 hn_pos sws trees (y₂.regs i1), q₂'') := by
  obtain ⟨y₁, hex1, u_a, wt_a, q₂', hmem1, hfr1, huB1, hwB1, hi1_1, hh2_1, hsz1,
    hua_lt, hua_av, hav1, hwf1, hq2_1, hpop1⟩ :=
    popOne_spec hn_pos rfl y hyo hyn hywtb hywb hys hyi1 hyh2 (by omega) (by omega)
      hy_sws hfit_wtb hfit_wb2 hwf hq₂
  let y₁' : Data 30 := (y₁.set uA (y₁.regs uB)).set wA (y₁.regs wB)
  have hy1'_sws : Block.HoldsList wtb sws y₁'.mem := hmem1 ▸ hy_sws
  have hi1_1' : y₁'.regs i1 = y₁.regs i1 := by wram_simp [y₁']
  have hh2_1' : y₁'.regs h2 = y₁.regs h2 := by wram_simp [y₁']
  obtain ⟨y₂, hex2, u_b, wt_b, q₂'', hmem2, hfr2, huB2, hwB2, hi1_2, hh2_2, hsz2,
    hub_lt, hub_av1, hav2, hwf2, hq2_2, hpop2⟩ :=
    popOne_spec (s := s) (trees := trees) hn_pos rfl y₁'
      (by wram_simp [y₁']; rw [hfr1 one (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hyo)
      (by wram_simp [y₁']; rw [hfr1 len (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hyn)
      (by wram_simp [y₁']; rw [hfr1 wtBase (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hywtb)
      (by wram_simp [y₁']; rw [hfr1 workBase (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hywb)
      (by wram_simp [y₁']; rw [hfr1 step (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact hys)
      (by rw [hi1_1']; exact hi1_1)
      (by rw [hh2_1']; exact hh2_1)
      (by omega) (by rw [hi1_1', hh2_1']; omega)
      hy1'_sws hfit_wtb hfit_wb2 hwf1
      (by dsimp only [y₁', Data.set_mem]; rw [hh2_1', hmem1]; exact hq2_1)
  simp only [hi1_1', hh2_1'] at hsz2 hub_av1 hav2 hpop2
  have fr12 (r : Fin 30) (h1 : r ≠ i1) (h2 : r ≠ h2) (h3 : r ≠ uA) (h4 : r ≠ wA)
      (h5 : r ≠ uB) (h6 : r ≠ wB) (h7 : r ≠ addr) (h8 : r ≠ tmp1) (h9 : r ≠ tmp2) :
      y₂.regs r = y.regs r := by
    rw [hfr2 r h1 h2 h5 h6 h7 h8 h9]
    simp only [y₁', Data.set_regs, Function.update_of_ne h4, Function.update_of_ne h3]
    exact hfr1 r h1 h2 h5 h6 h7 h8 h9
  have huA2 : y₂.regs uA = u_a := by
    rw [hfr2 uA (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    wram_simp [y₁', huB1]
  have hwA2 : y₂.regs wA = wt_a := by
    rw [hfr2 wA (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    wram_simp [y₁', hwB1]
  have hub_av : Avail sws.length (y.regs i1) (y.regs h2) s u_b ∧ u_b ≠ u_a :=
    (hav1 u_b).mp hub_av1
  have hex_pop2 : ExecWithin w mergePopTwo y y₂ 24 := by
    unfold mergePopTwo
    exact (hex1.seq (ExecWithin.copy.seq (ExecWithin.copy.seq hex2))).mono (by omega)
  refine ⟨y₂, u_a, wt_a, u_b, wt_b, y₁.regs i1, q₂', q₂'', hex_pop2, hmem2.trans hmem1,
    (fr12 zero (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hyz,
    (fr12 one (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hyo,
    (fr12 len (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hyn,
    (fr12 wtBase (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hywtb,
    (fr12 workBase (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hywb,
    (fr12 nSub1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hyns,
    (fr12 permBase (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hypb,
    (fr12 finalOut (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hyfo,
    (fr12 step (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hys,
    fr12 wpl (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    huA2, hwA2, huB2, hwB2, hi1_2, hh2_2,
    pool_step_arith hlt hpool_sz hsz1 hsz2 hh2_2,
    hua_lt, hub_lt, hua_av, hub_av.1, hub_av.2,
    fun v => by
      have hv2 := hav2 v; have hv1 := hav1 v
      exact ⟨fun h => ⟨(hv1.mp (hv2.mp h).1).1, (hv1.mp (hv2.mp h).1).2, (hv2.mp h).2⟩,
        fun ⟨h, hna, hnb⟩ => hv2.mpr ⟨hv1.mpr ⟨h, hna⟩, hnb⟩⟩,
    hwf1, hwf2, by simpa only [y₁', Data.set_mem, hmem1] using hq2_2, hpop1, hpop2⟩

private theorem mergeTail_exec {w wtb wb pb_init fo_init s u_a wt_a u_b wt_b : ℕ}
    (sws : List ℕ) (y₂ : Data 30)
    (hy2_z : y₂.regs zero = 0) (hy2_o : y₂.regs one = 1) (hy2_n : y₂.regs len = sws.length)
    (hy2_wtb : y₂.regs wtBase = wtb) (hy2_wb : y₂.regs workBase = wb)
    (hy2_ns : y₂.regs nSub1 = sws.length - 1)
    (hy2_pb : y₂.regs permBase = pb_init) (hy2_fo : y₂.regs finalOut = fo_init)
    (hy2_step : y₂.regs step = s)
    (huA2 : y₂.regs uA = u_a) (hwA2 : y₂.regs wA = wt_a)
    (huB2 : y₂.regs uB = u_b) (hwB2 : y₂.regs wB = wt_b)
    (hs_lt : s < sws.length - 1)
    (hfit_mem : Fits w (wb + 5 * sws.length + 1))
    (hfit_sum : Fits w (wt_a + wt_b))
    (hfit_wpl_new : Fits w (y₂.regs wpl + (wt_a + wt_b))) :
    ∃ z : Data 30, ExecWithin w mergeTail y₂ z 12 ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs len = sws.length ∧
      z.regs wtBase = wtb ∧ z.regs workBase = wb ∧ z.regs nSub1 = sws.length - 1 ∧
      z.regs permBase = pb_init ∧ z.regs finalOut = fo_init ∧
      z.regs i1 = y₂.regs i1 ∧ z.regs h2 = y₂.regs h2 ∧
      z.regs step = s + 1 ∧ z.regs wpl = y₂.regs wpl + (wt_a + wt_b) ∧
      z.mem = Function.update (Function.update (Function.update y₂.mem
        (wb + s) (wt_a + wt_b)) (wb + sws.length + s) u_a)
        (wb + 2 * sws.length + s) u_b := by
  refine WP.exists_execWithin ?_
  unfold mergeTail
  wram_exec [hy2_o, hy2_n, hy2_wb, hy2_step, huA2, hwA2, huB2, hwB2,
    hfit_sum, hfit_wpl_new]
  refine ⟨by wram_simp [hy2_z], by wram_simp [hy2_o], by wram_simp [hy2_n],
    by wram_simp [hy2_wtb], by wram_simp [hy2_wb], by wram_simp [hy2_ns],
    by wram_simp [hy2_pb], by wram_simp [hy2_fo],
    by wram_simp, by wram_simp, by wram_simp, by wram_simp, ?_⟩
  wram_simp [Data.write_mem]
  rw [show wb + sws.length + sws.length + s = wb + 2 * sws.length + s by omega]

private theorem mergeBody_exec {w wtb wb pb_init fo_init : ℕ}
    (sws : List ℕ) (hn_pos : 0 < sws.length) (x_mem : ℕ → ℕ)
    (hsws : Block.HoldsList wtb sws x_mem)
    (hdisj : wtb + sws.length ≤ wb)
    (hfit_mem : Fits w (wb + 5 * sws.length + 1))
    (hfit_wpl : Fits w (sws.length * sws.sum))
    (y : Data 30)
    (hy : MergeInv sws hn_pos wtb wb pb_init fo_init x_mem (y.regs step) y)
    (hlt : y.regs step < sws.length - 1) :
    ∃ z, ExecWithin w mergeBody y z 36 ∧
      MergeInv sws hn_pos wtb wb pb_init fo_init x_mem (y.regs step + 1) z ∧
      z.regs step = y.regs step + 1 := by
  have hsum_fit : Fits w sws.sum := hfit_wpl.of_le (by
    simpa using Nat.mul_le_mul_right sws.sum hn_pos)
  obtain ⟨s, hs_def⟩ : ∃ s_v, y.regs step = s_v := ⟨_, rfl⟩
  rw [hs_def] at hy hlt ⊢
  obtain ⟨hyz, hyo, hyn, hywtb, hywb, hyns, hypb, hyfo, hyi1, hyh2, hpool_sz, hmod,
    trees, i1_hist, h2_hist, q₂, hlen_t, htrees_leaf, hi1_0, hh2_0, hi1_s, hh2_s,
    hhist, hwf, hq₂, hwt_eq, hsum_eq, hwpl_eq, hwpl_le, hloop_eq⟩ := hy
  have hy_sws : Block.HoldsList wtb sws y.mem :=
    hsws.frame fun a ha1 ha2 => hmod a (by
      rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  obtain ⟨y₂, u_a, wt_a, u_b, wt_b, i1_mid, q₂', q₂'', hex_pop2, hmem2_eq,
    hy2_z, hy2_o, hy2_n, hy2_wtb, hy2_wb, hy2_ns, hy2_pb, hy2_fo, hy2_step, hy2_wpl,
    huA2, hwA2, huB2, hwB2, hi1_2, hh2_2, hpool_next,
    hua_lt, hub_lt, hua_av, hub_av, hub_ne_a, hav_both,
    hwf1, hwf2, hq2_2, hpop1, hpop2⟩ :=
    popTwo_exec sws hn_pos trees y hyz hyo hyn hywtb hywb hyns hypb hyfo hs_def
      hyi1 hyh2 hlt hpool_sz hy_sws (hfit_mem.of_le (by omega)) (hfit_mem.of_le (by omega))
      hwf hq₂
  have hperm1 := popMin_perm hwf hpop1
  have hperm2 := popMin_perm hwf1 hpop2
  have hperm_ab :
      (mkQ1 hn_pos sws trees (y.regs i1) ++ q₂.toList).Perm
        (⟨trees.getD u_a (.leaf ⟨0, hn_pos⟩), wt_a⟩ ::
          ⟨trees.getD u_b (.leaf ⟨0, hn_pos⟩), wt_b⟩ ::
          (mkQ1 hn_pos sws trees (y₂.regs i1) ++ q₂''.toList)) :=
    hperm1.trans (hperm2.cons _)
  have hsum_ab := (hperm_ab.map WeightedTree.wt).sum_eq
  simp only [List.map_cons, List.sum_cons] at hsum_ab
  have hwt_sum_le : wt_a + wt_b ≤ sws.sum := by omega
  have hwpl_new_le : y.regs wpl + (wt_a + wt_b) ≤ (s + 1) * sws.sum := by
    rw [Nat.succ_mul]; omega
  obtain ⟨z, hex_tail, hzz, hzo, hzn, hzwtb, hzwb, hzns, hzpb, hzfo,
    hzi1, hzh2, hzstep, hzwpl, hzmem⟩ :=
    mergeTail_exec sws y₂ hy2_z hy2_o hy2_n hy2_wtb hy2_wb hy2_ns hy2_pb hy2_fo hy2_step
      huA2 hwA2 huB2 hwB2 hlt hfit_mem (hsum_fit.of_le hwt_sum_le)
      (by rw [hy2_wpl]; exact hfit_wpl.of_le <|
        hwpl_new_le.trans (Nat.mul_le_mul_right sws.sum (by omega : s + 1 ≤ sws.length)))
  rw [hmem2_eq] at hzmem
  rw [hy2_wpl] at hzwpl
  have hex_body : ExecWithin w mergeBody y z 36 := by
    unfold mergeBody
    exact (hex_pop2.seq hex_tail).mono (by omega)
  obtain ⟨T_new, hT_new⟩ : ∃ t : CodeTree (Fin sws.length),
      t = .branch (trees.getD u_a (.leaf ⟨0, hn_pos⟩)) (trees.getD u_b (.leaf ⟨0, hn_pos⟩)) :=
    ⟨_, rfl⟩
  have hmod_z : Modifies (Block.mk wb (3 * sws.length)).footprint x_mem z.mem := by
    rw [hzmem]
    intro addr_c hc
    rw [Block.mem_footprint, Block.Owns] at hc
    dsimp only at hc
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hmod addr_c (by rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  have hq2_z :
      (q₂''.enqueue ⟨T_new, wt_a + wt_b⟩).toList =
        mkQ2 hn_pos (trees ++ [T_new]) z.mem wb (z.regs h2) (s + 1) := by
    rw [FifoQueue.toList_enqueue, hq2_2, hzh2]
    symm
    refine mkQ2_snoc hn_pos trees T_new y.mem z.mem wb (y₂.regs h2) s (wt_a + wt_b) hlen_t hh2_2
      (fun k hk => ?_) ?_
    · rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    · rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]
  have ha_wt : wt_a = (trees.getD u_a (.leaf ⟨0, hn_pos⟩)).weight (symWeight sws) :=
    hwt_eq ⟨trees.getD u_a (.leaf ⟨0, hn_pos⟩), wt_a⟩ (hperm_ab.symm.subset List.mem_cons_self)
  have hb_wt : wt_b = (trees.getD u_b (.leaf ⟨0, hn_pos⟩)).weight (symWeight sws) :=
    hwt_eq ⟨trees.getD u_b (.leaf ⟨0, hn_pos⟩), wt_b⟩
      (hperm_ab.symm.subset (List.mem_cons_of_mem _ List.mem_cons_self))
  have hpool_perm_next :
      (mkQ1 hn_pos sws (trees ++ [T_new]) (z.regs i1) ++
          (q₂''.enqueue ⟨T_new, wt_a + wt_b⟩).toList).Perm
        (⟨T_new, wt_a + wt_b⟩ :: (mkQ1 hn_pos sws trees (y₂.regs i1) ++ q₂''.toList)) := by
    rw [hzi1, mkQ1_append_tree hn_pos sws trees T_new (by omega),
      FifoQueue.toList_enqueue, ← List.append_assoc]
    exact List.perm_append_singleton (⟨T_new, wt_a + wt_b⟩ : WeightedTree (Fin sws.length) ℕ) _
  refine ⟨z, hex_body, ⟨hzz, hzo, hzn, hzwtb, hzwb, hzns, hzpb, hzfo,
    by rw [hzi1]; exact hi1_2,
    by rw [hzh2]; exact le_trans hh2_2 (Nat.le_succ _),
    by rw [hzi1, hzh2]; exact hpool_next,
    hmod_z, trees ++ [T_new],
    (fun k => if k = s + 1 then z.regs i1 else i1_hist k),
    (fun k => if k = s + 1 then z.regs h2 else h2_hist k),
    q₂''.enqueue ⟨T_new, wt_a + wt_b⟩,
    by simp only [List.length_append, List.length_singleton, hlen_t, Nat.add_assoc],
    fun i hi => by
      rw [getD_append_left trees [T_new] (by omega)]
      exact htrees_leaf i hi,
    by simp [hi1_0], by simp [hh2_0],
    by simp, by simp,
    ?_, FifoQueue.wf_enqueue q₂'' ⟨T_new, wt_a + wt_b⟩, hq2_z, ?_, ?_, ?_,
    by rw [hzwpl]; exact hwpl_new_le, ?_⟩, hzstep⟩
  · intro k hk
    by_cases hks : k < s
    · have hk_ne : k ≠ s + 1 := by omega
      have hmem_lc : z.mem (wb + sws.length + k) = y.mem (wb + sws.length + k) := by
        rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      have hmem_rc : z.mem (wb + 2 * sws.length + k) = y.mem (wb + 2 * sws.length + k) := by
        rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      rcases hhist k hks with ⟨hl, hr, hne_lr, hbr, hav_l, hav_r, hav_step⟩
      refine ⟨by rwa [hmem_lc], by rwa [hmem_rc], by rwa [hmem_lc, hmem_rc], ?_, ?_, ?_, ?_⟩
      · simp only [hmem_lc, hmem_rc]
        rw [getD_append_left trees [T_new] (by omega),
          getD_append_left trees [T_new] (by omega),
          getD_append_left trees [T_new] (by omega)]
        exact hbr
      · simpa [hk_ne, hmem_lc] using hav_l
      · simpa [hk_ne, hmem_rc] using hav_r
      · intro v
        simpa [hk_ne, hks.ne, hmem_lc, hmem_rc] using hav_step v
    · have rfl_k : k = s := by omega
      subst rfl_k
      have hmem_lc : z.mem (wb + sws.length + k) = u_a := by
        rw [hzmem, Function.update_of_ne (by omega), Function.update_self]
      have hmem_rc : z.mem (wb + 2 * sws.length + k) = u_b := by
        rw [hzmem, Function.update_self]
      refine ⟨by rw [hmem_lc]; exact hua_lt, by rw [hmem_rc]; exact hub_lt,
        by rw [hmem_lc, hmem_rc]; exact hub_ne_a.symm, ?_, ?_, ?_, ?_⟩
      · simp only [hmem_lc, hmem_rc]
        have hidx : sws.length + k = trees.length := hlen_t.symm
        rw [hidx, getD_append_singleton_self,
          getD_append_left trees [T_new] (by omega),
          getD_append_left trees [T_new] (by omega), hT_new]
      · simp [hi1_s, hh2_s, hmem_lc, hua_av]
      · simp [hi1_s, hh2_s, hmem_rc, hub_av]
      · intro v
        simp only [↓reduceIte, show ¬ (k = k + 1) by omega,
          hi1_s, hh2_s, hzi1, hzh2, hmem_lc, hmem_rc]
        have hvb := hav_both v
        simp only [Avail] at hvb ⊢
        omega
  · intro e he
    rcases List.mem_cons.mp (hpool_perm_next.subset he) with rfl | hrest
    · simp [hT_new, ha_wt, hb_wt]
    · exact hwt_eq e (hperm_ab.symm.subset
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest)))
  · rw [(hpool_perm_next.map WeightedTree.wt).sum_eq]
    simp only [List.map_cons, List.sum_cons]
    omega
  · have hwpl_perm := (hperm_ab.map fun e : WeightedTree (Fin sws.length) ℕ =>
      e.tree.weightedPathLength (symWeight sws)).sum_eq
    simp only [List.map_cons, List.sum_cons] at hwpl_perm
    rw [(hpool_perm_next.map fun e : WeightedTree (Fin sws.length) ℕ =>
      e.tree.weightedPathLength (symWeight sws)).sum_eq]
    simp only [List.map_cons, List.sum_cons, hT_new,
      CodeTree.weightedPathLength_branch, ← ha_wt, ← hb_wt, hzwpl, hwpl_eq, hwpl_perm]
    omega
  · rw [hzi1, mkQ1_append_tree hn_pos sws trees T_new (by omega), ← hloop_eq]
    conv_rhs => rw [twoQueueLoop_step]
    simp [hpop1, hpop2, hT_new]

private theorem depthBody_exec {w wb pb_init fo_init : ℕ}
    (sws : List ℕ) (hn_pos : 0 < sws.length) (x_mem yM_mem : ℕ → ℕ)
    (trees : List (CodeTree (Fin sws.length))) (i1_hist h2_hist : ℕ → ℕ)
    (T_root : CodeTree (Fin sws.length))
    (hfit_mem : Fits w (wb + 5 * sws.length + 1))
    (hhist : ∀ k < sws.length - 1,
      let u_l := yM_mem (wb + sws.length + k)
      let u_r := yM_mem (wb + 2 * sws.length + k)
      u_l < sws.length + k ∧ u_r < sws.length + k ∧ u_l ≠ u_r ∧
        trees.getD (sws.length + k) (.leaf ⟨0, hn_pos⟩) =
          .branch (trees.getD u_l (.leaf ⟨0, hn_pos⟩)) (trees.getD u_r (.leaf ⟨0, hn_pos⟩)) ∧
        Avail sws.length (i1_hist k) (h2_hist k) k u_l ∧
        Avail sws.length (i1_hist k) (h2_hist k) k u_r ∧
        (∀ v, Avail sws.length (i1_hist (k + 1)) (h2_hist (k + 1)) (k + 1) v ↔
          (Avail sws.length (i1_hist k) (h2_hist k) k v ∧ v ≠ u_l ∧ v ≠ u_r) ∨
            v = sws.length + k))
    (y : Data 30)
    (hy : DepthInv sws hn_pos wb pb_init fo_init x_mem yM_mem
      trees i1_hist h2_hist T_root (y.regs step) y)
    (hlt : y.regs step < sws.length - 1) :
    ∃ z, ExecWithin w depthBody y z 18 ∧
      DepthInv sws hn_pos wb pb_init fo_init x_mem yM_mem
        trees i1_hist h2_hist T_root (y.regs step + 1) z ∧
      z.regs step = y.regs step + 1 := by
  let dfltTree : CodeTree (Fin sws.length) := .leaf ⟨0, hn_pos⟩
  set j := y.regs step with hj_def
  obtain ⟨hyz, hyo, hyn, hywb, hyns, hypb, hyfo, hywpl, hyout, hym_out, hym_child,
    hmodD, hdepth_inv⟩ := hy
  obtain ⟨k, hk_def⟩ : ∃ kv, kv = sws.length - 2 - j := ⟨_, rfl⟩
  have hk_lt : k < sws.length - 1 := by omega
  have hm_eq : sws.length - 1 - j = k + 1 := by omega
  have hm_next : sws.length - 1 - (j + 1) = k := by omega
  rcases hhist k hk_lt with ⟨hl_lt, hr_lt, hne_lr, hbr_k, hav_l, hav_r, hav_step⟩
  obtain ⟨u_l, hul_def⟩ : ∃ v, v = yM_mem (wb + sws.length + k) := ⟨_, rfl⟩
  obtain ⟨u_r, hur_def⟩ : ∃ v, v = yM_mem (wb + 2 * sws.length + k) := ⟨_, rfl⟩
  rw [← hul_def] at hl_lt hne_lr hbr_k hav_l hav_step
  rw [← hur_def] at hr_lt hne_lr hbr_k hav_r hav_step
  have hy_lc : y.mem (wb + sws.length + k) = u_l :=
    (hym_child _ (by omega) (by omega)).trans hul_def.symm
  have hparent_av : Avail sws.length (i1_hist (sws.length - 1 - j))
      (h2_hist (sws.length - 1 - j)) (sws.length - 1 - j) (sws.length + k) := by
    rw [hm_eq]; exact (hav_step (sws.length + k)).mpr (Or.inr rfl)
  obtain ⟨_, hd_le, hparent_enc⟩ := hdepth_inv (sws.length + k) hparent_av
  obtain ⟨d_val, hd_def⟩ : ∃ dv, dv = y.mem (wb + 3 * sws.length + 1 + (sws.length + k)) :=
    ⟨_, rfl⟩
  rw [← hd_def] at hd_le hparent_enc
  have hy_dp : y.mem (wb + 3 * sws.length + 1 +
      (sws.length + ((sws.length - 1 - 1) - j))) = d_val := by
    rw [hd_def]; congr 1; omega
  have hy_lc' : y.mem (wb + sws.length + ((sws.length - 1 - 1) - j)) = u_l := by
    rw [show wb + sws.length + ((sws.length - 1 - 1) - j) = wb + sws.length + k by omega]
    exact hy_lc
  have hy_rc' : y.mem (wb + sws.length + sws.length + ((sws.length - 1 - 1) - j)) = u_r := by
    rw [show wb + sws.length + sws.length + ((sws.length - 1 - 1) - j) =
      wb + 2 * sws.length + k by omega]
    exact (hym_child _ (by omega) (by omega)).trans hur_def.symm
  refine WP.exists_execWithin ?_
  unfold depthBody
  wram_exec [hyo, hyn, hywb, hyns, hyout, ← hj_def, hy_dp, hy_lc', hy_rc']
  refine ⟨⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hyn],
    by wram_simp [hywb], by wram_simp [hyns], by wram_simp [hypb], by wram_simp [hyfo],
    by wram_simp [hywpl], by wram_simp [hyout], ?_, ?_, ?_, ?_⟩, by wram_simp [← hj_def]⟩
  · wram_simp [Data.write_mem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hym_out
  · intro a ha1 ha2
    wram_simp [Data.write_mem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hym_child a ha1 ha2
  · wram_simp [Data.write_mem]
    exact modifies_write (modifies_write hmodD ⟨by omega, by omega⟩) ⟨by omega, by omega⟩
  · intro u hu
    rw [hm_next] at hu
    wram_simp [Data.write_mem]
    by_cases hul : u = u_l
    · subst u
      rw [Function.update_of_ne (by omega), Function.update_self]
      refine ⟨by omega, by omega, fun hnd => ?_⟩
      obtain ⟨hnd_p, henc_p⟩ := hparent_enc hnd
      rw [hbr_k, CodeTree.leaves_branch, List.nodup_append] at hnd_p
      refine ⟨hnd_p.1, fun a c hc => ?_⟩
      have hp_c : (trees.getD (sws.length + k) dfltTree).encodeSym a =
          some (false :: c) := by
        rw [hbr_k]
        change (match (trees.getD u_l dfltTree).encodeSym a with
          | some c => some (false :: c)
          | none => Option.map (true :: ·) ((trees.getD u_r dfltTree).encodeSym a)) =
          some (false :: c)
        rw [hc]
      obtain ⟨cr, hcr, hlen_cr⟩ := henc_p a (false :: c) hp_c
      exact ⟨cr, hcr, by simp only [List.length_cons] at hlen_cr; omega⟩
    · by_cases hur : u = u_r
      · subst u
        rw [Function.update_self]
        refine ⟨by omega, by omega, fun hnd => ?_⟩
        obtain ⟨hnd_p, henc_p⟩ := hparent_enc hnd
        rw [hbr_k, CodeTree.leaves_branch, List.nodup_append] at hnd_p
        refine ⟨hnd_p.2.1, fun a c hc => ?_⟩
        have ha_in_r : a ∈ (trees.getD u_r dfltTree).leaves := by
          rw [← CodeTree.map_fst_codewords]
          exact List.mem_map.mpr ⟨(a, c), CodeTree.mem_codewords_of_encodeSym hc, rfl⟩
        have ha_not_l : a ∉ (trees.getD u_l dfltTree).leaves := fun hal =>
          hnd_p.2.2 a hal a ha_in_r rfl
        have hp_c : (trees.getD (sws.length + k) dfltTree).encodeSym a =
            some (true :: c) := by
          rw [hbr_k]
          change (match (trees.getD u_l dfltTree).encodeSym a with
            | some c => some (false :: c)
            | none => Option.map (true :: ·) ((trees.getD u_r dfltTree).encodeSym a)) =
            some (true :: c)
          rw [CodeTree.encodeSym_eq_none_of_notMem ha_not_l, hc]
          rfl
        obtain ⟨cr, hcr, hlen_cr⟩ := henc_p a (true :: c) hp_c
        exact ⟨cr, hcr, by simp only [List.length_cons] at hlen_cr; omega⟩
      · have hu_prev : Avail sws.length (i1_hist (sws.length - 1 - j))
            (h2_hist (sws.length - 1 - j)) (sws.length - 1 - j) u := by
          rw [hm_eq]; exact (hav_step u).mpr (Or.inl ⟨hu, hul, hur⟩)
        obtain ⟨hu_lt, hud_le, hu_enc⟩ := hdepth_inv u hu_prev
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact ⟨hu_lt, by omega, hu_enc⟩

private theorem twoQueueCore_exec {w wtb wb : ℕ} (sws : List ℕ) (x : Data 30)
    (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hn : x.regs len = sws.length)
    (hwtb : x.regs wtBase = wtb) (hwb : x.regs workBase = wb)
    (hsws : Block.HoldsList wtb sws x.mem)
    (hdisj : wtb + sws.length ≤ wb)
    (hfit_mem : Fits w (wb + 5 * sws.length + 1))
    (hfit_wpl : Fits w (sws.length * sws.sum)) :
    ∃ y : Data 30, ExecWithin w twoQueueCore x y (58 * sws.length + 20) ∧
      ∃ lens : List ℕ,
        Modifies (Block.mk wb (5 * sws.length + 1)).footprint x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs len = sws.length ∧
        y.regs permBase = x.regs permBase ∧ y.regs finalOut = x.regs finalOut ∧
        y.regs outPtr = (if sws = [] then wb else wb + 3 * sws.length) ∧
        outputList y.mem (y.regs outPtr) = lens ∧
        lens.length = sws.length ∧
        Fits w (y.regs outPtr + lens.length) ∧
        (sws = [] → lens = [] ∧ y.regs wpl = 0) ∧
        (sws ≠ [] → sws.Pairwise (· ≤ ·) →
          ∃ T : CodeTree (Fin sws.length),
            huffmanFromSorted (symWeight sws) (List.finRange sws.length) = some T ∧
            IsHuffmanBuild (symWeight sws) ((List.finRange sws.length).map .leaf) T ∧
            T.leaves.Perm (List.finRange sws.length) ∧
            y.regs wpl = T.weightedPathLength (symWeight sws) ∧
            ∀ i : Fin sws.length, ∃ c, T.encodeSym i = some c ∧ c.length = lens.getD i.val 0) := by
  by_cases h0 : sws.length = 0
  · have hnil : sws = [] := List.length_eq_zero_iff.mp h0
    refine WP.exists_execWithin ?_
    unfold twoQueueCore
    wram_exec [hz, hn, hwb, h0]
    refine ⟨[], ?_, by wram_simp [hz], by wram_simp [ho], by wram_simp [hn],
      by wram_simp, by wram_simp, by wram_simp [hnil], ?_, by simp [hnil], ?_,
      fun _ => ⟨rfl, by wram_simp⟩, fun hne => absurd hnil hne⟩
    · wram_simp
      exact Modifies.write_of_owns (base := wb) (n := 5 * sws.length + 1) ⟨le_rfl, by omega⟩ 0
    · wram_simp
      rw [outputList_eq_iff]
      exact ⟨by simp, Block.holdsList_nil _ _⟩
    · wram_simp
      exact hfit_mem.of_le (by simp [hnil])
  · have hn_pos : 0 < sws.length := Nat.pos_of_ne_zero h0
    have hne_sws : sws ≠ [] := List.ne_nil_of_length_pos hn_pos
    let dfltTree : CodeTree (Fin sws.length) := .leaf ⟨0, hn_pos⟩
    refine WP.exists_execWithin ?_
    unfold twoQueueCore
    wram_exec [hz, ho, hn, hn_pos]
    refine WP.of_spec
      (ExecWithin.loop_count (index := step) (limit := nSub1) (N := sws.length - 1) (T := 36)
        (MergeInv sws hn_pos wtb wb (x.regs permBase) (x.regs finalOut) x.mem)
        (fun _ hu => hu.nSub1_eq)
        (mergeBody_exec sws hn_pos x.mem hsws hdisj hfit_mem hfit_wpl) ?_ ?_) ?_
    · wram_simp; omega
    · let trees₀ : List (CodeTree (Fin sws.length)) := (List.finRange sws.length).map .leaf
      have hq1_0 : mkQ1 hn_pos sws trees₀ 0 =
          (List.finRange sws.length).map fun i => ⟨.leaf i, symWeight sws i⟩ := by
        apply List.ext_getElem (by simp [mkQ1])
        intro i hi1 _
        have hi_n : i < sws.length := by simpa [mkQ1] using hi1
        have hi_fr : i < (List.finRange sws.length).length := by simpa using hi_n
        simp [mkQ1, trees₀, symWeight, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi_fr, List.getElem?_eq_getElem hi_n]
      refine ⟨by wram_simp [hz], by wram_simp [ho], by wram_simp [hn],
        by wram_simp [hwtb], by wram_simp [hwb], by wram_simp,
        by wram_simp, by wram_simp, by wram_simp; omega, by wram_simp,
        by wram_simp, Modifies.refl _ _,
        trees₀, (fun _ => 0), (fun _ => 0), FifoQueue.empty, by wram_simp; simp [trees₀],
        fun i hi => by
          have hi_fr : i < (List.finRange sws.length).length := by simpa using hi
          simp [trees₀, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_fr],
        rfl, rfl, by wram_simp, by wram_simp,
        fun k hk => by wram_simp at hk,
        FifoQueue.wf_empty, (mkQ2_eq_nil hn_pos trees₀ x.mem wb (by wram_simp)).symm,
        ?_, ?_, ?_, by wram_simp; simp, ?_⟩
      · intro e he
        wram_simp at he
        simp only [hq1_0, FifoQueue.toList_empty, List.append_nil, List.mem_map] at he
        rcases he with ⟨i, _, rfl⟩; rfl
      · wram_simp
        simp only [hq1_0, FifoQueue.toList_empty, List.append_nil,
          List.map_map, Function.comp_def, symWeight]
        have hmap_sws : List.map (fun j : Fin sws.length => sws[j.val])
            (List.finRange sws.length) = sws := by
          apply List.ext_getElem (by simp); intro j _ _; simp
        exact congrArg List.sum hmap_sws
      · wram_simp
        simp [hq1_0, FifoQueue.toList_empty, List.map_map, Function.comp_def]
      · wram_simp
        simp [hq1_0, huffmanFromSorted]
    · rintro yM ⟨hPM, _⟩
      obtain ⟨hyMz, hyMo, hyMn, _, hyMwb, hyMns, hyMpb, hyMfo, hyMi1, hyMh2, hpoolM_sz, hmodM,
        trees, i1_hist, h2_hist, q₂M, hlen_tM, htrees_leaf, hi1_0, hh2_0, hi1_end, hh2_end,
        hhist, hwfM, hq2M, _, _, hwplM_eq, _, hloopM_eq⟩ := hPM
      let rootIdx := 2 * sws.length - 2
      have hroot_av : Avail sws.length (yM.regs i1) (yM.regs h2) (sws.length - 1) rootIdx := by
        rcases Nat.eq_or_lt_of_le hn_pos with h1 | h2
        · have rfl_n : sws.length = 1 := h1.symm
          simp only [Avail, rootIdx, rfl_n]; omega
        · have hlast := (hhist (sws.length - 2) (by omega)).2.2.2.2.2.2 rootIdx
          rw [show sws.length - 2 + 1 = sws.length - 1 by omega, hi1_end, hh2_end] at hlast
          exact hlast.mpr (Or.inr (by omega))
      have hsole_av : ∀ v, Avail sws.length (yM.regs i1) (yM.regs h2) (sws.length - 1) v ↔
          v = rootIdx := by
        intro v
        constructor
        · intro hv; simp only [Avail] at hv hroot_av; omega
        · rintro rfl; exact hroot_av
      let T_root : CodeTree (Fin sws.length) := trees.getD rootIdx dfltTree
      have hpoolM_singleton :
          ∃ wt_r, mkQ1 hn_pos sws trees (yM.regs i1) ++ q₂M.toList = [⟨T_root, wt_r⟩] ∧
            twoQueueLoop (mkQ1 hn_pos sws trees (yM.regs i1)) q₂M = some T_root := by
        by_cases hi_end : yM.regs i1 < sws.length
        · have hh_end : sws.length - 1 ≤ yM.regs h2 := by omega
          have hi_eq : yM.regs i1 = rootIdx :=
            (hsole_av (yM.regs i1)).mp (Or.inl ⟨le_rfl, hi_end⟩)
          have hq1_s :
              mkQ1 hn_pos sws trees (yM.regs i1) = [⟨T_root, sws.getD (yM.regs i1) 0⟩] := by
            rw [mkQ1_eq_cons hn_pos sws trees hi_end, mkQ1_eq_nil hn_pos sws trees (by omega)]
            simp [T_root, hi_eq, dfltTree]
          have hq2_s : q₂M.toList = [] := hq2M.trans (mkQ2_eq_nil hn_pos trees yM.mem wb hh_end)
          refine ⟨sws.getD (yM.regs i1) 0, by simp [hq1_s, hq2_s], ?_⟩
          rw [twoQueueLoop_step]
          have hpm1 := popMin_spec_toList (mkQ1 hn_pos sws trees (yM.regs i1)) hwfM
          rw [hq1_s, hq2_s] at hpm1; dsimp only at hpm1
          rw [hq1_s, hpm1]; dsimp only
          have hpm2 := popMin_spec_toList ([] : List (WeightedTree (Fin sws.length) ℕ)) hwfM
          rw [hq2_s] at hpm2; dsimp only at hpm2
          rw [hpm2]
        · have hi_ge : sws.length ≤ yM.regs i1 := by omega
          have hh_lt : yM.regs h2 < sws.length - 1 := by omega
          have hh_eq : sws.length + yM.regs h2 = rootIdx :=
            (hsole_av (sws.length + yM.regs h2)).mp (Or.inr ⟨by omega, by omega⟩)
          have hq1_s : mkQ1 hn_pos sws trees (yM.regs i1) = [] :=
            mkQ1_eq_nil hn_pos sws trees hi_ge
          have hq2_s : q₂M.toList = [⟨T_root, yM.mem (wb + yM.regs h2)⟩] := by
            rw [hq2M, mkQ2_eq_cons hn_pos trees yM.mem wb hh_lt,
              mkQ2_eq_nil hn_pos trees yM.mem wb (by omega)]
            simp [T_root, hh_eq, dfltTree]
          refine ⟨yM.mem (wb + yM.regs h2), by simp [hq1_s, hq2_s], ?_⟩
          rw [twoQueueLoop_step]
          have hpm1 := popMin_spec_toList ([] : List (WeightedTree (Fin sws.length) ℕ)) hwfM
          rw [hq2_s] at hpm1; dsimp only at hpm1
          rcases hpm1 with ⟨q₂_empty, hp1, hwf_empty, hto_empty⟩
          rw [hq1_s, hp1]; dsimp only
          have hpm2 := popMin_spec_toList ([] : List (WeightedTree (Fin sws.length) ℕ)) hwf_empty
          rw [hto_empty] at hpm2; dsimp only at hpm2
          rw [hpm2]
      rcases hpoolM_singleton with ⟨_, hpool_one, hloop_root⟩
      have hhuff_eq : huffmanFromSorted (symWeight sws) (List.finRange sws.length) = some T_root :=
        hloopM_eq.symm.trans hloop_root
      have hwpl_root : yM.regs wpl = T_root.weightedPathLength (symWeight sws) := by
        rw [hwplM_eq, hpool_one]; simp
      wram_exec [hyMz, hyMo, hyMn, hyMwb, hyMns]
      refine WP.of_spec
        (ExecWithin.loop_count (index := step) (limit := nSub1) (N := sws.length - 1) (T := 18)
          (DepthInv sws hn_pos wb (x.regs permBase) (x.regs finalOut) x.mem yM.mem
            trees i1_hist h2_hist T_root)
          (fun _ hu => hu.nSub1_eq)
          (depthBody_exec sws hn_pos x.mem yM.mem trees i1_hist h2_hist T_root hfit_mem hhist)
          ?_ ?_) ?_
      · wram_simp; omega
      · refine ⟨by wram_simp [hyMz], by wram_simp [hyMo], by wram_simp [hyMn],
          by wram_simp [hyMwb], by wram_simp [hyMns], by wram_simp [hyMpb],
          by wram_simp [hyMfo], by wram_simp [hwpl_root],
          by wram_simp; omega, ?_, ?_, ?_, ?_⟩
        · wram_simp [Data.write_mem]
          rw [Function.update_of_ne (by omega),
            show wb + (sws.length + sws.length + sws.length) = wb + 3 * sws.length by omega,
            Function.update_self]
        · intro a ha1 ha2
          wram_simp [Data.write_mem]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · wram_simp [Data.write_mem]
          exact modifies_write
            (modifies_write (modifies_mono hmodM le_rfl (by omega)) ⟨by omega, by omega⟩)
            ⟨by omega, by omega⟩
        · intro u hu
          wram_simp [Data.write_mem] at hu ⊢
          rw [hi1_end, hh2_end, hsole_av] at hu
          subst hu
          have heq : wb + 3 * sws.length + 1 + rootIdx =
              wb + (sws.length + sws.length + sws.length) + 1 +
                (sws.length - 1 + (sws.length - 1)) := by omega
          rw [heq, Function.update_self]
          exact ⟨by omega, le_rfl, fun hnd => ⟨hnd, fun a c hc => ⟨c, hc, by omega⟩⟩⟩
      · rintro yF ⟨hPF, _⟩
        obtain ⟨hyFz, hyFo, hyFn, _, _, hyFpb, hyFfo, hyFwpl, hyFout, hyFm_out, _,
          hmodF, hdepthF⟩ := hPF
        let outAddr := wb + 3 * sws.length
        let lens := outputList yF.mem outAddr
        have hlens_len : lens.length = sws.length := by simp [lens, outAddr, hyFm_out]
        refine ⟨by wram_simp; omega, lens, hmodF, hyFz, hyFo, hyFn, hyFpb, hyFfo,
          by simp [hne_sws, hyFout],
          by simp [hyFout, lens, outAddr],
          hlens_len,
          by rw [hyFout, hlens_len]; exact hfit_mem.of_le (by omega),
          fun hnil => absurd hnil hne_sws,
          fun _ hsorted => ?_⟩
        have hsorted_fin : (List.finRange sws.length).Pairwise
            (fun a b : Fin sws.length => symWeight sws a ≤ symWeight sws b) := by
          rw [List.pairwise_iff_getElem] at hsorted ⊢
          intro i j hi hj hij
          simpa [symWeight] using hsorted i j (by simpa using hi) (by simpa using hj) hij
        have hne_fin : (List.finRange sws.length : List (Fin sws.length)) ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp [hn_pos.ne'] at this
        obtain ⟨T₀, hT₀_eq, hT₀_build, hT₀_perm⟩ :=
          huffmanFromSorted_spec hne_fin hsorted_fin (fun _ _ => Nat.zero_le _)
        have hroot_eq : T_root = T₀ := Option.some.inj (hhuff_eq.symm.trans hT₀_eq)
        subst hroot_eq
        have hnodup_root : T_root.leaves.Nodup :=
          (List.nodup_finRange _).perm hT₀_perm.symm
        refine ⟨T_root, hhuff_eq, hT₀_build, hT₀_perm, hyFwpl, fun i => ?_⟩
        have hi_av : Avail sws.length (i1_hist (sws.length - 1 - (sws.length - 1)))
            (h2_hist (sws.length - 1 - (sws.length - 1)))
            (sws.length - 1 - (sws.length - 1)) i.val := by
          simp only [Nat.sub_self, hi1_0, hh2_0, Avail]
          exact Or.inl ⟨Nat.zero_le _, i.isLt⟩
        obtain ⟨_, _, hi_enc⟩ := hdepthF i.val hi_av
        obtain ⟨_, henc_leaf⟩ := hi_enc hnodup_root
        have hleaf_eq : trees.getD i.val dfltTree = .leaf i := htrees_leaf i.val i.isLt
        have hleaf_enc : (trees.getD i.val dfltTree).encodeSym i = some [] := by
          rw [hleaf_eq]; simp [CodeTree.encodeSym]
        obtain ⟨cr, hcr, hlen_cr⟩ := henc_leaf i [] hleaf_enc
        simp only [List.length_nil, Nat.add_zero] at hlen_cr
        have hlens_i : lens.getD i.val 0 = yF.mem (wb + 3 * sws.length + 1 + i.val) := by
          have hi_lt : i.val < lens.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]
          simp [lens, getElem_outputList, outAddr]
        exact ⟨cr, hcr, hlen_cr.trans hlens_i.symm⟩

/-! ## End-to-End `O(n)` Word-RAM Huffman on Pre-Sorted Weights -/

private def fromSortedSetup : Code .standard 30 := ram[
  zero ← #0;
  one ← #1;
  len ← *zero;
  wtBase ← #1;
  workBase ← len + one ]

/-- Structured `O(n)` Word-RAM Huffman builder from standard input `State.init ws`. -/
def fromSortedCode : Code .standard 30 := .seq fromSortedSetup twoQueueCore

/-- Compiled `O(n)` Word-RAM Huffman program returning the codeword-length list via
`ExecutesList`. -/
def fromSortedProgram : Program .standard 30 := fromSortedCode.program outPtr

private theorem exec_executesList_of_eq {B : Basis} {r w t : ℕ} (c : Code B r)
    (out : Fin r) {ws lens : List ℕ} {y : Data r}
    (hex : Exec w c (Data.init ws) y t)
    (hout : outputList y.mem (y.regs out) = lens)
    (hfit : Fits w (y.regs out + lens.length)) :
    ExecutesList w (c.program out) (.init ws) lens (t + 1) := by
  subst hout
  exact hex.executesList out hfit

/-- **Linear-Time `O(n)` Word-RAM Huffman Construction from Pre-Sorted Weights**
([VanLeeuwen1976]): on any list `ws : List ℕ` of `n = ws.length` nondecreasing symbol weights in
`State.init ws` at word width `w` satisfying `Fits w (6 * n + 2)` and `Fits w (n * ws.sum)`,
`fromSortedProgram` halts within `58 * n + 26` instructions outputting a codeword-length list `lens`
(`lens.length = n`) via `ExecutesList` such that (when `ws ≠ []`) there is a tree `T` produced by
`huffmanFromSorted` certified by `IsHuffmanBuild` whose codeword for each symbol `i : Fin n` has
length `lens.getD i 0` (hence minimizing weighted codeword length over all injective
`IsUniquelyDecodable` and `IsPrefixFree` binary codes). -/
theorem fromSortedProgram_spec {w : ℕ} (ws : List ℕ)
    (hfit_mem : Fits w (6 * ws.length + 2))
    (hfit_wpl : Fits w (ws.length * ws.sum)) :
    ∃ (lens : List ℕ) (steps : ℕ),
      ExecutesList w fromSortedProgram (.init ws) lens steps ∧
      steps ≤ 58 * ws.length + 26 ∧
      lens.length = ws.length ∧
      (ws = [] → lens = []) ∧
      (ws ≠ [] → ws.Pairwise (· ≤ ·) →
        ∃ T : CodeTree (Fin ws.length),
          huffmanFromSorted (symWeight ws) (List.finRange ws.length) = some T ∧
          IsHuffmanBuild (symWeight ws) ((List.finRange ws.length).map .leaf) T ∧
          T.leaves.Perm (List.finRange ws.length) ∧
          (∀ i : Fin ws.length, ∃ c, T.encodeSym i = some c ∧ c.length = lens.getD i.val 0) ∧
          (∀ code : Fin ws.length → List Bool,
            Set.InjOn code {a | a ∈ List.finRange ws.length} →
            InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ List.finRange ws.length}) →
            T.weightedPathLength (symWeight ws) ≤
              ((List.finRange ws.length).map fun a => (code a).length * symWeight ws a).sum)) := by
  have hsetup : ∃ x₁ : Data 30, ExecWithin w fromSortedSetup (Data.init ws) x₁ 5 ∧
      x₁.mem = (Data.init ws : Data 30).mem ∧
      x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧ x₁.regs len = ws.length ∧
      x₁.regs wtBase = 1 ∧ x₁.regs workBase = ws.length + 1 := by
    refine WP.exists_execWithin ?_
    unfold fromSortedSetup
    wram_exec [Data.init_regs, Data.init_mem_zero]
    exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₁, hex_s, hmem_s, hz1, ho1, hn1, hwtb1, hwb1⟩ := hsetup
  obtain ⟨y, hex_tq, lens, _, _, _, _, _, _, _, hout_eq, hlens_len, hfit_out, hnil, hpos⟩ :=
    twoQueueCore_exec ws x₁ hz1 ho1 hn1 hwtb1 hwb1
      (hmem_s ▸ (outputList_eq_iff.mp (outputList_init ws)).2)
      (by omega) (hfit_mem.of_le (by omega)) hfit_wpl
  obtain ⟨t_exact, ht_le, hex_code⟩ := hex_s.seq hex_tq
  have hex_list : ExecutesList w fromSortedProgram (.init ws) lens (t_exact + 1) := by
    rw [fromSortedProgram, ← hout_eq]
    exact hex_code.executesList outPtr (by rwa [hout_eq])
  refine ⟨lens, t_exact + 1, hex_list, by omega, hlens_len, fun h => (hnil h).1, fun hne hs => ?_⟩
  obtain ⟨T, hT_eq, hT_build, hT_perm, _, hT_enc⟩ := hpos hne hs
  refine ⟨T, hT_eq, hT_build, hT_perm, hT_enc, fun code hinj hud => ?_⟩
  have hne_fin : (List.finRange ws.length) ≠ [] := by
    intro h0
    have := congrArg List.length h0
    simp [(List.length_pos_iff.mpr hne).ne'] at this
  exact hT_build.weightedPathLength_le_of_isUniquelyDecodable
    hne_fin (List.nodup_finRange _) (fun _ _ => Nat.zero_le _) hinj hud

/-! ## Bottom-Up Iterative Index Merge Sort (`O(n log n)`) -/

private def initPermBody : Code .standard 30 := ram[
  addr ← permBase + step;
  *addr ← step;
  step ← step + one ]

private def mergeElemBody : Code .standard 30 := ram[
  if pA < mid then [
    if pB < hi then [
      addr ← permBase + pA; uA ← *addr;
      addr ← permBase + pB; uB ← *addr;
      addr ← keyBase + uA; wA ← *addr;
      addr ← keyBase + uB; wB ← *addr;
      if wB < wA then [
        addr ← bufBase + outIdx; *addr ← uB; pB ← pB + one
      ] else [
        addr ← bufBase + outIdx; *addr ← uA; pA ← pA + one
      ]
    ] else [
      addr ← permBase + pA; uA ← *addr;
      addr ← bufBase + outIdx; *addr ← uA; pA ← pA + one
    ]
  ] else [
    addr ← permBase + pB; uB ← *addr;
    addr ← bufBase + outIdx; *addr ← uB; pB ← pB + one
  ];
  outIdx ← outIdx + one ]

private def mergePassSetup : Code .standard 30 := ram[
  mid ← lo + wRun;
  if len < mid then [ mid ← len ] else [ mid ← mid ];
  hi ← mid + wRun;
  if len < hi then [ hi ← len ] else [ hi ← hi ];
  pA ← lo;
  pB ← mid;
  outIdx ← lo ]

private def mergePassBody : Code .standard 30 :=
  .seq mergePassSetup (.seq (.loop (.lt outIdx hi) mergeElemBody) (.op (.copy lo hi)))

private def copyBackBody : Code .standard 30 := ram[
  addr ← bufBase + step;
  tmp1 ← *addr;
  addr ← permBase + step;
  *addr ← tmp1;
  step ← step + one ]

private def outerPassBody : Code .standard 30 := ram[
  lo ← #0;
  while lo < len do [ ⟪mergePassBody⟫ ];
  step ← #0;
  while step < len do [ ⟪copyBackBody⟫ ];
  wRun ← wRun + wRun ]

private def mergeSortPerm : Code .standard 30 := ram[
  step ← #0;
  while step < len do [ ⟪initPermBody⟫ ];
  wRun ← #1;
  while wRun < len do [ ⟪outerPassBody⟫ ] ]

private structure OuterInv (ws : List ℕ) (kb pb bb wtb_init wb_init fo_init : ℕ)
    (x_mem : ℕ → ℕ) (y : Data 30) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  len_eq : y.regs len = ws.length
  keyBase_eq : y.regs keyBase = kb
  permBase_eq : y.regs permBase = pb
  bufBase_eq : y.regs bufBase = bb
  wtBase_eq : y.regs wtBase = wtb_init
  workBase_eq : y.regs workBase = wb_init
  finalOut_eq : y.regs finalOut = fo_init
  mod : Modifies (Block.mk pb (bb + ws.length - pb)).footprint x_mem y.mem
  state :
    ∃ (pass : ℕ) (L : List ℕ),
      pass ≤ Nat.clog 2 ws.length ∧
      y.regs wRun = 2 ^ pass ∧
      Block.HoldsList pb L y.mem ∧
      L.Perm (List.range ws.length) ∧
      (∀ q : ℕ, (slice L (q * 2 ^ pass) (2 ^ pass)).Pairwise
        (fun a b => ws.getD a 0 ≤ ws.getD b 0))

private structure MidInv (ws L : List ℕ) (kb pb bb wtb_init wb_init fo_init W : ℕ)
    (y_mem : ℕ → ℕ) (u : Data 30) : Prop where
  zero_eq : u.regs zero = 0
  one_eq : u.regs one = 1
  len_eq : u.regs len = ws.length
  keyBase_eq : u.regs keyBase = kb
  permBase_eq : u.regs permBase = pb
  bufBase_eq : u.regs bufBase = bb
  wtBase_eq : u.regs wtBase = wtb_init
  workBase_eq : u.regs workBase = wb_init
  finalOut_eq : u.regs finalOut = fo_init
  wRun_eq : u.regs wRun = W
  lo_le : u.regs lo ≤ ws.length
  lo_div : u.regs lo < ws.length → ∃ p : ℕ, u.regs lo = p * (2 * W)
  mod : Modifies (Block.mk bb ws.length).footprint y_mem u.mem
  state :
    ∃ acc : List ℕ,
      acc.length = u.regs lo ∧
      (∀ j : ℕ, (hj : j < acc.length) → u.mem (bb + j) = acc[j]) ∧
      acc.Perm (L.take (u.regs lo)) ∧
      (∀ q : ℕ, (slice acc (q * (2 * W)) (2 * W)).Pairwise
        (fun a b => ws.getD a 0 ≤ ws.getD b 0))

private structure InInv (ws L : List ℕ)
    (kb pb bb wtb_init wb_init fo_init W lo_v mid_v hi_v : ℕ)
    (u_mem : ℕ → ℕ) (idx_v : ℕ) (v : Data 30) : Prop where
  zero_eq : v.regs zero = 0
  one_eq : v.regs one = 1
  len_eq : v.regs len = ws.length
  keyBase_eq : v.regs keyBase = kb
  permBase_eq : v.regs permBase = pb
  bufBase_eq : v.regs bufBase = bb
  wtBase_eq : v.regs wtBase = wtb_init
  workBase_eq : v.regs workBase = wb_init
  finalOut_eq : v.regs finalOut = fo_init
  wRun_eq : v.regs wRun = W
  lo_eq : v.regs lo = lo_v
  mid_eq : v.regs mid = mid_v
  hi_eq : v.regs hi = hi_v
  pA_lo : lo_v ≤ v.regs pA
  pA_hi : v.regs pA ≤ mid_v
  pB_lo : mid_v ≤ v.regs pB
  pB_hi : v.regs pB ≤ hi_v
  idx_lo : lo_v ≤ idx_v
  rem_sum : (mid_v - v.regs pA) + (hi_v - v.regs pB) = hi_v - idx_v
  mod : Modifies (Block.mk (bb + lo_v) (idx_v - lo_v)).footprint u_mem v.mem
  state :
    ∃ pref : List ℕ,
      pref.length = idx_v - lo_v ∧
      (∀ d : ℕ, (hd : d < pref.length) → v.mem (bb + lo_v + d) = pref[d]) ∧
      pref ++ List.merge (slice L (v.regs pA) (mid_v - v.regs pA))
          (slice L (v.regs pB) (hi_v - v.regs pB))
          (fun a b => decide (ws.getD a 0 ≤ ws.getD b 0)) =
        List.merge (slice L lo_v (mid_v - lo_v)) (slice L mid_v (hi_v - mid_v))
          (fun a b => decide (ws.getD a 0 ≤ ws.getD b 0))

private structure InitPermInv (ws : List ℕ) (kb pb bb wtb_init wb_init fo_init : ℕ)
    (x_mem : ℕ → ℕ) (s : ℕ) (y : Data 30) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  len_eq : y.regs len = ws.length
  keyBase_eq : y.regs keyBase = kb
  permBase_eq : y.regs permBase = pb
  bufBase_eq : y.regs bufBase = bb
  wtBase_eq : y.regs wtBase = wtb_init
  workBase_eq : y.regs workBase = wb_init
  finalOut_eq : y.regs finalOut = fo_init
  mod : Modifies (Block.mk pb ws.length).footprint x_mem y.mem
  init_cells : ∀ j < s, y.mem (pb + j) = j

private structure CopyBackInv (ws L' : List ℕ) (kb pb bb wtb_init wb_init fo_init W : ℕ)
    (uM_mem : ℕ → ℕ) (s : ℕ) (v : Data 30) : Prop where
  zero_eq : v.regs zero = 0
  one_eq : v.regs one = 1
  len_eq : v.regs len = ws.length
  keyBase_eq : v.regs keyBase = kb
  permBase_eq : v.regs permBase = pb
  bufBase_eq : v.regs bufBase = bb
  wtBase_eq : v.regs wtBase = wtb_init
  workBase_eq : v.regs workBase = wb_init
  finalOut_eq : v.regs finalOut = fo_init
  wRun_eq : v.regs wRun = W
  mod : Modifies (Block.mk pb ws.length).footprint uM_mem v.mem
  copied : ∀ j : ℕ, (hj : j < s) → (hjL : j < L'.length) → v.mem (pb + j) = L'[j]

private theorem mergeElemBody_exec {w kb pb bb wtb_init wb_init fo_init W lo_v mid_v hi_v : ℕ}
    (ws L : List ℕ) (u_mem : ℕ → ℕ)
    (hL_len : L.length = ws.length)
    (hL_bound : ∀ v ∈ L, v < ws.length)
    (hhi_le : hi_v ≤ ws.length)
    (hdisj1 : kb + ws.length ≤ pb) (hdisj2 : pb + ws.length ≤ bb)
    (hfit : Fits w (bb + 2 * ws.length + 1))
    (hu_ws : Block.HoldsList kb ws u_mem)
    (hu_L : Block.HoldsList pb L u_mem)
    (v : Data 30)
    (hv : InInv ws L kb pb bb wtb_init wb_init fo_init W lo_v mid_v hi_v u_mem (v.regs outIdx) v)
    (hlt_in : v.regs outIdx < hi_v) :
    ∃ v', ExecWithin w mergeElemBody v v' 16 ∧
      InInv ws L kb pb bb wtb_init wb_init fo_init
        W lo_v mid_v hi_v u_mem (v.regs outIdx + 1) v' ∧
      v'.regs outIdx = v.regs outIdx + 1 := by
  obtain ⟨hvz, hvo, hvn, hvkb, hvpb, hvbb, hvwtb, hvwb, hvfo, hvw, hvlo, hvmid, hvhi,
    hpa1, hpa2, hpb1, hpb2, hidx_lo, hrem_sum, hmod_in, pref, hpref_len, hpref_mem,
    hmerge_inv⟩ := hv
  have hv_ws : Block.HoldsList kb ws v.mem :=
    hu_ws.frame fun a ha1 ha2 => hmod_in a (by
      rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  have hv_L : Block.HoldsList pb L v.mem :=
    hu_L.frame fun a ha1 ha2 => hmod_in a (by
      rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  refine WP.exists_execWithin ?_
  unfold mergeElemBody
  by_cases hcA : v.regs pA < mid_v
  · obtain ⟨hread_uA, huA_lt_n, hread_wA⟩ :=
      holdsList_read_key hv_ws hv_L hL_bound (by omega : v.regs pA < L.length)
    have hslA := slice_eq_cons L hcA (by omega)
    by_cases hcB : v.regs pB < hi_v
    · obtain ⟨hread_uB, huB_lt_n, hread_wB⟩ :=
        holdsList_read_key hv_ws hv_L hL_bound (by omega : v.regs pB < L.length)
      have hslB := slice_eq_cons L hcB (by omega)
      by_cases hcW : ws.getD L[v.regs pB] 0 < ws.getD L[v.regs pA] 0
      · have hcmp_f : decide (ws.getD L[v.regs pA] 0 ≤ ws.getD L[v.regs pB] 0) = false := by
          simp only [decide_eq_false_iff_not]; omega
        obtain ⟨hmod_snoc, hmem_snoc⟩ :=
          prefix_snoc_mem (elem := L[v.regs pB]) hpref_len hidx_lo hmod_in hpref_mem
        wram_exec [hvo, hvkb, hvpb, hvbb, hvmid, hvhi, hcA, hcB,
          hread_uA, hread_uB, hread_wA, hread_wB, hcW]
        refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
          by wram_simp [hvkb], by wram_simp [hvpb], by wram_simp [hvbb],
          by wram_simp [hvwtb], by wram_simp [hvwb], by wram_simp [hvfo],
          by wram_simp [hvw], by wram_simp [hvlo], by wram_simp [hvmid],
          by wram_simp [hvhi], by wram_simp [hpa1], by wram_simp [hpa2],
          by wram_simp; omega, by wram_simp; omega, by omega,
          by wram_simp; omega, by wram_simp [Data.write_mem]; exact hmod_snoc,
          pref ++ [L[v.regs pB]], by simp [hpref_len]; omega,
          by wram_simp [Data.write_mem]; exact hmem_snoc, ?_⟩, by wram_simp⟩
        wram_simp
        rw [List.append_assoc, List.singleton_append, ← hmerge_inv, hslA, hslB,
          List.cons_merge_cons, hcmp_f]
        rfl
      · have hcmp_t : decide (ws.getD L[v.regs pA] 0 ≤ ws.getD L[v.regs pB] 0) = true := by
          simp only [decide_eq_true_eq]; omega
        obtain ⟨hmod_snoc, hmem_snoc⟩ :=
          prefix_snoc_mem (elem := L[v.regs pA]) hpref_len hidx_lo hmod_in hpref_mem
        wram_exec [hvo, hvkb, hvpb, hvbb, hvmid, hvhi, hcA, hcB,
          hread_uA, hread_uB, hread_wA, hread_wB, hcW]
        refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
          by wram_simp [hvkb], by wram_simp [hvpb], by wram_simp [hvbb],
          by wram_simp [hvwtb], by wram_simp [hvwb], by wram_simp [hvfo],
          by wram_simp [hvw], by wram_simp [hvlo], by wram_simp [hvmid],
          by wram_simp [hvhi], by wram_simp; omega, by wram_simp; omega,
          by wram_simp [hpb1], by wram_simp [hpb2], by omega,
          by wram_simp; omega, by wram_simp [Data.write_mem]; exact hmod_snoc,
          pref ++ [L[v.regs pA]], by simp [hpref_len]; omega,
          by wram_simp [Data.write_mem]; exact hmem_snoc, ?_⟩, by wram_simp⟩
        wram_simp
        rw [List.append_assoc, List.singleton_append, ← hmerge_inv, hslA, hslB,
          List.cons_merge_cons, hcmp_t]
        rfl
    · have hslB : slice L (v.regs pB) (hi_v - v.regs pB) = [] := by
        rw [show hi_v - v.regs pB = 0 by omega, slice_zero]
      obtain ⟨hmod_snoc, hmem_snoc⟩ :=
        prefix_snoc_mem (elem := L[v.regs pA]) hpref_len hidx_lo hmod_in hpref_mem
      wram_exec [hvo, hvpb, hvbb, hvmid, hvhi, hcA, hcB, hread_uA]
      refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
        by wram_simp [hvkb], by wram_simp [hvpb], by wram_simp [hvbb],
        by wram_simp [hvwtb], by wram_simp [hvwb], by wram_simp [hvfo],
        by wram_simp [hvw], by wram_simp [hvlo], by wram_simp [hvmid],
        by wram_simp [hvhi], by wram_simp; omega, by wram_simp; omega,
        by wram_simp [hpb1], by wram_simp [hpb2], by omega,
        by wram_simp; omega, by wram_simp [Data.write_mem]; exact hmod_snoc,
        pref ++ [L[v.regs pA]], by simp [hpref_len]; omega,
        by wram_simp [Data.write_mem]; exact hmem_snoc, ?_⟩, by wram_simp⟩
      wram_simp
      rw [List.append_assoc, List.singleton_append, ← hmerge_inv, hslA, hslB]
      simp
  · have hcB : v.regs pB < hi_v := by omega
    have hpb_lt_L : v.regs pB < L.length := by omega
    have hread_uB : v.mem (pb + v.regs pB) = L[v.regs pB] := hv_L.get _ hpb_lt_L
    have hslA : slice L (v.regs pA) (mid_v - v.regs pA) = [] := by
      rw [show mid_v - v.regs pA = 0 by omega, slice_zero]
    have hslB := slice_eq_cons L hcB (by omega)
    obtain ⟨hmod_snoc, hmem_snoc⟩ :=
      prefix_snoc_mem (elem := L[v.regs pB]) hpref_len hidx_lo hmod_in hpref_mem
    wram_exec [hvo, hvpb, hvbb, hvmid, hcA, hread_uB]
    refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
      by wram_simp [hvkb], by wram_simp [hvpb], by wram_simp [hvbb],
      by wram_simp [hvwtb], by wram_simp [hvwb], by wram_simp [hvfo],
      by wram_simp [hvw], by wram_simp [hvlo], by wram_simp [hvmid],
      by wram_simp [hvhi], by wram_simp [hpa1], by wram_simp [hpa2],
      by wram_simp; omega, by wram_simp; omega, by omega,
      by wram_simp; omega, by wram_simp [Data.write_mem]; exact hmod_snoc,
      pref ++ [L[v.regs pB]], by simp [hpref_len]; omega,
      by wram_simp [Data.write_mem]; exact hmem_snoc, ?_⟩, by wram_simp⟩
    wram_simp
    rw [List.append_assoc, List.singleton_append, ← hmerge_inv, hslA, hslB]
    simp

private theorem mergePassSetup_exec {w kb pb bb wtb_init wb_init fo_init W lo_v mid_v hi_v : ℕ}
    (ws L : List ℕ) (u : Data 30)
    (hW_lt : W < ws.length) (hlo_lt : lo_v < ws.length)
    (hmid_def : mid_v = min ws.length (lo_v + W))
    (hhi_def : hi_v = min ws.length (mid_v + W))
    (hdisj2 : pb + ws.length ≤ bb)
    (hfit : Fits w (bb + 2 * ws.length + 1))
    (huz : u.regs zero = 0) (huo : u.regs one = 1) (hun : u.regs len = ws.length)
    (hukb : u.regs keyBase = kb) (hupb : u.regs permBase = pb) (hubb : u.regs bufBase = bb)
    (huwtb : u.regs wtBase = wtb_init) (huwb : u.regs workBase = wb_init)
    (hufo : u.regs finalOut = fo_init) (huw : u.regs wRun = W) (hlo_def : u.regs lo = lo_v) :
    ∃ u1 : Data 30, ExecWithin w mergePassSetup u u1 11 ∧
      InInv ws L kb pb bb wtb_init wb_init fo_init
        W lo_v mid_v hi_v u.mem (u1.regs outIdx) u1 ∧
      u1.regs outIdx = lo_v := by
  refine WP.exists_execWithin ?_
  unfold mergePassSetup
  by_cases hm1 : ws.length < lo_v + W
  · have hm_eq : mid_v = ws.length := by omega
    have hh2 : ws.length < ws.length + W := by omega
    have hh_eq : hi_v = ws.length := by omega
    wram_exec [hun, huw, hlo_def, hm1, hh2]
    refine ⟨⟨by wram_simp [huz], by wram_simp [huo], by wram_simp [hun],
      by wram_simp [hukb], by wram_simp [hupb], by wram_simp [hubb],
      by wram_simp [huwtb], by wram_simp [huwb], by wram_simp [hufo],
      by wram_simp [huw], by wram_simp [hlo_def], by wram_simp [hm_eq],
      by wram_simp [hh_eq], by wram_simp [hlo_def]; omega,
      by wram_simp [hlo_def, hm_eq]; omega,
      by wram_simp [hm_eq]; omega, by wram_simp [hm_eq, hh_eq]; omega,
      by wram_simp [hlo_def]; omega,
      by wram_simp [hlo_def, hm_eq, hh_eq],
      Modifies.refl _ _, [], by wram_simp [hlo_def]; rfl,
      fun d hd => absurd hd (Nat.not_lt_zero d),
      by wram_simp [hlo_def, hm_eq, hh_eq]; simp⟩,
      by wram_simp [hlo_def]⟩
  · have hm_eq : mid_v = lo_v + W := by omega
    by_cases hh2 : ws.length < mid_v + W
    · have hh_eq : hi_v = ws.length := by omega
      have hh2' : ws.length < lo_v + W + W := by omega
      wram_exec [hun, huw, hlo_def, hm1, hh2']
      refine ⟨⟨by wram_simp [huz], by wram_simp [huo], by wram_simp [hun],
        by wram_simp [hukb], by wram_simp [hupb], by wram_simp [hubb],
        by wram_simp [huwtb], by wram_simp [huwb], by wram_simp [hufo],
        by wram_simp [huw], by wram_simp [hlo_def], by wram_simp [hm_eq],
        by wram_simp [hh_eq], by wram_simp [hlo_def]; omega,
        by wram_simp [hlo_def, hm_eq]; omega,
        by wram_simp [hm_eq]; omega, by wram_simp [hm_eq, hh_eq]; omega,
        by wram_simp [hlo_def]; omega,
        by wram_simp [hlo_def, hm_eq, hh_eq]; omega,
        Modifies.refl _ _, [], by wram_simp [hlo_def]; rfl,
        fun d hd => absurd hd (Nat.not_lt_zero d),
        by wram_simp [hlo_def, hm_eq, hh_eq]; simp⟩,
        by wram_simp [hlo_def]⟩
    · have hh_eq : hi_v = lo_v + W + W := by omega
      have hh2' : ¬ (ws.length < lo_v + W + W) := by omega
      wram_exec [hun, huw, hlo_def, hm1, hh2']
      refine ⟨⟨by wram_simp [huz], by wram_simp [huo], by wram_simp [hun],
        by wram_simp [hukb], by wram_simp [hupb], by wram_simp [hubb],
        by wram_simp [huwtb], by wram_simp [huwb], by wram_simp [hufo],
        by wram_simp [huw], by wram_simp [hlo_def], by wram_simp [hm_eq],
        by wram_simp [hh_eq], by wram_simp [hlo_def]; omega,
        by wram_simp [hlo_def, hm_eq]; omega,
        by wram_simp [hm_eq]; omega, by wram_simp [hm_eq, hh_eq]; omega,
        by wram_simp [hlo_def]; omega,
        by wram_simp [hlo_def, hm_eq, hh_eq]; omega,
        Modifies.refl _ _, [], by wram_simp [hlo_def]; rfl,
        fun d hd => absurd hd (Nat.not_lt_zero d),
        by wram_simp [hlo_def, hm_eq, hh_eq]; simp⟩,
        by wram_simp [hlo_def]⟩

private theorem mergePassBody_exec {w kb pb bb wtb_init wb_init fo_init W : ℕ}
    (ws L : List ℕ) (y_mem : ℕ → ℕ)
    (hL_len : L.length = ws.length)
    (hL_bound : ∀ v ∈ L, v < ws.length)
    (hL_chunks : ∀ q : ℕ, (slice L (q * W) W).Pairwise (fun a b => ws.getD a 0 ≤ ws.getD b 0))
    (_hW_pos : 0 < W) (hW_lt : W < ws.length)
    (hdisj1 : kb + ws.length ≤ pb) (hdisj2 : pb + ws.length ≤ bb)
    (hfit : Fits w (bb + 2 * ws.length + 1))
    (u : Data 30)
    (hu_ws : Block.HoldsList kb ws u.mem)
    (hu_L : Block.HoldsList pb L u.mem)
    (hu : MidInv ws L kb pb bb wtb_init wb_init fo_init W y_mem u)
    (hcu : (Cond.lt lo len).Holds u) :
    ∃ u' T_m, ExecWithin w mergePassBody u u' T_m ∧
      MidInv ws L kb pb bb wtb_init wb_init fo_init W y_mem u' ∧
      T_m + 2 + 34 * (ws.length - u'.regs lo) ≤ 34 * (ws.length - u.regs lo) := by
  obtain ⟨huz, huo, hun, hukb, hupb, hubb, huwtb, huwb, hufo, huw, hulo_le, hulo_div,
    hmodM_u, acc, hacc_len, hacc_mem, hacc_perm, hacc_chunks⟩ := hu
  obtain ⟨lo_v, hlo_def⟩ : ∃ l, u.regs lo = l := ⟨_, rfl⟩
  rw [hlo_def] at hulo_le hulo_div hacc_len hacc_perm ⊢
  have hlo_lt : lo_v < ws.length := by simpa only [Cond.holds_lt, hun, hlo_def] using hcu
  obtain ⟨p, hlo_eq⟩ := hulo_div hlo_lt
  obtain ⟨mid_v, hmid_def⟩ : ∃ m, m = min ws.length (lo_v + W) := ⟨_, rfl⟩
  obtain ⟨hi_v, hhi_def⟩ : ∃ h, h = min ws.length (mid_v + W) := ⟨_, rfl⟩
  have hhi_eq : hi_v = min ws.length (lo_v + 2 * W) := by omega
  have hk_pos : 1 ≤ hi_v - lo_v := by omega
  obtain ⟨u1, hex_ms, hP1, hout1⟩ :=
    mergePassSetup_exec ws L u hW_lt hlo_lt hmid_def hhi_def hdisj2 hfit
      huz huo hun hukb hupb hubb huwtb huwb hufo huw hlo_def
  obtain ⟨u2, hex_in, hP2, _⟩ :=
    ExecWithin.loop_count (index := outIdx) (limit := hi) (N := hi_v) (T := 16)
      (InInv ws L kb pb bb wtb_init wb_init fo_init W lo_v mid_v hi_v u.mem)
      (fun _ hq => hq.hi_eq)
      (mergeElemBody_exec ws L u.mem hL_len hL_bound (by omega) hdisj1 hdisj2 hfit hu_ws hu_L)
      (by omega) hP1
  obtain ⟨hu2z, hu2o, hu2n, hu2kb, hu2pb, hu2bb, hu2wtb, hu2wb, hu2fo, hu2w,
    _, _, hu2hi, hpa1, hpa2, hpb1, hpb2, _, hrem_end, hmod_u2,
    M, hM_len, hM_mem, hM_eq⟩ := hP2
  have hpA_end : u2.regs pA = mid_v := by omega
  have hpB_end : u2.regs pB = hi_v := by omega
  rw [hpA_end, hpB_end, Nat.sub_self, Nat.sub_self, slice_zero, slice_zero] at hM_eq
  simp only [List.nil_merge, List.append_nil] at hM_eq
  have h2pW : (2 * p) * W = lo_v := by
    rw [hlo_eq, Nat.mul_comm 2 p, Nat.mul_assoc]
  have hA_eq : slice L lo_v (mid_v - lo_v) = slice L ((2 * p) * W) W := by
    rw [h2pW]
    simp only [slice]
    have hlen_drop : (L.drop lo_v).length = ws.length - lo_v := by simp [hL_len]
    have hmid_sub : mid_v - lo_v = min (L.drop lo_v).length W := by rw [hlen_drop]; omega
    rw [hmid_sub, take_min_length]
  have hA_sorted :
      (slice L lo_v (mid_v - lo_v)).Pairwise (fun a b => ws.getD a 0 ≤ ws.getD b 0) :=
    hA_eq ▸ hL_chunks (2 * p)
  have hB_sorted :
      (slice L mid_v (hi_v - mid_v)).Pairwise (fun a b => ws.getD a 0 ≤ ws.getD b 0) := by
    by_cases hm_lt : lo_v + W < ws.length
    · have hm_eq : mid_v = (2 * p + 1) * W := by
        have h1 : (2 * p + 1) * W = lo_v + W := by rw [Nat.add_mul, Nat.one_mul, h2pW]
        rw [h1]; omega
      have hB_eq : slice L mid_v (hi_v - mid_v) = slice L ((2 * p + 1) * W) W := by
        rw [hm_eq]
        simp only [slice]
        have hlen_drop : (L.drop ((2 * p + 1) * W)).length =
            ws.length - (2 * p + 1) * W := by simp [hL_len]
        have hhi_sub : hi_v - (2 * p + 1) * W =
            min (L.drop ((2 * p + 1) * W)).length W := by
          rw [hlen_drop, ← hm_eq]; omega
        rw [hhi_sub, take_min_length]
      exact hB_eq ▸ hL_chunks (2 * p + 1)
    · have h0_B : hi_v - mid_v = 0 := by omega
      simp [h0_B, slice_zero]
  have hM_sorted : M.Pairwise (fun a b => ws.getD a 0 ≤ ws.getD b 0) := by
    rw [hM_eq]
    have hpm := List.pairwise_merge
      (le := fun a b => decide (ws.getD a 0 ≤ ws.getD b 0))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; exact le_trans h1 h2)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (slice L lo_v (mid_v - lo_v)) (slice L mid_v (hi_v - mid_v))
      (by simpa using hA_sorted)
      (by simpa using hB_sorted)
    simpa using hpm
  have hM_perm : M.Perm (slice L lo_v (mid_v - lo_v) ++ slice L mid_v (hi_v - mid_v)) := by
    rw [hM_eq]; exact List.merge_perm_append _
  have htake_hi :
      L.take lo_v ++ (slice L lo_v (mid_v - lo_v) ++ slice L mid_v (hi_v - mid_v)) =
        L.take hi_v := by
    rw [← List.append_assoc, take_append_slice L (by omega : lo_v ≤ mid_v),
      take_append_slice L (by omega : mid_v ≤ hi_v)]
  have haccM_perm : (acc ++ M).Perm (L.take hi_v) := by
    rw [← htake_hi]; exact hacc_perm.append hM_perm
  let u' := u2.set lo (u2.regs hi)
  have hex_mp : ExecWithin w mergePassBody u u' (18 * (hi_v - lo_v) + 14) := by
    unfold mergePassBody
    refine (hex_ms.seq (hex_in.seq ExecWithin.copy)).mono ?_
    rw [hout1]; omega
  refine ⟨u', 18 * (hi_v - lo_v) + 14, hex_mp, ?_, ?_⟩
  · refine ⟨by wram_simp [u', hu2z], by wram_simp [u', hu2o], by wram_simp [u', hu2n],
      by wram_simp [u', hu2kb], by wram_simp [u', hu2pb], by wram_simp [u', hu2bb],
      by wram_simp [u', hu2wtb], by wram_simp [u', hu2wb], by wram_simp [u', hu2fo],
      by wram_simp [u', hu2w], by wram_simp [u', hu2hi]; omega, ?_, ?_, acc ++ M,
      by simp only [List.length_append, hacc_len, hM_len]; wram_simp [u', hu2hi]; omega,
      ?_, by wram_simp [u', hu2hi]; exact haccM_perm, ?_⟩
    · intro hlt_hi
      wram_simp [u', hu2hi] at hlt_hi ⊢
      have hhi_full : hi_v = lo_v + 2 * W := by omega
      exact ⟨p + 1, by rw [hhi_full, hlo_eq, Nat.add_mul, Nat.one_mul]⟩
    · intro a ha
      rw [Block.mem_footprint, Block.Owns] at ha; dsimp only at ha
      have h1 : u2.mem a = u.mem a := hmod_u2 a (by
        rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
      exact h1.trans (hmodM_u a (by rw [Block.mem_footprint, Block.Owns]; dsimp only; omega))
    · intro j hj
      by_cases hj_lo : j < lo_v
      · have hj_acc : j < acc.length := by omega
        rw [List.getElem_append_left hj_acc]
        have h1 : u2.mem (bb + j) = u.mem (bb + j) := hmod_u2 (bb + j) (by
          rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
        exact h1.trans (hacc_mem j hj_acc)
      · have hj_ge : acc.length ≤ j := by omega
        have hd_lt : j - lo_v < M.length := by simp at hj; omega
        rw [List.getElem_append_right hj_ge]
        simpa [u', hacc_len, show bb + lo_v + (j - lo_v) = bb + j by omega] using
          hM_mem (j - lo_v) hd_lt
    · intro q
      rcases lt_trichotomy q p with hqp | rfl | hpq
      · have hle_acc : q * (2 * W) + 2 * W ≤ acc.length := by
          have hq1 : (q + 1) * (2 * W) ≤ p * (2 * W) :=
            Nat.mul_le_mul_right (2 * W) (Nat.succ_le_of_lt hqp)
          rw [Nat.succ_mul] at hq1; omega
        rw [slice_append_left hle_acc]
        exact hacc_chunks q
      · have hdrop_eq : slice (acc ++ M) (q * (2 * W)) (2 * W) = M := by
          rw [slice, show q * (2 * W) = acc.length by omega,
            List.drop_left' rfl, List.take_of_length_le (by omega)]
        rw [hdrop_eq]; exact hM_sorted
      · have hge_end : (acc ++ M).length ≤ q * (2 * W) := by
          have hp1 : (p + 1) * (2 * W) ≤ q * (2 * W) :=
            Nat.mul_le_mul_right (2 * W) (Nat.succ_le_of_lt hpq)
          rw [Nat.succ_mul] at hp1
          simp only [List.length_append, hacc_len, hM_len]
          omega
        rw [slice, List.drop_eq_nil_of_le hge_end, List.take_nil]
        exact .nil
  · have hlo_u' : u'.regs lo = hi_v := by wram_simp [u', hu2hi]
    rw [hlo_u']
    have hk1 : 18 * (hi_v - lo_v) + 16 ≤ 34 * (hi_v - lo_v) := by omega
    have hsub : 34 * (ws.length - hi_v) + 34 * (hi_v - lo_v) = 34 * (ws.length - lo_v) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega

private theorem mergeSortPerm_exec {w kb pb bb : ℕ} (ws : List ℕ) (x : Data 30)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hn : x.regs len = ws.length)
    (hkb : x.regs keyBase = kb) (hpb : x.regs permBase = pb) (hbb : x.regs bufBase = bb)
    (hws : Block.HoldsList kb ws x.mem)
    (hdisj1 : kb + ws.length ≤ pb) (hdisj2 : pb + ws.length ≤ bb)
    (hfit : Fits w (bb + 2 * ws.length + 1)) :
    ∃ y : Data 30, ExecWithin w mergeSortPerm x y
        (50 * ws.length * Nat.clog 2 ws.length + 5 * ws.length + 6) ∧
      ∃ perm : List ℕ,
        Modifies ((Block.mk pb (bb + ws.length - pb)).footprint) x.mem y.mem ∧
        Block.HoldsList pb perm y.mem ∧
        perm.Perm (List.range ws.length) ∧
        perm.Pairwise (fun a b => ws.getD a 0 ≤ ws.getD b 0) ∧
        y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs len = ws.length ∧
        y.regs keyBase = kb ∧ y.regs permBase = pb ∧ y.regs bufBase = bb ∧
        y.regs wtBase = x.regs wtBase ∧ y.regs workBase = x.regs workBase ∧
        y.regs finalOut = x.regs finalOut := by
  have hinit_body (y : Data 30)
      (hy : InitPermInv ws kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut)
        x.mem (y.regs step) y)
      (hlt : y.regs step < ws.length) :
      ∃ z, ExecWithin w initPermBody y z 3 ∧
        InitPermInv ws kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut)
          x.mem (y.regs step + 1) z ∧
        z.regs step = y.regs step + 1 := by
    obtain ⟨hyz, hyo, hyn, hykb, hypb, hybb, hywtb, hywb, hyfo, hmod, hpre⟩ := hy
    refine WP.exists_execWithin ?_
    unfold initPermBody
    wram_exec [hyo, hypb]
    refine ⟨⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hyn],
      by wram_simp [hykb], by wram_simp [hypb], by wram_simp [hybb],
      by wram_simp [hywtb], by wram_simp [hywb], by wram_simp [hyfo], ?_, ?_⟩, by wram_simp⟩
    · wram_simp [Data.write_mem]
      exact modifies_write (modifies_mono hmod le_rfl (by omega)) ⟨by omega, by omega⟩
    · intro j hj
      wram_simp [Data.write_mem]
      by_cases hjeq : j = y.regs step
      · subst hjeq; exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]; exact hpre j (by omega)
  have houter_body (y : Data 30)
      (hy : OuterInv ws kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) x.mem y)
      (hc : (Cond.lt wRun len).Holds y) :
      ∃ z, ExecWithin w outerPassBody y z (41 * ws.length + 7) ∧
        OuterInv ws kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) x.mem z ∧
        Nat.clog 2 ws.length - Nat.log 2 (z.regs wRun) <
          Nat.clog 2 ws.length - Nat.log 2 (y.regs wRun) := by
    obtain ⟨hyz, hyo, hyn, hykb, hypb, hybb, hywtb, hywb, hyfo, hmodO,
      pass, L, hpass_le, hwrun, hL_hold, hL_perm, hL_chunks⟩ := hy
    have hL_len : L.length = ws.length := by simpa using hL_perm.length_eq
    have hL_bound : ∀ v ∈ L, v < ws.length := fun v hv => List.mem_range.mp (hL_perm.subset hv)
    let W := 2 ^ pass
    have hW_pos : 0 < W := Nat.two_pow_pos pass
    have hW_lt : W < ws.length := by simpa only [Cond.holds_lt, hwrun, hyn] using hc
    have hpass_lt : pass < Nat.clog 2 ws.length :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hW_lt
    have hmid_body (u : Data 30)
        (hu : MidInv ws L kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) W y.mem u)
        (hcu : (Cond.lt lo len).Holds u) :
        ∃ u' T_m, ExecWithin w mergePassBody u u' T_m ∧
          MidInv ws L kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) W y.mem u' ∧
          T_m + 2 + 34 * (ws.length - u'.regs lo) ≤ 34 * (ws.length - u.regs lo) := by
      have hu_ws : Block.HoldsList kb ws u.mem := by
        refine hws.frame fun a ha1 ha2 => ?_
        have h1 : u.mem a = y.mem a := hu.mod a (by
          rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
        have h2 : y.mem a = x.mem a := hmodO a (by
          rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
        exact h1.trans h2
      have hu_L : Block.HoldsList pb L u.mem :=
        hL_hold.frame fun a ha1 ha2 => hu.mod a (by
          rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
      exact mergePassBody_exec ws L y.mem hL_len hL_bound hL_chunks hW_pos hW_lt hdisj1 hdisj2 hfit
        u hu_ws hu_L hu hcu
    refine WP.exists_execWithin ?_
    unfold outerPassBody
    wram_exec
    refine WP.of_spec
      (ExecWithin.loop_potential (cond := .lt lo len) (body := mergePassBody)
        (MidInv ws L kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) W y.mem)
        (fun u => 34 * (ws.length - u.regs lo)) hmid_body ?_) ?_
    · refine ⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hyn],
        by wram_simp [hykb], by wram_simp [hypb], by wram_simp [hybb],
        by wram_simp [hywtb], by wram_simp [hywb], by wram_simp [hyfo],
        by wram_simp [hwrun]; rfl, by wram_simp; omega,
        fun _ => ⟨0, by wram_simp; simp⟩,
        Modifies.refl _ _, [], by wram_simp; rfl,
        fun j hj => absurd hj (Nat.not_lt_zero j),
        by wram_simp; simp, fun q => by simp [slice]⟩
    · rintro uM ⟨hIM, hstopM⟩
      obtain ⟨huMz, huMo, huMn, huMkb, huMpb, huMbb, huMwtb, huMwb, huMfo, huMw,
        huMlo_le, _, hmodM_end, L', hL'_len, hL'_mem, hL'_perm, hL'_chunks⟩ := hIM
      have hlo_end : uM.regs lo = ws.length := by
        simp only [Cond.holds_lt, huMn] at hstopM; omega
      rw [hlo_end, ← hL_len, List.take_length] at hL'_perm
      have hL'_perm_n : L'.Perm (List.range ws.length) := hL'_perm.trans hL_perm
      have hL'_len_n : L'.length = ws.length := by rw [hL'_len, hlo_end]
      have hcp_body (v : Data 30)
          (hv : CopyBackInv ws L' kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut)
            W uM.mem (v.regs step) v)
          (hlt_cp : v.regs step < ws.length) :
          ∃ v', ExecWithin w copyBackBody v v' 5 ∧
            CopyBackInv ws L' kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut)
              W uM.mem (v.regs step + 1) v' ∧
            v'.regs step = v.regs step + 1 := by
        obtain ⟨hvz, hvo, hvn, hvkb, hvpb, hvbb, hvwtb, hvwb, hvfo, hvw, hmod_cp, hpre_cp⟩ := hv
        have hs_lt : v.regs step < L'.length := by omega
        have hread_buf : v.mem (bb + v.regs step) = L'[v.regs step] := by
          have h1 : v.mem (bb + v.regs step) = uM.mem (bb + v.regs step) :=
            hmod_cp (bb + v.regs step) (by
              rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
          exact h1.trans (hL'_mem _ hs_lt)
        refine WP.exists_execWithin ?_
        unfold copyBackBody
        wram_exec [hvo, hvpb, hvbb, hread_buf]
        refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
          by wram_simp [hvkb], by wram_simp [hvpb], by wram_simp [hvbb],
          by wram_simp [hvwtb], by wram_simp [hvwb], by wram_simp [hvfo],
          by wram_simp [hvw], ?_, ?_⟩, by wram_simp⟩
        · wram_simp [Data.write_mem]
          exact modifies_write (modifies_mono hmod_cp le_rfl (by omega)) ⟨by omega, by omega⟩
        · intro j hj hjL
          wram_simp [Data.write_mem]
          by_cases hjeq : j = v.regs step
          · subst hjeq; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega)]; exact hpre_cp j (by omega) hjL
      wram_exec
      refine WP.of_spec
        (ExecWithin.loop_count (index := step) (limit := len) (N := ws.length) (T := 5)
          (CopyBackInv ws L' kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) W uM.mem)
          (fun _ hq => hq.len_eq) hcp_body (by wram_simp; omega) ?_) ?_
      · refine ⟨by wram_simp [huMz], by wram_simp [huMo], by wram_simp [huMn],
          by wram_simp [huMkb], by wram_simp [huMpb], by wram_simp [huMbb],
          by wram_simp [huMwtb], by wram_simp [huMwb], by wram_simp [huMfo],
          by wram_simp [huMw], Modifies.refl _ _,
          fun _ hj => by wram_simp at hj⟩
      · rintro uC ⟨hPC, _⟩
        obtain ⟨huCz, huCo, huCn, huCkb, huCpb, huCbb, huCwtb, huCwb, huCfo, huCw,
          hmod_cp_end, hpre_cp_end⟩ := hPC
        wram_exec [huCw]
        have hpow_succ : W + W = 2 ^ (pass + 1) := by simp [W, Nat.pow_succ]; omega
        refine ⟨⟨by wram_simp [huCz], by wram_simp [huCo],
          by wram_simp [huCn], by wram_simp [huCkb], by wram_simp [huCpb],
          by wram_simp [huCbb], by wram_simp [huCwtb], by wram_simp [huCwb],
          by wram_simp [huCfo], ?_, pass + 1, L', by omega,
          by wram_simp [hpow_succ], ?_, hL'_perm_n, ?_⟩, ?_⟩
        · intro a ha
          rw [Block.mem_footprint, Block.Owns] at ha; dsimp only at ha
          wram_simp
          have h1 : uC.mem a = uM.mem a := hmod_cp_end a (by
            rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
          have h2 : uM.mem a = y.mem a := hmodM_end a (by
            rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
          have h3 : y.mem a = x.mem a := hmodO a (by
            rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
          exact h1.trans (h2.trans h3)
        · intro i
          wram_simp
          have hi_L' : i.val < L'.length := i.isLt
          exact hpre_cp_end i.val (by omega) hi_L'
        · intro q
          simpa [show 2 ^ (pass + 1) = 2 * W by simp [W, Nat.pow_succ]; omega] using hL'_chunks q
        · wram_simp [hpow_succ, hwrun, Nat.log_pow Nat.one_lt_two]
          omega
  refine WP.exists_execWithin ?_
  unfold mergeSortPerm
  wram_exec
  refine WP.of_spec
    (ExecWithin.loop_count (index := step) (limit := len) (N := ws.length) (T := 3)
      (InitPermInv ws kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) x.mem)
      (fun _ hu => hu.len_eq) hinit_body (by wram_simp; omega) ?_) ?_
  · refine ⟨by wram_simp [hz], by wram_simp [ho], by wram_simp [hn],
      by wram_simp [hkb], by wram_simp [hpb], by wram_simp [hbb],
      by wram_simp, by wram_simp, by wram_simp, Modifies.refl _ _,
      fun _ hj => by wram_simp at hj⟩
  · rintro yI ⟨hPI, _⟩
    obtain ⟨hyIz, hyIo, hyIn, hyIkb, hyIpb, hyIbb, hyIwtb, hyIwb, hyIfo, hmodI, hpreI⟩ := hPI
    wram_exec
    refine WP.of_spec
      (ExecWithin.loop_invariant (cond := .lt wRun len) (body := outerPassBody)
        (OuterInv ws kb pb bb (x.regs wtBase) (x.regs workBase) (x.regs finalOut) x.mem)
        (fun y => Nat.clog 2 ws.length - Nat.log 2 (y.regs wRun)) (T := 41 * ws.length + 7)
        houter_body ?_) ?_
    · refine ⟨by wram_simp [hyIz], by wram_simp [hyIo], by wram_simp [hyIn],
        by wram_simp [hyIkb], by wram_simp [hyIpb], by wram_simp [hyIbb],
        by wram_simp [hyIwtb], by wram_simp [hyIwb], by wram_simp [hyIfo], ?_,
        0, List.range ws.length, Nat.zero_le _, by wram_simp; rfl, ?_, List.Perm.refl _, ?_⟩
      · intro a ha
        rw [Block.mem_footprint, Block.Owns] at ha; dsimp only at ha
        exact hmodI a (by rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
      · intro i
        have hi_lt : i.val < ws.length := by simpa using i.isLt
        change yI.mem (pb + i.val) = (List.range ws.length)[i.val]
        simp [hpreI i.val hi_lt]
      · intro q
        refine pairwise_of_length_le_one ?_
        simp [slice]
    · rintro yF ⟨hIF, hstopF⟩
      obtain ⟨hyFz, hyFo, hyFn, hyFkb, hyFpb, hyFbb, hyFwtb, hyFwb, hyFfo, hmodF,
        pass, perm, _, hwrunF, hperm_hold, hperm_range, hperm_chunks⟩ := hIF
      have hge_n : ws.length ≤ 2 ^ pass := by
        simp only [Cond.holds_lt, hwrunF, hyFn] at hstopF; omega
      have hperm_len : perm.length = ws.length := by simpa using hperm_range.length_eq
      have hperm_sorted : perm.Pairwise (fun a b => ws.getD a 0 ≤ ws.getD b 0) := by
        have h0 := hperm_chunks 0
        simpa [slice, List.take_of_length_le (hperm_len ▸ hge_n)] using h0
      refine ⟨?_, perm, hmodF, hperm_hold, hperm_range, hperm_sorted,
        hyFz, hyFo, hyFn, hyFkb, hyFpb, hyFbb, hyFwtb, hyFwb, hyFfo⟩
      wram_simp
      simp only [Nat.log_one_right, Nat.sub_zero]
      have h1 : Nat.clog 2 ws.length * (41 * ws.length + 7 + 2) ≤
          Nat.clog 2 ws.length * (50 * ws.length) := by
        rcases eq_or_ne ws.length 0 with h0 | hpos
        · simp [h0]
        · exact Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_comm (Nat.clog 2 ws.length) (50 * ws.length)] at h1
      omega

/-! ## End-to-End `O(n log n)` Word-RAM Huffman on Unsorted Weights -/

private def huffmanSetup : Code .standard 30 := ram[
  zero ← #0;
  one ← #1;
  len ← *zero;
  keyBase ← #1;
  permBase ← len + one;
  bufBase ← permBase + len;
  wtBase ← bufBase + len;
  workBase ← wtBase + len;
  tmp1 ← len + len;
  tmp1 ← tmp1 + tmp1;
  tmp1 ← tmp1 + len;
  tmp1 ← tmp1 + one;
  finalOut ← workBase + tmp1 ]

private def gatherBody : Code .standard 30 := ram[
  addr ← permBase + step;
  tmp1 ← *addr;
  addr ← keyBase + tmp1;
  tmp2 ← *addr;
  addr ← wtBase + step;
  *addr ← tmp2;
  step ← step + one ]

private def scatterBody : Code .standard 30 := ram[
  addr ← permBase + step;
  tmp1 ← *addr;
  tmp2 ← outPtr + one;
  addr ← tmp2 + step;
  tmp3 ← *addr;
  tmp2 ← finalOut + one;
  addr ← tmp2 + tmp1;
  *addr ← tmp3;
  step ← step + one ]

private def huffmanPostSort : Code .standard 30 :=
  .seq (ram[ step ← #0; while step < len do [ ⟪gatherBody⟫ ] ])
    (.seq twoQueueCore
      (ram[ *finalOut ← len; step ← #0; while step < len do [ ⟪scatterBody⟫ ]; outPtr ← finalOut ]))

/-- Structured `O(n log n)` Word-RAM Huffman builder from arbitrary unsorted input
`State.init ws`. -/
def huffmanCode : Code .standard 30 :=
  .seq huffmanSetup (.seq mergeSortPerm huffmanPostSort)

private structure GathInv (ws sws : List ℕ) (kb pb wtb wb fo : ℕ)
    (yS_mem : ℕ → ℕ) (s : ℕ) (v : Data 30) : Prop where
  zero_eq : v.regs zero = 0
  one_eq : v.regs one = 1
  len_eq : v.regs len = ws.length
  keyBase_eq : v.regs keyBase = kb
  permBase_eq : v.regs permBase = pb
  wtBase_eq : v.regs wtBase = wtb
  workBase_eq : v.regs workBase = wb
  finalOut_eq : v.regs finalOut = fo
  mod : Modifies (Block.mk wtb ws.length).footprint yS_mem v.mem
  gathered : ∀ j : ℕ, (hj : j < s) → (hj' : j < sws.length) → v.mem (wtb + j) = sws[j]

private structure ScatInv (ws perm sortedLens : List ℕ) (pb tqOut fo : ℕ)
    (yQ_mem : ℕ → ℕ) (s : ℕ) (v : Data 30) : Prop where
  zero_eq : v.regs zero = 0
  one_eq : v.regs one = 1
  len_eq : v.regs len = ws.length
  permBase_eq : v.regs permBase = pb
  outPtr_eq : v.regs outPtr = tqOut
  finalOut_eq : v.regs finalOut = fo
  mem_fo : v.mem fo = ws.length
  mod : Modifies (Block.mk fo (ws.length + 1)).footprint yQ_mem v.mem
  written : ∀ j : ℕ, (hj : j < s) → (hjp : j < perm.length) →
    v.mem (fo + 1 + perm[j]) = sortedLens.getD j 0

private theorem gather_exec {w kb pb wtb wb fo : ℕ} (ws perm sws : List ℕ) (yS : Data 30)
    (hySz : yS.regs zero = 0) (hySo : yS.regs one = 1) (hySn : yS.regs len = ws.length)
    (hySkb : yS.regs keyBase = kb) (hySpb : yS.regs permBase = pb)
    (hySwtb : yS.regs wtBase = wtb) (hySwb : yS.regs workBase = wb)
    (hySfo : yS.regs finalOut = fo)
    (hsws_def : sws = perm.map (ws.getD · 0))
    (hperm_len : perm.length = ws.length)
    (hperm_bound : ∀ v ∈ perm, v < ws.length)
    (hperm_hold : Block.HoldsList pb perm yS.mem)
    (hyS_ws : Block.HoldsList kb ws yS.mem)
    (hdisj_kb : kb + ws.length ≤ wtb)
    (hdisj_pb : pb + ws.length ≤ wtb)
    (hfit : Fits w (wtb + ws.length)) :
    ∃ yG : Data 30,
      ExecWithin w (ram[ step ← #0; while step < len do [ ⟪gatherBody⟫ ] ]) yS yG
        (9 * ws.length + 3) ∧
      GathInv ws sws kb pb wtb wb fo yS.mem ws.length yG := by
  have hgath_body (v : Data 30)
      (hv : GathInv ws sws kb pb wtb wb fo yS.mem (v.regs step) v)
      (hlt : v.regs step < ws.length) :
      ∃ v', ExecWithin w gatherBody v v' 7 ∧
        GathInv ws sws kb pb wtb wb fo yS.mem (v.regs step + 1) v' ∧
        v'.regs step = v.regs step + 1 := by
    obtain ⟨hvz, hvo, hvn, hvkb, hvpb, hvwtb, hvwb, hvfo, hmodG, hpreG⟩ := hv
    have hv_perm : Block.HoldsList pb perm v.mem :=
      hperm_hold.frame fun a ha1 ha2 => Modifies.block_iff.mp hmodG a (by dsimp only; omega)
    have hv_ws : Block.HoldsList kb ws v.mem :=
      hyS_ws.frame fun a ha1 ha2 => Modifies.block_iff.mp hmodG a (by dsimp only; omega)
    obtain ⟨hread_p, hp_lt_n, hread_w⟩ :=
      holdsList_read_key hv_ws hv_perm hperm_bound (by omega : v.regs step < perm.length)
    refine WP.exists_execWithin ?_
    unfold gatherBody
    wram_exec [hvo, hvkb, hvpb, hvwtb, hread_p, hread_w]
    refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
      by wram_simp [hvkb], by wram_simp [hvpb], by wram_simp [hvwtb],
      by wram_simp [hvwb], by wram_simp [hvfo],
      by wram_simp [Data.write_mem]; exact modifies_write hmodG ⟨by omega, by omega⟩,
      ?_⟩, by wram_simp⟩
    · intro j hj hj'
      wram_simp [Data.write_mem]
      by_cases hjeq : j = v.regs step
      · subst hjeq; rw [Function.update_self]; simp [hsws_def]
      · rw [Function.update_of_ne (by omega)]; exact hpreG j (by omega) hj'
  refine WP.exists_execWithin ?_
  wram_exec
  refine WP.of_spec
    (ExecWithin.loop_count (index := step) (limit := len) (N := ws.length) (T := 7)
      (GathInv ws sws kb pb wtb wb fo yS.mem)
      (fun _ hq => hq.len_eq) hgath_body (by wram_simp; omega) ?_) ?_
  · refine ⟨by wram_simp [hySz], by wram_simp [hySo], by wram_simp [hySn],
      by wram_simp [hySkb], by wram_simp [hySpb],
      by wram_simp [hySwtb], by wram_simp [hySwb],
      by wram_simp [hySfo], Modifies.refl _ _,
      fun _ hj => by wram_simp at hj⟩
  · rintro yG ⟨hPG, _⟩
    exact ⟨by wram_simp; omega, hPG⟩

private theorem scatter_exec {w pb tqOut fo : ℕ} (ws perm sortedLens : List ℕ) (yQ : Data 30)
    (hyQz : yQ.regs zero = 0) (hyQo : yQ.regs one = 1) (hyQn : yQ.regs len = ws.length)
    (hyQpb : yQ.regs permBase = pb) (hyQout : yQ.regs outPtr = tqOut)
    (hyQfo : yQ.regs finalOut = fo)
    (hperm_len : perm.length = ws.length)
    (hperm_bound : ∀ v ∈ perm, v < ws.length)
    (hperm_nodup : perm.Nodup)
    (hyQ_perm : Block.HoldsList pb perm yQ.mem)
    (hsorted_out : outputList yQ.mem tqOut = sortedLens)
    (hsorted_len : sortedLens.length = ws.length)
    (hpb_lt : pb + ws.length ≤ fo)
    (htqOut_lt : tqOut + ws.length < fo)
    (hfit : Fits w (fo + 1 + ws.length)) :
    ∃ yF : Data 30,
      ExecWithin w
        (ram[ *finalOut ← len; step ← #0;
              while step < len do [ ⟪scatterBody⟫ ]; outPtr ← finalOut ])
        yQ yF (11 * ws.length + 5) ∧
      yF.regs outPtr = fo ∧ yF.mem fo = ws.length ∧
      (∀ j : ℕ, (hj : j < ws.length) → (hjp : j < perm.length) →
        yF.mem (fo + 1 + perm[j]) = sortedLens.getD j 0) := by
  have hscat_body (v : Data 30)
      (hv : ScatInv ws perm sortedLens pb tqOut fo yQ.mem (v.regs step) v)
      (hlt : v.regs step < ws.length) :
      ∃ v', ExecWithin w scatterBody v v' 9 ∧
        ScatInv ws perm sortedLens pb tqOut fo yQ.mem (v.regs step + 1) v' ∧
        v'.regs step = v.regs step + 1 := by
    obtain ⟨hvz, hvo, hvn, hvpb, hvout, hvfo, hv_mfo, hmodSc, hpreSc⟩ := hv
    have hs_p : v.regs step < perm.length := by omega
    have hread_p : v.mem (pb + v.regs step) = perm[v.regs step] := by
      have h1 : v.mem (pb + v.regs step) = yQ.mem (pb + v.regs step) :=
        hmodSc (pb + v.regs step) (by
          rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
      exact h1.trans (hyQ_perm.get _ hs_p)
    have hp_lt_n : perm[v.regs step] < ws.length := hperm_bound _ (List.getElem_mem hs_p)
    have hread_d : v.mem (tqOut + 1 + v.regs step) = sortedLens.getD (v.regs step) 0 := by
      have h1 : v.mem (tqOut + 1 + v.regs step) = yQ.mem (tqOut + 1 + v.regs step) :=
        hmodSc (tqOut + 1 + v.regs step) (by
          rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
      have hs_sl : v.regs step < sortedLens.length := by omega
      rw [h1, ← hsorted_out, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hsorted_out]; exact hs_sl), getElem_outputList]
      rfl
    refine WP.exists_execWithin ?_
    unfold scatterBody
    wram_exec [hvo, hvpb, hvout, hvfo, hread_p, hread_d]
    refine ⟨⟨by wram_simp [hvz], by wram_simp [hvo], by wram_simp [hvn],
      by wram_simp [hvpb], by wram_simp [hvout], by wram_simp [hvfo], ?_, ?_, ?_⟩,
      by wram_simp⟩
    · wram_simp [Data.write_mem]
      rw [Function.update_of_ne (by omega)]
      exact hv_mfo
    · wram_simp [Data.write_mem]
      exact modifies_write hmodSc ⟨by omega, by omega⟩
    · intro j hj hjp
      wram_simp [Data.write_mem]
      by_cases hjeq : j = v.regs step
      · subst hjeq; exact Function.update_self _ _ _
      · have hne_idx : perm[j] ≠ perm[v.regs step] := fun heq =>
          hjeq ((hperm_nodup.getElem_inj_iff (i := j) (j := v.regs step)).mp heq)
        rw [Function.update_of_ne (by omega)]
        exact hpreSc j (by omega) hjp
  refine WP.exists_execWithin ?_
  wram_exec [hyQn, hyQpb, hyQfo]
  refine WP.of_spec
    (ExecWithin.loop_count (index := step) (limit := len) (N := ws.length) (T := 9)
      (ScatInv ws perm sortedLens pb tqOut fo yQ.mem)
      (fun _ hq => hq.len_eq) hscat_body (by wram_simp; omega) ?_) ?_
  · refine ⟨by wram_simp [hyQz], by wram_simp [hyQo], by wram_simp [hyQn],
      by wram_simp [hyQpb], by wram_simp [hyQout], by wram_simp [hyQfo],
      by wram_simp [Data.write_mem]; exact Function.update_self _ _ _,
      by
        wram_simp [Data.write_mem]
        exact Modifies.write_of_owns (base := fo) (n := ws.length + 1)
          ⟨le_rfl, by omega⟩ ws.length,
      fun _ hj => by wram_simp at hj⟩
  · rintro yF ⟨hPF, _⟩
    obtain ⟨_, _, _, _, _, hyFfo, hyF_mfo, _, hscat_done⟩ := hPF
    wram_exec [hyFfo]
    exact ⟨by wram_simp, hyF_mfo, hscat_done⟩

private theorem huffmanSetup_exec {w : ℕ} (ws : List ℕ)
    (hfit_mem : Fits w (10 * ws.length + 3)) :
    ∃ x₁ : Data 30, ExecWithin w huffmanSetup (Data.init ws) x₁ 13 ∧
      x₁.mem = (Data.init ws : Data 30).mem ∧
      x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧ x₁.regs len = ws.length ∧
      x₁.regs keyBase = 1 ∧ x₁.regs permBase = ws.length + 1 ∧
      x₁.regs bufBase = 2 * ws.length + 1 ∧
      x₁.regs wtBase = 3 * ws.length + 1 ∧ x₁.regs workBase = 4 * ws.length + 1 ∧
      x₁.regs finalOut = 9 * ws.length + 2 := by
  refine WP.exists_execWithin ?_
  unfold huffmanSetup
  wram_exec [Data.init_regs, Data.init_mem_zero]
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp; omega, by wram_simp; omega,
    by wram_simp; omega, by wram_simp; omega⟩

private theorem transport_unsorted_huffman (ws perm sws sortedLens finalLens : List ℕ)
    (hne : ws ≠ [])
    (hperm_range : perm.Perm (List.range ws.length))
    (hperm_len : perm.length = ws.length)
    (hperm_bound : ∀ v ∈ perm, v < ws.length)
    (hperm_nodup : perm.Nodup)
    (hsws_def : sws = perm.map (ws.getD · 0))
    (hsws_len : sws.length = ws.length)
    (hfl_len : finalLens.length = ws.length)
    (hfl_perm : ∀ j : ℕ, (hj : j < ws.length) → (hjp : j < perm.length) →
      finalLens.getD perm[j] 0 = sortedLens.getD j 0)
    (T_s : CodeTree (Fin sws.length))
    (hTs_build : IsHuffmanBuild (symWeight sws) ((List.finRange sws.length).map .leaf) T_s)
    (hTs_perm : T_s.leaves.Perm (List.finRange sws.length))
    (hTs_enc : ∀ j : Fin sws.length,
      ∃ c, T_s.encodeSym j = some c ∧ c.length = sortedLens.getD j.val 0) :
    ∃ T : CodeTree (Fin ws.length),
      IsHuffmanBuild (symWeight ws) ((List.finRange ws.length).map .leaf) T ∧
      T.leaves.Perm (List.finRange ws.length) ∧
      (∀ i : Fin ws.length, ∃ c, T.encodeSym i = some c ∧ c.length = finalLens.getD i.val 0) ∧
      (∀ code : Fin ws.length → List Bool,
        Set.InjOn code {a | a ∈ List.finRange ws.length} →
        InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ List.finRange ws.length}) →
        T.weightedPathLength (symWeight ws) ≤
          ((List.finRange ws.length).map fun a => (code a).length * symWeight ws a).sum) := by
  let permFn : Fin sws.length → Fin ws.length := fun j =>
    ⟨perm[j.val]'(by omega), hperm_bound _ (List.getElem_mem (by omega))⟩
  have hpermFn_inj : Function.Injective permFn := by
    intro a b hab
    have hv : perm[a.val]'(by omega) = perm[b.val]'(by omega) := congrArg Fin.val hab
    exact Fin.ext ((hperm_nodup.getElem_inj_iff).mp hv)
  have hweight_permFn : ∀ j : Fin sws.length, symWeight ws (permFn j) = symWeight sws j := by
    intro j
    have hj_n : perm[j.val]'(by omega) < ws.length :=
      hperm_bound _ (List.getElem_mem (by omega))
    simp [symWeight, permFn, hsws_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_n]
  let T : CodeTree (Fin ws.length) := T_s.map permFn
  have hmap_fin_perm :
      ((List.finRange sws.length).map permFn).Perm (List.finRange ws.length) := by
    refine (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange _).map hpermFn_inj) (List.nodup_finRange _)).mpr fun i => ?_
    simp only [List.mem_finRange, iff_true, List.mem_map]
    have hi_in : i.val ∈ perm := hperm_range.symm.subset (List.mem_range.mpr i.isLt)
    obtain ⟨j, hj, hpj⟩ := List.mem_iff_getElem.mp hi_in
    exact ⟨⟨j, by omega⟩, trivial, Fin.ext hpj⟩
  have hleaf_perm :
      (((List.finRange sws.length).map .leaf).map (CodeTree.map permFn)).Perm
        ((List.finRange ws.length).map .leaf) := by
    simpa [List.map_map, Function.comp_def, CodeTree.map] using
      hmap_fin_perm.map CodeTree.leaf
  have hT_build : IsHuffmanBuild (symWeight ws) ((List.finRange ws.length).map .leaf) T :=
    IsHuffmanBuild.of_perm hleaf_perm.symm (isHuffmanBuild_map hweight_permFn hTs_build)
  have hT_leaves : T.leaves.Perm (List.finRange ws.length) := by
    rw [CodeTree.leaves_map]
    exact (hTs_perm.map permFn).trans hmap_fin_perm
  refine ⟨T, hT_build, hT_leaves, ?_, fun code hinj hud => ?_⟩
  · intro i
    have hi_mem : i ∈ (List.finRange sws.length).map permFn :=
      hmap_fin_perm.symm.subset (List.mem_finRange i)
    rcases List.mem_map.mp hi_mem with ⟨j, _, rfl⟩
    obtain ⟨c, hc_enc, hc_len⟩ := hTs_enc j
    have hT_enc_j : T.encodeSym (permFn j) = some c := by
      simpa [T] using (encodeSym_map_of_injective hpermFn_inj T_s j).trans hc_enc
    have hfl_j : finalLens.getD (permFn j).val 0 = sortedLens.getD j.val 0 :=
      hfl_perm j.val (by omega) (by omega)
    exact ⟨c, hT_enc_j, hc_len.trans hfl_j.symm⟩
  · have hne_fin : (List.finRange ws.length) ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp [(List.length_pos_iff.mpr hne).ne'] at this
    exact hT_build.weightedPathLength_le_of_isUniquelyDecodable
      hne_fin (List.nodup_finRange _) (fun _ _ => Nat.zero_le _) hinj hud

private theorem huffmanCode_exec {w : ℕ} (ws : List ℕ)
    (hfit_mem : Fits w (10 * ws.length + 3))
    (hfit_wpl : Fits w (ws.length * ws.sum)) :
    ∃ (yF : Data 30) (finalLens : List ℕ),
      ExecWithin w huffmanCode (Data.init ws) yF
        (50 * ws.length * Nat.clog 2 ws.length + 84 * ws.length + 49) ∧
      yF.regs outPtr = 9 * ws.length + 2 ∧
      outputList yF.mem (yF.regs outPtr) = finalLens ∧
      finalLens.length = ws.length ∧
      (ws ≠ [] →
        ∃ T : CodeTree (Fin ws.length),
          IsHuffmanBuild (symWeight ws) ((List.finRange ws.length).map .leaf) T ∧
          T.leaves.Perm (List.finRange ws.length) ∧
          (∀ i : Fin ws.length, ∃ c, T.encodeSym i = some c ∧ c.length = finalLens.getD i.val 0) ∧
          (∀ code : Fin ws.length → List Bool,
            Set.InjOn code {a | a ∈ List.finRange ws.length} →
            InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ List.finRange ws.length}) →
            T.weightedPathLength (symWeight ws) ≤
              ((List.finRange ws.length).map fun a => (code a).length * symWeight ws a).sum)) := by
  have hinit_ws : Block.HoldsList 1 ws (Data.init ws : Data 30).mem :=
    (outputList_eq_iff.mp (outputList_init ws)).2
  obtain ⟨x₁, hex_setup, hmem1, hz1, ho1, hn1, hkb1, hpb1, hbb1, hwtb1, hwb1, hfo1⟩ :=
    huffmanSetup_exec ws hfit_mem
  obtain ⟨yS, hex_sort, perm, hmodS, hperm_hold, hperm_range, hperm_sorted,
    hySz, hySo, hySn, hySkb, hySpb, _, hySwtb, hySwb, hySfo⟩ :=
    mergeSortPerm_exec ws x₁ hz1 ho1 hn1 hkb1 hpb1 hbb1
      (hmem1 ▸ hinit_ws) (by omega) (by omega) (hfit_mem.of_le (by omega))
  have hperm_len : perm.length = ws.length := by simpa using hperm_range.length_eq
  have hperm_bound : ∀ v ∈ perm, v < ws.length := fun v hv =>
    List.mem_range.mp (hperm_range.subset hv)
  have hperm_nodup : perm.Nodup := hperm_range.nodup_iff.mpr List.nodup_range
  have hyS_ws : Block.HoldsList 1 ws yS.mem :=
    (hmem1 ▸ hinit_ws).frame fun a ha1 ha2 => hmodS a (by
      rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  obtain ⟨sws, hsws_def⟩ : ∃ s : List ℕ, s = perm.map (ws.getD · 0) := ⟨_, rfl⟩
  have hsws_len : sws.length = ws.length := by simp [hsws_def, hperm_len]
  have hsws_perm : sws.Perm ws := by
    have hmap_range : (List.range ws.length).map (ws.getD · 0) = ws := by
      apply List.ext_getElem (by simp)
      intro j _ hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [hsws_def]
    exact (hperm_range.map (ws.getD · 0)).trans (by rw [hmap_range])
  have hsws_sum : sws.sum = ws.sum := hsws_perm.sum_eq
  have hsws_sorted : sws.Pairwise (· ≤ ·) := by
    rw [hsws_def]
    exact List.Pairwise.map _ (fun _ _ h => h) hperm_sorted
  obtain ⟨yG, hex_gath, hyGz, hyGo, hyGn, _, hyGpb, hyGwtb, hyGwb, hyGfo, hmodG_end,
    hsws_mem⟩ :=
    gather_exec ws perm sws yS hySz hySo hySn hySkb hySpb
      (hySwtb.trans hwtb1) (hySwb.trans hwb1) (hySfo.trans hfo1)
      hsws_def hperm_len hperm_bound hperm_hold hyS_ws
      (by omega) (by omega) (hfit_mem.of_le (by omega))
  have hyG_sws : Block.HoldsList (3 * ws.length + 1) sws yG.mem := by
    intro i
    have hi : i.val < sws.length := i.isLt
    exact hsws_mem i.val (by omega) hi
  have hyG_perm : Block.HoldsList (ws.length + 1) perm yG.mem :=
    hperm_hold.frame fun a ha1 ha2 => hmodG_end a (by
      rw [Block.mem_footprint, Block.Owns]; dsimp only; omega)
  obtain ⟨yQ, hex_tq, sortedLens, hmodQ, hyQz, hyQo, hyQn, hyQpb, hyQfo, hyQout,
    hsorted_out, hsorted_len, _, _, hQ_pos⟩ :=
    twoQueueCore_exec sws yG hyGz hyGo (by rw [hyGn, hsws_len]) hyGwtb hyGwb hyG_sws
      (by omega) (hfit_mem.of_le (by rw [hsws_len]; omega)) (by rwa [hsws_len, hsws_sum])
  have hyQ_perm : Block.HoldsList (ws.length + 1) perm yQ.mem :=
    hyG_perm.frame fun a ha1 ha2 => hmodQ a (by
      rw [Block.mem_footprint, Block.Owns]; dsimp only; rw [hsws_len]; omega)
  have htqOut_lt : yQ.regs outPtr + ws.length < 9 * ws.length + 2 := by
    rw [hyQout]; split <;> omega
  obtain ⟨yF, hex_scat, hyF_out, hyF_mfo, hscat_done⟩ :=
    scatter_exec ws perm sortedLens yQ hyQz hyQo (hyQn.trans hsws_len)
      (hyQpb.trans hyGpb) rfl (hyQfo.trans hyGfo)
      hperm_len hperm_bound hperm_nodup hyQ_perm hsorted_out (hsorted_len.trans hsws_len)
      (by omega) htqOut_lt (hfit_mem.of_le (by omega))
  have hex_all : ExecWithin w huffmanCode (Data.init ws) yF
      (50 * ws.length * Nat.clog 2 ws.length + 84 * ws.length + 49) := by
    unfold huffmanCode huffmanPostSort
    refine (hex_setup.seq (hex_sort.seq (hex_gath.seq (hex_tq.seq hex_scat)))).mono ?_
    rw [hsws_len]
    omega
  obtain ⟨finalLens, hfl_def⟩ : ∃ l : List ℕ, l = outputList yF.mem (9 * ws.length + 2) :=
    ⟨_, rfl⟩
  have hfl_len : finalLens.length = ws.length := by simp [hfl_def, hyF_mfo]
  have hout_eq : outputList yF.mem (yF.regs outPtr) = finalLens := by rw [hyF_out, hfl_def]
  refine ⟨yF, finalLens, hex_all, hyF_out, hout_eq, hfl_len, fun hne => ?_⟩
  have hsws_ne : sws ≠ [] := by
    intro h0
    have := congrArg List.length h0
    simp [hsws_len, (List.length_pos_iff.mpr hne).ne'] at this
  obtain ⟨T_s, _, hTs_build, hTs_perm, _, hTs_enc⟩ := hQ_pos hsws_ne hsws_sorted
  refine transport_unsorted_huffman ws perm sws sortedLens finalLens hne
    hperm_range hperm_len hperm_bound hperm_nodup hsws_def hsws_len hfl_len
    (fun j hj hjp => ?_) T_s hTs_build hTs_perm hTs_enc
  have hj_lt : perm[j] < finalLens.length := by
    rw [hfl_len]; exact hperm_bound _ (List.getElem_mem hjp)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt]
  simp only [hfl_def, getElem_outputList]
  exact hscat_done j hj hjp

/-- Compiled `O(n log n)` Word-RAM Huffman program returning the codeword-length list via
`ExecutesList`. -/
def huffmanProgram : Program .standard 30 := huffmanCode.program outPtr

/-- **`O(n log n)` Word-RAM Huffman Construction from Unsorted Weights**
([Huffman1952]; [VanLeeuwen1976]; [CLRS2009], Section 16.3): on any list `ws : List ℕ` of
`n = ws.length` nonnegative symbol weights in `State.init ws` at word width `w` satisfying
`Fits w (10 * n + 3)` and `Fits w (n * ws.sum)`, `huffmanProgram` halts within
`50 * n * Nat.clog 2 n + 84 * n + 50` instructions outputting a codeword-length list `lens`
(`lens.length = n`) via `ExecutesList` certified by `IsHuffmanBuild` and optimal among all
injective `IsUniquelyDecodable` (and `IsPrefixFree`) binary codes. -/
theorem huffmanProgram_spec {w : ℕ} (ws : List ℕ)
    (hfit_mem : Fits w (10 * ws.length + 3))
    (hfit_wpl : Fits w (ws.length * ws.sum)) :
    ∃ (lens : List ℕ) (steps : ℕ),
      ExecutesList w huffmanProgram (.init ws) lens steps ∧
      steps ≤ 50 * ws.length * Nat.clog 2 ws.length + 84 * ws.length + 50 ∧
      lens.length = ws.length ∧
      (ws = [] → lens = []) ∧
      (ws ≠ [] →
        ∃ T : CodeTree (Fin ws.length),
          IsHuffmanBuild (symWeight ws) ((List.finRange ws.length).map .leaf) T ∧
          T.leaves.Perm (List.finRange ws.length) ∧
          (∀ i : Fin ws.length, ∃ c, T.encodeSym i = some c ∧ c.length = lens.getD i.val 0) ∧
          (∀ code : Fin ws.length → List Bool,
            Set.InjOn code {a | a ∈ List.finRange ws.length} →
            InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ List.finRange ws.length}) →
            T.weightedPathLength (symWeight ws) ≤
              ((List.finRange ws.length).map fun a => (code a).length * symWeight ws a).sum)) := by
  obtain ⟨yF, finalLens, ⟨t_exact, ht_le, hex_code⟩, hyF_out, hout_eq, hfl_len, hpos⟩ :=
    huffmanCode_exec ws hfit_mem hfit_wpl
  have hex_list : ExecutesList w huffmanProgram (.init ws) finalLens (t_exact + 1) :=
    exec_executesList_of_eq huffmanCode outPtr hex_code hout_eq (by
      rw [hyF_out, hfl_len]; exact hfit_mem.of_le (by omega))
  exact ⟨finalLens, t_exact + 1, hex_list, by omega, hfl_len,
    fun hnil => List.length_eq_zero_iff.mp (by simpa [hnil] using hfl_len), hpos⟩

end Cslib.Algorithms.WordRAM.Huffman
