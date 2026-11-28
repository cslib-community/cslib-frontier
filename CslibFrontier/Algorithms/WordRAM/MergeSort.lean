/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ListArray
public import Mathlib.Data.Nat.Log

import CslibFrontier.Computability.WordRAM.Copy
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.Sort

/-!
# Stable Key-Indexed Bottom-Up Merge Sort on the Word RAM

This module implements deterministic `O(n log n)` bottom-up iterative key-indexed permutation merge
sort (`mergeSortPerm`) over `Cslib.WordRAM.Basis.standard`. Given an `n`-word array `keys : List ℕ`
at `keyBase`, an `n`-word output slice at `permBase`, and an `n`-word scratch buffer at `bufBase`
(`keyBase + n ≤ permBase` and `permBase + n ≤ bufBase`), `mergeSortPerm` initializes
`perm[0..n) := [0, …, n - 1]` and performs `⌈log₂ n⌉` bottom-up merge passes using
`Cslib.WordRAM.ArrayCopy.program` for each pass's copy-back step.

Because equal keys break ties toward the left run, `mergeSortPerm` preserves the strict asymmetric
order `StableKeyOrder keys`, so indexing any list `xs` by the resulting permutation `perm` agrees
propositionally (`=`) with Lean's stable `List.mergeSort` (`filterMap_getElem?_eq_mergeSort`).

## Main definitions

* `Cslib.Algorithms.WordRAM.MergeSort.Reg.len`, `Cslib.Algorithms.WordRAM.MergeSort.Reg.keyBase`,
  `Cslib.Algorithms.WordRAM.MergeSort.Reg.permBase`,
  `Cslib.Algorithms.WordRAM.MergeSort.Reg.bufBase`: caller parameter registers of the 18-register
  program.
* `Cslib.Algorithms.WordRAM.MergeSort.StableKeyOrder`: strict tie-breaking key order
  `keys[a] < keys[b] ∨ (keys[a] = keys[b] ∧ a < b)`.
* `Cslib.Algorithms.WordRAM.MergeSort.mergeSortPerm`: structured 18-register Word-RAM key-indexed
  merge sort program.

## Main results

* `Cslib.Algorithms.WordRAM.MergeSort.mergeSortPerm_exec`: `52 * n * ⌈log₂ n⌉ + 5 * n + 7`
  instruction bound producing a stable index permutation `perm` of `List.range keys.length`.
* `Cslib.Algorithms.WordRAM.MergeSort.filterMap_getElem?_eq_mergeSort`: indexing `xs` by any stable
  key permutation equals `xs.mergeSort (fun x y => decide (key x ≤ key y))`.

## References

* [D. E. Knuth, *The Art of Computer Programming, Volume 3: Sorting and Searching*,
  Section 5.2.4][Knuth1998]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*
  (3rd ed.), Section 2.3][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.MergeSort

open Cslib.WordRAM

/-- Strict tie-breaking key order on `0 .. keys.length - 1`: orders indices by strictly increasing
`keys.getD · 0`, breaking ties by smaller original index. -/
@[expose] def StableKeyOrder (keys : List ℕ) (a b : ℕ) : Prop :=
  keys.getD a 0 < keys.getD b 0 ∨ (keys.getD a 0 = keys.getD b 0 ∧ a < b)

theorem StableKeyOrder.le {keys : List ℕ} {a b : ℕ} (h : StableKeyOrder keys a b) :
    keys.getD a 0 ≤ keys.getD b 0 := by
  rcases h with h | ⟨h, _⟩ <;> omega

theorem StableKeyOrder.asym {keys : List ℕ} {a b : ℕ} (h : StableKeyOrder keys a b) :
    ¬ StableKeyOrder keys b a := by
  simp only [StableKeyOrder] at h ⊢; omega

/-! ## Pure Stability Equivalence with `List.mergeSort` -/

private theorem pairwise_stable_merge {β : Type*} (k idx : β → ℕ) {A B : List β}
    (hA : A.Pairwise (fun p q => k p < k q ∨ (k p = k q ∧ idx p < idx q)))
    (hB : B.Pairwise (fun p q => k p < k q ∨ (k p = k q ∧ idx p < idx q)))
    (hAB : ∀ p ∈ A, ∀ q ∈ B, idx p < idx q) :
    (List.merge A B (fun p q => decide (k p ≤ k q))).Pairwise
      (fun p q => k p < k q ∨ (k p = k q ∧ idx p < idx q)) := by
  induction A generalizing B with
  | nil => simpa using hB
  | cons a as iha =>
    induction B with
    | nil => simpa using hA
    | cons b bs ihb =>
      rw [List.cons_merge_cons]
      obtain ⟨ha_as, has_pw⟩ := List.pairwise_cons.mp hA
      obtain ⟨hb_bs, hbs_pw⟩ := List.pairwise_cons.mp hB
      by_cases hle : k a ≤ k b
      · simp only [decide_eq_true hle, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun z hz => ?_, iha has_pw hB fun p hp q hq =>
          hAB p (List.mem_cons_of_mem a hp) q hq⟩
        rcases List.mem_append.mp ((List.merge_perm_append _).subset hz) with hzas | hzbs
        · exact ha_as z hzas
        · have hab_idx : idx a < idx z := hAB a List.mem_cons_self z hzbs
          rcases List.mem_cons.mp hzbs with rfl | hzb'
          · omega
          · have hbz := hb_bs z hzb'; omega
      · have hlt : k b < k a := by omega
        simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun z hz => ?_, ihb hbs_pw fun p hp q hq =>
          hAB p hp q (List.mem_cons_of_mem b hq)⟩
        rcases List.mem_append.mp ((List.merge_perm_append _).subset hz) with hzas | hzbs
        · rcases List.mem_cons.mp hzas with rfl | hza'
          · exact Or.inl hlt
          · have haz := ha_as z hza'; omega
        · exact hb_bs z hzbs

private theorem pairwise_stableKeyOrder_merge {keys A B : List ℕ}
    (hA : A.Pairwise (StableKeyOrder keys)) (hB : B.Pairwise (StableKeyOrder keys))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (List.merge A B (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0))).Pairwise
      (StableKeyOrder keys) :=
  pairwise_stable_merge (keys.getD · 0) id hA hB hAB

private theorem pairwise_stablePair_merge {α : Type*} (key : α → ℕ)
    {A B : List (α × ℕ)}
    (hA : A.Pairwise (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2)))
    (hB : B.Pairwise (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2)))
    (hAB : ∀ p ∈ A, ∀ q ∈ B, p.2 < q.2) :
    (List.merge A B (fun p q => decide (key p.1 ≤ key q.1))).Pairwise
      (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2)) :=
  pairwise_stable_merge (fun p => key p.1) Prod.snd hA hB hAB

private theorem map_fst_merge_zip {α : Type*} (key : α → ℕ) (A B : List (α × ℕ)) :
    (List.merge A B (fun p q => decide (key p.1 ≤ key q.1))).map Prod.fst =
      List.merge (A.map Prod.fst) (B.map Prod.fst) (fun x y => decide (key x ≤ key y)) := by
  induction A generalizing B with
  | nil => simp
  | cons a as iha =>
    induction B with
    | nil => simp
    | cons b bs ihb =>
      rw [List.cons_merge_cons, List.map_cons, List.map_cons, List.cons_merge_cons]
      by_cases h : decide (key a.1 ≤ key b.1) = true
      · simp [h, iha (b :: bs)]
      · simp [h, ihb]

private theorem mergeSort_zipIdx_spec {α : Type*} (xs : List α) (key : α → ℕ) (s : ℕ) :
    (((xs.zipIdx s).mergeSort (fun p q => decide (key p.1 ≤ key q.1))).Pairwise
      (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2))) ∧
    ((xs.zipIdx s).mergeSort (fun p q => decide (key p.1 ≤ key q.1))).map Prod.fst =
      xs.mergeSort (fun x y => decide (key x ≤ key y)) := by
  suffices ∀ k (xs : List α) (s : ℕ), xs.length ≤ k →
      (((xs.zipIdx s).mergeSort (fun p q => decide (key p.1 ≤ key q.1))).Pairwise
        (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2))) ∧
      ((xs.zipIdx s).mergeSort (fun p q => decide (key p.1 ≤ key q.1))).map Prod.fst =
        xs.mergeSort (fun x y => decide (key x ≤ key y)) from this xs.length xs s le_rfl
  intro k
  induction k with
  | zero =>
    intro xs s hk
    obtain rfl : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hk)
    simp
  | succ k ih =>
    intro xs s hk
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩
    · simp
    · simp
    · have hL_le : ((x₁ :: x₂ :: rest).take ((rest.length + 3) / 2)).length ≤ k := by
        rw [List.length_take_of_le (by simp; omega)]
        simp only [List.length_cons] at hk; omega
      have hR_le : ((x₁ :: x₂ :: rest).drop ((rest.length + 3) / 2)).length ≤ k := by
        rw [List.length_drop]
        simp only [List.length_cons] at hk ⊢; omega
      obtain ⟨hpwL, hmapL⟩ := ih ((x₁ :: x₂ :: rest).take ((rest.length + 3) / 2)) s hL_le
      obtain ⟨hpwR, hmapR⟩ := ih ((x₁ :: x₂ :: rest).drop ((rest.length + 3) / 2))
        (s + ((x₁ :: x₂ :: rest).take ((rest.length + 3) / 2)).length) hR_le
      let L := (x₁ :: x₂ :: rest).take ((rest.length + 3) / 2)
      let R := (x₁ :: x₂ :: rest).drop ((rest.length + 3) / 2)
      have hLR : L ++ R = x₁ :: x₂ :: rest := List.take_append_drop _ _
      have hlenL : L.length = (rest.length + 3) / 2 :=
        List.length_take_of_le (by simp; omega)
      have hlenR : R.length = (rest.length + 2) - (rest.length + 3) / 2 := by
        simp [R]
      have hzip : (x₁ :: x₂ :: rest).zipIdx s = L.zipIdx s ++ R.zipIdx (s + L.length) := by
        rw [← hLR, List.zipIdx_append]
      have hms_zip :
          ((x₁ :: x₂ :: rest).zipIdx s).mergeSort (fun p q => decide (key p.1 ≤ key q.1)) =
            List.merge
              ((L.zipIdx s).mergeSort (fun p q => decide (key p.1 ≤ key q.1)))
              ((R.zipIdx (s + L.length)).mergeSort (fun p q => decide (key p.1 ≤ key q.1)))
              (fun p q => decide (key p.1 ≤ key q.1)) := by
        rw [hzip]
        exact List.mergeSort_append (L.zipIdx s) (R.zipIdx (s + L.length))
          (by simp [hlenL, hlenR]; omega) (by simp [hlenL, hlenR]; omega)
      have hms_plain :
          (x₁ :: x₂ :: rest).mergeSort (fun x y => decide (key x ≤ key y)) =
            List.merge
              (L.mergeSort (fun x y => decide (key x ≤ key y)))
              (R.mergeSort (fun x y => decide (key x ≤ key y)))
              (fun x y => decide (key x ≤ key y)) := by
        rw [← hLR]
        exact List.mergeSort_append L R
          (by simp [hlenL, hlenR]; omega) (by simp [hlenL, hlenR]; omega)
      constructor
      · rw [hms_zip]
        refine pairwise_stablePair_merge key hpwL hpwR fun p hp q hq => ?_
        have hp' := List.snd_lt_add_of_mem_zipIdx ((List.mergeSort_perm _ _).subset hp)
        have hq' := List.le_snd_of_mem_zipIdx ((List.mergeSort_perm _ _).subset hq)
        omega
      · rw [hms_zip, map_fst_merge_zip, hmapL, hmapR, hms_plain]

/-- Indexing `xs : List α` by any permutation `perm` of `List.range xs.length` ordered by
`StableKeyOrder (xs.map key)` yields `xs.mergeSort (fun x y => decide (key x ≤ key y))`
identically. -/
theorem filterMap_getElem?_eq_mergeSort {α : Type*} (xs : List α) (key : α → ℕ)
    {perm : List ℕ} (hperm : perm.Perm (List.range xs.length))
    (hpw : perm.Pairwise (StableKeyOrder (xs.map key))) :
    perm.filterMap (xs[·]?) = xs.mergeSort (fun x y => decide (key x ≤ key y)) := by
  let Z := xs.zipIdx 0
  have hZ_len : Z.length = xs.length := by simp [Z]
  have hperm_Z : (perm.filterMap (Z[·]?)).Perm Z := by
    conv_rhs => rw [← List.filterMap_range_getElem? (xs := Z), hZ_len]
    exact hperm.filterMap (Z[·]?)
  have hpw_Z : (perm.filterMap (Z[·]?)).Pairwise
      (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2)) := by
    have hbound : ∀ i ∈ perm, i < xs.length := fun i hi => List.mem_range.mp (hperm.subset hi)
    have h1 : ∀ {L : List ℕ}, (∀ i ∈ L, i < xs.length) →
        L.Pairwise (StableKeyOrder (xs.map key)) →
        (L.filterMap (Z[·]?)).Pairwise
          (fun p q => key p.1 < key q.1 ∨ (key p.1 = key q.1 ∧ p.2 < q.2)) := by
      intro L hL hLpw
      induction hLpw with
      | nil => exact .nil
      | @cons a as ha _ ih =>
        have ha_lt : a < xs.length := hL a List.mem_cons_self
        have haZ : a < Z.length := by omega
        rw [List.filterMap_cons_some (List.getElem?_eq_getElem haZ), List.pairwise_cons]
        refine ⟨fun q hq => ?_, ih fun i hi => hL i (List.mem_cons_of_mem a hi)⟩
        rcases List.mem_filterMap.mp hq with ⟨b, hb_mem, hb_eq⟩
        have hb_lt : b < xs.length := hL b (List.mem_cons_of_mem a hb_mem)
        have hbZ : b < Z.length := by omega
        rw [List.getElem?_eq_getElem hbZ, Option.some.injEq] at hb_eq
        subst hb_eq
        have hab := ha b hb_mem
        simp only [StableKeyOrder, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem ha_lt, List.getElem?_eq_getElem hb_lt,
          Option.map_some, Option.getD_some] at hab
        simpa [Z] using hab
    exact h1 hbound hpw
  obtain ⟨hms_pw, hms_map⟩ := mergeSort_zipIdx_spec xs key 0
  have heq_Z : perm.filterMap (Z[·]?) =
      Z.mergeSort (fun p q => decide (key p.1 ≤ key q.1)) :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => absurd hab (by omega)) hpw_Z hms_pw
      (hperm_Z.trans (List.mergeSort_perm _ _).symm)
  have hmap_fm : ∀ {L : List ℕ}, (∀ i ∈ L, i < xs.length) →
      (L.filterMap (Z[·]?)).map Prod.fst = L.filterMap (xs[·]?) := by
    intro L hbound
    induction L with
    | nil => rfl
    | cons a as ih =>
      have ha_lt : a < xs.length := hbound a List.mem_cons_self
      have haZ : a < Z.length := by omega
      rw [List.filterMap_cons_some (List.getElem?_eq_getElem haZ),
        List.filterMap_cons_some (List.getElem?_eq_getElem ha_lt),
        List.map_cons, ih (fun i hi => hbound i (List.mem_cons_of_mem a hi))]
      simp [Z]
  rw [← hmap_fm (fun i hi => List.mem_range.mp (hperm.subset hi)), heq_Z, hms_map]

/-! ## Private Slice & Memory Helpers -/

private def slice {α : Type*} (L : List α) (a k : ℕ) : List α :=
  (L.drop a).take k

private theorem slice_zero {α : Type*} (L : List α) (a : ℕ) : slice L a 0 = [] := by
  simp [slice]

private theorem slice_eq_cons {α : Type*} (L : List α) {a b : ℕ} (hab : a < b)
    (hb : b ≤ L.length) :
    slice L a (b - a) = L[a]'(by omega) :: slice L (a + 1) (b - (a + 1)) := by
  have ha : a < L.length := by omega
  rw [slice, List.drop_eq_getElem_cons ha, show b - a = (b - (a + 1)) + 1 by omega,
    List.take_succ_cons]
  rfl

private theorem take_append_slice {α : Type*} (L : List α) {a b : ℕ} (hab : a ≤ b) :
    L.take a ++ slice L a (b - a) = L.take b := by
  rw [slice, ← List.take_add, Nat.add_sub_of_le hab]

private theorem slice_append_left {α : Type*} {xs ys : List α} {a k : ℕ}
    (h : a + k ≤ xs.length) : slice (xs ++ ys) a k = slice xs a k := by
  rw [slice, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]
  rfl

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

private theorem holdsList_read_key {kb pb : ℕ} {keys L : List ℕ} {mem : ℕ → ℕ}
    (hkeys : Block.HoldsList kb keys mem) (hL : Block.HoldsList pb L mem)
    (hbound : ∀ v ∈ L, v < keys.length) {p : ℕ} (hp : p < L.length) :
    mem (pb + p) = L[p] ∧ L[p] < keys.length ∧ mem (kb + L[p]) = keys.getD L[p] 0 := by
  have hu : L[p] < keys.length := hbound _ (List.getElem_mem hp)
  refine ⟨hL.get p hp, hu, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
  exact hkeys.get _ hu

/-! ## Registers (`Fin 18`) and Structured Program -/

namespace Reg

/-- Number of elements `n = keys.length` to sort. -/
abbrev len : Fin 18 := 0
/-- Base address `kb` of the `n`-word key array `keys`. -/
abbrev keyBase : Fin 18 := 1
/-- Base address `pb` of the `n`-word output index permutation `perm`. -/
abbrev permBase : Fin 18 := 2
/-- Base address `bb` of the `n`-word merge scratch buffer. -/
abbrev bufBase : Fin 18 := 3

private abbrev one : Fin 18 := 4
private abbrev step : Fin 18 := 5
private abbrev wRun : Fin 18 := 6
private abbrev lo : Fin 18 := 7
private abbrev mid : Fin 18 := 8
private abbrev hi : Fin 18 := 9
private abbrev pA : Fin 18 := 10
private abbrev pB : Fin 18 := 11
private abbrev outIdx : Fin 18 := 12
private abbrev uA : Fin 18 := 13
private abbrev wA : Fin 18 := 14
private abbrev uB : Fin 18 := 15
private abbrev wB : Fin 18 := 16
private abbrev addr : Fin 18 := 17

end Reg

open Reg

private def copyMap : Fin 7 → Fin 18
  | 0 => bufBase
  | 1 => permBase
  | 2 => len
  | 3 => step
  | 4 => addr
  | 5 => uA
  | 6 => one

private theorem copyMap_injective : Function.Injective copyMap := by decide

private def initPermBody : Code .standard 18 := ram[
  addr ← permBase + step;
  *addr ← step;
  step ← step + one ]

private def mergeElemBody : Code .standard 18 := ram[
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

private def mergePassSetup : Code .standard 18 := ram[
  mid ← lo + wRun;
  if len < mid then [ mid ← len ] else [ mid ← mid ];
  hi ← mid + wRun;
  if len < hi then [ hi ← len ] else [ hi ← hi ];
  pA ← lo;
  pB ← mid;
  outIdx ← lo ]

private def mergePassBody : Code .standard 18 :=
  .seq mergePassSetup (.seq (.loop (.lt outIdx hi) mergeElemBody) (.op (.copy lo hi)))

private def outerPassBody : Code .standard 18 := ram[
  one ← #1;
  lo ← #0;
  while lo < len do [ ⟪mergePassBody⟫ ];
  ⟪ArrayCopy.program.rename copyMap⟫;
  wRun ← wRun + wRun ]

/-- Deterministic bottom-up iterative key-indexed permutation merge sort over `Basis.standard`. -/
def mergeSortPerm : Code .standard 18 := ram[
  one ← #1;
  step ← #0;
  while step < len do [ ⟪initPermBody⟫ ];
  wRun ← #1;
  while wRun < len do [ ⟪outerPassBody⟫ ] ]

/-! ## Loop Invariants and Execution Proof -/

private structure OuterInv (keys : List ℕ) (kb pb bb : ℕ) (x_mem : ℕ → ℕ) (y : Data 18) : Prop where
  len_eq : y.regs len = keys.length
  keyBase_eq : y.regs keyBase = kb
  permBase_eq : y.regs permBase = pb
  bufBase_eq : y.regs bufBase = bb
  mod : Modifies (Block.mk pb (bb + keys.length - pb)).footprint x_mem y.mem
  state :
    ∃ (pass : ℕ) (L : List ℕ),
      pass ≤ Nat.clog 2 keys.length ∧
      y.regs wRun = 2 ^ pass ∧
      Block.HoldsList pb L y.mem ∧
      L.Perm (List.range keys.length) ∧
      (∀ q : ℕ, (slice L (q * 2 ^ pass) (2 ^ pass)).Pairwise (StableKeyOrder keys)) ∧
      (∀ q : ℕ, ∀ v ∈ slice L (q * 2 ^ pass) (2 ^ pass),
        q * 2 ^ pass ≤ v ∧ v < (q + 1) * 2 ^ pass)

private structure MidInv (keys L : List ℕ) (kb pb bb W : ℕ)
    (y_mem : ℕ → ℕ) (u : Data 18) : Prop where
  one_eq : u.regs one = 1
  len_eq : u.regs len = keys.length
  keyBase_eq : u.regs keyBase = kb
  permBase_eq : u.regs permBase = pb
  bufBase_eq : u.regs bufBase = bb
  wRun_eq : u.regs wRun = W
  lo_le : u.regs lo ≤ keys.length
  lo_div : u.regs lo < keys.length → ∃ p : ℕ, u.regs lo = p * (2 * W)
  mod : Modifies (Block.mk bb keys.length).footprint y_mem u.mem
  state :
    ∃ acc : List ℕ,
      acc.length = u.regs lo ∧
      (∀ j : ℕ, (hj : j < acc.length) → u.mem (bb + j) = acc[j]) ∧
      acc.Perm (L.take (u.regs lo)) ∧
      (∀ q : ℕ, (slice acc (q * (2 * W)) (2 * W)).Pairwise (StableKeyOrder keys)) ∧
      (∀ q : ℕ, ∀ v ∈ slice acc (q * (2 * W)) (2 * W),
        q * (2 * W) ≤ v ∧ v < (q + 1) * (2 * W))

private structure InInv (keys L : List ℕ) (kb pb bb W lo_v mid_v hi_v : ℕ)
    (u_mem : ℕ → ℕ) (idx_v : ℕ) (v : Data 18) : Prop where
  one_eq : v.regs one = 1
  len_eq : v.regs len = keys.length
  keyBase_eq : v.regs keyBase = kb
  permBase_eq : v.regs permBase = pb
  bufBase_eq : v.regs bufBase = bb
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
          (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0)) =
        List.merge (slice L lo_v (mid_v - lo_v)) (slice L mid_v (hi_v - mid_v))
          (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0))

private structure InitPermInv (keys : List ℕ) (kb pb bb : ℕ)
    (x_mem : ℕ → ℕ) (s : ℕ) (y : Data 18) : Prop where
  one_eq : y.regs one = 1
  len_eq : y.regs len = keys.length
  keyBase_eq : y.regs keyBase = kb
  permBase_eq : y.regs permBase = pb
  bufBase_eq : y.regs bufBase = bb
  mod : Modifies (Block.mk pb keys.length).footprint x_mem y.mem
  init_cells : ∀ j < s, y.mem (pb + j) = j

private theorem mergeElemBody_exec {w kb pb bb W lo_v mid_v hi_v : ℕ}
    (keys L : List ℕ) (u_mem : ℕ → ℕ)
    (hL_len : L.length = keys.length)
    (hL_bound : ∀ v ∈ L, v < keys.length)
    (hhi_le : hi_v ≤ keys.length)
    (hdisj1 : kb + keys.length ≤ pb) (hdisj2 : pb + keys.length ≤ bb)
    (hfit : Fits w (bb + 2 * keys.length + 1))
    (hu_keys : Block.HoldsList kb keys u_mem)
    (hu_L : Block.HoldsList pb L u_mem)
    (v : Data 18)
    (hv : InInv keys L kb pb bb W lo_v mid_v hi_v u_mem (v.regs outIdx) v)
    (hlt_in : v.regs outIdx < hi_v) :
    ∃ v', ExecWithin w mergeElemBody v v' 16 ∧
      InInv keys L kb pb bb W lo_v mid_v hi_v u_mem (v.regs outIdx + 1) v' ∧
      v'.regs outIdx = v.regs outIdx + 1 := by
  obtain ⟨hvo, hvn, hvkb, hvpb, hvbb, hvw, hvlo, hvmid, hvhi,
    hpa1, hpa2, hpb1, hpb2, hidx_lo, hrem_sum, hmod_in, pref, hpref_len, hpref_mem,
    hmerge_inv⟩ := hv
  have hv_keys : Block.HoldsList kb keys v.mem :=
    hu_keys.frame fun a ha1 ha2 => Modifies.block_iff.mp hmod_in a (by dsimp only; omega)
  have hv_L : Block.HoldsList pb L v.mem :=
    hu_L.frame fun a ha1 ha2 => Modifies.block_iff.mp hmod_in a (by dsimp only; omega)
  have hstep (elem pa' pb' : ℕ) (v' : Data 18)
      (hbds : lo_v ≤ pa' ∧ pa' ≤ mid_v ∧ mid_v ≤ pb' ∧ pb' ≤ hi_v ∧
        (mid_v - pa') + (hi_v - pb') = hi_v - (v.regs outIdx + 1))
      (hmrg : elem :: List.merge (slice L pa' (mid_v - pa')) (slice L pb' (hi_v - pb'))
          (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0)) =
        List.merge (slice L (v.regs pA) (mid_v - v.regs pA))
          (slice L (v.regs pB) (hi_v - v.regs pB))
          (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0)))
      (hmem : v'.mem = Function.update v.mem (bb + v.regs outIdx) elem)
      (ho : v'.regs one = 1) (hn : v'.regs len = keys.length)
      (hkb : v'.regs keyBase = kb) (hpb : v'.regs permBase = pb) (hbb : v'.regs bufBase = bb)
      (hw : v'.regs wRun = W) (hlo : v'.regs lo = lo_v) (hmid : v'.regs mid = mid_v)
      (hhi : v'.regs hi = hi_v) (hpA : v'.regs pA = pa') (hpB : v'.regs pB = pb')
      (hout : v'.regs outIdx = v.regs outIdx + 1) :
      InInv keys L kb pb bb W lo_v mid_v hi_v u_mem (v.regs outIdx + 1) v' ∧
        v'.regs outIdx = v.regs outIdx + 1 := by
    obtain ⟨hpA1, hpA2, hpB1, hpB2, hrem⟩ := hbds
    obtain ⟨hmod_snoc, hmem_snoc⟩ :=
      prefix_snoc_mem (elem := elem) hpref_len hidx_lo hmod_in hpref_mem
    refine ⟨⟨ho, hn, hkb, hpb, hbb, hw, hlo, hmid, hhi,
      hpA ▸ hpA1, hpA ▸ hpA2, hpB ▸ hpB1, hpB ▸ hpB2, by omega,
      by rwa [hpA, hpB], hmem ▸ hmod_snoc, pref ++ [elem],
      by simp [hpref_len]; omega, hmem ▸ hmem_snoc, ?_⟩, hout⟩
    rw [List.append_assoc, List.singleton_append, hpA, hpB, hmrg, hmerge_inv]
  refine WP.exists_execWithin ?_
  unfold mergeElemBody
  by_cases hcA : v.regs pA < mid_v
  · obtain ⟨hread_uA, huA_lt_n, hread_wA⟩ :=
      holdsList_read_key hv_keys hv_L hL_bound (by omega : v.regs pA < L.length)
    have hslA := slice_eq_cons L hcA (by omega)
    by_cases hcB : v.regs pB < hi_v
    · obtain ⟨hread_uB, huB_lt_n, hread_wB⟩ :=
        holdsList_read_key hv_keys hv_L hL_bound (by omega : v.regs pB < L.length)
      have hslB := slice_eq_cons L hcB (by omega)
      by_cases hcW : keys.getD L[v.regs pB] 0 < keys.getD L[v.regs pA] 0
      · have hcmp_f : decide (keys.getD L[v.regs pA] 0 ≤ keys.getD L[v.regs pB] 0) = false := by
          simp only [decide_eq_false_iff_not]; omega
        wram_exec [hvo, hvkb, hvpb, hvbb, hvmid, hvhi, hcA, hcB,
          hread_uA, hread_uB, hread_wA, hread_wB, hcW]
        refine hstep L[v.regs pB] (v.regs pA) (v.regs pB + 1) _ (by omega) ?_
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hslA, hslB, List.cons_merge_cons, hcmp_f]
          rfl
        all_goals wram_simp [Data.write_mem, hvo, hvn, hvkb, hvpb, hvbb, hvw, hvlo, hvmid, hvhi]
      · have hcmp_t : decide (keys.getD L[v.regs pA] 0 ≤ keys.getD L[v.regs pB] 0) = true := by
          simp only [decide_eq_true_eq]; omega
        wram_exec [hvo, hvkb, hvpb, hvbb, hvmid, hvhi, hcA, hcB,
          hread_uA, hread_uB, hread_wA, hread_wB, hcW]
        refine hstep L[v.regs pA] (v.regs pA + 1) (v.regs pB) _ (by omega) ?_
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hslA, hslB, List.cons_merge_cons, hcmp_t]
          rfl
        all_goals wram_simp [Data.write_mem, hvo, hvn, hvkb, hvpb, hvbb, hvw, hvlo, hvmid, hvhi]
    · have hsubB : hi_v - v.regs pB = 0 := by omega
      have hslB : slice L (v.regs pB) (hi_v - v.regs pB) = [] := by rw [hsubB, slice_zero]
      wram_exec [hvo, hvpb, hvbb, hvmid, hvhi, hcA, hcB, hread_uA]
      refine hstep L[v.regs pA] (v.regs pA + 1) (v.regs pB) _ (by omega) ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [hslA, hslB]
      all_goals wram_simp [Data.write_mem, hvo, hvn, hvkb, hvpb, hvbb, hvw, hvlo, hvmid, hvhi]
  · have hcB : v.regs pB < hi_v := by omega
    have hread_uB : v.mem (pb + v.regs pB) = L[v.regs pB]'(by omega) := hv_L.get _ (by omega)
    have hsubA : mid_v - v.regs pA = 0 := by omega
    have hslA : slice L (v.regs pA) (mid_v - v.regs pA) = [] := by rw [hsubA, slice_zero]
    have hslB := slice_eq_cons L hcB (by omega)
    wram_exec [hvo, hvpb, hvbb, hvmid, hcA, hread_uB]
    refine hstep L[v.regs pB] (v.regs pA) (v.regs pB + 1) _ (by omega) ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [hslA, hslB]
    all_goals wram_simp [Data.write_mem, hvo, hvn, hvkb, hvpb, hvbb, hvw, hvlo, hvmid, hvhi]

private theorem mergePassSetup_exec {w kb pb bb W lo_v mid_v hi_v : ℕ}
    (keys L : List ℕ) (u : Data 18)
    (hW_lt : W < keys.length) (hlo_lt : lo_v < keys.length)
    (hmid_def : mid_v = min keys.length (lo_v + W))
    (hhi_def : hi_v = min keys.length (mid_v + W))
    (hfit : Fits w (bb + 2 * keys.length + 1))
    (huo : u.regs one = 1) (hun : u.regs len = keys.length)
    (hukb : u.regs keyBase = kb) (hupb : u.regs permBase = pb) (hubb : u.regs bufBase = bb)
    (huw : u.regs wRun = W) (hlo_def : u.regs lo = lo_v) :
    ∃ u1 : Data 18, ExecWithin w mergePassSetup u u1 11 ∧
      InInv keys L kb pb bb W lo_v mid_v hi_v u.mem (u1.regs outIdx) u1 ∧
      u1.regs outIdx = lo_v := by
  have hle1 : lo_v ≤ mid_v := by omega
  have hle2 : mid_v ≤ hi_v := by omega
  have hrem : (mid_v - lo_v) + (hi_v - mid_v) = hi_v - lo_v := by omega
  have hinv (u1 : Data 18) (hmem : u1.mem = u.mem)
      (ho : u1.regs one = 1) (hn : u1.regs len = keys.length)
      (hkb : u1.regs keyBase = kb) (hpb : u1.regs permBase = pb) (hbb : u1.regs bufBase = bb)
      (hw : u1.regs wRun = W) (hlo : u1.regs lo = lo_v) (hmid : u1.regs mid = mid_v)
      (hhi : u1.regs hi = hi_v) (hpA : u1.regs pA = lo_v) (hpB : u1.regs pB = mid_v)
      (hout : u1.regs outIdx = lo_v) :
      InInv keys L kb pb bb W lo_v mid_v hi_v u.mem (u1.regs outIdx) u1 ∧
        u1.regs outIdx = lo_v :=
    ⟨⟨ho, hn, hkb, hpb, hbb, hw, hlo, hmid, hhi, hpA.symm ▸ le_rfl, hpA.symm ▸ hle1,
      hpB.symm ▸ le_rfl, hpB.symm ▸ hle2, hout.symm ▸ le_rfl,
      by rwa [hpA, hpB, hout], hmem ▸ Modifies.refl _ _, [],
      by simp [hout], fun d hd => absurd hd (Nat.not_lt_zero d),
      by simp [hpA, hpB]⟩, hout⟩
  refine WP.exists_execWithin ?_
  unfold mergePassSetup
  by_cases hm1 : keys.length < lo_v + W
  · have hm_eq : mid_v = keys.length := by omega
    have hh2 : keys.length < keys.length + W := by omega
    have hh_eq : hi_v = keys.length := by omega
    wram_exec [hun, huw, hlo_def, hm1, hh2]
    refine hinv _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals wram_simp [huo, hun, hukb, hupb, hubb, huw, hlo_def, hm_eq, hh_eq]
  · have hm_eq : mid_v = lo_v + W := by omega
    by_cases hh2 : keys.length < mid_v + W
    · have hh_eq : hi_v = keys.length := by omega
      have hh2' : keys.length < lo_v + W + W := by omega
      wram_exec [hun, huw, hlo_def, hm1, hh2']
      refine hinv _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals wram_simp [huo, hun, hukb, hupb, hubb, huw, hlo_def, hm_eq, hh_eq]
    · have hh_eq : hi_v = lo_v + W + W := by omega
      have hh2' : ¬ (keys.length < lo_v + W + W) := by omega
      wram_exec [hun, huw, hlo_def, hm1, hh2']
      refine hinv _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals wram_simp [huo, hun, hukb, hupb, hubb, huw, hlo_def, hm_eq, hh_eq]

private theorem mergeRuns_stable {keys L M : List ℕ} {W p lo_v mid_v hi_v : ℕ}
    (hL_len : L.length = keys.length)
    (hlo_eq : lo_v = p * (2 * W))
    (hmid_def : mid_v = min keys.length (lo_v + W))
    (hhi_def : hi_v = min keys.length (mid_v + W))
    (hL_pw : ∀ q : ℕ, (slice L (q * W) W).Pairwise (StableKeyOrder keys))
    (hL_rng : ∀ q : ℕ, ∀ v ∈ slice L (q * W) W, q * W ≤ v ∧ v < (q + 1) * W)
    (hM_eq : M = List.merge (slice L lo_v (mid_v - lo_v)) (slice L mid_v (hi_v - mid_v))
      (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0))) :
    M.Pairwise (StableKeyOrder keys) ∧
      (∀ z ∈ M, p * (2 * W) ≤ z ∧ z < (p + 1) * (2 * W)) := by
  have h2pW : (2 * p) * W = lo_v := by rw [hlo_eq, Nat.mul_comm 2 p, Nat.mul_assoc]
  have hA_eq : slice L lo_v (mid_v - lo_v) = slice L ((2 * p) * W) W := by
    rw [h2pW]; simp only [slice]
    have hmid_sub : mid_v - lo_v = min W (L.drop lo_v).length := by simp [hL_len]; omega
    rw [hmid_sub, ← List.take_eq_take_min]
  have hB_cases :
      slice L mid_v (hi_v - mid_v) = slice L ((2 * p + 1) * W) W ∨
        slice L mid_v (hi_v - mid_v) = [] := by
    by_cases hm_lt : lo_v + W < keys.length
    · have hm_eq : mid_v = (2 * p + 1) * W := by
        have h1 : (2 * p + 1) * W = lo_v + W := by rw [Nat.add_mul, Nat.one_mul, h2pW]
        rw [h1]; omega
      left
      rw [hm_eq]; simp only [slice]
      have hhi_sub : hi_v - (2 * p + 1) * W = min W (L.drop ((2 * p + 1) * W)).length := by
        simp [hL_len, ← hm_eq]; omega
      rw [hhi_sub, ← List.take_eq_take_min]
    · right
      rw [show hi_v - mid_v = 0 by omega, slice_zero]
  have hB_pw : (slice L mid_v (hi_v - mid_v)).Pairwise (StableKeyOrder keys) := by
    rcases hB_cases with hB_eq | hB_nil
    · exact hB_eq ▸ hL_pw (2 * p + 1)
    · rw [hB_nil]; exact .nil
  have hB_sub : ∀ y ∈ slice L mid_v (hi_v - mid_v), y ∈ slice L ((2 * p + 1) * W) W := by
    intro y hy
    rcases hB_cases with hB_eq | hB_nil
    · rwa [← hB_eq]
    · rw [hB_nil] at hy; simp at hy
  have hM_perm : M.Perm (slice L lo_v (mid_v - lo_v) ++ slice L mid_v (hi_v - mid_v)) := by
    rw [hM_eq]; exact List.merge_perm_append _
  refine ⟨?_, fun z hz => ?_⟩
  · rw [hM_eq]
    refine pairwise_stableKeyOrder_merge (hA_eq ▸ hL_pw (2 * p)) hB_pw fun a ha b hb => ?_
    have ha' := hL_rng (2 * p) a (hA_eq ▸ ha)
    have hb' := hL_rng (2 * p + 1) b (hB_sub b hb)
    omega
  · rcases List.mem_append.mp (hM_perm.subset hz) with hzA | hzB
    · have h1 := hL_rng (2 * p) z (hA_eq ▸ hzA)
      have hp1 : 2 * p * W = p * (2 * W) := by rw [Nat.mul_comm 2 p, Nat.mul_assoc]
      have hp2 : (2 * p + 1) * W ≤ (p + 1) * (2 * W) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, ← hp1]; omega
      omega
    · have h1 := hL_rng (2 * p + 1) z (hB_sub z hzB)
      have hp1 : p * (2 * W) ≤ (2 * p + 1) * W := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm p 2]; omega
      have hp2 : (2 * p + 1 + 1) * W = (p + 1) * (2 * W) := by
        change (2 * (p + 1)) * W = (p + 1) * (2 * W)
        rw [Nat.mul_comm 2 (p + 1), Nat.mul_assoc]
      omega

/-- Each block of the given width is stable-sorted and contains only indices in the
corresponding original interval. The last block may be shorter than the width. -/
structure StableRuns (keys : List ℕ) (width : ℕ) (indices : List ℕ) : Prop where
  /-- Every block is sorted by key and then by original index. -/
  ordered : ∀ q : ℕ, ((indices.drop (q * width)).take width).Pairwise (StableKeyOrder keys)
  /-- Every index in a block belongs to that block's original interval. -/
  index_bounds : ∀ q a : ℕ, a ∈ (indices.drop (q * width)).take width →
    q * width ≤ a ∧ a < (q + 1) * width

/-- The completed prefix of a pass permutes the same prefix of the source and has
stable-sorted, range-bounded blocks at the new width. -/
structure StableMergePrefix (keys source : List ℕ) (width written : ℕ)
    (output : List ℕ) : Prop where
  /-- The output occupies exactly the written prefix. -/
  length_eq : output.length = written
  /-- The output contains exactly the indices of the written part of the source. -/
  perm : output.Perm (source.take written)
  /-- The written blocks have the new width. -/
  runs : StableRuns keys width output

/-- The initial list of original indices has stable runs of width one. -/
theorem stableRuns_range (keys : List ℕ) : StableRuns keys 1 (List.range keys.length) := by
  constructor
  · intro q
    have hlen : ((List.range keys.length).drop (q * 1) |>.take 1).length ≤ 1 := by
      simp only [List.length_take]
      exact Nat.min_le_left ..
    generalize hb : ((List.range keys.length).drop (q * 1)).take 1 = b at hlen ⊢
    cases b with
    | nil => exact .nil
    | cons a b =>
      cases b with
      | nil => exact List.pairwise_singleton _ _
      | cons x xs => simp at hlen
  · intro q a ha
    simp only [Nat.mul_one] at ha ⊢
    by_cases hq : q < keys.length
    · have hq' : q < (List.range keys.length).length := by simpa using hq
      rw [List.drop_eq_getElem_cons hq', List.take_succ_cons, List.take_zero,
        List.mem_singleton, List.getElem_range] at ha
      subst a
      exact ⟨le_rfl, Nat.lt_succ_self _⟩
    · rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hq), List.take_nil] at ha
      exact (List.not_mem_nil ha).elim

/-- A merge pass starts with an empty written prefix. -/
theorem stableMergePrefix_empty (keys source : List ℕ) (width : ℕ) :
    StableMergePrefix keys source width 0 [] := by
  refine ⟨rfl, by simp, ⟨?_, ?_⟩⟩
  · intro q
    simp
  · intro q a ha
    simp at ha

/-- Appending the merge of the two adjacent source blocks advances the output prefix.
The target block has twice the width and remains stable-sorted and range-bounded. -/
theorem stableMergePrefix_step {keys source output merged : List ℕ} {width p lo mid hi : ℕ}
    (hlen : source.length = keys.length)
    (hs : StableRuns keys width source)
    (ho : StableMergePrefix keys source (2 * width) lo output)
    (hlo : lo = p * (2 * width))
    (hmid : mid = min keys.length (lo + width))
    (hhi : hi = min keys.length (mid + width))
    (hm : merged = ((source.drop lo).take (mid - lo)).merge
      ((source.drop mid).take (hi - mid)) (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0))) :
    StableMergePrefix keys source (2 * width) hi (output ++ merged) := by
  have hlen_pre := ho.perm.length_eq
  rw [ho.length_eq, List.length_take, hlen] at hlen_pre
  have hlo_le : lo ≤ keys.length := by omega
  have hM_len : merged.length = hi - lo := by
    rw [hm]
    have hml := (List.merge_perm_append (fun a b => decide (keys.getD a 0 ≤ keys.getD b 0))
      (xs := (source.drop lo).take (mid - lo)) (ys := (source.drop mid).take (hi - mid))).length_eq
    rw [hml, List.length_append, List.length_take, List.length_take, List.length_drop,
      List.length_drop, hlen]
    omega
  have hM_le : merged.length ≤ 2 * width := by omega
  obtain ⟨hmOrder, hmRange⟩ :=
    mergeRuns_stable hlen hlo hmid hhi hs.ordered hs.index_bounds hm
  have hmPerm : merged.Perm (slice source lo (mid - lo) ++ slice source mid (hi - mid)) :=
    hm ▸ List.merge_perm_append _
  have htake :
      source.take lo ++ (slice source lo (mid - lo) ++ slice source mid (hi - mid)) =
        source.take hi := by
    rw [← List.append_assoc, take_append_slice source (by omega : lo ≤ mid),
      take_append_slice source (by omega : mid ≤ hi)]
  have hblock (q : ℕ) :
      slice (output ++ merged) (q * (2 * width)) (2 * width) =
        slice output (q * (2 * width)) (2 * width) ∨
      (q = p ∧ slice (output ++ merged) (q * (2 * width)) (2 * width) = merged) ∨
      slice (output ++ merged) (q * (2 * width)) (2 * width) = [] := by
    rcases lt_trichotomy q p with hqp | rfl | hpq
    · have hq1 := Nat.mul_le_mul_right (2 * width) (Nat.succ_le_of_lt hqp)
      rw [Nat.succ_mul] at hq1
      exact Or.inl (slice_append_left (by rw [ho.length_eq, hlo]; omega))
    · have hqEq : q * (2 * width) = output.length := hlo.symm.trans ho.length_eq.symm
      refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      rw [slice, hqEq, List.drop_left' rfl, List.take_of_length_le hM_le]
    · have hp1 := Nat.mul_le_mul_right (2 * width) (Nat.succ_le_of_lt hpq)
      rw [Nat.succ_mul] at hp1
      have hend : (output ++ merged).length ≤ q * (2 * width) := by
        simp only [List.length_append, ho.length_eq, hlo]
        omega
      refine Or.inr (Or.inr ?_)
      rw [slice, List.drop_eq_nil_of_le hend, List.take_nil]
  refine ⟨by simp only [List.length_append, ho.length_eq, hM_len]; omega, ?_, ⟨?_, ?_⟩⟩
  · rw [← htake]
    exact ho.perm.append hmPerm
  · intro q
    change (slice (output ++ merged) (q * (2 * width)) (2 * width)).Pairwise _
    rcases hblock q with h | ⟨-, h⟩ | h
    · rw [h]
      exact ho.runs.ordered q
    · rwa [h]
    · rw [h]
      exact .nil
  · intro q a ha
    change a ∈ slice (output ++ merged) (q * (2 * width)) (2 * width) at ha
    rcases hblock q with h | ⟨rfl, h⟩ | h
    · exact ho.runs.index_bounds q a (by rw [h] at ha; exact ha)
    · exact hmRange a (h ▸ ha)
    · simp [h] at ha

/-- When the run width covers the full input, its indices are stable-sorted. -/
theorem StableRuns.finish {keys indices : List ℕ} {width : ℕ}
    (h : StableRuns keys width indices) (hlen : indices.length ≤ width) :
    indices.Pairwise (StableKeyOrder keys) := by
  simpa only [Nat.zero_mul, List.drop_zero, List.take_of_length_le hlen] using h.ordered 0

/-- A completed pass whose width covers the full input returns a stable permutation. -/
theorem StableMergePrefix.finish {keys source output : List ℕ} {width : ℕ}
    (h : StableMergePrefix keys source width source.length output)
    (hlen : source.length ≤ width) : output.Perm source ∧ output.Pairwise (StableKeyOrder keys) :=
  ⟨by simpa only [List.take_length] using h.perm, h.runs.finish (h.length_eq ▸ hlen)⟩

private theorem mergePassBody_exec {w kb pb bb W : ℕ}
    (keys L : List ℕ) (y_mem : ℕ → ℕ)
    (hL_len : L.length = keys.length)
    (hL_bound : ∀ v ∈ L, v < keys.length)
    (hL_pw : ∀ q : ℕ, (slice L (q * W) W).Pairwise (StableKeyOrder keys))
    (hL_rng : ∀ q : ℕ, ∀ v ∈ slice L (q * W) W, q * W ≤ v ∧ v < (q + 1) * W)
    (_hW_pos : 0 < W) (hW_lt : W < keys.length)
    (hdisj1 : kb + keys.length ≤ pb) (hdisj2 : pb + keys.length ≤ bb)
    (hfit : Fits w (bb + 2 * keys.length + 1))
    (u : Data 18)
    (hu_keys : Block.HoldsList kb keys u.mem)
    (hu_L : Block.HoldsList pb L u.mem)
    (hu : MidInv keys L kb pb bb W y_mem u)
    (hcu : (Cond.lt lo len).Holds u) :
    ∃ u' T_m, ExecWithin w mergePassBody u u' T_m ∧
      MidInv keys L kb pb bb W y_mem u' ∧
      T_m + 2 + 34 * (keys.length - u'.regs lo) ≤ 34 * (keys.length - u.regs lo) := by
  obtain ⟨huo, hun, hukb, hupb, hubb, huw, hulo_le, hulo_div,
    hmodM_u, acc, hacc_len, hacc_mem, hacc_perm, hacc_pw, hacc_rng⟩ := hu
  obtain ⟨lo_v, hlo_def⟩ : ∃ l, u.regs lo = l := ⟨_, rfl⟩
  rw [hlo_def] at hulo_le hulo_div hacc_len hacc_perm ⊢
  have hlo_lt : lo_v < keys.length := by simpa only [Cond.holds_lt, hun, hlo_def] using hcu
  obtain ⟨p, hlo_eq⟩ := hulo_div hlo_lt
  obtain ⟨mid_v, hmid_def⟩ : ∃ m, m = min keys.length (lo_v + W) := ⟨_, rfl⟩
  obtain ⟨hi_v, hhi_def⟩ : ∃ h, h = min keys.length (mid_v + W) := ⟨_, rfl⟩
  have hhi_eq : hi_v = min keys.length (lo_v + 2 * W) := by omega
  obtain ⟨u1, hex_ms, hP1, hout1⟩ :=
    mergePassSetup_exec keys L u hW_lt hlo_lt hmid_def hhi_def hfit
      huo hun hukb hupb hubb huw hlo_def
  obtain ⟨u2, hex_in, hP2, _⟩ :=
    ExecWithin.loop_count (index := outIdx) (limit := hi) (N := hi_v) (T := 16)
      (InInv keys L kb pb bb W lo_v mid_v hi_v u.mem)
      (fun _ hq => hq.hi_eq)
      (mergeElemBody_exec keys L u.mem hL_len hL_bound (by omega) hdisj1 hdisj2 hfit hu_keys hu_L)
      (by omega) hP1
  obtain ⟨hu2o, hu2n, hu2kb, hu2pb, hu2bb, hu2w,
    _, _, hu2hi, hpa1, hpa2, hpb1, hpb2, _, hrem_end, hmod_u2,
    M, hM_len, hM_mem, hM_eq⟩ := hP2
  have hpA_end : u2.regs pA = mid_v := by omega
  have hpB_end : u2.regs pB = hi_v := by omega
  rw [hpA_end, hpB_end, Nat.sub_self, Nat.sub_self, slice_zero, slice_zero] at hM_eq
  simp only [List.nil_merge, List.append_nil] at hM_eq
  have hprefix := stableMergePrefix_step hL_len ⟨hL_pw, hL_rng⟩
    ⟨hacc_len, hacc_perm, ⟨hacc_pw, hacc_rng⟩⟩ hlo_eq hmid_def hhi_def hM_eq
  let u' := u2.set lo (u2.regs hi)
  have hex_mp : ExecWithin w mergePassBody u u' (18 * (hi_v - lo_v) + 14) := by
    unfold mergePassBody
    refine (hex_ms.seq (hex_in.seq ExecWithin.copy)).mono ?_
    rw [hout1]; omega
  refine ⟨u', 18 * (hi_v - lo_v) + 14, hex_mp, ?_, ?_⟩
  · refine ⟨by wram_simp [u', hu2o], by wram_simp [u', hu2n],
      by wram_simp [u', hu2kb], by wram_simp [u', hu2pb], by wram_simp [u', hu2bb],
      by wram_simp [u', hu2w], by wram_simp [u', hu2hi]; omega, ?_, ?_, acc ++ M,
      by wram_simp [u', hu2hi]; exact hprefix.length_eq,
      ?_, by wram_simp [u', hu2hi]; exact hprefix.perm,
      hprefix.runs.ordered, hprefix.runs.index_bounds⟩
    · intro hlt_hi
      wram_simp [u', hu2hi] at hlt_hi ⊢
      have hhi_full : hi_v = lo_v + 2 * W := by omega
      exact ⟨p + 1, by rw [hhi_full, hlo_eq, Nat.add_mul, Nat.one_mul]⟩
    · rw [Modifies.block_iff]
      intro a ha; dsimp only at ha
      have h1 := Modifies.block_iff.mp hmod_u2 a (by dsimp only; omega)
      exact h1.trans (Modifies.block_iff.mp hmodM_u a (by dsimp only; omega))
    · intro j hj
      by_cases hj_lo : j < lo_v
      · have hj_acc : j < acc.length := by omega
        rw [List.getElem_append_left hj_acc]
        have h1 := Modifies.block_iff.mp hmod_u2 (bb + j) (by dsimp only; omega)
        exact h1.trans (hacc_mem j hj_acc)
      · have hj_ge : acc.length ≤ j := by omega
        have hd_lt : j - lo_v < M.length := by simp at hj; omega
        have haddr : bb + lo_v + (j - lo_v) = bb + j := by omega
        rw [List.getElem_append_right hj_ge]
        simpa [u', hacc_len, haddr] using hM_mem (j - lo_v) hd_lt
  · have hlo_u' : u'.regs lo = hi_v := by wram_simp [u', hu2hi]
    rw [hlo_u']
    have hk1 : 18 * (hi_v - lo_v) + 16 ≤ 34 * (hi_v - lo_v) := by omega
    have hsub : 34 * (keys.length - hi_v) + 34 * (hi_v - lo_v) = 34 * (keys.length - lo_v) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega

/-- **`O(n log n)` Word-RAM Stable Key-Indexed Permutation Merge Sort**: given `keys : List ℕ` at
`kb` and disjoint `n`-word output and scratch blocks at `pb` and `bb` (`kb + n ≤ pb` and
`pb + n ≤ bb`), `mergeSortPerm` halts within `52 * n * Nat.clog 2 n + 5 * n + 7` instructions and
writes a permutation `perm` of `List.range n` at `pb` sorted under both `StableKeyOrder keys` and
`fun a b => keys.getD a 0 ≤ keys.getD b 0`. -/
theorem mergeSortPerm_exec {w kb pb bb : ℕ} (keys : List ℕ) (x : Data 18)
    (hn : x.regs len = keys.length)
    (hkb : x.regs keyBase = kb) (hpb : x.regs permBase = pb) (hbb : x.regs bufBase = bb)
    (hkeys : Block.HoldsList kb keys x.mem)
    (hdisj1 : kb + keys.length ≤ pb) (hdisj2 : pb + keys.length ≤ bb)
    (hfit : Fits w (bb + 2 * keys.length + 1)) :
    ∃ y : Data 18, ExecWithin w mergeSortPerm x y
        (52 * keys.length * Nat.clog 2 keys.length + 5 * keys.length + 7) ∧
      ∃ perm : List ℕ,
        Modifies (Block.mk pb (bb + keys.length - pb)).footprint x.mem y.mem ∧
        Block.HoldsList pb perm y.mem ∧
        perm.Perm (List.range keys.length) ∧
        perm.Pairwise (StableKeyOrder keys) ∧
        perm.Pairwise (fun a b => keys.getD a 0 ≤ keys.getD b 0) ∧
        y.regs len = keys.length ∧
        y.regs keyBase = kb ∧ y.regs permBase = pb ∧ y.regs bufBase = bb := by
  have hfit1 : Fits w 1 := hfit.of_le (by omega)
  have hinit_body (y : Data 18)
      (hy : InitPermInv keys kb pb bb x.mem (y.regs step) y)
      (hlt : y.regs step < keys.length) :
      ∃ z, ExecWithin w initPermBody y z 3 ∧
        InitPermInv keys kb pb bb x.mem (y.regs step + 1) z ∧
        z.regs step = y.regs step + 1 := by
    obtain ⟨hyo, hyn, hykb, hypb, hybb, hmod, hpre⟩ := hy
    refine WP.exists_execWithin ?_
    unfold initPermBody
    wram_exec [hyo, hypb]
    refine ⟨⟨by wram_simp [hyo], by wram_simp [hyn],
      by wram_simp [hykb], by wram_simp [hypb], by wram_simp [hybb], ?_, ?_⟩, by wram_simp⟩
    · wram_simp [Data.write_mem]
      rw [Modifies.block_iff]
      intro a ha; dsimp only at ha
      rw [Function.update_of_ne (by omega)]
      exact Modifies.block_iff.mp hmod a (by dsimp only; omega)
    · intro j hj
      wram_simp [Data.write_mem]
      by_cases hjeq : j = y.regs step
      · subst hjeq; exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]; exact hpre j (by omega)
  have houter_body (y : Data 18)
      (hy : OuterInv keys kb pb bb x.mem y)
      (hc : (Cond.lt wRun len).Holds y) :
      ∃ z, ExecWithin w outerPassBody y z (41 * keys.length + 9) ∧
        OuterInv keys kb pb bb x.mem z ∧
        Nat.clog 2 keys.length - Nat.log 2 (z.regs wRun) <
          Nat.clog 2 keys.length - Nat.log 2 (y.regs wRun) := by
    obtain ⟨hyn, hykb, hypb, hybb, hmodO,
      pass, L, hpass_le, hwrun, hL_hold, hL_perm, hL_pw, hL_rng⟩ := hy
    have hL_len : L.length = keys.length := by simpa using hL_perm.length_eq
    have hL_bound : ∀ v ∈ L, v < keys.length := fun v hv => List.mem_range.mp (hL_perm.subset hv)
    let W := 2 ^ pass
    have hW_pos : 0 < W := Nat.two_pow_pos pass
    have hW_lt : W < keys.length := by simpa only [Cond.holds_lt, hwrun, hyn] using hc
    have hpass_lt : pass < Nat.clog 2 keys.length :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hW_lt
    have hmid_body (u : Data 18)
        (hu : MidInv keys L kb pb bb W y.mem u)
        (hcu : (Cond.lt lo len).Holds u) :
        ∃ u' T_m, ExecWithin w mergePassBody u u' T_m ∧
          MidInv keys L kb pb bb W y.mem u' ∧
          T_m + 2 + 34 * (keys.length - u'.regs lo) ≤ 34 * (keys.length - u.regs lo) := by
      have hu_keys : Block.HoldsList kb keys u.mem := by
        refine hkeys.frame fun a ha1 ha2 => ?_
        have h1 := Modifies.block_iff.mp hu.mod a (by dsimp only; omega)
        have h2 := Modifies.block_iff.mp hmodO a (by dsimp only; omega)
        exact h1.trans h2
      have hu_L : Block.HoldsList pb L u.mem :=
        hL_hold.frame fun a ha1 ha2 => Modifies.block_iff.mp hu.mod a (by dsimp only; omega)
      exact mergePassBody_exec keys L y.mem hL_len hL_bound hL_pw hL_rng hW_pos hW_lt
        hdisj1 hdisj2 hfit u hu_keys hu_L hu hcu
    refine WP.exists_execWithin ?_
    unfold outerPassBody
    wram_exec [hfit1]
    refine WP.of_spec
      (ExecWithin.loop_potential (cond := .lt lo len) (body := mergePassBody)
        (MidInv keys L kb pb bb W y.mem)
        (fun u => 34 * (keys.length - u.regs lo)) hmid_body ?_) ?_
    · have hp := stableMergePrefix_empty keys L (2 * W)
      refine ⟨by wram_simp, by wram_simp [hyn],
        by wram_simp [hykb], by wram_simp [hypb], by wram_simp [hybb],
        by wram_simp [hwrun]; rfl, by wram_simp; omega,
        fun _ => ⟨0, by wram_simp; simp⟩,
        Modifies.refl _ _, [], by wram_simp; rfl,
        fun j hj => absurd hj (Nat.not_lt_zero j),
        by wram_simp; exact hp.perm, hp.runs.ordered, hp.runs.index_bounds⟩
    · rintro uM ⟨hIM, hstopM⟩
      obtain ⟨huMo, huMn, huMkb, huMpb, huMbb, huMw,
        huMlo_le, _, hmodM_end, L', hL'_len, hL'_mem, hL'_perm, hL'_pw, hL'_rng⟩ := hIM
      have hlo_end : uM.regs lo = keys.length := by
        simp only [Cond.holds_lt, huMn] at hstopM; omega
      rw [hlo_end, ← hL_len, List.take_length] at hL'_perm
      have hL'_perm_n : L'.Perm (List.range keys.length) := hL'_perm.trans hL_perm
      have hL'_len_n : L'.length = keys.length := by rw [hL'_len, hlo_end]
      have hsrc_uM : (uM.comap copyMap).regs ArrayCopy.src = bb := by
        simpa [Data.comap, copyMap, ArrayCopy.src] using huMbb
      have hdst_uM : (uM.comap copyMap).regs ArrayCopy.dst = pb := by
        simpa [Data.comap, copyMap, ArrayCopy.dst] using huMpb
      have hlen_uM : (uM.comap copyMap).regs ArrayCopy.len = keys.length := by
        simpa [Data.comap, copyMap, ArrayCopy.len] using huMn
      have hcopy := ExecWithin.rename_post copyMap_injective
        (ArrayCopy.exec_of_separated_or_eq (uM.comap copyMap) hfit1
          (by rw [hsrc_uM, hlen_uM]; exact hfit.of_le (by omega))
          (by rw [hdst_uM, hlen_uM]; exact hfit.of_le (by omega))
          (by rw [hsrc_uM, hdst_uM, hlen_uM]; exact Or.inr (Or.inl hdisj2)))
      rw [hlen_uM] at hcopy
      apply WP.seq
      refine WP.of_spec hcopy ?_
      rintro uC ⟨⟨huCm, huCs, huCd, huCl⟩, hout_cp⟩
      rw [hsrc_uM, hdst_uM] at huCm
      change uC.mem = ArrayCopy.copyPrefix uM.mem bb pb keys.length at huCm
      have huCbb : uC.regs bufBase = bb := by
        simpa [Data.comap, copyMap, ArrayCopy.src, huMbb] using huCs
      have huCpb : uC.regs permBase = pb := by
        simpa [Data.comap, copyMap, ArrayCopy.dst, huMpb] using huCd
      have huCn : uC.regs len = keys.length := by
        simpa [Data.comap, copyMap, ArrayCopy.len, huMn] using huCl
      have huCkb : uC.regs keyBase = kb :=
        (hout_cp keyBase (by decide)).trans huMkb
      have huCw : uC.regs wRun = W :=
        (hout_cp wRun (by decide)).trans huMw
      have hfit_w2 : Fits w (W + W) := hfit.of_le (by omega)
      wram_exec [huCw, hfit_w2]
      have hpow_succ : W + W = 2 ^ (pass + 1) := by simp [W, Nat.pow_succ]; omega
      refine ⟨⟨by wram_simp [huCn], by wram_simp [huCkb],
        by wram_simp [huCpb], by wram_simp [huCbb], ?_, pass + 1, L', by omega,
        by wram_simp [hpow_succ], ?_, hL'_perm_n, ?_, ?_⟩, ?_⟩
      · wram_simp
        rw [Modifies.block_iff]
        intro a ha; dsimp only at ha
        rw [huCm, ArrayCopy.copyPrefix_outside (by omega)]
        have h2 := Modifies.block_iff.mp hmodM_end a (by dsimp only; omega)
        have h3 := Modifies.block_iff.mp hmodO a (by dsimp only; omega)
        exact h2.trans h3
      · intro i
        change (uC.set wRun (W + W)).mem (pb + i.val) = L'[i.val]
        wram_simp
        have hi_L' : i.val < L'.length := i.isLt
        have hi_lt : i.val < keys.length := hL'_len_n ▸ hi_L'
        rw [huCm, ArrayCopy.copyPrefix_read hi_lt]
        exact hL'_mem i.val hi_L'
      · intro q
        simpa [show 2 ^ (pass + 1) = 2 * W by simp [W, Nat.pow_succ]; omega] using hL'_pw q
      · intro q z hz
        have h2W : 2 ^ (pass + 1) = 2 * W := by simp [W, Nat.pow_succ]; omega
        rw [h2W] at hz ⊢
        exact hL'_rng q z hz
      · wram_simp [hpow_succ, hwrun, Nat.log_pow Nat.one_lt_two]
        omega
  refine WP.exists_execWithin ?_
  unfold mergeSortPerm
  wram_exec [hfit1]
  refine WP.of_spec
    (ExecWithin.loop_count (index := step) (limit := len) (N := keys.length) (T := 3)
      (InitPermInv keys kb pb bb x.mem)
      (fun _ hu => hu.len_eq) hinit_body (by wram_simp; omega) ?_) ?_
  · refine ⟨by wram_simp, by wram_simp [hn],
      by wram_simp [hkb], by wram_simp [hpb], by wram_simp [hbb],
      Modifies.refl _ _, fun _ hj => by wram_simp at hj⟩
  · rintro yI ⟨hPI, _⟩
    obtain ⟨hyIo, hyIn, hyIkb, hyIpb, hyIbb, hmodI, hpreI⟩ := hPI
    wram_exec [hfit1]
    refine WP.of_spec
      (ExecWithin.loop_invariant (cond := .lt wRun len) (body := outerPassBody)
        (OuterInv keys kb pb bb x.mem)
        (fun y => Nat.clog 2 keys.length - Nat.log 2 (y.regs wRun)) (T := 41 * keys.length + 9)
        houter_body ?_) ?_
    · have hRuns := stableRuns_range keys
      refine ⟨by wram_simp [hyIn], by wram_simp [hyIkb],
        by wram_simp [hyIpb], by wram_simp [hyIbb], ?_,
        0, List.range keys.length, Nat.zero_le _, by wram_simp; rfl, ?_, List.Perm.refl _,
        hRuns.ordered, hRuns.index_bounds⟩
      · rw [Modifies.block_iff]
        intro a ha; dsimp only at ha
        exact Modifies.block_iff.mp hmodI a (by dsimp only; omega)
      · intro i
        have hi_lt : i.val < keys.length := by simpa using i.isLt
        change yI.mem (pb + i.val) = (List.range keys.length)[i.val]
        simp [hpreI i.val hi_lt]
    · rintro yF ⟨hIF, hstopF⟩
      obtain ⟨hyFn, hyFkb, hyFpb, hyFbb, hmodF,
        pass, perm, _, hwrunF, hperm_hold, hperm_range, hperm_pw, hperm_rng⟩ := hIF
      have hge_n : keys.length ≤ 2 ^ pass := by
        simp only [Cond.holds_lt, hwrunF, hyFn] at hstopF; omega
      have hperm_len : perm.length = keys.length := by simpa using hperm_range.length_eq
      have hperm_stable : perm.Pairwise (StableKeyOrder keys) :=
        StableRuns.finish ⟨hperm_pw, hperm_rng⟩ (hperm_len ▸ hge_n)
      refine ⟨?_, perm, hmodF, hperm_hold, hperm_range, hperm_stable,
        hperm_stable.imp StableKeyOrder.le, hyFn, hyFkb, hyFpb, hyFbb⟩
      wram_simp
      simp only [Nat.log_one_right, Nat.sub_zero]
      have h1 : Nat.clog 2 keys.length * (41 * keys.length + 9 + 2) ≤
          Nat.clog 2 keys.length * (52 * keys.length) := by
        rcases eq_or_ne keys.length 0 with h0 | hpos
        · simp [h0]
        · exact Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_comm (Nat.clog 2 keys.length) (52 * keys.length)] at h1
      omega

end Cslib.Algorithms.WordRAM.MergeSort
