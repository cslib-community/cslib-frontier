/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Sort
import Batteries.Data.List.Perm
import CslibFrontier.Foundations.Data.List.FilterMap
import CslibFrontier.Foundations.Data.List.Lex
import CslibFrontier.Foundations.Data.List.SortedCount
import Mathlib.Order.WithBot

/-!
# The Burrows–Wheeler transform and its inversion by the LF-mapping

The Burrows–Wheeler transform of a word `w` over a linearly ordered alphabet sorts all rotations
of `w` lexicographically (the matrix `M`), and outputs the last column `L` of `M` together with
the index `I` of the row equal to `w` ([BurrowsWheeler1994], Section 2, Algorithm C). It is
inverted by following the *LF-mapping* `T`: if `L[r]` is the `k`-th occurrence of a symbol `c`
in `L`, then `T r` is the position of the `k`-th occurrence of `c` in the first column `F`
(Algorithm D, step D2). Row `T r` of `M`, rotated left by one place, is row `r`, so the word is
read off backwards from `I` as `w[n - 1 - i] = L[T^[i] I]` (step D3).

The LF-mapping is computed from `L` alone as `T r = C[L[r]] + P[r]`, where `C[c]` counts the
symbols of `L` smaller than `c`, and `P[r]` counts the occurrences of `L[r]` in `L[0..r-1]`
(Section 4.2). The occurrence correspondence holds because `F` is sorted, and the rows that
start with `c`, rotated left by one place, are the rows that end in `c` in the same relative
order. Lexicographic order on equal-length rows is preserved by moving a common first symbol to
the end.

## Conventions

* The alphabet `α` is an arbitrary `LinearOrder`; rows are compared by Mathlib's lexicographic
  order on `List α`. No end-of-word sentinel is used.
* `bwtIndex w` is the *first* row of the sorted matrix equal to `w`, numbered from zero, as in
  [BurrowsWheeler1994], Algorithm C, step C1. Periodic words (`w = u ^ p`) have repeated rows.
  The transform still determines them, although the sequence `T^[i] (bwtIndex w)`,
  `i < |w|`, then repeats and is not a permutation of the rows (the remark after step D3).
* The empty word has the matrix `[[]]`, the last column `[]` and the index `0`.

## Main definitions

* `bwtMatrix w`: the rotations of `w`, sorted lexicographically.
* `bwtLast w`, `bwtFirst w`: the last and first columns of `bwtMatrix w`.
* `bwtIndex w`: the index of the first row of `bwtMatrix w` equal to `w`.
* `bwt w = (bwtLast w, bwtIndex w)`: the Burrows–Wheeler transform.
* `lfMap L r`: the LF-mapping `L.countP (· < L[r]) + (L.take r).count L[r]`, computed from the
  last column alone.
* `lfDecode L k r acc`: `k` LF steps from row `r`, prepending the symbols read.
* `inverseBwt (L, I)`: `L.length` LF steps from row `I`.

## Main results

* `bwtFirst_eq_mergeSort_bwtLast`: `F` is the sorted `L` (step D1).
* `rotate_one_getElem_bwtMatrix_lfMap`: row `lfMap (bwtLast w) r`, rotated left by one place,
  is row `r` (the LF-mapping, row form).
* `getElem?_bwtFirst_lfMap`, `count_take_bwtFirst_lfMap`: `F[lfMap L r] = L[r]`, and both are
  the same occurrence of that symbol (the LF-mapping, step D2).
* `lfMap_bwtLast_injOn`, `map_lfMap_range_perm`: the LF-mapping permutes the rows (step D2).
* `getElem?_bwtLast_iterate_lfMap`: `L[T^[i] I] = w[n - 1 - i]` (step D3).
* `inverseBwt_bwt`: `inverseBwt (bwt w) = w`, hence `bwt_injective`.

## References

* [BurrowsWheeler1994]
-/

public section

namespace Cslib.Algorithms.Lean.BurrowsWheeler

open List

variable {α : Type*}

/-! ## Order-free facts about rotations -/

private theorem map_rotate_one_cyclicPermutations (w : List α) :
    w.cyclicPermutations.map (·.rotate 1) = w.cyclicPermutations.rotate 1 := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  · apply List.ext_getElem (by simp)
    intro n h₁ h₂
    simp only [List.getElem_map, List.getElem_cyclicPermutations, List.getElem_rotate,
      List.rotate_rotate, List.length_cyclicPermutations_of_ne_nil w hw]
    rw [← List.rotate_mod w (n + 1)]

private theorem getLast?_rotate_one : ∀ u : List α, (u.rotate 1).getLast? = u.head?
  | [] => rfl
  | a :: u => by simp

private theorem filterMap_head?_cyclicPermutations (w : List α) :
    w.cyclicPermutations.filterMap List.head? = w := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_filterMap_of_forall_isSome fun u hu => Option.isSome_iff_ne_none.mpr <|
    mt List.head?_eq_none_iff.mp (by
      rwa [← Ne, ← List.length_pos_iff, List.length_mem_cyclicPermutations w hu,
        List.length_pos_iff])]
  rcases lt_or_ge i w.length with hi | hi
  · rw [List.getElem?_eq_getElem (by rwa [List.length_cyclicPermutations_of_ne_nil w hw]),
      List.getElem_cyclicPermutations, Option.bind_some, List.head?_rotate hi]
  · simp [List.length_cyclicPermutations_of_ne_nil w hw, hi]

variable [LinearOrder α]

/-! ## The transform -/

/-- The Burrows–Wheeler matrix: the rotations of `w`, sorted lexicographically
([BurrowsWheeler1994], Section 2, step C1). -/
def bwtMatrix (w : List α) : List (List α) :=
  w.cyclicPermutations.mergeSort (· ≤ ·)

/-- The last column `L` of the Burrows–Wheeler matrix ([BurrowsWheeler1994], Section 2,
step C2). -/
def bwtLast (w : List α) : List α := (bwtMatrix w).filterMap List.getLast?

/-- The first column `F` of the Burrows–Wheeler matrix ([BurrowsWheeler1994], Section 2,
step D1). -/
def bwtFirst (w : List α) : List α := (bwtMatrix w).filterMap List.head?

/-- The index `I` of the first row of the Burrows–Wheeler matrix equal to `w`, numbered from
zero ([BurrowsWheeler1994], Section 2, step C1). -/
def bwtIndex (w : List α) : ℕ := (bwtMatrix w).idxOf w

/-- The Burrows–Wheeler transform `(L, I)` ([BurrowsWheeler1994], Section 2, Algorithm C). -/
def bwt (w : List α) : List α × ℕ := (bwtLast w, bwtIndex w)

/-- The LF-mapping `T` of [BurrowsWheeler1994], Section 2, step D2, computed from the last
column as in Section 4.2: `T r = C[L[r]] + P[r]`, where `C[c]` counts the symbols of `L`
smaller than `c`, and `P[r]` counts the occurrences of `L[r]` before position `r`. It is the
identity out of range. -/
@[expose] def lfMap (L : List α) (r : ℕ) : ℕ :=
  match L[r]? with
  | some c => L.countP (· < c) + (L.take r).count c
  | none => r

/-- `lfDecode L k r acc` takes `k` LF steps from row `r`, prepending the last-column symbol of
each visited row to `acc` ([BurrowsWheeler1994], Section 2, step D3). It stops early out of
range. -/
@[expose] def lfDecode (L : List α) : ℕ → ℕ → List α → List α
  | 0, _, acc => acc
  | k + 1, r, acc =>
    match L[r]? with
    | some c => lfDecode L k (lfMap L r) (c :: acc)
    | none => acc

/-- The inverse Burrows–Wheeler transform: `L.length` LF steps from row `I`
([BurrowsWheeler1994], Section 2, Algorithm D). -/
@[expose] def inverseBwt (p : List α × ℕ) : List α := lfDecode p.1 p.1.length p.2 []

@[simp] theorem fst_bwt (w : List α) : (bwt w).1 = bwtLast w := by rw [bwt]

@[simp] theorem snd_bwt (w : List α) : (bwt w).2 = bwtIndex w := by rw [bwt]

/-! ## Basic facts -/

theorem bwtMatrix_perm (w : List α) : bwtMatrix w ~ w.cyclicPermutations :=
  List.mergeSort_perm _ _

theorem pairwise_bwtMatrix (w : List α) : (bwtMatrix w).Pairwise (· ≤ ·) :=
  List.pairwise_mergeSort' _ _

theorem length_of_mem_bwtMatrix {w u : List α} (hu : u ∈ bwtMatrix w) : u.length = w.length :=
  List.length_mem_cyclicPermutations w ((bwtMatrix_perm w).subset hu)

theorem length_bwtMatrix {w : List α} (hw : w ≠ []) : (bwtMatrix w).length = w.length := by
  rw [(bwtMatrix_perm w).length_eq, List.length_cyclicPermutations_of_ne_nil w hw]

theorem mem_bwtMatrix_self (w : List α) : w ∈ bwtMatrix w :=
  (bwtMatrix_perm w).symm.subset (List.mem_cyclicPermutations_self w)

theorem bwtIndex_lt_length (w : List α) : bwtIndex w < (bwtMatrix w).length :=
  List.idxOf_lt_length_of_mem (mem_bwtMatrix_self w)

/-- Row `bwtIndex w` of the matrix is `w`. -/
theorem getElem_bwtMatrix_bwtIndex (w : List α) :
    (bwtMatrix w)[bwtIndex w]'(bwtIndex_lt_length w) = w :=
  List.getElem_idxOf (bwtIndex_lt_length w)

@[simp] theorem bwtMatrix_nil : bwtMatrix ([] : List α) = [[]] := by simp [bwtMatrix]

@[simp] theorem bwtLast_nil : bwtLast ([] : List α) = [] := by simp [bwtLast]

@[simp] theorem bwtFirst_nil : bwtFirst ([] : List α) = [] := by simp [bwtFirst]

/-- Rotating every row of the matrix left by one place permutes its rows. -/
theorem map_rotate_one_bwtMatrix_perm (w : List α) :
    (bwtMatrix w).map (·.rotate 1) ~ bwtMatrix w :=
  calc (bwtMatrix w).map (·.rotate 1)
      ~ w.cyclicPermutations.map (·.rotate 1) := (bwtMatrix_perm w).map _
    _ = w.cyclicPermutations.rotate 1 := map_rotate_one_cyclicPermutations w
    _ ~ w.cyclicPermutations := List.rotate_perm _ _
    _ ~ bwtMatrix w := (bwtMatrix_perm w).symm

/-- Heads of rows, with `⊥` for the empty row. -/
private def headKey (u : List α) : WithBot α := u.head?

private theorem headKey_mono {u v : List α} (h : u ≤ v) : headKey u ≤ headKey v := by
  match u, v, h with
  | [], _, _ => exact bot_le
  | _ :: _, [], h => exact absurd h (not_le.mpr (List.nil_lt_cons _ _))
  | a :: u, b :: v, h =>
    change (a : WithBot α) ≤ b
    exact WithBot.coe_le_coe.mpr (List.cons_le_cons_iff'.mp h |>.elim le_of_lt (·.1.le))

/-- The rows starting with `c`, each rotated left by one place, are exactly the rows ending in
`c`, in the same order. -/
theorem filter_head_map_rotate_one (w : List α) (c : α) :
    ((bwtMatrix w).filter (·.head? = some c)).map (·.rotate 1) =
      (bwtMatrix w).filter (·.getLast? = some c) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · refine List.Pairwise.map _ ?_ (List.Pairwise.and_mem.mp ((pairwise_bwtMatrix w).filter _))
    rintro u v ⟨hu, hv, huv⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hu hv
    match u, v, hu.2, hv.2 with
    | _ :: u', _ :: v', rfl, hcv =>
      cases Option.some.inj hcv
      have hlen : u'.length = v'.length := by
        simpa using (length_of_mem_bwtMatrix hu.1).trans (length_of_mem_bwtMatrix hv.1).symm
      simp only [List.rotate_cons_succ, List.rotate_zero]
      rcases ((List.cons_le_cons_iff'.mp huv).resolve_left (lt_irrefl _)).2.lt_or_eq with h | rfl
      · exact (List.append_lt_append_of_lt_of_length_eq h hlen _ _).le
      · exact le_rfl
  · exact (pairwise_bwtMatrix w).filter _
  · simpa [List.filter_map, Function.comp_def, getLast?_rotate_one] using
      (map_rotate_one_bwtMatrix_perm w).filter (·.getLast? = some c)

private theorem isSome_getLast?_of_mem {w u : List α} (hw : w ≠ []) (hu : u ∈ bwtMatrix w) :
    u.getLast?.isSome :=
  Option.isSome_iff_ne_none.mpr <| mt List.getLast?_eq_none_iff.mp <| by
    rwa [← Ne, ← List.length_pos_iff, length_of_mem_bwtMatrix hu, List.length_pos_iff]

private theorem isSome_head?_of_mem {w u : List α} (hw : w ≠ []) (hu : u ∈ bwtMatrix w) :
    u.head?.isSome :=
  Option.isSome_iff_ne_none.mpr <| mt List.head?_eq_none_iff.mp <| by
    rwa [← Ne, ← List.length_pos_iff, length_of_mem_bwtMatrix hu, List.length_pos_iff]

/-- Entry `r` of the last column is the last symbol of row `r`. -/
theorem getElem?_bwtLast (w : List α) (r : ℕ) :
    (bwtLast w)[r]? = (bwtMatrix w)[r]?.bind List.getLast? := by
  rcases eq_or_ne w [] with rfl | hw
  · cases r <;> simp
  · exact List.getElem?_filterMap_of_forall_isSome (fun _ => isSome_getLast?_of_mem hw) r

/-- Entry `r` of the first column is the first symbol of row `r`. -/
theorem getElem?_bwtFirst (w : List α) (r : ℕ) :
    (bwtFirst w)[r]? = (bwtMatrix w)[r]?.bind List.head? := by
  rcases eq_or_ne w [] with rfl | hw
  · cases r <;> simp
  · exact List.getElem?_filterMap_of_forall_isSome (fun _ => isSome_head?_of_mem hw) r

@[simp] theorem length_bwtLast (w : List α) : (bwtLast w).length = w.length := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  · rw [bwtLast, List.filterMap_length_eq_length.mpr fun u hu => isSome_getLast?_of_mem hw hu,
      length_bwtMatrix hw]

/-- The first column is a permutation of the word ([BurrowsWheeler1994], Section 2, step D1). -/
theorem bwtFirst_perm (w : List α) : bwtFirst w ~ w := by
  simpa [bwtFirst, filterMap_head?_cyclicPermutations] using
    (bwtMatrix_perm w).filterMap List.head?

/-- The last column is a permutation of the word ([BurrowsWheeler1994], Section 2, step D1). -/
theorem bwtLast_perm (w : List α) : bwtLast w ~ w := by
  have h := (map_rotate_one_bwtMatrix_perm w).filterMap List.getLast?
  rw [List.filterMap_map, show (List.getLast? ∘ (·.rotate 1) : List α → _) = List.head? from
    funext getLast?_rotate_one] at h
  exact h.symm.trans (bwtFirst_perm w)

theorem pairwise_bwtFirst (w : List α) : (bwtFirst w).Pairwise (· ≤ ·) :=
  (pairwise_bwtMatrix w).filterMap _ fun _ _ huv _ ha _ hb =>
    WithBot.coe_le_coe.mp (by simpa [headKey, ha, hb, WithBot.some_eq_coe] using headKey_mono huv)

/-- The first column is the sorted last column ([BurrowsWheeler1994], Section 2, step D1). -/
theorem bwtFirst_eq_mergeSort_bwtLast (w : List α) :
    bwtFirst w = (bwtLast w).mergeSort (· ≤ ·) :=
  List.Perm.eq_of_pairwise' (pairwise_bwtFirst w) (List.pairwise_mergeSort' _ _)
    ((bwtFirst_perm w).trans ((bwtLast_perm w).symm.trans (List.mergeSort_perm _ _).symm))

/-! ## The LF-mapping -/

private theorem exists_lfMap (w : List α) {r : ℕ} (hr : r < (bwtMatrix w).length) :
    ∃ h : lfMap (bwtLast w) r < (bwtMatrix w).length,
      ((bwtMatrix w)[lfMap (bwtLast w) r]).rotate 1 = (bwtMatrix w)[r] := by
  rcases eq_or_ne w [] with rfl | hw
  · simp only [bwtLast_nil, lfMap, List.getElem?_nil]
    exact ⟨hr, by simp⟩
  let M := bwtMatrix w
  have hsome : ∀ u ∈ M, u.getLast?.isSome := fun _ => isSome_getLast?_of_mem hw
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hsome _ (List.getElem_mem hr))
  have hLr : (bwtLast w)[r]? = some c := by simp [getElem?_bwtLast, hr, hc]
  have hcount : ((bwtLast w).take r).count c = (M.take r).countP (·.getLast? = some c) := by
    rw [bwtLast, List.take_filterMap_of_forall_isSome hsome, List.count_eq_countP,
      List.countP_filterMap]
    exact List.countP_congr fun u _ => by cases u.getLast? <;> simp
  have hless : (bwtLast w).countP (· < c) = M.countP (fun u => headKey u < c) := by
    rw [bwtLast, List.countP_filterMap, ← (map_rotate_one_bwtMatrix_perm w).countP_eq,
      List.countP_map]
    refine List.countP_congr fun u hu => ?_
    obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil (by
      rwa [← List.length_pos_iff, length_of_mem_bwtMatrix hu, List.length_pos_iff])
    simp only [headKey, List.head?_cons, WithBot.some_eq_coe, WithBot.coe_lt_coe]
    simp
  have hlf : lfMap (bwtLast w) r =
      M.countP (fun u => headKey u < c) + (M.take r).countP (·.getLast? = some c) := by
    simp only [lfMap, hLr, hless, hcount]
  have hpos := List.getElem?_filter_countP_take (fun u => decide (u.getLast? = some c)) hr
    (by simpa using hc)
  rw [← filter_head_map_rotate_one, List.getElem?_map,
    show (bwtMatrix w).filter (·.head? = some c) = M.filter (fun u => headKey u = c) from rfl,
    List.Pairwise.filter_key_eq headKey (c : WithBot α) ((pairwise_bwtMatrix w).imp headKey_mono),
    List.getElem?_take, List.getElem?_drop] at hpos
  split_ifs at hpos with hk
  · obtain ⟨v, hv, hvr⟩ := Option.map_eq_some_iff.mp hpos
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    rw [hlf]
    exact ⟨hlt, hvr⟩
  · simp at hpos

/-- The LF-mapping stays inside the matrix. -/
theorem lfMap_bwtLast_lt (w : List α) {r : ℕ} (hr : r < (bwtMatrix w).length) :
    lfMap (bwtLast w) r < (bwtMatrix w).length :=
  (exists_lfMap w hr).1

/-- **LF-mapping, row form** ([BurrowsWheeler1994], Section 2, step D2): row
`lfMap (bwtLast w) r`, rotated left by one place, is row `r`. -/
theorem rotate_one_getElem_bwtMatrix_lfMap (w : List α) {r : ℕ}
    (hr : r < (bwtMatrix w).length) :
    ((bwtMatrix w)[lfMap (bwtLast w) r]'(lfMap_bwtLast_lt w hr)).rotate 1 = (bwtMatrix w)[r] :=
  (exists_lfMap w hr).2

/-- **LF-mapping, symbol form:** the first symbol of row `lfMap (bwtLast w) r` is the last
symbol of row `r`. -/
theorem getElem?_bwtFirst_lfMap (w : List α) (r : ℕ) :
    (bwtFirst w)[lfMap (bwtLast w) r]? = (bwtLast w)[r]? := by
  rcases lt_or_ge r (bwtMatrix w).length with hr | hr
  · rw [getElem?_bwtFirst, getElem?_bwtLast, List.getElem?_eq_getElem hr,
      List.getElem?_eq_getElem (lfMap_bwtLast_lt w hr), Option.bind_some, Option.bind_some,
      ← rotate_one_getElem_bwtMatrix_lfMap w hr, getLast?_rotate_one]
  · have hL : (bwtLast w)[r]? = none := by simp [getElem?_bwtLast, List.getElem?_eq_none hr]
    simp [hL, lfMap, getElem?_bwtFirst, List.getElem?_eq_none hr]

/-- **LF-mapping, occurrence form** ([BurrowsWheeler1994], Section 2, step D2): if entry `r` of
the last column is the `k`-th occurrence of `c` there, then entry `lfMap (bwtLast w) r` of the
first column is the `k`-th occurrence of `c` there. -/
theorem count_take_bwtFirst_lfMap (w : List α) {r : ℕ} {c : α}
    (hc : (bwtLast w)[r]? = some c) :
    ((bwtFirst w).take (lfMap (bwtLast w) r)).count c = ((bwtLast w).take r).count c := by
  have hperm := (bwtFirst_perm w).trans (bwtLast_perm w).symm
  rw [lfMap, hc]
  dsimp only
  rw [← hperm.countP_eq, List.Pairwise.count_take_countP_lt_add c _ (pairwise_bwtFirst w),
    hperm.count_eq]
  exact Nat.min_eq_left ((List.take_sublist _ _).count_le c)

/-- The LF-mapping is one-to-one on the rows ([BurrowsWheeler1994], Section 2, step D2). -/
theorem lfMap_bwtLast_injOn (w : List α) {r r' : ℕ} (hr : r < (bwtMatrix w).length)
    (hr' : r' < (bwtMatrix w).length) (h : lfMap (bwtLast w) r = lfMap (bwtLast w) r') :
    r = r' := by
  rcases eq_or_ne w [] with rfl | hw
  · simp only [bwtMatrix_nil, List.length_singleton] at hr hr'
    omega
  have hlen : (bwtLast w).length = (bwtMatrix w).length := by
    rw [length_bwtLast, length_bwtMatrix hw]
  -- the key step: an earlier occurrence index has a strictly smaller rank
  have key {a b : ℕ} (hab : a < b) (hb : b < (bwtMatrix w).length)
      (hab' : lfMap (bwtLast w) a = lfMap (bwtLast w) b) : False := by
    have ha : a < (bwtLast w).length := by omega
    have hc : (bwtLast w)[a]? = some (bwtLast w)[a] := List.getElem?_eq_getElem ha
    have hcb : (bwtLast w)[b]? = some (bwtLast w)[a] := by
      rw [← getElem?_bwtFirst_lfMap, ← hab', getElem?_bwtFirst_lfMap, hc]
    have e1 := hab' ▸ count_take_bwtFirst_lfMap w hc
    rw [count_take_bwtFirst_lfMap w hcb] at e1
    have hmono :=
      ((List.take_prefix_take_left (l := bwtLast w) hab).sublist).count_le (bwtLast w)[a]
    rw [List.take_add_one, List.count_append, hc] at hmono
    simp at hmono
    omega
  rcases lt_trichotomy r r' with hlt | rfl | hgt
  · exact (key hlt hr' h).elim
  · rfl
  · exact (key hgt hr h.symm).elim

/-- The LF-mapping permutes the rows ([BurrowsWheeler1994], Section 2, step D2). -/
theorem map_lfMap_range_perm (w : List α) :
    (List.range (bwtMatrix w).length).map (lfMap (bwtLast w)) ~
      List.range (bwtMatrix w).length := by
  refine (List.subperm_of_subset
    (List.Nodup.map_on (fun _ hx _ hy => lfMap_bwtLast_injOn w
      (List.mem_range.mp hx) (List.mem_range.mp hy)) List.nodup_range)
    fun x hx => ?_).perm_of_length_le (by simp)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact List.mem_range.mpr (lfMap_bwtLast_lt w (List.mem_range.mp hr))

/-- One decoding step: if row `r` holds `w.rotate (k + 1)`, then entry `r` of the last column is
`w[k]`, and the LF-mapping moves to a row holding `w.rotate k`. -/
theorem bwtLast_lfMap_step (w : List α) {k r : ℕ} (hk : k < w.length)
    (hr : r < (bwtMatrix w).length) (hrow : (bwtMatrix w)[r] = w.rotate (k + 1)) :
    (bwtLast w)[r]? = some w[k] ∧
      (bwtMatrix w)[lfMap (bwtLast w) r]'(lfMap_bwtLast_lt w hr) = w.rotate k := by
  refine ⟨?_, List.rotate_injective 1 ?_⟩
  · rw [getElem?_bwtLast, List.getElem?_eq_getElem hr, Option.bind_some, hrow,
      List.getLast?_eq_getElem?, List.length_rotate, List.getElem?_rotate (by omega),
      show w.length - 1 + (k + 1) = k + w.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hk, List.getElem?_eq_getElem hk]
  · change ((bwtMatrix w)[lfMap (bwtLast w) r]'(lfMap_bwtLast_lt w hr)).rotate 1 =
      (w.rotate k).rotate 1
    rw [rotate_one_getElem_bwtMatrix_lfMap w hr, hrow, List.rotate_rotate]

/-- After `i ≤ |w|` LF steps from `bwtIndex w`, the current row holds `w.rotate (|w| - i)`. -/
theorem getElem?_bwtMatrix_iterate_lfMap (w : List α) :
    ∀ i ≤ w.length,
      (bwtMatrix w)[(lfMap (bwtLast w))^[i] (bwtIndex w)]? = some (w.rotate (w.length - i))
  | 0, _ => by
    rw [Function.iterate_zero_apply, Nat.sub_zero, List.rotate_length,
      List.getElem?_eq_getElem (bwtIndex_lt_length w), getElem_bwtMatrix_bwtIndex]
  | i + 1, hi => by
    obtain ⟨hr, hrow⟩ :=
      List.getElem?_eq_some_iff.mp (getElem?_bwtMatrix_iterate_lfMap w i (by omega))
    rw [show w.length - i = w.length - 1 - i + 1 by omega] at hrow
    rw [Function.iterate_succ_apply', List.getElem?_eq_getElem (lfMap_bwtLast_lt w hr),
      (bwtLast_lfMap_step w (by omega) hr hrow).2,
      show w.length - 1 - i = w.length - (i + 1) by omega]

/-- **Decoding formula** ([BurrowsWheeler1994], Section 2, step D3): `w[n - 1 - i]` is the
last-column symbol of the row reached by `i` LF steps from `bwtIndex w`. -/
theorem getElem?_bwtLast_iterate_lfMap (w : List α) {i : ℕ} (hi : i < w.length) :
    (bwtLast w)[(lfMap (bwtLast w))^[i] (bwtIndex w)]? = w[w.length - 1 - i]? := by
  obtain ⟨hr, hrow⟩ :=
    List.getElem?_eq_some_iff.mp (getElem?_bwtMatrix_iterate_lfMap w i hi.le)
  rw [show w.length - i = w.length - 1 - i + 1 by omega] at hrow
  rw [(bwtLast_lfMap_step w (by omega) hr hrow).1, List.getElem?_eq_getElem (by omega)]

/-! ## Inversion -/

/-- Decoding invariant: from a row holding the rotation `w.rotate k`, `k` LF steps prepend
`w[0], …, w[k-1]` to the accumulator. -/
theorem lfDecode_bwtLast (w : List α) :
    ∀ (k : ℕ), k ≤ w.length → ∀ (r : ℕ) (hr : r < (bwtMatrix w).length),
      (bwtMatrix w)[r] = w.rotate k → lfDecode (bwtLast w) k r (w.drop k) = w
  | 0, _, _, _, _ => by simp [lfDecode]
  | k + 1, hk, r, hr, hrow => by
    obtain ⟨hL, hrow'⟩ := bwtLast_lfMap_step w (by omega) hr hrow
    simp only [lfDecode, hL, ← List.drop_eq_getElem_cons (by omega : k < w.length)]
    exact lfDecode_bwtLast w k (by omega) _ (lfMap_bwtLast_lt w hr) hrow'

/-- **Invertibility** ([BurrowsWheeler1994], Section 2, Algorithm D): the LF-mapping decoder
recovers the word from its transform. -/
theorem inverseBwt_bwt (w : List α) : inverseBwt (bwt w) = w := by
  simpa [inverseBwt, List.drop_length] using lfDecode_bwtLast w w.length le_rfl _
    (bwtIndex_lt_length w) ((List.rotate_length w).symm ▸ getElem_bwtMatrix_bwtIndex w)

theorem leftInverse_inverseBwt_bwt :
    Function.LeftInverse (inverseBwt : List α × ℕ → List α) bwt :=
  inverseBwt_bwt

/-- The Burrows–Wheeler transform, with its index, is injective. -/
theorem bwt_injective : Function.Injective (bwt : List α → List α × ℕ) :=
  leftInverse_inverseBwt_bwt.injective

end Cslib.Algorithms.Lean.BurrowsWheeler
