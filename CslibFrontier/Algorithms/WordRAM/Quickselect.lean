/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.Quicksort
import CslibFrontier.Computability.WordRAM.Randomized.LoopSegment
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Data.List.Sort

/-!
# In-place randomized quickselect on the word RAM

Iterative in-place 3-way randomized quickselect over `Cslib.WordRAM.Basis.standard`. Given an
`n`-word slice starting at address `base` and a `0`-indexed target rank `k < n`, the algorithm
selects the `k`-th smallest element `input.mergeSort[k]` in place using zero auxiliary memory
words (`O(1)` registers only).

The selection loop maintains a single active subarray `[lo, hi)` of length `m = hi - lo`
containing the target address `target = base + k` (`lo ≤ target < hi`). When `2 ≤ m`, each
iteration samples a uniform pivot offset `off ← rand (m - 1)` with pivot value
`piv = mem (lo + off)` and applies Dutch National Flag 3-way partitioning to split `[lo, hi)` into
`< piv` on `[lo, lt)`, `= piv` on `[lt, gt)`, and `> piv` on `[gt, hi)`:
1. **Pathwise correctness and zero auxiliary space:** Every execution path halts cleanly and
   returns `input.mergeSort[k]`. The final memory permutes `[base, base + n)` in place so that
   `mem (base + k) = input.mergeSort[k]`, `mem (base + i) ≤ mem (base + k)` for `i < k`, and
   `mem (base + k) ≤ mem (base + i)` for `k < i < n`. All memory outside
   `Finset.Ico base (base + n)` is unchanged.
2. **Strict worst-case bounds:** Because the `= piv` region `[lt, gt)` contains the sampled pivot,
   `lt < gt` holds and each iteration strictly decreases `m = hi - lo`. Every execution path
   makes at most `n - 1` `rand` calls and executes at most `10 * n ^ 2 + 15` instructions.
3. **Unconditional linear expected running time (including duplicates):** All copies of `piv` in
   `[lo, hi)` land in `[lt, gt)`. When `lt ≤ target < gt`, the active range collapses immediately
   to length `1`; otherwise, for a sampled pivot of sorted rank `r < m` in `[lo, hi)`, the next
   active subarray has length at most `max r (m - 1 - r)`. The identity
   `4 * ∑_{r < m} max r (m - 1 - r) ≤ 3 * m ^ 2` gives a `(3 / 4)`-shrinking linear potential
   `80 * m` on the active subarray length `m`, proving
   `expectedTime w program (.init (k :: input)) ≤ 80 * n + 15` uniformly over all `k < n` and all
   duplicate-key patterns.
4. **Total out-of-range handling:** On `State.init (k :: input)` satisfying
   `InputFits w (k :: input)` with `n ≤ k`, `program` skips `selectSlice` and halts
   deterministically in `8` instructions with output `0`, `0` `rand` calls, and unchanged memory.

## Main definitions

* `Cslib.Algorithms.WordRAM.Quickselect.samplePivot`,
  `Cslib.Algorithms.WordRAM.Quickselect.narrowRange`,
  `Cslib.Algorithms.WordRAM.Quickselect.partitionAndNarrow`,
  `Cslib.Algorithms.WordRAM.Quickselect.selectStep`,
  `Cslib.Algorithms.WordRAM.Quickselect.selectSetup`,
  `Cslib.Algorithms.WordRAM.Quickselect.loadHeader`: structured building blocks of the selection
  loop and `Data.init` header.
* `Cslib.Algorithms.WordRAM.Quickselect.selectSlice`: reusable 16-register structured subroutine
  selecting rank `regs rk` in `[regs base, regs base + regs len)` in place.
* `Cslib.Algorithms.WordRAM.Quickselect.code`, `Cslib.Algorithms.WordRAM.Quickselect.program`:
  structured and compiled 16-register randomized quickselect on `State.init (k :: input)`.
* `Cslib.Algorithms.WordRAM.Quickselect.worstCaseTime`: quadratic worst-case step bound
  `10 * n ^ 2 + 15`.
* `Cslib.Algorithms.WordRAM.Quickselect.expectedTimeBound`: linear expected step bound
  `80 * n + 15`.

## Main results

* `Cslib.Algorithms.WordRAM.Quickselect.selectSlice_spec`: `ExecRandWithin` and linear
  `expectedCodeTime` specification for `selectSlice` on an arbitrary slice `[base, base + n)`.
* `Cslib.Algorithms.WordRAM.Quickselect.loadHeader_spec`,
  `Cslib.Algorithms.WordRAM.Quickselect.code_spec`,
  `Cslib.Algorithms.WordRAM.Quickselect.code_out_of_range_spec`: structured `loadHeader` and `code`
  specifications for `k < input.length` and `input.length ≤ k`.
* `Cslib.Algorithms.WordRAM.Quickselect.quickselect_correct_and_bounds`: joint certificate of
  `RandHaltsWithin`, `RandCallsBounded` (`≤ n - 1`), pathwise order-statistic output, in-place
  partition order, zero-auxiliary-memory `Modifies` frame, and `O(n)` `expectedTime` at word size
  `w ≥ logWidth 2 input.length`.
* `Cslib.Algorithms.WordRAM.Quickselect.quickselect_out_of_range`: deterministic `8`-step halting
  when `input.length ≤ k`.

Classical randomized selection (`RANDOMIZED-SELECT`) appears in [CLRS2009], Section 9.2; see also
[MitzenmacherUpfal2017], Section 3.5 (sampling-based median selection, related background). The
3-way Dutch National Flag word-RAM formulation, zero-auxiliary-memory frame, pure-`ℕ` linear drift
potential `80 * m`, and duplicate-key rank domination are original to this formalization.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.2.
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017], Section 3.5.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.Algorithms.WordRAM.Quickselect

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Quicksort (memSlice length_memSlice getElem_memSlice
  mem_memSlice_iff memSlice_congr memSlice_append partition_counts_and_lt sum_countP_pivot_le)

/-! ## Expected-selection linear potential recurrence -/

/-- Elementary sum bound for randomized selection: `4 * ∑_{r < m} max r (m - 1 - r) ≤ 3 * m ^ 2`
for every `m : ℕ`. -/
private theorem four_mul_sum_max_le : ∀ m : ℕ,
    4 * ∑ r ∈ Finset.range m, max r (m - 1 - r) ≤ 3 * m ^ 2
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have ih := four_mul_sum_max_le m
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∑ r ∈ Finset.range m, max (r + 1) (m + 2 - 1 - (r + 1)) =
        (∑ r ∈ Finset.range m, max r (m - 1 - r)) + m :=
      (Finset.sum_congr rfl fun r hr => by
        rw [Finset.mem_range] at hr; omega :
          ∑ r ∈ Finset.range m, max (r + 1) (m + 2 - 1 - (r + 1)) =
            ∑ r ∈ Finset.range m, (max r (m - 1 - r) + 1)).trans
        (by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one])
    rw [hmid, show max 0 (m + 2 - 1 - 0) = m + 1 by omega,
      show max (m + 1) (m + 2 - 1 - (m + 1)) = m + 1 by omega,
      show (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 by ring]
    omega

/-- Linear expected-time potential `Φ(m) = 0` for `m < 2` and `80 * m` for `m ≥ 2`. -/
private def expSubCost (m : ℕ) : ℕ :=
  if m < 2 then 0 else 80 * m

private theorem expSubCost_le (m : ℕ) : expSubCost m ≤ 80 * m := by
  unfold expSubCost
  split_ifs <;> omega

/-! ## Order-statistic characterization and word-size bound -/

private theorem countP_ge_succ_of_prefix {l : List ℕ} {k : ℕ} (hk : k < l.length) {p : ℕ → Bool}
    (h : ∀ i (hi : i < l.length), i ≤ k → p (l[i]'hi) = true) :
    k + 1 ≤ l.countP p := by
  have htake : (l.take (k + 1)).countP p = k + 1 := by
    rw [List.countP_eq_length.mpr fun _ hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.length_take] at hi
      simpa only [List.getElem_take] using h i (by omega) (by omega), List.length_take]
    omega
  calc k + 1 = (l.take (k + 1)).countP p := htake.symm
    _ ≤ (l.take (k + 1) ++ l.drop (k + 1)).countP p := by rw [List.countP_append]; omega
    _ = l.countP p := by rw [List.take_append_drop]

private theorem countP_le_of_suffix {l : List ℕ} (k : ℕ) {p : ℕ → Bool}
    (h : ∀ i (hi : i < l.length), k ≤ i → p (l[i]'hi) = false) :
    l.countP p ≤ k := by
  have hdrop : (l.drop k).countP p = 0 := List.countP_eq_zero.mpr fun _ hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_drop] at hj
    simp [List.getElem_drop, h (k + j) (by omega) (by omega)]
  calc l.countP p = (l.take k ++ l.drop k).countP p := by rw [List.take_append_drop]
    _ = (l.take k).countP p := by rw [List.countP_append, hdrop, add_zero]
    _ ≤ (l.take k).length := List.countP_le_length
    _ ≤ k := by simp

/-- If `xs` is a permutation of `ys` partitioned around index `k < ys.length` so that
`xs[i] ≤ xs[k]` for `i < k` and `xs[k] ≤ xs[i]` for `k < i < xs.length`, then `xs[k]` equals the
`k`-th sorted element `ys.mergeSort[k]` (regardless of duplicate keys). -/
private theorem eq_mergeSort_getElem_of_perm_of_partitioned {xs ys : List ℕ} {k : ℕ}
    (hperm : xs.Perm ys) (hk : k < ys.length)
    (hleft : ∀ i (hi : i < k),
      xs[i]'(by have := hperm.length_eq; omega) ≤ xs[k]'(by have := hperm.length_eq; omega))
    (hright : ∀ i, k < i → (hi : i < xs.length) →
      xs[k]'(by have := hperm.length_eq; omega) ≤ xs[i]'hi) :
    xs[k]'(by rw [hperm.length_eq]; exact hk) =
      ys.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) := by
  have hkx : k < xs.length := hperm.length_eq ▸ hk
  have hks : k < ys.mergeSort.length := (List.length_mergeSort ys).symm ▸ hk
  have hp_sort : xs.Perm ys.mergeSort := hperm.trans (List.mergeSort_perm ys _).symm
  have hp_pw := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≤ ·) ys)
  set v := xs[k]'hkx; set s := ys.mergeSort[k]'hks
  apply Nat.le_antisymm <;> by_contra hnot
  · have hlt : s < v := Nat.lt_of_not_ge hnot
    have hge := countP_ge_succ_of_prefix (p := (· < v)) hks fun i hi hik => decide_eq_true <|
      hik.eq_or_lt.elim (fun h => by subst h; exact hlt) fun h =>
        (hp_pw i k hi hks h).trans_lt hlt
    have hle := countP_le_of_suffix (p := (· < v)) k (l := xs) fun i hi hki =>
      decide_eq_false <| Nat.not_lt.mpr <|
        hki.eq_or_lt.elim (fun h => by subst h; exact le_rfl) fun h => hright i h hi
    have := hp_sort.countP_eq (· < v); omega
  · have hlt : v < s := Nat.lt_of_not_ge hnot
    have hge := countP_ge_succ_of_prefix (p := (· ≤ v)) hkx fun i _ hik => decide_eq_true <|
      hik.eq_or_lt.elim (fun h => by subst h; exact le_rfl) (hleft i)
    have hle := countP_le_of_suffix (p := (· ≤ v)) k (l := ys.mergeSort) fun i hi hki =>
      decide_eq_false <| Nat.not_le.mpr <|
        hki.eq_or_lt.elim (fun h => by subst h; exact hlt) fun h =>
          hlt.trans_le (hp_pw k i hks hi h)
    have := hp_sort.countP_eq (· ≤ v); omega

/-- `logWidth 2 n ≤ w` suffices to fit every address up to `n + 2` for all `n : ℕ`. -/
private theorem fits_add_two {n w : ℕ} (hw : logWidth 2 n ≤ w) :
    Fits w (n + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Fits.mono (w := 2) (by decide) (by simpa [logWidth] using hw)
  · exact (fits_of_lt_pow (k := 2) (n := n)
      (by rw [show (n + 1) ^ 2 = n * n + 2 * n + 1 by ring]; nlinarith)).mono hw

/-! ## Structured WordRAM quickselect program (`r = 16`) -/

namespace Reg

/-- Output register (also `0` initially in `Data.init`). -/
@[simp] abbrev ans : Fin 16 := 0
/-- Constant `1` (`Quicksort.Reg.one`). -/
@[simp] abbrev one : Fin 16 := Quicksort.Reg.one
/-- Target `0`-indexed rank `k`. -/
@[simp] abbrev rk : Fin 16 := 2
/-- Slice length `n`. -/
@[simp] abbrev len : Fin 16 := 3
/-- Slice base address `base`. -/
@[simp] abbrev base : Fin 16 := 4
/-- Target cell address `base + k`. -/
@[simp] abbrev target : Fin 16 := 5
/-- Maintained value `lo + 1` for the loop test `lo + 1 < hi`. -/
@[simp] abbrev lo1 : Fin 16 := 6
/-- Active subarray start address `lo` (`Quicksort.Reg.lo`). -/
@[simp] abbrev lo : Fin 16 := Quicksort.Reg.lo
/-- Active subarray exclusive end address `hi` (`Quicksort.Reg.hi`). -/
@[simp] abbrev hi : Fin 16 := Quicksort.Reg.hi
/-- 3-way partition `< piv` boundary `lt` (`Quicksort.Reg.lt`). -/
@[simp] abbrev lt : Fin 16 := Quicksort.Reg.lt
/-- 3-way partition scan cursor `cur` (`Quicksort.Reg.cur`). -/
@[simp] abbrev cur : Fin 16 := Quicksort.Reg.cur
/-- 3-way partition `> piv` boundary `gt` (`Quicksort.Reg.gt`). -/
@[simp] abbrev gt : Fin 16 := Quicksort.Reg.gt
/-- Pivot value `piv` (`Quicksort.Reg.piv`). -/
@[simp] abbrev piv : Fin 16 := Quicksort.Reg.piv
/-- Element scratch `val` (`Quicksort.Reg.val`). -/
@[simp] abbrev val : Fin 16 := Quicksort.Reg.val
/-- Swap scratch `val2` (`Quicksort.Reg.val2`). -/
@[simp] abbrev val2 : Fin 16 := Quicksort.Reg.val2
/-- Offset / address scratch `tmp` (`Quicksort.Reg.tmp`). -/
@[simp] abbrev tmp : Fin 16 := Quicksort.Reg.tmp

end Reg

open Reg

/-- Sample a uniform pivot offset `tmp ← rand (hi - (lo + 1))` (`2` instructions, `1` `rand`
call). -/
def samplePivot : Code .standard 16 := ram[
  tmp ← hi - lo1;
  tmp ← rand tmp ]

/-- Narrow `[lo, hi)` (alongside `lo1 = lo + 1`) to the unique 3-way partition region containing
`target` (`≤ 6` instructions, zero `.sub`/`.div`/`.mod` operations). -/
def narrowRange : Code .standard 16 := ram[
  if target < lt then [
    hi ← lt
  ] else [
    if target < gt then [
      lo ← target;
      lo1 ← target + one;
      hi ← lo1
    ] else [
      lo ← gt;
      lo1 ← lo + one
    ]
  ] ]

/-- Partition `[lo, hi)` around the pivot at `lo + tmp` and narrow `[lo, hi)` around `target`. -/
def partitionAndNarrow : Code .standard 16 := ram[
  ⟪Quicksort.partInit⟫;
  while cur < gt do [ ⟪Quicksort.partStep⟫ ];
  ⟪narrowRange⟫ ]

/-- One iteration of the quickselect loop on `[lo, hi)` (`lo + 1 < hi`). -/
def selectStep : Code .standard 16 := ram[
  ⟪samplePivot⟫;
  ⟪partitionAndNarrow⟫ ]

/-- Deterministic `5`-instruction setup of `selectSlice`. -/
def selectSetup : Code .standard 16 := ram[
  one ← #1;
  target ← base + rk;
  lo ← base;
  lo1 ← lo + one;
  hi ← base + len ]

/-- Reusable structured in-place quickselect subroutine on `[regs base, regs base + regs len)`:
permutes the slice in place around rank `regs rk` and stores the selected element in `ans`. -/
def selectSlice : Code .standard 16 := ram[
  ⟪selectSetup⟫;
  while lo1 < hi do [ ⟪selectStep⟫ ];
  ans ← *target ]

/-- Deterministic `4`-instruction header reading `len = M[0] - 1` and `rk = M[1]` on
`Data.init (k :: input)`. -/
def loadHeader : Code .standard 16 := ram[
  len ← *ans;
  one ← #1;
  rk ← *one;
  len ← len - one ]

/-- Structured 16-register quickselect on `Data.init (k :: input)`: selects `input.mergeSort[k]`
in `[2, input.length + 2)` when `k < input.length`, and sets `ans ← 0` otherwise. -/
def code : Code .standard 16 := ram[
  ⟪loadHeader⟫;
  if rk < len then [
    base ← one + one;
    ⟪selectSlice⟫
  ] else [
    ans ← #0
  ] ]

/-- Compiled flat 16-register randomized quickselect program halting with `ans`. -/
def program : Program .standard 16 :=
  code.program ans

/-- Quadratic worst-case instruction budget `10 * n ^ 2 + 15`. -/
def worstCaseTime (n : ℕ) : ℕ :=
  10 * n ^ 2 + 15

/-- Linear expected instruction budget `80 * n + 15`. -/
def expectedTimeBound (n : ℕ) : ℕ :=
  80 * n + 15

/-! ## Selection invariant and subroutine specifications -/

/-- Cut property at address `cut` across `[vbase, vbase + n)`: every element before `cut` is at
most every element from `cut` onward. -/
private def IsCut (vbase n cut : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ a b, vbase ≤ a → a < cut → cut ≤ b → b < vbase + n → mem a ≤ mem b

/-- Outer loop invariant of `selectSlice` on `[vbase, vbase + n)` for rank `k < n`. -/
private structure SelectInv (w vbase n k : ℕ) (s₀ : List ℕ) (mem₀ : ℕ → ℕ)
    (x : Data 16) : Prop where
  /-- Register `one` holds `1`. -/
  one_eq : x.regs one = 1
  /-- Register `target` holds `vbase + k`. -/
  target_eq : x.regs target = vbase + k
  /-- Register `lo1` holds `lo + 1`. -/
  lo1_eq : x.regs lo1 = x.regs lo + 1
  /-- `vbase + n` fits in a `w`-bit word. -/
  fits_end : Fits w (vbase + n)
  /-- `vbase ≤ lo`. -/
  base_le_lo : vbase ≤ x.regs lo
  /-- `lo ≤ vbase + k`. -/
  lo_le_target : x.regs lo ≤ vbase + k
  /-- `vbase + k < hi`. -/
  target_lt_hi : vbase + k < x.regs hi
  /-- `hi ≤ vbase + n`. -/
  hi_le_end : x.regs hi ≤ vbase + n
  /-- `mem[vbase .. vbase + n)` is a permutation of `s₀`. -/
  perm : (memSlice vbase (vbase + n) x.mem).Perm s₀
  /-- Only `Finset.Ico vbase (vbase + n)` has been modified since `mem₀`. -/
  modifies : Modifies (Finset.Ico vbase (vbase + n)) mem₀ x.mem
  /-- `lo` is an order cut of `[vbase, vbase + n)`. -/
  cut_lo : IsCut vbase n (x.regs lo) x.mem
  /-- `hi` is an order cut of `[vbase, vbase + n)`. -/
  cut_hi : IsCut vbase n (x.regs hi) x.mem

private theorem perm_global_of_sub {vbase n vlo vhi : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hlo : vbase ≤ vlo) (hhi : vhi ≤ vbase + n) (hle : vlo ≤ vhi)
    (hperm : (memSlice vlo vhi mem₂).Perm (memSlice vlo vhi mem₁))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₁ mem₂) :
    (memSlice vbase (vbase + n) mem₂).Perm (memSlice vbase (vbase + n) mem₁) := by
  have hsub (a b : ℕ) (ha : ∀ x, a ≤ x → x < b → ¬(vlo ≤ x ∧ x < vhi)) :
      memSlice a b mem₂ = memSlice a b mem₁ :=
    memSlice_congr fun x h1 h2 => hmod x (by rw [Finset.mem_Ico]; exact ha x h1 h2)
  rw [memSlice_append hlo (by omega) mem₂, memSlice_append hle hhi mem₂,
    memSlice_append hlo (by omega) mem₁, memSlice_append hle hhi mem₁,
    hsub vbase vlo (fun _ _ _ => by omega), hsub vhi (vbase + n) (fun _ _ _ => by omega)]
  exact List.Perm.append_left _ (hperm.append_right _)

private theorem cut_preserved_lo {vbase n vlo vhi : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hhi : vhi ≤ vbase + n)
    (hperm : (memSlice vlo vhi mem₂).Perm (memSlice vlo vhi mem₁))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₁ mem₂)
    (hcut : IsCut vbase n vlo mem₁) :
    IsCut vbase n vlo mem₂ := fun a b ha1 ha2 hb1 hb2 => by
  rw [hmod a (by rw [Finset.mem_Ico]; omega)]
  by_cases hb_hi : b < vhi
  · obtain ⟨b', hb'1, hb'2, heq⟩ := mem_memSlice_iff.mp <|
      hperm.mem_iff.mp (mem_memSlice_iff.mpr ⟨b, hb1, hb_hi, rfl⟩)
    exact heq ▸ hcut a b' ha1 ha2 hb'1 (by omega)
  · rw [hmod b (by rw [Finset.mem_Ico]; omega)]; exact hcut a b ha1 ha2 hb1 hb2

private theorem cut_preserved_hi {vbase n vlo vhi : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hlo : vbase ≤ vlo)
    (hperm : (memSlice vlo vhi mem₂).Perm (memSlice vlo vhi mem₁))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₁ mem₂)
    (hcut : IsCut vbase n vhi mem₁) :
    IsCut vbase n vhi mem₂ := fun a b ha1 ha2 hb1 hb2 => by
  rw [hmod b (by rw [Finset.mem_Ico]; omega)]
  by_cases ha_lo : vlo ≤ a
  · obtain ⟨a', ha'1, ha'2, heq⟩ := mem_memSlice_iff.mp <|
      hperm.mem_iff.mp (mem_memSlice_iff.mpr ⟨a, ha_lo, ha2, rfl⟩)
    exact heq ▸ hcut a' b (by omega) ha'2 hb1 hb2
  · rw [hmod a (by rw [Finset.mem_Ico]; omega)]; exact hcut a b ha1 ha2 hb1 hb2

/-- Any boundary `t` inside `[vlt, vgt]` after 3-way partitioning `[vlo, vhi)` is a global cut of
`[vbase, vbase + n)`. -/
private theorem cut_of_between_lt_gt {vbase n vlo vlt vgt vhi vpiv t : ℕ} {mem : ℕ → ℕ}
    (hbnd : vlo ≤ vlt ∧ vlt ≤ t ∧ t ≤ vgt ∧ vgt ≤ vhi)
    (hcut_lo : IsCut vbase n vlo mem)
    (hcut_hi : IsCut vbase n vhi mem)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → mem a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → mem a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < mem a) :
    IsCut vbase n t mem := fun a b ha1 ha2 hb1 hb2 => by
  by_cases ha_lo : a < vlo
  · exact hcut_lo a b ha1 ha_lo (by omega) hb2
  · by_cases hb_hi : vhi ≤ b
    · exact hcut_hi a b ha1 (by omega) hb_hi hb2
    · have ha_le : mem a ≤ vpiv := if h : a < vlt then (hlt_z a (by omega) h).le
        else (heq_z a (by omega) (by omega)).le
      have hb_ge : vpiv ≤ mem b := if h : b < vgt then (heq_z b (by omega) h).symm.le
        else (hgt_z b (by omega) (by omega)).le
      exact ha_le.trans hb_ge

/-- Deterministic execution of `narrowRange` after 3-way partition exit (`≤ 6` steps). -/
private theorem narrowRange_spec {w vbase n k vlo vlt vgt vhi vpiv : ℕ}
    {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hone : x.regs one = 1) (htarget : x.regs target = vbase + k)
    (hlo : x.regs lo = vlo) (hlo1 : x.regs lo1 = vlo + 1) (hhi : x.regs hi = vhi)
    (hlt_r : x.regs lt = vlt) (hgt_r : x.regs gt = vgt)
    (hfit : Fits w (vbase + n))
    (hbase_lo : vbase ≤ vlo) (hlo_t : vlo ≤ vbase + k)
    (ht_hi : vbase + k < vhi) (hhi_end : vhi ≤ vbase + n)
    (hlg : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi)
    (hperm : (memSlice vbase (vbase + n) x.mem).Perm s₀)
    (hmod : Modifies (Finset.Ico vbase (vbase + n)) mem₀ x.mem)
    (hcut_lo : IsCut vbase n vlo x.mem) (hcut_hi : IsCut vbase n vhi x.mem)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → x.mem a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → x.mem a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < x.mem a) :
    ∃ y t_nr, Exec w narrowRange x y t_nr ∧ t_nr ≤ 6 ∧
      SelectInv w vbase n k s₀ mem₀ y ∧
      (y.regs hi - y.regs lo = vlt - vlo ∨
       y.regs hi - y.regs lo = 1 ∨
       y.regs hi - y.regs lo = vhi - vgt) := by
  have hcut (t : ℕ) (h₁ : vlt ≤ t) (h₂ : t ≤ vgt) : IsCut vbase n t x.mem :=
    cut_of_between_lt_gt ⟨hlg.1, h₁, h₂, hlg.2.2⟩ hcut_lo hcut_hi hlt_z heq_z hgt_z
  wram_exec [narrowRange, hone, htarget, hlo, hlo1, hhi, hlt_r, hgt_r]
  all_goals
    refine ⟨⟨?_, ?_, ?_, hfit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals wram_simp [hone, htarget, hlo, hlo1, hhi, true_or, or_true]
  all_goals first | assumption | omega | (refine hcut _ ?_ ?_ <;> omega)

/-- Deterministic specification of `partitionAndNarrow` for a sampled pivot offset
`off < x.regs hi - x.regs lo` when `2 ≤ x.regs hi - x.regs lo`
(`≤ 11 * (x.regs hi - x.regs lo) + 13` steps). -/
private theorem partitionAndNarrow_spec {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hm2 : 2 ≤ x.regs hi - x.regs lo)
    {off : ℕ} (hoff : off < x.regs hi - x.regs lo) (htmp : x.regs tmp = off) :
    ∃ y t_pn, Exec w partitionAndNarrow x y t_pn ∧
      t_pn ≤ 11 * (x.regs hi - x.regs lo) + 13 ∧
      SelectInv w vbase n k s₀ mem₀ y ∧
      (y.regs hi - y.regs lo =
          (memSlice (x.regs lo) (x.regs hi) x.mem).countP (· < x.mem (x.regs lo + off)) ∨
       y.regs hi - y.regs lo = 1 ∨
       y.regs hi - y.regs lo =
          (memSlice (x.regs lo) (x.regs hi) x.mem).countP (x.mem (x.regs lo + off) < ·)) ∧
      y.regs hi - y.regs lo < x.regs hi - x.regs lo := by
  let vlo := x.regs lo; let vhi := x.regs hi
  have hlo : x.regs Quicksort.Reg.lo = vlo := rfl
  have hhi : x.regs Quicksort.Reg.hi = vhi := rfl
  have hfit_end := hI.fits_end; have hhi_end := hI.hi_le_end; have hbase_lo := hI.base_le_lo
  wram_exec [partitionAndNarrow, Quicksort.partInit, hlo, hhi, htmp]
  refine WP.Exact.name fun p₀ hp₀ => ?_
  have hp₀_inv : Quicksort.PartInv w vlo vhi (x.mem (vlo + off)) p₀.mem p₀ := by
    subst hp₀
    refine ⟨?_, ?_, ?_, ?_, hfit_end.of_le hhi_end, ?_, ?_, ?_, ?_, .refl _, .refl _ _, ?_, ?_, ?_⟩
    all_goals wram_simp [hI.one_eq, hlo, hhi]
    all_goals omega
  obtain ⟨y_p, ⟨t_loop, ht_loop, e_loop⟩, hIp, hcg_eq⟩ := Quicksort.partLoop_spec hp₀_inv
    (by wram_simp [hp₀]) (by wram_simp [hp₀]) (by wram_simp [hp₀])
  rw [show p₀.mem = x.mem by subst hp₀; rfl] at hIp
  refine WP.Exact.of_exec e_loop ?_
  have heq_gt : ∀ a, y_p.regs lt ≤ a → a < y_p.regs gt → y_p.mem a = x.mem (vlo + off) :=
    fun a h1 h2 => hIp.eq_zone a h1 (hcg_eq ▸ h2)
  obtain ⟨hlt_gt, hcnt_lt, hcnt_gt⟩ := partition_counts_and_lt
    ⟨hIp.lo_le_lt, hIp.lt_le_cur.trans_eq hcg_eq, hIp.gt_le_hi⟩ hIp.perm hIp.lt_zone heq_gt
    hIp.gt_zone (mem_memSlice_iff.mpr ⟨vlo + off, by omega, by omega, rfl⟩)
  have hmod_yp : Modifies (Finset.Ico vbase (vbase + n)) mem₀ y_p.mem := fun a ha => by
    rw [Finset.mem_Ico] at ha
    exact (hIp.modifies a (by rw [Finset.mem_Ico]; omega)).trans
      (hI.modifies a (by rw [Finset.mem_Ico]; exact ha))
  refine WP.Exact.mono (narrowRange_spec hIp.one_eq
    ((e_loop.regs_eq (by decide)).trans (by wram_simp [hp₀, hI.target_eq]))
    hIp.lo_eq ((e_loop.regs_eq (by decide)).trans (by wram_simp [hp₀, hI.lo1_eq]; rfl))
    hIp.hi_eq rfl rfl hfit_end hbase_lo hI.lo_le_target hI.target_lt_hi hhi_end
    ⟨hIp.lo_le_lt, hlt_gt, hIp.gt_le_hi⟩
    ((perm_global_of_sub hbase_lo hhi_end (by omega) hIp.perm hIp.modifies).trans hI.perm) hmod_yp
    (cut_preserved_lo hhi_end hIp.perm hIp.modifies hI.cut_lo)
    (cut_preserved_hi hbase_lo hIp.perm hIp.modifies hI.cut_hi)
    hIp.lt_zone heq_gt hIp.gt_zone) ?_
  rintro y t_nr ⟨ht_nr, hIy, hcases⟩
  have h1 : vlo ≤ y_p.regs lt := hIp.lo_le_lt; have h2 : y_p.regs gt ≤ vhi := hIp.gt_le_hi
  have hlt_gt' : y_p.regs lt < y_p.regs gt := hlt_gt
  have hcl : y_p.regs lt - vlo = _ := hcnt_lt; have hcg : vhi - y_p.regs gt = _ := hcnt_gt
  refine ⟨by omega, hIy, by rwa [← hcl, ← hcg], by rcases hcases with h | h | h <;> omega⟩

/-- The loop condition `lo1 < hi` of `selectStep` leaves a window of at least two elements. -/
private theorem two_le_hi_sub_lo {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    2 ≤ x.regs hi - x.regs lo := by
  have hlt : x.regs lo1 < x.regs hi := by simpa only [Cond.holds_lt] using hc
  rw [hI.lo1_eq] at hlt; omega

/-- Execute `samplePivot` to sample a uniform offset `off : Fin (hi - lo - 1 + 1)` into `tmp`. -/
private theorem samplePivot_spec {w : ℕ} {x : Data 16} (hlo1 : x.regs lo1 = x.regs lo + 1)
    (hfit : Fits w (x.regs hi)) :
    ExecRand w samplePivot x
      ((fun off : Fin (x.regs hi - x.regs lo - 1 + 1) => (x.set tmp off.val, 2)) <$>
        ProbComp.unifFin (x.regs hi - x.regs lo - 1)) := by
  let s₁ := x.set tmp (x.regs hi - x.regs lo - 1)
  have hsub : x.regs hi - (x.regs lo + 1) = x.regs hi - x.regs lo - 1 := by omega
  have esub : Exec w (.op (.bin .sub tmp hi lo1)) x s₁ 1 := by
    simpa only [s₁, hlo1, BinOp.eval, hsub] using
      Exec.bin (w := w) (f := .sub) (d := tmp) (i := hi) (j := lo1) (x := x)
        (hfit.of_le (by simp only [hlo1, BinOp.eval]; omega))
  have hs₁_tmp : s₁.regs tmp = x.regs hi - x.regs lo - 1 := by simp [s₁]
  have erand : ExecRand (B := .standard) w (.rand tmp tmp) s₁
      (ProbComp.unifFin (x.regs hi - x.regs lo - 1) >>= fun off => pure (s₁.set tmp off.val, 1)) :=
    hs₁_tmp ▸ ExecRand.rand (hfit.of_le (by rw [hs₁_tmp]; omega))
  have heq : (fun z : Data 16 × ℕ => (z.1, 1 + z.2)) <$>
      (ProbComp.unifFin (x.regs hi - x.regs lo - 1) >>= fun off => pure (s₁.set tmp off.val, 1)) =
      (fun off : Fin (x.regs hi - x.regs lo - 1 + 1) => (x.set tmp off.val, 2)) <$>
        ProbComp.unifFin (x.regs hi - x.regs lo - 1) := by
    simp only [← bind_pure_comp, bind_assoc, pure_bind]
    refine congrArg (ProbComp.unifFin _ >>= ·) (funext fun off => ?_)
    exact congrArg pure (Prod.ext (Data.ext (by simp [s₁, Function.update_idem]) rfl) rfl)
  simpa only [samplePivot, heq] using esub.seqRand erand

/-- Randomized specification of `selectStep` when `lo1 < hi` holds (`2 ≤ hi - lo`). -/
private theorem selectStep_spec {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    ∃ (y : Fin (x.regs hi - x.regs lo - 1 + 1) → Data 16)
      (t : Fin (x.regs hi - x.regs lo - 1 + 1) → ℕ),
      ExecRand w selectStep x
        ((fun off => (y off, 2 + t off)) <$> ProbComp.unifFin (x.regs hi - x.regs lo - 1)) ∧
      ∀ off : Fin (x.regs hi - x.regs lo - 1 + 1),
        t off ≤ 11 * (x.regs hi - x.regs lo) + 13 ∧
        SelectInv w vbase n k s₀ mem₀ (y off) ∧
        (let u := memSlice (x.regs lo) (x.regs hi) x.mem
         let pivVal := u[off.val]'(by
           rw [length_memSlice]; have := two_le_hi_sub_lo hI hc; have := off.isLt; omega)
         ((y off).regs hi - (y off).regs lo = u.countP (· < pivVal) ∨
          (y off).regs hi - (y off).regs lo = 1 ∨
          (y off).regs hi - (y off).regs lo = u.countP (pivVal < ·))) ∧
        (y off).regs hi - (y off).regs lo < x.regs hi - x.regs lo := by
  have hm2 := two_le_hi_sub_lo hI hc
  have hpn_all (off : Fin (x.regs hi - x.regs lo - 1 + 1)) := by
    have hI_off : SelectInv w vbase n k s₀ mem₀ (x.set tmp off.val) := by
      refine ⟨?_, ?_, ?_, hI.fits_end, ?_, ?_, ?_, ?_, hI.perm, hI.modifies, ?_, ?_⟩
      all_goals wram_simp [hI.one_eq, hI.target_eq, hI.lo1_eq, hI.base_le_lo, hI.lo_le_target,
        hI.target_lt_hi, hI.hi_le_end, hI.cut_lo, hI.cut_hi]
    exact partitionAndNarrow_spec hI_off (off := off.val) (by wram_simp; exact hm2)
      (by wram_simp; have := off.isLt; omega) (by wram_simp)
  choose y t hspec using hpn_all
  refine ⟨y, t, execRand_seq_det_map (samplePivot_spec hI.lo1_eq
    (hI.fits_end.of_le hI.hi_le_end)) fun off => (hspec off).1, fun off => ?_⟩
  obtain ⟨-, ht_le, hIy, hcases, hlt⟩ := hspec off
  have hhi_s : (x.set tmp off.val).regs hi = x.regs hi := by wram_simp
  have hlo_s : (x.set tmp off.val).regs lo = x.regs lo := by wram_simp
  rw [hhi_s, hlo_s] at ht_le hcases hlt
  rw [Data.set_mem] at hcases
  refine ⟨ht_le, hIy, ?_, hlt⟩
  simpa only [getElem_memSlice (by have := off.isLt; omega : off.val < x.regs hi - x.regs lo)]
    using hcases

/-- Quadratic worst-case potential `0` for `m < 2` and `10 * m ^ 2` for `m ≥ 2`. -/
private def stepPotential (x : Data 16) : ℕ :=
  let m := x.regs hi - x.regs lo
  if m < 2 then 0 else 10 * m ^ 2

/-- `rand`-call potential `hi - lo - 1`. -/
private def callPotential (x : Data 16) : ℕ :=
  x.regs hi - x.regs lo - 1

/-- Linear expected-time potential `(expSubCost (hi - lo) : ℝ≥0∞)`. -/
private def expPotential (x : Data 16) : ℝ≥0∞ :=
  (expSubCost (x.regs hi - x.regs lo) : ℝ≥0∞)

private theorem selectStep_worstCase {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    ∃ T_b R_b, ExecRandWithin w selectStep x
      (fun y => SelectInv w vbase n k s₀ mem₀ y ∧
        T_b + 2 + stepPotential y ≤ stepPotential x ∧
        R_b + callPotential y ≤ callPotential x) T_b R_b := by
  have hm2 := two_le_hi_sub_lo hI hc
  obtain ⟨y, t, hexec, hspec⟩ := selectStep_spec hI hc
  let m := x.regs hi - x.regs lo
  refine ⟨11 * m + 15, 1, ⟨_, hexec,
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbComp.isQueryBounded_unifFin (m - 1)),
    fun z hz => ?_⟩⟩
  obtain ⟨off, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨ht_le, hIy, -, hm_lt⟩ := hspec off
  have hstep : 11 * m + 15 + 2 + stepPotential (y off) ≤ stepPotential x := by
    change 11 * m + 15 + 2 + stepPotential (y off) ≤ if m < 2 then 0 else 10 * m ^ 2
    simp only [show ¬m < 2 by omega, ↓reduceIte]
    dsimp only [stepPotential]
    split_ifs with hlt
    · nlinarith
    · have : ((y off).regs hi - (y off).regs lo) ^ 2 ≤ (m - 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      obtain ⟨d, hd⟩ : ∃ d, m = d + 3 := ⟨m - 3, by omega⟩
      rw [hd] at this ⊢; nlinarith
  exact ⟨⟨hIy, hstep, by simp only [callPotential]; omega⟩, by dsimp only; omega⟩

private theorem sum_expCost_pivot_le (u : List ℕ) :
    u.length * (20 * u.length) + 80 * ∑ off : Fin u.length,
      max (u.countP (· < u[off.val])) (u.countP (u[off.val] < ·)) ≤
      80 * u.length * u.length := by
  have hpiv := sum_countP_pivot_le max (fun ha hb => max_le_max ha hb) u
  have hfour := four_mul_sum_max_le u.length
  nlinarith

private theorem selectStep_drift {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    ∃ mb, ExecRand w selectStep x mb ∧
      (∀ z ∈ mb.support,
        SelectInv w vbase n k s₀ mem₀ z.1 ∧ callPotential z.1 < callPotential x) ∧
      ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + expPotential z.1) ≤ expPotential x := by
  have hm2 := two_le_hi_sub_lo hI hc
  obtain ⟨y, t, hexec, hspec⟩ := selectStep_spec hI hc
  let m := x.regs hi - x.regs lo
  let u := memSlice (x.regs lo) (x.regs hi) x.mem
  have hlen_u : u.length = m := length_memSlice _ _ _
  refine ⟨_, hexec, fun z hz => ?_, ?_⟩
  · obtain ⟨off, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨-, hIy, -, hm_lt⟩ := hspec off
    exact ⟨hIy, by simp only [callPotential]; omega⟩
  · rw [ProbComp.expect_map, ProbComp.expect_unifFin, expPotential]
    let pivMax (off : Fin (m - 1 + 1)) : ℕ :=
      max (u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega)))
          (u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·))
    have hm_eq : m - 1 + 1 = u.length := by omega
    have hsum : ∑ off : Fin (m - 1 + 1),
        (2 + t off + 2 + expSubCost ((y off).regs hi - (y off).regs lo)) ≤ expSubCost m * m :=
      calc _ ≤ ∑ off : Fin (m - 1 + 1), (20 * m + 80 * pivMax off) :=
            Finset.sum_le_sum fun off _ => by
              obtain ⟨ht_le, -, hcases, -⟩ := hspec off
              rcases hcases with h | h | h <;> rw [h] <;>
                simp only [expSubCost, pivMax, u] <;> split_ifs <;> omega
        _ = (m - 1 + 1) * (20 * m) + 80 * ∑ off, pivMax off := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, smul_eq_mul, Finset.mul_sum]
        _ ≤ 80 * m * m := by
            rw [Fintype.sum_equiv (finCongr hm_eq) pivMax
              (fun off => max (u.countP (· < u[off.val])) (u.countP (u[off.val] < ·)))
              fun _ => rfl]
            simpa only [hm_eq, hlen_u] using sum_expCost_pivot_le u
        _ = expSubCost m * m := by simp only [expSubCost, show ¬m < 2 by omega, ↓reduceIte]
    calc _ ≤ ((expSubCost m * m : ℕ) : ℝ≥0∞) / m := by
          have : ∑ off : Fin (m - 1 + 1), (((2 + t off : ℕ) : ℝ≥0∞) + 2 + expPotential (y off)) =
              ((∑ off : Fin (m - 1 + 1), (2 + t off + 2 +
                expSubCost ((y off).regs hi - (y off).regs lo)) : ℕ) : ℝ≥0∞) := by
            unfold expPotential; push_cast; rfl
          dsimp only; rw [this, show ((m - 1 : ℕ) : ℝ≥0∞) + 1 = m by norm_cast; omega]; gcongr
      _ = expSubCost m := by
          rw [Nat.cast_mul]; exact ENNReal.mul_div_cancel_right (by positivity)
            (ENNReal.natCast_ne_top m)

/-- Deterministic `5`-step execution of `selectSetup`. -/
private theorem selectSetup_spec {w : ℕ} {x : Data 16}
    (hk : x.regs rk < x.regs len) (hfit : Fits w (x.regs base + x.regs len)) :
    ∃ x_init, Exec w selectSetup x x_init 5 ∧
      x_init.mem = x.mem ∧
      x_init.regs lo = x.regs base ∧
      x_init.regs hi = x.regs base + x.regs len ∧
      SelectInv w (x.regs base) (x.regs len) (x.regs rk)
        (memSlice (x.regs base) (x.regs base + x.regs len) x.mem) x.mem x_init := by
  wram_exec [selectSetup]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hfit, ?_, ?_, ?_, ?_, .refl _, .refl _ _, fun a b => ?_,
    fun a b => ?_⟩
  all_goals wram_simp
  all_goals omega

/-- Extracting order-statistic and partition-order properties from `SelectInv` at loop exit
(`¬(lo1 < hi)`). -/
private theorem SelectInv.exit_post {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {y : Data 16}
    (hIy : SelectInv w vbase n k s₀ mem₀ y) (hnc : ¬(Cond.lt lo1 hi).Holds y)
    (hs₀_len : s₀.length = n) (hk : k < n) :
    y.mem (vbase + k) = s₀.mergeSort[k]'(by rw [List.length_mergeSort, hs₀_len]; exact hk) ∧
    (∀ i < k, y.mem (vbase + i) ≤ y.mem (vbase + k)) ∧
    (∀ i, k < i → i < n → y.mem (vbase + k) ≤ y.mem (vbase + i)) := by
  have hnlt : ¬(y.regs lo + 1 < y.regs hi) := by simpa only [Cond.holds_lt, hIy.lo1_eq] using hnc
  have := hIy.lo_le_target; have := hIy.target_lt_hi
  have hlo_eq : y.regs lo = vbase + k := by omega
  have hhi_eq : y.regs hi = vbase + k + 1 := by omega
  have hleft : ∀ i < k, y.mem (vbase + i) ≤ y.mem (vbase + k) := fun i hik =>
    hIy.cut_lo (vbase + i) (vbase + k) (by omega) (by omega) (by omega) (by omega)
  have hright : ∀ i, k < i → i < n → y.mem (vbase + k) ≤ y.mem (vbase + i) := fun i hki hin =>
    hIy.cut_hi (vbase + k) (vbase + i) (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_, hleft, hright⟩
  rw [← getElem_memSlice (a := vbase) (b := vbase + n) (mem := y.mem) (i := k) (by omega)]
  exact eq_mergeSort_getElem_of_perm_of_partitioned hIy.perm (by omega)
    (fun i hik => by
      rw [getElem_memSlice (by omega), getElem_memSlice (by omega)]; exact hleft i hik)
    (fun i hki hi_len => by
      rw [length_memSlice] at hi_len
      rw [getElem_memSlice (by omega), getElem_memSlice hi_len]; exact hright i hki (by omega))

/-- **Specification of `selectSlice` on an arbitrary slice `[vbase, vbase + n)`.**
When `k = x.regs rk < x.regs len = n` and `Fits w (x.regs base + x.regs len)`:
1. `selectSlice` runs within `10 * n ^ 2 + 8` instructions and `n - 1` `rand` calls, permuting
   `[vbase, vbase + n)` in place, placing the `k`-th sorted element in both `y.mem (vbase + k)` and
   `y.regs ans`, partitioning `[vbase, vbase + n)` around `vbase + k`, and modifying only
   `Finset.Ico vbase (vbase + n)`;
2. Its expected instruction count satisfies `expectedCodeTime w selectSlice x ≤ 80 * n + 8`. -/
theorem selectSlice_spec {w : ℕ} {x : Data 16}
    (hk : x.regs rk < x.regs len) (hfit : Fits w (x.regs base + x.regs len)) :
    let vbase := x.regs base
    let n := x.regs len
    let k := x.regs rk
    let s₀ := memSlice vbase (vbase + n) x.mem
    ExecRandWithin w selectSlice x
      (fun y =>
        y.regs ans = s₀.mergeSort[k]'(by rw [List.length_mergeSort, length_memSlice]; omega) ∧
        (memSlice vbase (vbase + n) y.mem).Perm s₀ ∧
        y.mem (vbase + k) =
          s₀.mergeSort[k]'(by rw [List.length_mergeSort, length_memSlice]; omega) ∧
        (∀ i < k, y.mem (vbase + i) ≤ y.mem (vbase + k)) ∧
        (∀ i, k < i → i < n → y.mem (vbase + k) ≤ y.mem (vbase + i)) ∧
        Modifies (Finset.Ico vbase (vbase + n)) x.mem y.mem)
      (10 * n ^ 2 + 8) (n - 1) ∧
    expectedCodeTime w selectSlice x ≤ ((80 * n + 8 : ℕ) : ℝ≥0∞) := by
  dsimp only
  let vbase := x.regs base; let n := x.regs len; let k := x.regs rk
  let s₀ := memSlice vbase (vbase + n) x.mem
  obtain ⟨x_init, e_setup, _, hx_lo, hx_hi, hI_init⟩ := selectSetup_spec hk hfit
  have hstep_init : stepPotential x_init ≤ 10 * n ^ 2 := by
    simp only [stepPotential, hx_hi, hx_lo, Nat.add_sub_cancel_left]; split_ifs <;> nlinarith
  have hloop_wc := (ExecRandWithin.loop_potential (SelectInv w vbase n k s₀ x.mem) stepPotential
    callPotential (fun _ hs hc => selectStep_worstCase hs hc) hI_init).mono (fun _ h => h)
    (by omega : stepPotential x_init + 2 ≤ 10 * n ^ 2 + 2)
    (show callPotential x_init ≤ n - 1 by
      simp only [callPotential, hx_hi, hx_lo, Nat.add_sub_cancel_left]; exact le_rfl)
  refine ⟨((e_setup.within.execRandWithin rfl).seq fun _ hy => by
      subst hy
      exact hloop_wc.seq fun y ⟨hIy, hnc⟩ => by
        obtain ⟨hval, hleft, hright⟩ := hIy.exit_post hnc (by simp [s₀]) hk
        exact (ExecWithin.load (w := w) (d := ans) (a := target) (x := y)).execRandWithin
          ⟨by wram_simp [hIy.target_eq, hval]; rfl,
            hIy.perm, hval, hleft, hright, hIy.modifies⟩).mono
    (fun _ h => h) (by dsimp [n]; omega) (by dsimp [n]; omega), ?_⟩
  obtain ⟨⟨m_loop, hm_loop⟩, hloop_exp⟩ := expectedCodeTime_loop_le_of_drift
    (SelectInv w vbase n k s₀ x.mem) callPotential expPotential hI_init
    fun _ hs hc => selectStep_drift hs hc
  have hexp_init : expPotential x_init ≤ (80 * n : ℕ) := by
    simp only [expPotential, hx_hi, hx_lo, Nat.add_sub_cancel_left]
    exact_mod_cast expSubCost_le n
  rw [selectSlice, expectedCodeTime_seq_of_exec e_setup, expectedCodeTime_seq hm_loop]
  have hload_exp : ProbComp.expect m_loop
      (fun z => expectedCodeTime (B := .standard) w (.op (.load ans target)) z.1) = 1 := by
    rw [← ProbComp.expect_const m_loop 1]
    exact ProbComp.expect_congr_on_support fun _ _ => expectedCodeTime_op rfl
  rw [hload_exp]
  calc ((5 : ℕ) : ℝ≥0∞) + (expectedCodeTime w _ x_init + 1)
      ≤ ((5 : ℕ) : ℝ≥0∞) + ((80 * n : ℕ) + 2 + 1) := by gcongr; exact hloop_exp.trans (by gcongr)
    _ = ((80 * n + 8 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-! ## Top-level `program` specifications on `State.init (k :: input)` -/

/-- Deterministic `4`-step execution of `loadHeader` on `Data.init (k :: input)`. -/
theorem loadHeader_spec {w k : ℕ} {input : List ℕ} (hfit : InputFits w (k :: input)) :
    ∃ x_hdr : Data 16,
      Exec w loadHeader (Data.init (k :: input)) x_hdr 4 ∧
      x_hdr.mem = (Data.init (r := 16) (k :: input)).mem ∧
      x_hdr.regs one = 1 ∧
      x_hdr.regs rk = k ∧
      x_hdr.regs len = input.length := by
  have hfit_len1 : Fits w (input.length + 1) := by
    simpa only [List.length_cons] using hfit.1
  wram_exec [loadHeader,
    Data.init_regs, Data.init_mem_zero, Data.init_mem_succ, List.getD_cons_zero,
    List.length_cons]
  wram_simp

/-- Structured `7`-step execution of `code` when `input.length ≤ k`. -/
theorem code_out_of_range_spec {w k : ℕ} {input : List ℕ}
    (hk : input.length ≤ k) (hfit : InputFits w (k :: input)) :
    ∃ y : Data 16,
      Exec w code (Data.init (k :: input)) y 7 ∧
      y.regs ans = 0 ∧
      y.mem = (Data.init (r := 16) (k :: input)).mem := by
  wram_exec [code]
  wram_call (loadHeader_spec hfit) with x_hdr ⟨hmem, -, hrk, hlen⟩
  wram_exec [hrk, hlen]
  wram_simp [hmem]

/-- **Total out-of-range behavior (`input.length ≤ k`).**
Whenever `InputFits w (k :: input)` holds and `input.length ≤ k`, `program` executes
deterministically in `8` instructions returning `0`, making `0` `rand` calls and leaving memory
completely unchanged. -/
theorem quickselect_out_of_range {w k : ℕ} {input : List ℕ}
    (hk : input.length ≤ k) (hfit : InputFits w (k :: input)) :
    Executes w program (.init (k :: input)) 0 8 ∧
    RandHaltsWithin w program (.init (k :: input)) (worstCaseTime input.length) ∧
    RandCallsBounded w program (.init (k :: input)) (worstCaseTime input.length) 0 ∧
    (∀ cfg ∈ (runRand w program (worstCaseTime input.length)
        (.running (.init (k :: input)))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.Bounded w ∧
        y.mem = (Data.init (r := 16) (k :: input)).mem) ∧
    expectedTime w program (.init (k :: input)) = 8 := by
  obtain ⟨y_out, e_code, hy_ans, hmem_out⟩ := code_out_of_range_spec hk hfit
  have hexecutes : Executes w program (.init (k :: input)) 0 8 := by
    simpa only [program, State.init, hy_ans] using e_code.executes ans
  have hrun : runRand w program (worstCaseTime input.length) (.running (.init (k :: input))) =
      pure (.halted 0 y_out) := by
    simpa only [program, State.init, hy_ans] using
      e_code.runRand_program ans (T := worstCaseTime input.length)
        (by simp only [worstCaseTime]; omega)
  refine ⟨hexecutes, fun cfg hcfg => ?_, by rw [RandCallsBounded, hrun]; exact .pure _ 0,
    fun cfg hcfg => ?_, by simpa only [Nat.cast_ofNat] using hexecutes.expectedTime_eq⟩
  · rw [hrun] at hcfg; cases OracleComp.eq_of_mem_supportWith_pure hcfg; exact ⟨0, y_out, rfl⟩
  · have hbnd := runRand_bounded_init hfit hcfg
    rw [hrun] at hcfg; cases OracleComp.eq_of_mem_supportWith_pure hcfg
    exact ⟨y_out, rfl, hbnd.2, hmem_out⟩

/-- Structured `ExecRandWithin` and linear `expectedCodeTime` specification for `code` when
`k < input.length`. -/
theorem code_spec {w k : ℕ} {input : List ℕ}
    (hk : k < input.length) (hw : logWidth 2 input.length ≤ w)
    (hfit : InputFits w (k :: input)) :
    ExecRandWithin w code (Data.init (k :: input))
      (fun y =>
        y.regs ans = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (memSlice 2 (input.length + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < input.length → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (input.length + 2))
          (Data.init (r := 16) (k :: input)).mem y.mem)
      (10 * input.length ^ 2 + 14) (input.length - 1) ∧
    expectedCodeTime w code (Data.init (k :: input)) ≤
      ((80 * input.length + 14 : ℕ) : ℝ≥0∞) := by
  let n := input.length
  have hfit_end : Fits w (2 + n) := Nat.add_comm 2 n ▸ fits_add_two hw
  obtain ⟨x_hdr, e_hdr, hmem_hdr, hone_hdr, hrk_hdr, hlen_hdr⟩ := loadHeader_spec hfit
  have hc_pos : (Cond.lt rk len).Holds x_hdr := by
    simp only [Cond.holds_lt, hrk_hdr, hlen_hdr]; exact hk
  let x_base := x_hdr.set base 2
  have e_base : Exec w (.op (.bin .add base one one)) x_hdr x_base 1 := by
    simpa only [x_base, hone_hdr, BinOp.eval] using
      Exec.bin (w := w) (f := .add) (d := base) (i := one) (j := one) (x := x_hdr)
        (hfit_end.of_le (by simp only [hone_hdr, BinOp.eval]; omega))
  have hrk_b : x_base.regs rk = k := by wram_simp [x_base, hrk_hdr]
  have hlen_b : x_base.regs len = n := by wram_simp [x_base, hlen_hdr]; rfl
  have hbase_b : x_base.regs base = 2 := by wram_simp [x_base]
  have hslice_init : memSlice 2 (n + 2) (Data.init (r := 16) (k :: input)).mem = input :=
    List.ext_getElem (by simp [n]) fun i _ h2 => by
      rw [getElem_memSlice (by omega), show 2 + i = (i + 1) + 1 by omega]
      simp [Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  obtain ⟨hslice_wc, hslice_exp⟩ := selectSlice_spec (w := w) (x := x_base)
    (by rw [hrk_b, hlen_b]; exact hk) (by rw [hbase_b, hlen_b]; exact hfit_end)
  have hthen_wc := ((e_base.within.execRandWithin rfl).seq fun _ hy => by
      subst hy; exact hslice_wc).mono
    (fun y hy => by
      simpa only [hbase_b, hlen_b, hrk_b, x_base, Data.set_mem, hmem_hdr, Nat.add_comm 2 n,
        hslice_init] using hy)
    (by rw [hlen_b]; omega : 1 + (10 * x_base.regs len ^ 2 + 8) ≤ 10 * n ^ 2 + 9)
    (by rw [hlen_b]; omega : 0 + (x_base.regs len - 1) ≤ n - 1)
  refine ⟨((e_hdr.within.execRandWithin rfl).seq fun _ hy => by
      subst hy; exact ExecRandWithin.branch_pos (neg := ram[ ans ← #0 ]) hc_pos hthen_wc).mono
    (fun _ h => h) (by dsimp [n]; omega) (by dsimp [n]; omega), ?_⟩
  rw [code, expectedCodeTime_seq_of_exec e_hdr, expectedCodeTime_branch_pos hc_pos,
    expectedCodeTime_seq_of_exec e_base]
  rw [hlen_b] at hslice_exp
  calc ((4 : ℕ) : ℝ≥0∞) + (((1 : ℕ) : ℝ≥0∞) + expectedCodeTime w selectSlice x_base + 1)
      ≤ ((4 : ℕ) : ℝ≥0∞) + (((1 : ℕ) : ℝ≥0∞) + ((80 * n + 8 : ℕ) : ℝ≥0∞) + 1) := by gcongr
    _ = ((80 * n + 14 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **In-place randomized quickselect: correctness, zero auxiliary space, worst-case bounds,
`rand`-call bound, and linear expected running time.**

For any `input : List ℕ` of length `n`, target rank `k < n`, and word size `w ≥ logWidth 2 n` with
`InputFits w (k :: input)`:
1. `program` halts without faulting within `worstCaseTime n = 10 * n ^ 2 + 15` instructions on
   every execution path (`RandHaltsWithin`);
2. Every execution path makes at most `n - 1` `rand` calls (`RandCallsBounded`);
3. On every supported halting configuration, `program` returns `input.mergeSort[k]` with
   `y.Bounded w`, permutes `memSlice 2 (n + 2) y.mem` in place so that
   `y.mem (2 + k) = input.mergeSort[k]` with `y.mem (2 + i) ≤ y.mem (2 + k)` for `i < k` and
   `y.mem (2 + k) ≤ y.mem (2 + i)` for `k < i < n`, and leaves all memory outside
   `Finset.Ico 2 (n + 2)` untouched (`Modifies`, zero auxiliary heap words);
4. The expected instruction count satisfies
   `expectedTime w program (.init (k :: input)) ≤ expectedTimeBound n = 80 * n + 15`
   uniformly over all `k < n` and unconditionally across duplicate keys. -/
theorem quickselect_correct_and_bounds {w k : ℕ} {input : List ℕ}
    (hk : k < input.length) (hw : logWidth 2 input.length ≤ w)
    (hfit : InputFits w (k :: input)) :
    RandHaltsWithin w program (.init (k :: input)) (worstCaseTime input.length) ∧
    RandCallsBounded w program (.init (k :: input)) (worstCaseTime input.length)
      (input.length - 1) ∧
    (∀ cfg ∈ (runRand w program (worstCaseTime input.length)
        (.running (.init (k :: input)))).support,
      ∃ y : Data 16,
        cfg = .halted (input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk)) y ∧
        y.Bounded w ∧
        (memSlice 2 (input.length + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < input.length → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (input.length + 2))
          (Data.init (r := 16) (k :: input)).mem y.mem) ∧
    expectedTime w program (.init (k :: input)) ≤
      (expectedTimeBound input.length : ℝ≥0∞) := by
  obtain ⟨hcode_wc, hcode_exp⟩ := code_spec hk hw hfit
  obtain ⟨hHalts, hCalls, hPost⟩ :=
    hcode_wc.program ans (T' := worstCaseTime input.length) (by simp only [worstCaseTime]; omega)
  obtain ⟨m_code, hm_code, -, -⟩ := hcode_wc
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, ?_⟩
  · obtain ⟨y, hcfg_eq, hy_ans, hperm, hy_k, hleft, hright, hmod⟩ := hPost cfg hcfg
    rw [hy_ans] at hcfg_eq
    have hb := runRand_bounded_init hfit hcfg; rw [hcfg_eq] at hb
    exact ⟨y, hcfg_eq, hb.2, hperm, hy_k, hleft, hright, hmod⟩
  · rw [program, State.init, expectedCodeTime_program hm_code ans]
    exact (add_le_add_left hcode_exp 1).trans_eq <| by
      simp only [expectedTimeBound]; push_cast; ring

end Cslib.Algorithms.WordRAM.Quickselect
