/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Allocation
public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Randomized.Expected
public import CslibFrontier.Computability.WordRAM.Time
public import CslibFrontier.Foundations.NumberTheory.Harmonic
import CslibFrontier.Computability.WordRAM.Randomized.LoopSegment
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.WramOmega
import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order

/-!
# In-place randomized quicksort on the word RAM

Iterative in-place 3-way randomized quicksort over `Cslib.WordRAM.Basis.standard`, sorting an
`n`-word input array in `Block.mk 1 n` using an explicit `2 * n`-word range stack allocated at
`[n + 1, 3 * n + 1)`.

Using Dutch National Flag 3-way partitioning (`< piv`, `= piv`, `> piv`) around a uniformly
sampled pivot `off ← rand (hi - lo - 1)` ensures that:
1. **Pathwise correctness:** every execution path halts cleanly with `Block.mk 1 n` holding
   `input.mergeSort` (a sorted permutation of `input`), modifying memory only within
   `Finset.Ico 1 (3 * n + 1)`;
2. **Strict worst-case bounds:** only subranges of length `≥ 2` are pushed, and every partition
   strictly eliminates at least the sampled pivot, so stack potential `∑ (hi - lo - 1)` drops on
   every iteration — bounding every path to at most `n - 1` `rand` calls and
   `20 * n ^ 2 + 8 * n + 32` instructions;
3. **Unconditional `O(n log n)` expected running time (including duplicates):** equal elements
   fall into the middle `= piv` region and are never recursed on, so the left and right recursive
   sizes on sorted rank `r` are at most `r` and `m - 1 - r` regardless of duplicate keys.
   Bounding Mathlib's `harmonic` numbers via `harmonic_le_log_add_one`
   (`harmonic n ≤ Nat.log 2 n + 1`) yields
   `expectedTime w program (.init input) ≤ 120 * n * (Nat.log 2 n + 1) + 32` without
   transcendental analysis.

## Main definitions

* `Cslib.Algorithms.WordRAM.Quicksort.code`, `Cslib.Algorithms.WordRAM.Quicksort.program`:
  structured and compiled 16-register randomized quicksort program.
* `Cslib.Algorithms.WordRAM.Quicksort.worstCaseTime`: quadratic worst-case step bound
  `20 * n ^ 2 + 8 * n + 32`.
* `Cslib.Algorithms.WordRAM.Quicksort.expectedTimeBound`: `O(n log n)` expected step bound
  `120 * n * (Nat.log 2 n + 1) + 32`.

## Main results

* `Cslib.Algorithms.WordRAM.Quicksort.quicksort_correct_and_bounds`: joint certificate of
  `RandHaltsWithin`, `RandCallsBounded` (`≤ n - 1`), pathwise sorted-array realization + `Modifies`
  frame, and `O(n log n)` `expectedTime` at word size `w ≥ logWidth 3 input.length`.

Classical background on randomized quicksort, equal-key partitioning and the expected-cost
recurrence appears in [CLRS2009], Section 7.3, Section 7.4.2 and Problems 7-2–7-3;
[MitzenmacherUpfal2017], Section 2.5, gives additional expected-cost background. The word-RAM
implementation and step constants, constant-56 explicit-stack potential, ranked-loop drift
formulation and duplicate-key rank-domination proof are original to this formalization.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 7.3, Section 7.4.2 and Problems 7-2–7-3.
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017], Section 2.5.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM

/-! ## Expected-partition potential recurrence -/

/-- Potential contribution of a subarray of length `m` in the expected-time drift argument. -/
noncomputable def subCost (m : ℕ) : ℝ :=
  if m < 2 then 0 else 56 * ((m : ℝ) + 1) * (harmonic m : ℝ)

theorem subCost_of_lt_two {m : ℕ} (h : m < 2) : subCost m = 0 := by
  simp [subCost, h]

theorem subCost_nonneg (m : ℕ) : 0 ≤ subCost m := by
  unfold subCost
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by positivity) (by exact_mod_cast harmonic_nonneg m)

theorem subCost_le_formula (m : ℕ) :
    subCost m ≤ 56 * ((m : ℝ) + 1) * (harmonic m : ℝ) := by
  unfold subCost
  split_ifs
  · exact mul_nonneg (by positivity) (by exact_mod_cast harmonic_nonneg m)
  · exact le_rfl

theorem subCost_mono {a b : ℕ} (hab : a ≤ b) : subCost a ≤ subCost b := by
  unfold subCost
  split_ifs with ha hb
  · exact le_rfl
  · exact mul_nonneg (by positivity) (by exact_mod_cast harmonic_nonneg b)
  · omega
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    have : (harmonic a : ℝ) ≤ harmonic b := by exact_mod_cast harmonic_mono hab
    have : (0 : ℝ) ≤ harmonic a := by exact_mod_cast harmonic_nonneg a
    gcongr

/-- Key expected-quicksort recurrence: for `m ≥ 2`, `28 * m` plus the average over `r < m` of
`subCost r + subCost (m - 1 - r)` is at most `subCost m`. -/
theorem subCost_recurrence {m : ℕ} (hm : 2 ≤ m) :
    28 * (m : ℝ) +
      (∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r))) / (m : ℝ) ≤
        subCost m := by
  have hsum_harm : 2 * ∑ r ∈ Finset.range m, ((r : ℝ) + 1) * (harmonic r : ℝ) =
      (m : ℝ) * (m + 1) * (harmonic m : ℝ) - m * (m + 3) / 2 := by
    simpa [Rat.cast_sum] using congrArg (Rat.cast : ℚ → ℝ) (two_mul_sum_add_one_mul_harmonic m)
  have hsum_le : ∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r)) ≤
      56 * ((m : ℝ) * (m + 1) * (harmonic m : ℝ) - m * (m + 3) / 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_reflect, ← two_mul]
    calc
      2 * ∑ r ∈ Finset.range m, subCost r
        ≤ 2 * ∑ r ∈ Finset.range m, 56 * ((r : ℝ) + 1) * (harmonic r : ℝ) := by
          gcongr; exact subCost_le_formula _
      _ = 56 * (2 * ∑ r ∈ Finset.range m, ((r : ℝ) + 1) * (harmonic r : ℝ)) := by
          simp only [mul_assoc, ← Finset.mul_sum]; ring
      _ = _ := by rw [hsum_harm]
  rw [subCost, ite_eq_right (fun h => by omega), ← le_sub_iff_add_le',
    div_le_iff₀ (show (0 : ℝ) < m by exact_mod_cast (by omega : 0 < m))]
  linarith

/-! ## Memory slices, permutations, and 3-way partition rank bounds -/

/-- Read the subarray `mem[a .. b)` as a list of length `b - a`. -/
def memSlice (a b : ℕ) (mem : ℕ → ℕ) : List ℕ :=
  (List.range (b - a)).map fun i => mem (a + i)

@[simp]
theorem length_memSlice (a b : ℕ) (mem : ℕ → ℕ) :
    (memSlice a b mem).length = b - a := by
  simp [memSlice]

theorem getElem_memSlice {a b : ℕ} {mem : ℕ → ℕ} {i : ℕ} (hi : i < b - a) :
    (memSlice a b mem)[i]'(by simp [hi]) = mem (a + i) := by
  simp [memSlice]

theorem mem_memSlice_iff {a b v : ℕ} {mem : ℕ → ℕ} :
    v ∈ memSlice a b mem ↔ ∃ addr, a ≤ addr ∧ addr < b ∧ mem addr = v := by
  simp only [memSlice, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a + i, by omega, by omega, rfl⟩
  · rintro ⟨addr, hlo, hhi, rfl⟩
    exact ⟨addr - a, by omega, by congr 1; omega⟩

theorem memSlice_congr {a b : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : ∀ addr, a ≤ addr → addr < b → m₁ addr = m₂ addr) :
    memSlice a b m₁ = memSlice a b m₂ :=
  List.map_congr_left fun i hi => h (a + i) (by omega) (by rw [List.mem_range] at hi; omega)

theorem memSlice_append {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (mem : ℕ → ℕ) :
    memSlice a c mem = memSlice a b mem ++ memSlice b c mem := by
  unfold memSlice
  rw [show c - a = (b - a) + (c - b) by omega, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by dsimp only [Function.comp_apply]; congr 1; omega

/-- Swapping two addresses inside `[a, b)` preserves `List.Perm` on `memSlice a b`. -/
theorem memSlice_swap_perm {a b p q : ℕ} (hp : a ≤ p ∧ p < b) (hq : a ≤ q ∧ q < b)
    (mem : ℕ → ℕ) :
    (memSlice a b (Function.update (Function.update mem p (mem q)) q (mem p))).Perm
      (memSlice a b mem) := by
  let σ : Equiv.Perm (Fin (b - a)) := Equiv.swap ⟨p - a, by omega⟩ ⟨q - a, by omega⟩
  have hof : ∀ l : ℕ → ℕ, memSlice a b l = (List.finRange (b - a)).map (fun i => l (a + i.val)) :=
    fun l => List.ext_getElem (by simp [memSlice]) fun i h₁ _ => by simp [memSlice]
  have hfun : (fun i : Fin (b - a) =>
      Function.update (Function.update mem p (mem q)) q (mem p) (a + i.val)) =
      (fun i : Fin (b - a) => mem (a + (σ i).val)) := by
    funext i
    simp only [Function.update_apply, σ, Equiv.swap_apply_def, Fin.ext_iff]
    split_ifs <;> first
      | omega
      | exact congrArg mem (by simp only; omega)
  have hbij : ((List.finRange (b - a)).map σ).Perm (List.finRange (b - a)) :=
    (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map σ.injective)
      (List.nodup_finRange _)).mpr fun i =>
        by simpa only [List.mem_map, List.mem_finRange, true_and, iff_true] using
          ⟨σ.symm i, σ.apply_symm_apply i⟩
  simpa only [hof, hfun, List.map_map, Function.comp_def] using
    hbij.map (fun i : Fin (b - a) => mem (a + i.val))

private theorem countP_memSlice_eq_zero {a b : ℕ} {mem : ℕ → ℕ} {p : ℕ → Bool}
    (h : ∀ i, a ≤ i → i < b → p (mem i) = false) :
    (memSlice a b mem).countP p = 0 :=
  List.countP_eq_zero.mpr fun _ hv => by
    obtain ⟨i, h1, h2, rfl⟩ := mem_memSlice_iff.mp hv; simp [h i h1 h2]

private theorem countP_memSlice_eq_len {a b : ℕ} {mem : ℕ → ℕ} {p : ℕ → Bool}
    (h : ∀ i, a ≤ i → i < b → p (mem i) = true) :
    (memSlice a b mem).countP p = b - a := by
  rw [List.countP_eq_length.mpr fun _ hv => by
    obtain ⟨i, h1, h2, rfl⟩ := mem_memSlice_iff.mp hv; exact h i h1 h2, length_memSlice]

/-- At 3-way partition exit (`cur = gt`), `< piv` has exact count `lt - lo`, `> piv` has exact
count `hi - gt`, and `piv ∈ memSlice lo hi mem₀` implies `lt < gt`. -/
theorem partition_counts_and_lt {lo lt gt hi piv : ℕ} {mem₀ mem : ℕ → ℕ}
    (hbounds : lo ≤ lt ∧ lt ≤ gt ∧ gt ≤ hi)
    (hperm : (memSlice lo hi mem).Perm (memSlice lo hi mem₀))
    (hlt : ∀ a, lo ≤ a → a < lt → mem a < piv)
    (heq : ∀ a, lt ≤ a → a < gt → mem a = piv)
    (hgt : ∀ a, gt ≤ a → a < hi → piv < mem a)
    (hpiv : piv ∈ memSlice lo hi mem₀) :
    lt < gt ∧
      lt - lo = (memSlice lo hi mem₀).countP (· < piv) ∧
      hi - gt = (memSlice lo hi mem₀).countP (piv < ·) := by
  have hsplit : memSlice lo hi mem =
      memSlice lo lt mem ++ (memSlice lt gt mem ++ memSlice gt hi mem) := by
    rw [memSlice_append (by omega) hbounds.2.2, memSlice_append hbounds.1 hbounds.2.1,
      List.append_assoc]
  have hlt_lt : lt < gt := by
    rcases (by simpa only [hsplit, List.mem_append] using hperm.mem_iff.mpr hpiv) with
      h1 | h2 | h3 <;> obtain ⟨a, ha1, ha2, ha⟩ := mem_memSlice_iff.mp ‹_›
    · have := hlt a ha1 ha2; omega
    · omega
    · have := hgt a ha1 ha2; omega
  refine ⟨hlt_lt, ?_, ?_⟩ <;>
    rw [← hperm.countP_eq, hsplit, List.countP_append, List.countP_append]
  · rw [countP_memSlice_eq_len (p := (· < piv)) fun a h1 h2 => decide_eq_true (hlt a h1 h2),
      countP_memSlice_eq_zero (p := (· < piv)) fun a h1 h2 => by simp [heq a h1 h2],
      countP_memSlice_eq_zero (p := (· < piv)) fun a h1 h2 =>
        by simp [Nat.not_lt.mpr (hgt a h1 h2).le]]
    omega
  · rw [countP_memSlice_eq_zero (p := (piv < ·)) fun a h1 h2 =>
        by simp [Nat.not_lt.mpr (hlt a h1 h2).le],
      countP_memSlice_eq_zero (p := (piv < ·)) fun a h1 h2 => by simp [heq a h1 h2],
      countP_memSlice_eq_len (p := (piv < ·)) fun a h1 h2 => decide_eq_true (hgt a h1 h2)]
    omega

/-- On a sorted list `zs` (`Pairwise (· ≤ ·)`), at index `r < zs.length`, at most `r` elements are
strictly less than `zs[r]` and at most `zs.length - 1 - r` elements are strictly greater than
`zs[r]`. -/
theorem sorted_countP_bounds {zs : List ℕ} (hsorted : zs.Pairwise (· ≤ ·))
    {r : ℕ} (hr : r < zs.length) :
    zs.countP (· < zs[r]) ≤ r ∧ zs.countP (zs[r] < ·) ≤ zs.length - 1 - r := by
  have hp := List.pairwise_iff_getElem.mp hsorted
  have hle_of : ∀ {i j} (hi : i < zs.length) (hj : j < zs.length), i ≤ j → zs[i] ≤ zs[j] :=
    fun hi hj hij => hij.eq_or_lt.elim (fun h => h ▸ le_rfl) (hp _ _ hi hj)
  refine ⟨?_, ?_⟩
  · have hdrop0 : (zs.drop r).countP (· < zs[r]) = 0 := List.countP_eq_zero.mpr fun _ hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.length_drop] at hk
      rw [List.getElem_drop]
      simpa using hle_of hr (by omega) (by omega)
    calc zs.countP (· < zs[r])
        = (zs.take r ++ zs.drop r).countP (· < zs[r]) := by rw [List.take_append_drop]
      _ = (zs.take r).countP (· < zs[r]) := by rw [List.countP_append, hdrop0, add_zero]
      _ ≤ (zs.take r).length := List.countP_le_length
      _ ≤ r := by simp
  · have htake0 : (zs.take (r + 1)).countP (zs[r] < ·) = 0 :=
      List.countP_eq_zero.mpr fun _ hx => by
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        simp only [List.length_take] at hk
        rw [List.getElem_take]
        simpa using hle_of (by omega) hr (by omega)
    calc zs.countP (zs[r] < ·)
        = (zs.take (r + 1) ++ zs.drop (r + 1)).countP (zs[r] < ·) := by rw [List.take_append_drop]
      _ = (zs.drop (r + 1)).countP (zs[r] < ·) := by rw [List.countP_append, htake0, zero_add]
      _ ≤ (zs.drop (r + 1)).length := List.countP_le_length
      _ ≤ zs.length - 1 - r := by simp; omega

/-- **Averaging over uniform pivots.** For `f` monotone in both arguments, summing
`f (u.countP (· < piv)) (u.countP (piv < ·))` over the pivots `piv = u[k]` of a list `u` gives at
most `∑ r < u.length, f r (u.length - 1 - r)`, even when `u` has duplicate keys. -/
theorem sum_countP_pivot_le {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] (f : ℕ → ℕ → M)
    (hf : ∀ {a a' b b'}, a ≤ a' → b ≤ b' → f a b ≤ f a' b') (u : List ℕ) :
    ∑ k : Fin u.length, f (u.countP (· < u[k.val])) (u.countP (u[k.val] < ·)) ≤
      ∑ r ∈ Finset.range u.length, f r (u.length - 1 - r) := by
  have hperm : u.Perm u.mergeSort := (List.mergeSort_perm u _).symm
  have hlen : u.mergeSort.length = u.length := hperm.length_eq.symm
  let g : ℕ → M := fun piv => f (u.countP (· < piv)) (u.countP (piv < ·))
  change ∑ k : Fin u.length, g u[k.val] ≤ _
  rw [Fin.sum_univ_fun_getElem, (hperm.map g).sum_eq, ← Fin.sum_univ_fun_getElem, ← hlen,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun r _ => ?_
  have hb := sorted_countP_bounds (List.pairwise_mergeSort' (· ≤ ·) u) r.isLt
  exact hf ((hperm.countP_eq _).trans_le hb.1) ((hperm.countP_eq _).trans_le hb.2)

/-- Expected child `subCost` summed over all `m = u.length` uniform pivot choices is bounded by
`∑ r < m, (subCost r + subCost (m - 1 - r))`, even in the presence of duplicate keys. -/
theorem sum_subCost_pivot_le (u : List ℕ) :
    ∑ k : Fin u.length,
      (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))) ≤
        ∑ r ∈ Finset.range u.length, (subCost r + subCost (u.length - 1 - r)) :=
  sum_countP_pivot_le (fun a b => subCost a + subCost b)
    (fun ha hb => add_le_add (subCost_mono ha) (subCost_mono hb)) u

/-! ## Word-size arithmetic (`logWidth 3 n ≤ w`) and work-stack invariants -/

/-- `logWidth 3 n ≤ w` suffices to fit every address and temporary up to `3 * n + 3` for all
`n : ℕ` (including `n = 0`). -/
theorem fits_three_mul_add_three {n w : ℕ} (hw : logWidth 3 n ≤ w) :
    Fits w (3 * n + 3) := by
  rcases lt_or_ge n 2 with hn2 | hn2
  · interval_cases n <;> exact Fits.mono (w := 3) (by decide) (by simpa [logWidth] using hw)
  · exact (fits_of_lt_pow (k := 3) (n := n)
      (by rw [show (n + 1) ^ 3 = (n + 1) * (n + 1) * (n + 1) by ring]; nlinarith)).mono hw

/-- Two half-open intervals `[a₁, b₁)` and `[a₂, b₂)` are disjoint. -/
def IntervalDisjoint (p q : ℕ × ℕ) : Prop :=
  p.2 ≤ q.1 ∨ q.2 ≤ p.1

theorem IntervalDisjoint.symm {p q : ℕ × ℕ} (h : IntervalDisjoint p q) :
    IntervalDisjoint q p :=
  Or.symm h

private def stackFootprint (S : List (ℕ × ℕ)) : Finset ℕ :=
  S.foldr (fun q acc => Finset.Ico q.1 q.2 ∪ acc) ∅

private theorem mem_stackFootprint {x : ℕ} {S : List (ℕ × ℕ)}
    (hx : x ∈ stackFootprint S) : ∃ q ∈ S, x ∈ Finset.Ico q.1 q.2 := by
  induction S with
  | nil => simp [stackFootprint] at hx
  | cons q rest ih =>
    rw [stackFootprint, List.foldr_cons, Finset.mem_union] at hx
    rcases hx with hxq | hxrest
    · exact ⟨q, List.mem_cons_self, hxq⟩
    · obtain ⟨q', hq', hxq'⟩ := ih hxrest
      exact ⟨q', List.mem_cons_of_mem q hq', hxq'⟩

private theorem sum_len_eq_card_stackFootprint {S : List (ℕ × ℕ)}
    (hpwd : S.Pairwise IntervalDisjoint) :
    (S.map fun p => p.2 - p.1).sum = (stackFootprint S).card := by
  induction S with
  | nil => simp [stackFootprint]
  | cons p tl ih =>
    have hdisj : Disjoint (Finset.Ico p.1 p.2) (stackFootprint tl) := by
      rw [Finset.disjoint_left]
      intro x hxp hxtl
      obtain ⟨q, hq, hxq⟩ := mem_stackFootprint hxtl
      have hpq := List.rel_of_pairwise_cons hpwd hq
      rw [Finset.mem_Ico] at hxp hxq
      rcases hpq with h1 | h2 <;> omega
    have hunfold : stackFootprint (p :: tl) = Finset.Ico p.1 p.2 ∪ stackFootprint tl := rfl
    rw [hunfold, Finset.card_union_of_disjoint hdisj,
      Nat.card_Ico, List.map_cons, List.sum_cons, ih hpwd.of_cons]

/-- Every interval `(a, b) ∈ S` satisfies `1 ≤ a`, `a + 2 ≤ b`, and `b ≤ n + 1`, and the intervals
in `S` are pairwise disjoint. -/
def ValidStack (n : ℕ) (S : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 + 2 ≤ p.2 ∧ p.2 ≤ n + 1) ∧ S.Pairwise IntervalDisjoint

/-- Sum of lengths `∑ (b - a)` of intervals in `S` is at most `n` when `ValidStack n S` holds. -/
theorem ValidStack.sum_len_le {n : ℕ} {S : List (ℕ × ℕ)} (hS : ValidStack n S) :
    (S.map fun p => p.2 - p.1).sum ≤ n := by
  have hsub : stackFootprint S ⊆ Finset.Ico 1 (n + 1) := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_stackFootprint hx
    have hb := hS.1 q hq
    rw [Finset.mem_Ico] at hxq ⊢
    omega
  calc
    (S.map fun p => p.2 - p.1).sum = (stackFootprint S).card :=
      sum_len_eq_card_stackFootprint hS.2
    _ ≤ (Finset.Ico 1 (n + 1)).card := Finset.card_le_card hsub
    _ = n := by simp

/-- Twice `S.length` is at most `n` when `ValidStack n S` holds. -/
theorem ValidStack.two_mul_length_le {n : ℕ} {S : List (ℕ × ℕ)} (hS : ValidStack n S) :
    2 * S.length ≤ n := by
  have htwo : 2 * S.length ≤ (S.map fun p => p.2 - p.1).sum := by
    obtain ⟨hbnd, -⟩ := hS
    induction S with
    | nil => simp
    | cons p tl ih =>
      have hp := hbnd p List.mem_cons_self
      have hih := ih fun q hq => hbnd q (List.mem_cons_of_mem p hq)
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  exact htwo.trans hS.sum_len_le

/-- Global cross-interval order invariant: every pair `1 ≤ i < j < n + 1` not jointly contained in
any active stack interval `(a, b) ∈ S` is already ordered (`mem i ≤ mem j`). -/
def NoExternalInversions (n : ℕ) (mem : ℕ → ℕ) (S : List (ℕ × ℕ)) : Prop :=
  ∀ i j, 1 ≤ i → i < j → j < n + 1 →
    (∀ p ∈ S, ¬(p.1 ≤ i ∧ j < p.2)) → mem i ≤ mem j

/-! ## Structured WordRAM quicksort program (`r = 16`) -/

namespace Reg

/-- Constant `0`. -/
@[simp] abbrev zero : Fin 16 := 0
/-- Constant `1`. -/
@[simp] abbrev one : Fin 16 := 1
/-- Constant `2`. -/
@[simp] abbrev two : Fin 16 := 2
/-- Input array length `n`. -/
@[simp] abbrev len : Fin 16 := 3
/-- Base address `n + 1` of the `lo` work-stack array. -/
@[simp] abbrev stackLo : Fin 16 := 4
/-- Base address `2 * n + 1` of the `hi` work-stack array. -/
@[simp] abbrev stackHi : Fin 16 := 5
/-- Current stack pointer (`S.length`). -/
@[simp] abbrev sp : Fin 16 := 6
/-- Active subarray start address `lo`. -/
@[simp] abbrev lo : Fin 16 := 7
/-- Active subarray exclusive end address `hi`. -/
@[simp] abbrev hi : Fin 16 := 8
/-- 3-way partition `< piv` boundary `lt`. -/
@[simp] abbrev lt : Fin 16 := 9
/-- 3-way partition scan cursor `cur` (and `alloc` scratch during setup). -/
@[simp] abbrev cur : Fin 16 := 10
/-- 3-way partition `> piv` boundary `gt` (and `alloc` frontier during setup). -/
@[simp] abbrev gt : Fin 16 := 11
/-- Pivot value `piv`. -/
@[simp] abbrev piv : Fin 16 := 12
/-- Element scratch `val`. -/
@[simp] abbrev val : Fin 16 := 13
/-- Swap scratch `val2`. -/
@[simp] abbrev val2 : Fin 16 := 14
/-- Address / offset scratch `tmp`. -/
@[simp] abbrev tmp : Fin 16 := 15

end Reg

open Reg

/-- Swap memory cells `*a` and `*b` using scratch registers `v1, v2` (`4` instructions). -/
def swapCells (a b v1 v2 : Fin 16) : Code .standard 16 := ram[
  v1 ← *a;
  v2 ← *b;
  *a ← v2;
  *b ← v1 ]

/-- One Dutch National Flag 3-way partition step at cursor `cur` (`≤ 9` instructions). -/
def partStep : Code .standard 16 := ram[
  val ← *cur;
  if val < piv then [
    ⟪swapCells lt cur val val2⟫;
    lt ← lt + one;
    cur ← cur + one
  ] else [
    if piv < val then [
      gt ← gt - one;
      ⟪swapCells cur gt val val2⟫
    ] else [
      cur ← cur + one
    ]
  ] ]

/-- Push `[regs a, regs b)` onto `(stackLo, stackHi)` if `regs a + 2 ≤ regs b`. -/
def pushIfNonTrivial (a b : Fin 16) : Code .standard 16 := ram[
  tmp ← a + two;
  if b < tmp then [
    sp ← sp
  ] else [
    ⟪writeAt tmp stackLo sp a⟫;
    ⟪writeAt tmp stackHi sp b⟫;
    sp ← sp + one
  ] ]

/-- Deterministic prefix of `popAndSample`: decrement `sp`, load `lo` and `hi`, and compute
`tmp = hi - lo - 1` (`7` instructions). -/
def popPrefix : Code .standard 16 := ram[
  sp ← sp - one;
  ⟪readAt tmp lo stackLo sp⟫;
  ⟪readAt tmp hi stackHi sp⟫;
  tmp ← hi - lo;
  tmp ← tmp - one ]

/-- Pop the top range `[lo, hi)` from the stack and sample `tmp ← rand (hi - lo - 1)`. -/
def popAndSample : Code .standard 16 := ram[
  ⟪popPrefix⟫;
  tmp ← rand tmp ]

/-- Load pivot at `lo + tmp` and initialize `lt ← lo`, `cur ← lo`, `gt ← hi` (`5`
instructions). -/
def partInit : Code .standard 16 := ram[
  tmp ← lo + tmp;
  piv ← *tmp;
  lt ← lo;
  cur ← lo;
  gt ← hi ]

/-- Read the sampled pivot at `lo + tmp`, 3-way partition `[lo, hi)`, and push non-trivial
subranges `[lo, lt)` and `[gt, hi)`. -/
def partitionAndPush : Code .standard 16 := ram[
  ⟪partInit⟫;
  while cur < gt do [ ⟪partStep⟫ ];
  ⟪pushIfNonTrivial lo lt⟫;
  ⟪pushIfNonTrivial gt hi⟫ ]

/-- One iteration of the outer work-stack loop. -/
def outerBody : Code .standard 16 := ram[
  ⟪popAndSample⟫;
  ⟪partitionAndPush⟫ ]

/-- Allocate `stackLo` and `stackHi` of capacity `n` and push `[1, n + 1)` if `n ≥ 2`. -/
def setup : Code .standard 16 := ram[
  len ← *zero;
  one ← #1;
  gt ← len + one;
  ⟪alloc gt len stackLo cur zero one⟫;
  ⟪alloc gt len stackHi cur zero one⟫;
  two ← one + one;
  sp ← #0;
  lo ← one;
  hi ← len + one;
  ⟪pushIfNonTrivial lo hi⟫ ]

/-- Structured in-place 3-way randomized quicksort over 16 registers. -/
def code : Code .standard 16 := ram[
  ⟪setup⟫;
  while zero < sp do [ ⟪outerBody⟫ ] ]

/-- Compiled flat randomized quicksort program halting with `0` (in `zero`). -/
def program : Program .standard 16 :=
  code.program zero

/-- Quadratic worst-case instruction budget `20 * n ^ 2 + 8 * n + 32`. -/
def worstCaseTime (n : ℕ) : ℕ :=
  20 * n ^ 2 + 8 * n + 32

/-- `O(n log n)` expected instruction budget `120 * n * (⌊log₂ n⌋ + 1) + 32`. -/
def expectedTimeBound (n : ℕ) : ℕ :=
  120 * n * (Nat.log 2 n + 1) + 32

/-! ## Subroutine executions and partition invariants -/

/-- Swap two memory cells at addresses `p` and `q`. -/
def swapMem (mem : ℕ → ℕ) (p q : ℕ) : ℕ → ℕ :=
  Function.update (Function.update mem p (mem q)) q (mem p)

@[simp]
theorem swapMem_right (mem : ℕ → ℕ) (p q : ℕ) : swapMem mem p q q = mem p := by
  simp [swapMem]

@[simp]
theorem swapMem_left (mem : ℕ → ℕ) (p q : ℕ) : swapMem mem p q p = mem q := by
  by_cases hpq : p = q
  · subst hpq; simp [swapMem]
  · simp [swapMem, hpq]

theorem swapMem_of_ne {mem : ℕ → ℕ} {p q a : ℕ} (hap : a ≠ p) (haq : a ≠ q) :
    swapMem mem p q a = mem a := by
  simp [swapMem, hap, haq]

theorem modifies_swapMem {lo hi p q : ℕ} (hp : lo ≤ p ∧ p < hi) (hq : lo ≤ q ∧ q < hi)
    (mem : ℕ → ℕ) : Modifies (Finset.Ico lo hi) mem (swapMem mem p q) := by
  intro a ha
  rw [Finset.mem_Ico] at ha
  exact swapMem_of_ne (by omega) (by omega)

/-- `swapCells a b v1 v2` executes in `4` instructions, swapping `mem (regs a)` and `mem (regs b)`
and writing only scratch registers `v1, v2`. -/
theorem swapCells_exec {w : ℕ} {a b v1 v2 : Fin 16} {x : Data 16}
    (ha1 : a ≠ v1) (hb1 : b ≠ v1) (ha2 : a ≠ v2) (hb2 : b ≠ v2) (hv : v1 ≠ v2) :
    Exec w (swapCells a b v1 v2) x
      ⟨Function.update (Function.update x.regs v1 (x.mem (x.regs a))) v2 (x.mem (x.regs b)),
        swapMem x.mem (x.regs a) (x.regs b)⟩ 4 := by
  refine WP.Exact.exec ?_
  unfold swapCells
  wram_exec [ha1, hb1, ha2, hb2, hv]
  rfl

/-- Dutch National Flag 3-way partition loop invariant on `[lo, hi)`. -/
structure PartInv (w vlo vhi vpiv : ℕ) (mem₀ : ℕ → ℕ) (x : Data 16) : Prop where
  /-- Register `one` holds `1`. -/
  one_eq : x.regs one = 1
  /-- Register `lo` holds `vlo`. -/
  lo_eq : x.regs lo = vlo
  /-- Register `hi` holds `vhi`. -/
  hi_eq : x.regs hi = vhi
  /-- Register `piv` holds `vpiv`. -/
  piv_eq : x.regs piv = vpiv
  /-- `vhi` fits in `w` bits. -/
  fits_hi : Fits w vhi
  /-- `vlo ≤ lt`. -/
  lo_le_lt : vlo ≤ x.regs lt
  /-- `lt ≤ cur`. -/
  lt_le_cur : x.regs lt ≤ x.regs cur
  /-- `cur ≤ gt`. -/
  cur_le_gt : x.regs cur ≤ x.regs gt
  /-- `gt ≤ vhi`. -/
  gt_le_hi : x.regs gt ≤ vhi
  /-- `mem[vlo .. vhi)` is a permutation of `mem₀[vlo .. vhi)`. -/
  perm : (memSlice vlo vhi x.mem).Perm (memSlice vlo vhi mem₀)
  /-- Only `Finset.Ico vlo vhi` has been modified since `mem₀`. -/
  modifies : Modifies (Finset.Ico vlo vhi) mem₀ x.mem
  /-- `[vlo, lt)` holds elements `< vpiv`. -/
  lt_zone : ∀ a, vlo ≤ a → a < x.regs lt → x.mem a < vpiv
  /-- `[lt, cur)` holds elements `= vpiv`. -/
  eq_zone : ∀ a, x.regs lt ≤ a → a < x.regs cur → x.mem a = vpiv
  /-- `[gt, vhi)` holds elements `> vpiv`. -/
  gt_zone : ∀ a, x.regs gt ≤ a → a < vhi → vpiv < x.mem a

private theorem PartInv.of_swap {w vlo vhi vpiv p q : ℕ} {mem₀ : ℕ → ℕ} {x y : Data 16}
    (hI : PartInv w vlo vhi vpiv mem₀ x) (hmem : y.mem = swapMem x.mem p q)
    (hp : vlo ≤ p ∧ p < vhi) (hq : vlo ≤ q ∧ q < vhi)
    (hone : y.regs one = 1) (hlo : y.regs lo = vlo) (hhi : y.regs hi = vhi)
    (hpiv : y.regs piv = vpiv)
    (h1 : vlo ≤ y.regs lt) (h2 : y.regs lt ≤ y.regs cur)
    (h3 : y.regs cur ≤ y.regs gt) (h4 : y.regs gt ≤ vhi)
    (hlt : ∀ a, vlo ≤ a → a < y.regs lt → swapMem x.mem p q a < vpiv)
    (heq : ∀ a, y.regs lt ≤ a → a < y.regs cur → swapMem x.mem p q a = vpiv)
    (hgt : ∀ a, y.regs gt ≤ a → a < vhi → vpiv < swapMem x.mem p q a) :
    PartInv w vlo vhi vpiv mem₀ y :=
  ⟨hone, hlo, hhi, hpiv, hI.fits_hi, h1, h2, h3, h4,
    hmem ▸ (memSlice_swap_perm hp hq x.mem).trans hI.perm,
    hmem ▸ by simpa only [Finset.union_self] using
      hI.modifies.trans (modifies_swapMem hp hq x.mem),
    hmem ▸ hlt, hmem ▸ heq, hmem ▸ hgt⟩

private theorem partStep_spec {w vlo vhi vpiv : ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : PartInv w vlo vhi vpiv mem₀ x) (hcg : x.regs cur < x.regs gt) :
    ∃ y, ExecWithin w partStep x y 9 ∧
      PartInv w vlo vhi vpiv mem₀ y ∧ y.regs gt - y.regs cur < x.regs gt - x.regs cur := by
  have h1 := hI.lo_le_lt; have h2 := hI.lt_le_cur; have h3 := hI.gt_le_hi
  have hfit (v : ℕ) (hv : v ≤ vhi) : Fits w v := hI.fits_hi.of_le hv
  refine WP.exists_execWithin ?_
  unfold partStep swapCells
  wram_exec [hI.piv_eq, hI.one_eq, hfit]
  · refine ⟨hI.of_swap (p := x.regs lt) (q := x.regs cur) rfl ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
    all_goals wram_simp [hI.one_eq, hI.lo_eq, hI.hi_eq, hI.piv_eq]
    any_goals omega
    · intro a ha1 ha2; rcases eq_or_lt_of_le (Nat.le_of_lt_succ ha2) with rfl | hlt
      · simpa using ‹x.mem (x.regs cur) < vpiv›
      · rw [swapMem_of_ne (by omega) (by omega)]; exact hI.lt_zone a ha1 hlt
    · intro a ha1 ha2; rcases eq_or_lt_of_le (Nat.le_of_lt_succ ha2) with rfl | hcur
      · rw [swapMem_right]; exact hI.eq_zone (x.regs lt) le_rfl (by omega)
      · rw [swapMem_of_ne (by omega) (by omega)]; exact hI.eq_zone a (by omega) hcur
    · exact fun a ha1 ha2 => by rw [swapMem_of_ne (by omega) (by omega)]; exact hI.gt_zone a ha1 ha2
  · refine ⟨hI.of_swap (p := x.regs cur) (q := x.regs gt - 1) rfl ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
    all_goals wram_simp [hI.one_eq, hI.lo_eq, hI.hi_eq, hI.piv_eq]
    any_goals omega
    · exact fun a ha1 ha2 => by rw [swapMem_of_ne (by omega) (by omega)]; exact hI.lt_zone a ha1 ha2
    · exact fun a ha1 ha2 => by rw [swapMem_of_ne (by omega) (by omega)]; exact hI.eq_zone a ha1 ha2
    · intro a ha1 ha2; rcases eq_or_lt_of_le ha1 with rfl | hgt
      · simpa using ‹vpiv < x.mem (x.regs cur)›
      · rw [swapMem_of_ne (by omega) (by omega)]; exact hI.gt_zone a (by omega) ha2
  · refine ⟨⟨?_, ?_, ?_, ?_, hI.fits_hi, ?_, ?_, ?_, ?_, hI.perm, hI.modifies, hI.lt_zone, ?_,
      hI.gt_zone⟩, ?_⟩
    all_goals wram_simp [hI.one_eq, hI.lo_eq, hI.hi_eq, hI.piv_eq]
    any_goals omega
    intro a ha1 ha2; rcases eq_or_lt_of_le (Nat.le_of_lt_succ ha2) with rfl | hcur
    · have : ¬x.mem (x.regs cur) < vpiv := ‹_›; have : ¬vpiv < x.mem (x.regs cur) := ‹_›; omega
    · exact hI.eq_zone a ha1 hcur

/-- Full 3-way partition loop executes within `11 * (vhi - vlo) + 2` instructions and exits with
`cur = gt`. -/
theorem partLoop_spec {w vlo vhi vpiv : ℕ} {x : Data 16} (hI : PartInv w vlo vhi vpiv x.mem x)
    (_hlt_init : x.regs lt = vlo) (hcur_init : x.regs cur = vlo) (hgt_init : x.regs gt = vhi) :
    ∃ y, ExecWithin w (ram[ while cur < gt do [ ⟪partStep⟫ ] ]) x y (11 * (vhi - vlo) + 2) ∧
      PartInv w vlo vhi vpiv x.mem y ∧ y.regs cur = y.regs gt := by
  obtain ⟨y, hy, hIy, hnc⟩ := ExecWithin.loop_invariant
    (cond := Cond.lt cur gt) (body := partStep) (PartInv w vlo vhi vpiv x.mem)
    (fun z => z.regs gt - z.regs cur) (T := 9) (fun _ h hc => partStep_spec h hc) hI
  have hcur_le := hIy.cur_le_gt
  change ¬y.regs cur < y.regs gt at hnc
  exact ⟨y, hy.mono (by rw [hgt_init, hcur_init]; omega), hIy, by omega⟩

/-! ## Work-stack representation and `pushIfNonTrivial` -/

/-- Read the active work-stack directly from `(x.regs sp, x.mem)` at base addresses `n + 1` and
`2 * n + 1`. -/
def readStack (n : ℕ) (x : Data 16) : List (ℕ × ℕ) :=
  (List.range (x.regs sp)).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))

@[simp]
theorem length_readStack (n : ℕ) (x : Data 16) : (readStack n x).length = x.regs sp := by
  simp [readStack]

theorem readStack_congr {n : ℕ} {x y : Data 16} (hsp : y.regs sp = x.regs sp)
    (hmem : ∀ a, n + 1 ≤ a → y.mem a = x.mem a) : readStack n y = readStack n x := by
  simp only [readStack, hsp]
  refine List.map_congr_left fun i _ => ?_
  rw [hmem (n + 1 + i) (by omega), hmem (2 * n + 1 + i) (by omega)]

/-- `pushIfNonTrivial a b` runs within `8` instructions, appending `(va, vb)` to `readStack n` iff
`va + 2 ≤ vb`, and modifying memory only inside `Finset.Ico (n + 1) (3 * n + 1)`. -/
theorem pushIfNonTrivial_spec {w n : ℕ} {a b : Fin 16} {x : Data 16}
    (ha_tmp : a ≠ tmp) (hb_tmp : b ≠ tmp)
    (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hsLo : x.regs stackLo = n + 1) (hsHi : x.regs stackHi = 2 * n + 1)
    (hfit_all : Fits w (3 * n + 3))
    (hvb : x.regs a ≤ n + 1 ∧ x.regs b ≤ n + 1)
    (hcap : x.regs a + 2 ≤ x.regs b → x.regs sp < n) :
    ∃ y, ExecWithin w (pushIfNonTrivial a b) x y 8 ∧
      readStack n y =
        (if x.regs a + 2 ≤ x.regs b then readStack n x ++ [(x.regs a, x.regs b)]
         else readStack n x) ∧
      Modifies (Finset.Ico (n + 1) (3 * n + 1)) x.mem y.mem := by
  have hfit (v : ℕ) (hv : v ≤ 3 * n + 3) : Fits w v := hfit_all.of_le hv
  refine WP.exists_execWithin ?_
  unfold pushIfNonTrivial writeAt
  by_cases hge : x.regs a + 2 ≤ x.regs b
  · have hk_lt : x.regs sp < n := hcap hge
    have hnlt : ¬x.regs b < x.regs a + 2 := by omega
    wram_exec [htwo, hone, hsLo, hsHi, hnlt, hfit]
    refine ⟨?_, fun addr haddr => ?_⟩
    · simp only [hge, ↓reduceIte, readStack]
      wram_simp [Data.write_mem, hsLo, hsHi]
      rw [List.range_succ, List.map_append, List.map_singleton]
      congr 1
      · refine List.map_congr_left fun i hi => ?_
        rw [List.mem_range] at hi
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self]
    · rw [Finset.mem_Ico] at haddr
      wram_simp
  · have hlt : x.regs b < x.regs a + 2 := by omega
    wram_exec [htwo, hlt, hfit]
    simp only [hge, ↓reduceIte]
    exact ⟨readStack_congr (by wram_simp) fun _ _ => rfl, Modifies.refl _ _⟩

/-! ## Global outer-loop invariant and preservation across 3-way partition -/

/-- Full outer-loop machine invariant for in-place randomized quicksort. -/
structure OuterInv (w : ℕ) (input : List ℕ) (x : Data 16) : Prop where
  /-- Word size meets `logWidth 3 input.length ≤ w`. -/
  hw : logWidth 3 input.length ≤ w
  /-- Register `zero` holds `0`. -/
  zero_eq : x.regs zero = 0
  /-- Register `one` holds `1`. -/
  one_eq : x.regs one = 1
  /-- Register `two` holds `2`. -/
  two_eq : x.regs two = 2
  /-- Register `len` holds `input.length`. -/
  len_eq : x.regs len = input.length
  /-- Register `stackLo` holds `input.length + 1`. -/
  stackLo_eq : x.regs stackLo = input.length + 1
  /-- Register `stackHi` holds `2 * input.length + 1`. -/
  stackHi_eq : x.regs stackHi = 2 * input.length + 1
  /-- Active work-stack intervals are valid and pairwise disjoint. -/
  valid_stack : ValidStack input.length (readStack input.length x)
  /-- All inversions lie strictly inside active work-stack intervals. -/
  no_ext_inv : NoExternalInversions input.length x.mem (readStack input.length x)
  /-- `mem[1 .. n + 1)` is a permutation of `input`. -/
  perm : (memSlice 1 (input.length + 1) x.mem).Perm input
  /-- Only `Finset.Ico 1 (3 * n + 1)` has been modified since `Data.init input`. -/
  modifies : Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem x.mem

private theorem validStack_push_if {n a b : ℕ} {S : List (ℕ × ℕ)} (hS : ValidStack n S)
    (ha : 1 ≤ a) (hb : b ≤ n + 1) (hdisj : ∀ p ∈ S, IntervalDisjoint p (a, b)) :
    ValidStack n (if a + 2 ≤ b then S ++ [(a, b)] else S) := by
  split_ifs with hlen
  · refine ⟨fun p hp => ?_, List.pairwise_append.mpr ⟨hS.2, List.pairwise_singleton _ _, ?_⟩⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hS.1 p hp
      · rw [List.mem_singleton] at hp; subst hp; exact ⟨ha, hlen, hb⟩
    · intro p hp _ hq
      rw [List.mem_singleton] at hq; subst hq; exact hdisj p hp
  · exact hS

private theorem validStack_push_children {n vlo vlt vgt vhi : ℕ} {S₀ : List (ℕ × ℕ)}
    (hS : ValidStack n (S₀ ++ [(vlo, vhi)]))
    (hb : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi) :
    let S₁ := if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀
    ValidStack n S₁ ∧ ValidStack n (if vgt + 2 ≤ vhi then S₁ ++ [(vgt, vhi)] else S₁) := by
  intro S₁
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  obtain ⟨hS₀_pwd, -, hdisj_hi⟩ := List.pairwise_append.mp hS.2
  have hS₀ : ValidStack n S₀ := ⟨fun p hp => hS.1 p (List.mem_append_left _ hp), hS₀_pwd⟩
  have hdisj : ∀ p ∈ S₀, IntervalDisjoint p (vlo, vhi) :=
    fun p hp => hdisj_hi p hp (vlo, vhi) (List.mem_singleton_self _)
  have hS₁ : ValidStack n S₁ := validStack_push_if hS₀ hp_hi.1 (by omega) fun p hp =>
    (hdisj p hp).elim Or.inl fun h => Or.inr (by omega)
  refine ⟨hS₁, validStack_push_if hS₁ (by omega) hp_hi.2.2 fun p hp => ?_⟩
  have hsub : ∀ p ∈ S₀, IntervalDisjoint p (vgt, vhi) := fun p hp =>
    (hdisj p hp).elim (fun h => Or.inl (by omega)) Or.inr
  dsimp only [S₁] at hp
  split_ifs at hp
  · rcases List.mem_append.mp hp with hp₀ | hp₁
    · exact hsub p hp₀
    · rw [List.mem_singleton] at hp₁; subst hp₁; exact Or.inl (by omega)
  · exact hsub p hp

private theorem noExternalInversions_in_range {vlo vlt vgt vhi vpiv i j : ℕ}
    {mem₁ : ℕ → ℕ} {S₀ : List (ℕ × ℕ)} (hij : i < j) (hlo : vlo ≤ i) (hhi : j < vhi)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → mem₁ a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → mem₁ a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < mem₁ a)
    (hno : ∀ p ∈ (let S₁ := if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀
      if vgt + 2 ≤ vhi then S₁ ++ [(vgt, vhi)] else S₁), ¬(p.1 ≤ i ∧ j < p.2)) :
    mem₁ i ≤ mem₁ j := by
  rcases lt_or_ge i vlt with hi_lt | hi_ge_lt
  · rcases lt_or_ge j vlt with hj_lt | hj_ge_lt
    · exact absurd ⟨hlo, hj_lt⟩ (hno (vlo, vlt) (by split_ifs <;> simp_all <;> omega))
    · rcases lt_or_ge j vgt with hj_eq | hj_gt
      · have := hlt_z i hlo hi_lt; have := heq_z j hj_ge_lt hj_eq; omega
      · have := hlt_z i hlo hi_lt; have := hgt_z j hj_gt hhi; omega
  · rcases lt_or_ge i vgt with hi_eq | hi_gt
    · rcases lt_or_ge j vgt with hj_eq | hj_gt
      · have := heq_z i hi_ge_lt hi_eq; have := heq_z j (by omega) hj_eq; omega
      · have := heq_z i hi_ge_lt hi_eq; have := hgt_z j hj_gt hhi; omega
    · exact absurd ⟨hi_gt, hhi⟩ (hno (vgt, vhi) (by simp [show vgt + 2 ≤ vhi by omega]))

private theorem noExternalInversions_after_partition {n vlo vlt vgt vhi vpiv : ℕ}
    {S₀ : List (ℕ × ℕ)} {mem₀ mem₁ : ℕ → ℕ}
    (hS : ValidStack n (S₀ ++ [(vlo, vhi)]))
    (hinv₀ : NoExternalInversions n mem₀ (S₀ ++ [(vlo, vhi)]))
    (_hb : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi)
    (hperm : (memSlice vlo vhi mem₁).Perm (memSlice vlo vhi mem₀))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₀ mem₁)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → mem₁ a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → mem₁ a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < mem₁ a) :
    let S₁ := if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀
    let S₂ := if vgt + 2 ≤ vhi then S₁ ++ [(vgt, vhi)] else S₁
    NoExternalInversions n mem₁ S₂ := by
  intro S₁ S₂ i j hi1 hij hjn hno
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  obtain ⟨-, -, hdisj_hi⟩ := List.pairwise_append.mp hS.2
  have hex_orig : ∀ a, vlo ≤ a → a < vhi → ∃ a', vlo ≤ a' ∧ a' < vhi ∧ mem₁ a = mem₀ a' := by
    intro a ha1 ha2
    obtain ⟨a', ha'1, ha'2, heq⟩ :=
      mem_memSlice_iff.mp (hperm.subset (mem_memSlice_iff.mpr ⟨a, ha1, ha2, rfl⟩))
    exact ⟨a', ha'1, ha'2, heq.symm⟩
  have hno_split : ∀ a b, (vlo ≤ a ∧ a < vhi ∧ vhi ≤ b ∨ a < vlo ∧ vlo ≤ b ∧ b < vhi) →
      ∀ p ∈ S₀ ++ [(vlo, vhi)], ¬(p.1 ≤ a ∧ b < p.2) := by
    intro a b hab p hp
    rcases List.mem_append.mp hp with hp₀ | hp_last
    · rcases hdisj_hi p hp₀ (vlo, vhi) (List.mem_singleton_self _) with h | h <;>
        rcases hab with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · rw [List.mem_singleton.mp hp_last]; rcases hab with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
  by_cases hij_in : vlo ≤ i ∧ j < vhi
  · exact noExternalInversions_in_range hij hij_in.1 hij_in.2 hlt_z heq_z hgt_z hno
  · by_cases hi_in : vlo ≤ i ∧ i < vhi
    · obtain ⟨i', hi'1, hi'2, hi_eq⟩ := hex_orig i hi_in.1 hi_in.2
      rw [hi_eq, hmod j (by simp only [Finset.mem_Ico]; omega)]
      exact hinv₀ i' j (by omega) (by omega) hjn (hno_split i' j (Or.inl ⟨hi'1, hi'2, by omega⟩))
    · by_cases hj_in : vlo ≤ j ∧ j < vhi
      · obtain ⟨j', hj'1, hj'2, hj_eq⟩ := hex_orig j hj_in.1 hj_in.2
        rw [hmod i (by simp only [Finset.mem_Ico]; omega), hj_eq]
        exact hinv₀ i j' hi1 (by omega) (by omega) (hno_split i j' (Or.inr ⟨by omega, hj'1, hj'2⟩))
      · rw [hmod i (by simp only [Finset.mem_Ico]; omega),
          hmod j (by simp only [Finset.mem_Ico]; omega)]
        refine hinv₀ i j hi1 hij hjn fun p hp => ?_
        rcases List.mem_append.mp hp with hp₀ | hp_last
        · exact hno p (by dsimp only [S₂, S₁]; split_ifs <;> simp [hp₀])
        · rw [List.mem_singleton.mp hp_last]; omega

private theorem perm_full_of_subslice {n vlo vhi : ℕ} {mem₀ mem₁ : ℕ → ℕ}
    (hb : 1 ≤ vlo ∧ vlo ≤ vhi ∧ vhi ≤ n + 1)
    (hsub : (memSlice vlo vhi mem₁).Perm (memSlice vlo vhi mem₀))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₀ mem₁) :
    (memSlice 1 (n + 1) mem₁).Perm (memSlice 1 (n + 1) mem₀) := by
  rw [memSlice_append hb.1 (by omega) mem₁, memSlice_append hb.2.1 hb.2.2 mem₁,
    memSlice_append hb.1 (by omega) mem₀, memSlice_append hb.2.1 hb.2.2 mem₀]
  have hleft : memSlice 1 vlo mem₁ = memSlice 1 vlo mem₀ :=
    memSlice_congr fun a ha1 ha2 => hmod a (by simp [Finset.mem_Ico]; omega)
  have hright : memSlice vhi (n + 1) mem₁ = memSlice vhi (n + 1) mem₀ :=
    memSlice_congr fun a ha1 ha2 => hmod a (by simp [Finset.mem_Ico]; omega)
  rw [hleft, hright]
  exact List.Perm.append_left _ (hsub.append_right _)

/-- Append `(vlo, vlo + m₁)` and `(vhi - m₂, vhi)` to `S₀` when each has length at least `2`. -/
private def pushChildren (S₀ : List (ℕ × ℕ)) (vlo vhi m₁ m₂ : ℕ) : List (ℕ × ℕ) :=
  let S₁ := if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀
  if 2 ≤ m₂ then S₁ ++ [(vhi - m₂, vhi)] else S₁

private theorem pushIfValid_spec {w n va vb : ℕ} {a b : Fin 16} {S : List (ℕ × ℕ)} {x : Data 16}
    (ha_tmp : a ≠ tmp) (hb_tmp : b ≠ tmp) (ha : x.regs a = va) (hb : x.regs b = vb)
    (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hsLo : x.regs stackLo = n + 1) (hsHi : x.regs stackHi = 2 * n + 1)
    (hfit : Fits w (3 * n + 3)) (hread : readStack n x = S)
    (hvb : va ≤ n + 1 ∧ vb ≤ n + 1)
    (hV : ValidStack n (if va + 2 ≤ vb then S ++ [(va, vb)] else S)) :
    ∃ y, ExecWithin w (pushIfNonTrivial a b) x y 8 ∧
      readStack n y = (if va + 2 ≤ vb then S ++ [(va, vb)] else S) ∧
      Modifies (Finset.Ico (n + 1) (3 * n + 1)) x.mem y.mem := by
  obtain ⟨y, he, hr, hm⟩ := pushIfNonTrivial_spec ha_tmp hb_tmp hone htwo hsLo hsHi hfit
    (by rw [ha, hb]; exact hvb) fun hge => by
      rw [ha, hb] at hge
      have hV' : ValidStack n (S ++ [(va, vb)]) := by simpa only [hge, ↓reduceIte] using hV
      have h2 := hV'.two_mul_length_le
      rw [List.length_append, List.length_singleton, ← hread, length_readStack] at h2; omega
  exact ⟨y, he, by rwa [ha, hb, hread] at hr, hm⟩

private theorem pushChildren_eq_boundaries {S₀ : List (ℕ × ℕ)} {vlo vlt vgt vhi m₁ m₂ : ℕ}
    (hvlt : vlt = vlo + m₁) (hvgt : vgt = vhi - m₂) (hm₂ : m₂ ≤ vhi - vlo) :
    (if vgt + 2 ≤ vhi then (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀) ++ [(vgt, vhi)]
     else (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀)) =
      pushChildren S₀ vlo vhi m₁ m₂ := by
  have h1 : (vlo + 2 ≤ vlt) ↔ (2 ≤ m₁) := by omega
  have h2 : (vgt + 2 ≤ vhi) ↔ (2 ≤ m₂) := by omega
  subst hvlt hvgt
  simp only [pushChildren, h1, h2]

private theorem partInit_spec {w vlo vhi k : ℕ} {x : Data 16}
    (hlo : x.regs lo = vlo) (hhi : x.regs hi = vhi) (htmp : x.regs tmp = k)
    (hone : x.regs one = 1) (hk : k < vhi - vlo) (hfit : Fits w vhi) :
    ∃ y, ExecWithin w partInit x y 5 ∧
      y.mem = x.mem ∧
      PartInv w vlo vhi (x.mem (vlo + k)) x.mem y ∧
      y.regs lt = vlo ∧ y.regs cur = vlo ∧ y.regs gt = vhi := by
  have hfit_k : Fits w (vlo + k) := hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold partInit
  wram_exec [hlo, hhi, htmp, hfit_k]
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, hfit, ?_, ?_, ?_, ?_, List.Perm.refl _, Modifies.refl _ _,
      ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals wram_simp [hone, hlo, hhi]
  all_goals omega

private theorem outerInv_mem_after_partition {input : List ℕ} {vlo vlt vgt vhi vpiv : ℕ}
    {S₀ S₂ : List (ℕ × ℕ)} {mem₀ mem₁ mem₂ : ℕ → ℕ}
    (hS : ValidStack input.length (S₀ ++ [(vlo, vhi)]))
    (hinv₀ : NoExternalInversions input.length mem₀ (S₀ ++ [(vlo, vhi)]))
    (hperm₀ : (memSlice 1 (input.length + 1) mem₀).Perm input)
    (hmod₀ : Modifies (Finset.Ico 1 (3 * input.length + 1))
      (Data.init (r := 16) input).mem mem₀)
    (hb : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi)
    (hperm₁ : (memSlice vlo vhi mem₁).Perm (memSlice vlo vhi mem₀))
    (hmod₁ : Modifies (Finset.Ico vlo vhi) mem₀ mem₁)
    (hlt : ∀ a, vlo ≤ a → a < vlt → mem₁ a < vpiv)
    (heq : ∀ a, vlt ≤ a → a < vgt → mem₁ a = vpiv)
    (hgt : ∀ a, vgt ≤ a → a < vhi → vpiv < mem₁ a)
    (hmod₂ : Modifies (Finset.Ico (input.length + 1) (3 * input.length + 1)) mem₁ mem₂)
    (hS₂ : S₂ = if vgt + 2 ≤ vhi then
      (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀) ++ [(vgt, vhi)]
      else if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀) :
    NoExternalInversions input.length mem₂ S₂ ∧
    (memSlice 1 (input.length + 1) mem₂).Perm input ∧
    Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem mem₂ := by
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  have hslice_eq : ∀ a, 1 ≤ a → a < input.length + 1 → mem₂ a = mem₁ a := fun a h1 h2 =>
    hmod₂ a (by simp only [Finset.mem_Ico]; omega)
  have hno := noExternalInversions_after_partition hS hinv₀ hb hperm₁ hmod₁ hlt heq hgt
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · subst hS₂
    intro i j hi1 hij hjn h
    rw [hslice_eq i hi1 (by omega), hslice_eq j (by omega) hjn]
    exact hno i j hi1 hij hjn h
  · rw [memSlice_congr hslice_eq]
    exact (perm_full_of_subslice ⟨hp_hi.1, by omega, hp_hi.2.2⟩ hperm₁ hmod₁).trans hperm₀
  · rw [Finset.mem_Ico] at ha
    rw [hmod₂ a (by simp only [Finset.mem_Ico]; omega),
      hmod₁ a (by simp only [Finset.mem_Ico]; omega),
      hmod₀ a (by simp only [Finset.mem_Ico]; omega)]

/-- Deterministic execution of `partitionAndPush` after `popAndSample` has popped `(vlo, vhi)`
leaving stack `S₀` and sampled offset `k < vhi - vlo` into `tmp`. -/
theorem partitionAndPush_spec {w : ℕ} {input : List ℕ} {vlo vhi : ℕ} {S₀ : List (ℕ × ℕ)}
    {x : Data 16} (k : Fin (vhi - vlo))
    (hktmp : x.regs tmp = k.val)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hlen : x.regs len = input.length)
    (hsLo : x.regs stackLo = input.length + 1) (hsHi : x.regs stackHi = 2 * input.length + 1)
    (hlo : x.regs lo = vlo) (hhi : x.regs hi = vhi)
    (hw : logWidth 3 input.length ≤ w)
    (hread : readStack input.length x = S₀)
    (hS : ValidStack input.length (S₀ ++ [(vlo, vhi)]))
    (hinv₀ : NoExternalInversions input.length x.mem (S₀ ++ [(vlo, vhi)]))
    (hperm₀ : (memSlice 1 (input.length + 1) x.mem).Perm input)
    (hmod₀ : Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem x.mem) :
    let u := memSlice vlo vhi x.mem
    let m₁ := u.countP (· < u[k.val]'(by simp [u]))
    let m₂ := u.countP (u[k.val]'(by simp [u]) < ·)
    let S₁ := if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀
    let S₂ := if 2 ≤ m₂ then S₁ ++ [(vhi - m₂, vhi)] else S₁
    ∃ y t, Exec w partitionAndPush x y t ∧ t ≤ 11 * (vhi - vlo) + 23 ∧
      OuterInv w input y ∧ readStack input.length y = S₂ := by
  intro u m₁ m₂ S₁ S₂
  set n := input.length
  have hfit_all : Fits w (3 * n + 3) := fits_three_mul_add_three hw
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  obtain ⟨x₅, e_init, hx₅_mem, hPart₀, hlt₅, hcur₅, hgt₅⟩ :=
    partInit_spec hlo hhi hktmp hone k.isLt (hfit_all.of_le (by omega))
  obtain ⟨x₆, e_loop, hPart₆, hcg₆⟩ := partLoop_spec (hx₅_mem ▸ hPart₀) hlt₅ hcur₅ hgt₅
  rw [hx₅_mem] at hPart₆
  set vlt := x₆.regs lt; set vgt := x₆.regs gt
  have hpiv_u : x.mem (vlo + k.val) = u[k.val]'(by simp [u]) := (getElem_memSlice k.isLt).symm
  have heq_gt : ∀ a, vlt ≤ a → a < vgt → x₆.mem a = x.mem (vlo + k.val) :=
    fun a h1 h2 => hPart₆.eq_zone a h1 (hcg₆ ▸ h2)
  have hlt_le_gt : vlt ≤ vgt := hcg₆ ▸ hPart₆.lt_le_cur
  obtain ⟨hlt_gt, hm₁_eq, hm₂_eq⟩ := partition_counts_and_lt
    ⟨hPart₆.lo_le_lt, hlt_le_gt, hPart₆.gt_le_hi⟩
    hPart₆.perm hPart₆.lt_zone heq_gt hPart₆.gt_zone
    (mem_memSlice_iff.mpr ⟨vlo + k.val, by omega, by omega, rfl⟩)
  obtain ⟨hVS₁, hVS₂⟩ := validStack_push_children (vlt := vlt) (vgt := vgt) hS
    ⟨hPart₆.lo_le_lt, hlt_gt, hPart₆.gt_le_hi⟩
  have hread₆ : readStack n x₆ = S₀ := hread ▸ readStack_congr (by regs_frame)
    fun a ha => hPart₆.modifies a (by simp only [Finset.mem_Ico]; omega)
  have hbnd_lt := hPart₆.lo_le_lt; have hbnd_gt := hPart₆.gt_le_hi
  obtain ⟨x₇, e_push₁, hread₇, hmod₇⟩ := pushIfValid_spec (by decide) (by decide)
    hPart₆.lo_eq rfl hPart₆.one_eq (by regs_frame) (by regs_frame) (by regs_frame)
    hfit_all hread₆ ⟨by omega, by omega⟩ hVS₁
  obtain ⟨y, e_push₂, hread_y, hmod_y⟩ := pushIfValid_spec (by decide) (by decide)
    (show x₇.regs gt = vgt by regs_frame) (show x₇.regs hi = vhi by regs_frame)
    (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    hfit_all hread₇ ⟨by omega, by omega⟩ hVS₂
  have hm₁_def : m₁ = vlt - vlo := by dsimp only [m₁, u]; rw [← hpiv_u, ← hm₁_eq]
  have hm₂_def : m₂ = vhi - vgt := by dsimp only [m₂, u]; rw [← hpiv_u, ← hm₂_eq]
  have hS₂_eq : _ = S₂ := pushChildren_eq_boundaries (S₀ := S₀) (vlo := vlo) (vlt := vlt)
    (vgt := vgt) (vhi := vhi) (by omega) (by omega) (by omega)
  have hread_final : readStack n y = S₂ := hread_y.trans hS₂_eq
  obtain ⟨hno_y, hperm_y, hmod_y'⟩ := outerInv_mem_after_partition hS hinv₀ hperm₀ hmod₀
    ⟨hPart₆.lo_le_lt, hlt_gt, hPart₆.gt_le_hi⟩ hPart₆.perm hPart₆.modifies hPart₆.lt_zone
    heq_gt hPart₆.gt_zone (by simpa only [Finset.union_self] using hmod₇.trans hmod_y)
    hS₂_eq.symm
  obtain ⟨t, ht_le, he_all⟩ := (e_init.seq (e_loop.seq (e_push₁.seq e_push₂))).mono
    (show 5 + (11 * (vhi - vlo) + 2 + (8 + 8)) ≤ 11 * (vhi - vlo) + 23 by omega)
  exact ⟨y, t, he_all, ht_le, ⟨hw, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, hread_final ▸ hS₂_eq ▸ hVS₂, hread_final ▸ hno_y,
    hperm_y, hmod_y'⟩, hread_final⟩

/-! ## Randomized `popAndSample`, `outerBody`, `setup`, and headline bounds -/

private theorem readStack_eq_snoc {n k : ℕ} {x : Data 16} (hsp : x.regs sp = k + 1) :
    readStack n x =
      ((List.range k).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))) ++
        [(x.mem (n + 1 + k), x.mem (2 * n + 1 + k))] := by
  simp [readStack, hsp, List.range_succ]

private theorem popAndSample_spec {w n k_sp : ℕ} {x : Data 16}
    (hsp : x.regs sp = k_sp + 1) (hone : x.regs one = 1)
    (hsLo : x.regs stackLo = n + 1) (hsHi : x.regs stackHi = 2 * n + 1)
    (hfit_all : Fits w (3 * n + 3)) (hk : k_sp < n)
    (hhi : x.mem (2 * n + 1 + k_sp) ≤ n + 1) :
    let vlo := x.mem (n + 1 + k_sp)
    let vhi := x.mem (2 * n + 1 + k_sp)
    ∃ p : Data 16, ExecRand w popAndSample x
      ((fun k : Fin (vhi - vlo - 1 + 1) => (p.set tmp k.val, 8)) <$>
        ProbComp.unifFin (vhi - vlo - 1)) ∧
      p.mem = x.mem ∧ p.regs sp = k_sp ∧ p.regs lo = vlo ∧ p.regs hi = vhi ∧
      (∀ r, r ≠ sp → r ≠ lo → r ≠ hi → r ≠ tmp → p.regs r = x.regs r) := by
  intro vlo vhi
  have hfit (v : ℕ) (hv : v ≤ 3 * n + 3) : Fits w v := hfit_all.of_le hv
  obtain ⟨p, e_pre, hpmem, hsp_p, hlo_p, hhi_p, htmp_p⟩ :
      ∃ p, Exec w popPrefix x p 7 ∧ p.mem = x.mem ∧ p.regs sp = k_sp ∧
        p.regs lo = vlo ∧ p.regs hi = vhi ∧ p.regs tmp = vhi - vlo - 1 := by
    refine WP.Exact.exists_exec ?_
    unfold popPrefix readAt
    wram_exec [hsp, hone, hsLo, hsHi, hfit]
    wram_simp [Nat.add_sub_cancel, vlo, vhi]
  have hr := ExecRand.rand (B := .standard) (w := w) (dst := tmp) (src := tmp) (x := p)
    (by rw [htmp_p]; exact hfit_all.of_le (by dsimp only [vlo, vhi]; omega))
  rw [htmp_p] at hr
  have heq : (fun z : Data 16 × ℕ => (z.1, 7 + z.2)) <$> (do
      let k ← ProbComp.unifFin (vhi - vlo - 1); pure (p.set tmp k.val, 1)) =
      (fun k : Fin (vhi - vlo - 1 + 1) => (p.set tmp k.val, 8)) <$>
        ProbComp.unifFin (vhi - vlo - 1) := by
    simp only [← bind_pure_comp, bind_assoc, pure_bind]
  refine ⟨p, by simpa only [popAndSample, heq] using e_pre.seqRand hr,
    hpmem, hsp_p, hlo_p, hhi_p, fun r h1 h2 h3 h4 => e_pre.regs_eq ?_⟩
  simp [popPrefix, readAt, Code.Preserves, Op.bin, Op.dest, h1.symm, h2.symm, h3.symm, h4.symm]

/-- One iteration `outerBody` from an active state (`0 < sp`) pops `(vlo, vhi)`, samples a uniform
pivot `k ← unifFin (vhi - vlo - 1)` (`1` `rand` call), and runs `partitionAndPush` in at most
`11 * (vhi - vlo) + 31` total instructions. -/
theorem outerBody_spec {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : OuterInv w input x) (hc : (Cond.lt zero sp).Holds x) :
    ∃ S₀ vlo vhi,
      readStack input.length x = S₀ ++ [(vlo, vhi)] ∧
      ∃ (_ : vlo + 2 ≤ vhi),
      ∃ y : Fin (vhi - vlo - 1 + 1) → Data 16,
      ∃ t : Fin (vhi - vlo - 1 + 1) → ℕ,
        ExecRand w outerBody x
          ((fun k => (y k, 8 + t k)) <$> ProbComp.unifFin (vhi - vlo - 1)) ∧
        ∀ k : Fin (vhi - vlo - 1 + 1),
          t k ≤ 11 * (vhi - vlo) + 23 ∧
          OuterInv w input (y k) ∧
          let u := memSlice vlo vhi x.mem
          let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
          let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
          let S₁ := if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀
          readStack input.length (y k) =
            (if 2 ≤ m₂ then S₁ ++ [(vhi - m₂, vhi)] else S₁) := by
  set n := input.length
  have hsp_pos : 0 < x.regs sp := by simpa [Cond.holds_lt, hI.zero_eq] using hc
  set k_sp := x.regs sp - 1
  have hsp_succ : x.regs sp = k_sp + 1 := by omega
  set S₀ := (List.range k_sp).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))
  set vlo := x.mem (n + 1 + k_sp); set vhi := x.mem (2 * n + 1 + k_sp)
  have hstack_eq : readStack n x = S₀ ++ [(vlo, vhi)] := readStack_eq_snoc hsp_succ
  have hVS : ValidStack n (S₀ ++ [(vlo, vhi)]) := hstack_eq ▸ hI.valid_stack
  have hp_hi := hVS.1 (vlo, vhi) (by simp)
  have hk_lt_n : k_sp < n := by
    have h2 := hVS.two_mul_length_le
    simp only [List.length_append, List.length_singleton, S₀, List.length_map,
      List.length_range] at h2; omega
  obtain ⟨p, e_pop, hpmem, hsp_p, hlo_p, hhi_p, hfr_p⟩ := popAndSample_spec hsp_succ
    hI.one_eq hI.stackLo_eq hI.stackHi_eq (fits_three_mul_add_three hI.hw) hk_lt_n hp_hi.2.2
  choose y t hspec using fun k : Fin (vhi - vlo - 1 + 1) =>
    partitionAndPush_spec (x := p.set tmp k.val) ⟨k.val, by have := k.isLt; omega⟩
      (by simp) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      hI.hw (by simp [readStack, hsp_p, hpmem, S₀, n]) hVS
      (by rw [Data.set_mem, hpmem, ← hstack_eq]; exact hI.no_ext_inv)
      (by simpa only [Data.set_mem, hpmem] using hI.perm)
      (by simpa only [Data.set_mem, hpmem] using hI.modifies)
  exact ⟨S₀, vlo, vhi, hstack_eq, hp_hi.2.1, y, t,
    execRand_seq_det_map e_pop fun k => (hspec k).1,
    fun k => by simpa only [Data.set_mem, hpmem, vlo, vhi, n] using (hspec k).2⟩

/-- Quadratic worst-case step potential `∑_{(a,b) ∈ S} 20 * (b - a) ^ 2`. -/
def stepPotential (n : ℕ) (x : Data 16) : ℕ :=
  ((readStack n x).map fun p => 20 * (p.2 - p.1) ^ 2).sum

/-- `rand`-call potential `∑_{(a,b) ∈ S} (b - a - 1)`. -/
def callPotential (n : ℕ) (x : Data 16) : ℕ :=
  ((readStack n x).map fun p => p.2 - p.1 - 1).sum

/-- Expected-time potential `ENNReal.ofReal (∑_{(a,b) ∈ S} subCost (b - a))`. -/
noncomputable def expPotential (n : ℕ) (x : Data 16) : ℝ≥0∞ :=
  ENNReal.ofReal (((readStack n x).map fun p => subCost (p.2 - p.1)).sum)

private theorem countP_lt_add_gt_add_count (u : List ℕ) (piv : ℕ) :
    u.countP (· < piv) + u.countP (piv < ·) + u.count piv = u.length := by
  induction u with
  | nil => simp
  | cons a tl ih =>
    simp only [List.countP_cons, List.count_cons, List.length_cons, beq_iff_eq]
    rcases lt_trichotomy a piv with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]; omega
    · simp; omega
    · simp [h, h.ne', not_lt.mpr h.le]; omega

private theorem countP_lt_add_gt_le {u : List ℕ} {piv : ℕ} (hpiv : piv ∈ u) :
    u.countP (· < piv) + u.countP (piv < ·) + 1 ≤ u.length := by
  have := countP_lt_add_gt_add_count u piv
  have := List.count_pos_iff.mpr hpiv
  omega

/-- Pushing the children `(vlo, vlo + m₁)` and `(vhi - m₂, vhi)` of a popped segment, each only when
it has at least two elements, adds at most `f m₁ + f m₂` to a sum of nonnegative `f` over the
segment widths of the stack. -/
private theorem sum_childStack_le {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] (f : ℕ → M) (hf : ∀ d, 0 ≤ f d) {S₀ S : List (ℕ × ℕ)}
    {vlo vhi m₁ m₂ : ℕ} (hm₂ : m₂ ≤ vhi - vlo)
    (hS : S = pushChildren S₀ vlo vhi m₁ m₂) :
    (S.map fun p => f (p.2 - p.1)).sum ≤ (S₀.map fun p => f (p.2 - p.1)).sum + (f m₁ + f m₂) := by
  have hsub : vhi - (vhi - m₂) = m₂ := by omega
  subst hS
  unfold pushChildren
  split_ifs <;> simp only [List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton, Nat.add_sub_cancel_left, hsub, add_assoc]
  · exact le_rfl
  · exact add_le_add le_rfl (le_add_of_nonneg_right (hf _))
  · exact add_le_add le_rfl (le_add_of_nonneg_left (hf _))
  · exact le_add_of_nonneg_right (add_nonneg (hf _) (hf _))

private theorem outerBody_worstCase_step {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : OuterInv w input x) (hc : (Cond.lt zero sp).Holds x) :
    ∃ T_b, ExecRandWithin w outerBody x
      (fun y => OuterInv w input y ∧
        T_b + 2 + stepPotential input.length y ≤ stepPotential input.length x ∧
        1 + callPotential input.length y ≤ callPotential input.length x) T_b 1 := by
  obtain ⟨S₀, vlo, vhi, hstack, hge2, y, t, hexec, hspec⟩ := outerBody_spec hI hc
  let m := vhi - vlo
  refine ⟨11 * m + 31, _, hexec,
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbComp.isQueryBounded_unifFin (m - 1)),
    fun z hz => ?_⟩
  obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨ht_le, hIy, hread_yk⟩ := hspec k
  have hk_lt : k.val < (memSlice vlo vhi x.mem).length := by have := k.isLt; simp; omega
  have hm12_le : (memSlice vlo vhi x.mem).countP (· < (memSlice vlo vhi x.mem)[k.val]) +
      (memSlice vlo vhi x.mem).countP ((memSlice vlo vhi x.mem)[k.val] < ·) ≤ m - 1 := by
    have := countP_lt_add_gt_le (List.getElem_mem hk_lt)
    rw [length_memSlice] at this
    omega
  have hread_pc : readStack input.length (y k) = pushChildren S₀ vlo vhi
      ((memSlice vlo vhi x.mem).countP (· < (memSlice vlo vhi x.mem)[k.val]'hk_lt))
      ((memSlice vlo vhi x.mem).countP ((memSlice vlo vhi x.mem)[k.val]'hk_lt < ·)) := hread_yk
  have hstep := sum_childStack_le (fun d => 20 * d ^ 2) (fun _ => Nat.zero_le _)
    (by omega) hread_pc
  have hcall := sum_childStack_le (fun d => d - 1) (fun _ => Nat.zero_le _)
    (by omega) hread_pc
  have hsq : ∀ a b : ℕ, a + b ≤ m - 1 → 11 * m + 33 + (20 * a ^ 2 + 20 * b ^ 2) ≤ 20 * m ^ 2 := by
    intro a b hab
    have : a ^ 2 + b ^ 2 ≤ (m - 1) ^ 2 := by
      have := Nat.pow_le_pow_left hab 2; nlinarith
    obtain ⟨d, hd⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
    have hd1 : m - 1 = d + 1 := by omega
    rw [hd1] at this; rw [hd]; nlinarith
  have hq := hsq _ _ hm12_le
  dsimp only [m] at hq
  simp only [stepPotential, callPotential, hstack, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton] at hstep hcall ⊢
  exact ⟨⟨hIy, by omega, by omega⟩, by omega⟩

private theorem list_sum_subCost_nonneg (S : List (ℕ × ℕ)) :
    0 ≤ (S.map fun p => subCost (p.2 - p.1)).sum :=
  List.sum_nonneg fun _ hv => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hv; exact subCost_nonneg _

private theorem avg_subCost_pivot_le (u : List ℕ) (hm : 2 ≤ u.length) (base : ℝ) :
    (∑ k : Fin u.length, (28 * (u.length : ℝ) + base +
      (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))))) /
      (u.length : ℝ) ≤ base + subCost u.length := by
  have hm_pos : (0 : ℝ) < u.length := by exact_mod_cast (by omega : 0 < u.length)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    add_div, mul_div_cancel_left₀ _ hm_pos.ne']
  have hdiv : (∑ k : Fin u.length,
      (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·)))) / (u.length : ℝ) ≤
      (∑ r ∈ Finset.range u.length, (subCost r + subCost (u.length - 1 - r))) / (u.length : ℝ) :=
    div_le_div_of_nonneg_right (sum_subCost_pivot_le u) hm_pos.le
  linarith [subCost_recurrence hm]

private theorem ennreal_avg_subCost_le {m : ℕ} (u : List ℕ) (hlen : u.length = m) (hm : 2 ≤ m)
    {base : ℝ} (hbase : 0 ≤ base) {g : Fin (m - 1 + 1) → ℝ≥0∞}
    (hg : ∀ k : Fin (m - 1 + 1), g k ≤ ENNReal.ofReal (28 * (m : ℝ) + base +
      (subCost (u.countP (· < u[k.val]'(by have := k.isLt; omega))) +
       subCost (u.countP (u[k.val]'(by have := k.isLt; omega) < ·))))) :
    (∑ k : Fin (m - 1 + 1), g k) / (((m - 1 : ℕ) : ℝ≥0∞) + 1) ≤
      ENNReal.ofReal (base + subCost m) := by
  have hden : ((m - 1 : ℕ) : ℝ≥0∞) + 1 = ENNReal.ofReal (m : ℝ) := by
    rw [ENNReal.ofReal_natCast]; exact_mod_cast (by omega : m - 1 + 1 = m)
  let rhs : Fin (m - 1 + 1) → ℝ := fun k => 28 * (m : ℝ) + base +
    (subCost (u.countP (· < u[k.val]'(by have := k.isLt; omega))) +
     subCost (u.countP (u[k.val]'(by have := k.isLt; omega) < ·)))
  calc (∑ k, g k) / (((m - 1 : ℕ) : ℝ≥0∞) + 1)
      ≤ (∑ k, ENNReal.ofReal (rhs k)) / ENNReal.ofReal (m : ℝ) := by rw [hden]; gcongr; exact hg _
    _ = ENNReal.ofReal ((∑ k, rhs k) / m) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => add_nonneg (add_nonneg (by positivity) hbase)
            (add_nonneg (subCost_nonneg _) (subCost_nonneg _)),
          ENNReal.ofReal_div_of_pos (by exact_mod_cast (by omega : 0 < m))]
    _ ≤ ENNReal.ofReal (base + subCost m) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm_eq : m - 1 + 1 = u.length := by omega
        have heq := Fintype.sum_equiv (finCongr hm_eq) rhs (fun k : Fin u.length =>
            28 * (u.length : ℝ) + base +
              (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))))
          (fun k => by simp only [rhs, hlen, finCongr_apply, Fin.val_cast])
        simpa only [heq, hlen] using avg_subCost_pivot_le u (by omega) base

private theorem outerBody_drift_step {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : OuterInv w input x) (hc : (Cond.lt zero sp).Holds x) :
    ∃ mb, ExecRand w outerBody x mb ∧
      (∀ z ∈ mb.support,
        OuterInv w input z.1 ∧ callPotential input.length z.1 < callPotential input.length x) ∧
      ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + expPotential input.length z.1) ≤
        expPotential input.length x := by
  obtain ⟨S₀, vlo, vhi, hstack, hge2, y, t, hexec, hspec⟩ := outerBody_spec hI hc
  refine ⟨_, hexec, fun z hz => ?_, ?_⟩
  · obtain ⟨_, mb, hmb, -, hpot⟩ := outerBody_worstCase_step hI hc
    obtain rfl := hexec.unique hmb
    obtain ⟨⟨hIz, -, hcall⟩, _⟩ := hpot z hz
    exact ⟨hIz, by omega⟩
  · rw [ProbComp.expect_map, ProbComp.expect_unifFin, expPotential, hstack,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    refine ennreal_avg_subCost_le (memSlice vlo vhi x.mem) (length_memSlice vlo vhi x.mem)
      (by omega) (list_sum_subCost_nonneg S₀) fun k => ?_
    obtain ⟨ht_le, -, hread_yk⟩ := hspec k
    have hcost := sum_childStack_le subCost subCost_nonneg
      (List.countP_le_length.trans_eq (length_memSlice vlo vhi x.mem))
      (hread_yk : readStack input.length (y k) = pushChildren S₀ vlo vhi _ _)
    have hstep : ((8 + t k + 2 : ℕ) : ℝ) ≤ 28 * (vhi - vlo : ℕ) := by
      exact_mod_cast (by omega : 8 + t k + 2 ≤ 28 * (vhi - vlo))
    dsimp only
    rw [show ((8 + t k : ℕ) : ℝ≥0∞) + 2 = ENNReal.ofReal ((8 + t k + 2 : ℕ) : ℝ) by
          rw [ENNReal.ofReal_natCast]; push_cast; rfl,
        expPotential, ← ENNReal.ofReal_add (by positivity) (list_sum_subCost_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

private theorem outerInv_init_of_mem {w : ℕ} {input : List ℕ} {x : Data 16}
    (hw : logWidth 3 input.length ≤ w)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hlen : x.regs len = input.length)
    (hsLo : x.regs stackLo = input.length + 1) (hsHi : x.regs stackHi = 2 * input.length + 1)
    (hstack : readStack input.length x = if 2 ≤ input.length then [(1, input.length + 1)] else [])
    (hmem_out : Modifies (Finset.Ico (input.length + 1) (3 * input.length + 1))
      (Data.init (r := 16) input).mem x.mem) : OuterInv w input x := by
  have hslice : memSlice 1 (input.length + 1) x.mem = input := by
    rw [memSlice_congr fun a h1 h2 => hmem_out a (by simp only [Finset.mem_Ico]; omega)]
    refine List.ext_getElem (by simp) fun i _ h2 => ?_
    rw [getElem_memSlice (by omega), show 1 + i = i + 1 by omega]
    simp [Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  have hVS : ValidStack input.length (readStack input.length x) := by
    rw [hstack]; split_ifs with hn2
    · exact ⟨fun p hp => by rw [List.mem_singleton.mp hp]; exact ⟨le_rfl, by omega, le_rfl⟩,
        List.pairwise_singleton _ _⟩
    · exact ⟨fun _ hp => by simp at hp, List.Pairwise.nil⟩
  have hno_inv : NoExternalInversions input.length x.mem (readStack input.length x) := by
    rw [hstack]
    intro i j hi1 hij hjn hno
    simp only [show 2 ≤ input.length by omega, ↓reduceIte] at hno
    exact absurd ⟨hi1, hjn⟩ (hno (1, input.length + 1) (List.mem_singleton_self _))
  exact ⟨hw, hzero, hone, htwo, hlen, hsLo, hsHi, hVS, hno_inv, by rw [hslice],
    fun a ha => hmem_out a (by simp only [Finset.mem_Ico] at ha ⊢; omega)⟩

private theorem alloc_stack_spec {w n base : ℕ} {dst : Fin 16} {x : Data 16}
    (hd : [gt, len, dst, cur, zero, one].Nodup)
    (hgt : x.regs gt = base) (hlen : x.regs len = n)
    (h1 : Fits w 1) (hfit : Fits w (base + n)) :
    ∃ y, ExecWithin w (alloc gt len dst cur zero one) x y (4 * n + 7) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs dst = base ∧ y.regs gt = base + n ∧
      y.mem = clear x.mem base n ∧
      (∀ r, r ≠ zero → r ≠ one → r ≠ dst → r ≠ gt → r ≠ cur → y.regs r = x.regs r) := by
  have he := alloc_exec (w := w) (x := x) hd h1 (by rw [hgt, hlen]; exact hfit)
  have ⟨hdz, hdo, hdc, hgd⟩ : dst ≠ zero ∧ dst ≠ one ∧ dst ≠ cur ∧ gt ≠ dst := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
    tauto
  refine ⟨_, he.within.mono (by rw [hlen]), ?_, ?_, ?_, ?_, by rw [hgt, hlen],
    fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4]⟩
  all_goals simp [Function.update_of_ne, hdz.symm, hdo.symm, hdc, hgd.symm, hgt, hlen]

/-- `setup` executes deterministically from `Data.init input` within `8 * input.length + 29`
instructions, establishing `OuterInv` with initial stack `[(1, n + 1)]` (if `2 ≤ n`) or `[]`. -/
theorem setup_spec {w : ℕ} {input : List ℕ} (hw : logWidth 3 input.length ≤ w) :
    ∃ x_init t_s, Exec w setup (Data.init input) x_init t_s ∧
      t_s ≤ 8 * input.length + 29 ∧
      OuterInv w input x_init ∧
      readStack input.length x_init =
        (if 2 ≤ input.length then [(1, input.length + 1)] else []) := by
  set n := input.length; set x₀ : Data 16 := Data.init input
  have hfit_all : Fits w (3 * n + 3) := fits_three_mul_add_three hw
  have hfit (v : ℕ) (hv : v ≤ 3 * n + 3) : Fits w v := hfit_all.of_le hv
  have hx₀_zero : x₀.regs zero = 0 := rfl
  have hx₀_len : x₀.mem 0 = n := by simp [x₀, n]
  suffices h : ∃ x_init, ExecWithin w setup x₀ x_init (8 * n + 29) ∧
      OuterInv w input x_init ∧ readStack n x_init = (if 2 ≤ n then [(1, n + 1)] else []) by
    obtain ⟨x_init, ⟨t_s, hts_le, he⟩, hI, hs⟩ := h; exact ⟨x_init, t_s, he, hts_le, hI, hs⟩
  refine WP.exists_execWithin ?_
  unfold setup
  wram_exec [hx₀_zero, hx₀_len, hfit]
  wram_call (alloc_stack_spec (dst := stackLo) (base := n + 1) (n := n) (by decide)
    (by wram_simp) (by wram_simp) (hfit 1 (by omega)) (hfit _ (by omega)))
    with s₄ ⟨hs₄_z, hs₄_o, hs₄_lo, hs₄_gt, hs₄_mem, hs₄_fr⟩
  have hs₄_len : s₄.regs len = n := by regs_frame
  refine WP.seq ?_
  wram_call (alloc_stack_spec (dst := stackHi) (base := n + 1 + n) (n := n) (by decide)
    hs₄_gt hs₄_len (hfit 1 (by omega)) (hfit _ (by omega)))
    with s₅ ⟨hs₅_z, hs₅_o, hs₅_hi, hs₅_gt, hs₅_mem, hs₅_fr⟩
  have hs₅_len : s₅.regs len = n := by regs_frame
  have hs₅_lo : s₅.regs stackLo = n + 1 := by regs_frame
  wram_exec [hs₅_o, hs₅_len, hfit]
  obtain ⟨x_init, e_push, hread_init, hmod_push⟩ := pushIfNonTrivial_spec (w := w) (n := n)
    (a := lo) (b := hi) (x := (((s₅.set two 2).set sp 0).set lo 1).set hi (n + 1))
    (by decide) (by decide) (by wram_simp [hs₅_o]) (by wram_simp) (by wram_simp [hs₅_lo])
    (by wram_simp [hs₅_hi]; omega) hfit_all ⟨by wram_simp, by wram_simp; exact le_rfl⟩
    fun hge => by wram_simp at hge ⊢; omega
  have hstack : readStack n x_init = if 2 ≤ n then [(1, n + 1)] else [] := by
    rw [hread_init, show readStack n ((((s₅.set two 2).set sp 0).set lo 1).set hi (n + 1)) = []
      by simp [readStack]]; wram_simp; split_ifs <;> rfl
  have hmod_out : Modifies (Finset.Ico (n + 1) (3 * n + 1)) x₀.mem x_init.mem := fun a ha => by
    rw [Finset.mem_Ico] at ha
    rw [hmod_push a (by simp only [Finset.mem_Ico]; omega)]
    simp only [Data.set_mem, hs₅_mem, hs₄_mem]
    rw [clear_of_not_owns (by wram_omega), clear_of_not_owns (by wram_omega)]
  refine WP.of_execWithin e_push ⟨by omega, outerInv_init_of_mem hw ?_ ?_ ?_ ?_ ?_ ?_
    hstack hmod_out, hstack⟩
  all_goals
    rw [e_push.regs_eq (by decide)]
    wram_simp [hs₅_z, hs₅_o, hs₅_len, hs₅_lo, hs₅_hi, n]
  omega

private theorem expPotential_init_le {n : ℕ} {x_init : Data 16}
    (hstack : readStack n x_init = if 2 ≤ n then [(1, n + 1)] else []) :
    expPotential n x_init ≤ (112 * n * (Nat.log 2 n + 1) : ℕ) := by
  rw [expPotential, hstack, ← ENNReal.ofReal_natCast]
  split_ifs with hn2
  · simp only [List.map_singleton, List.sum_singleton, Nat.add_sub_cancel_right]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlog : (harmonic n : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
      exact_mod_cast harmonic_le_log_add_one n
    have hn_le : (n : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (by omega : n + 1 ≤ 2 * n)
    calc subCost n
        ≤ 56 * ((n : ℝ) + 1) * (harmonic n : ℝ) := subCost_le_formula n
      _ ≤ 56 * ((n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := by gcongr
      _ ≤ ((112 * n * (Nat.log 2 n + 1) : ℕ) : ℝ) := by
          push_cast; nlinarith [show (0 : ℝ) ≤ Nat.log 2 n + 1 by positivity]
  · simp

private theorem halted_sorted_realizes {w : ℕ} {input : List ℕ} {y : Data 16}
    (hI : OuterInv w input y) (hsp : y.regs sp = 0) :
    (memSlice 1 (input.length + 1) y.mem).Pairwise (· ≤ ·) ∧
    (Block.mk 1 input.length).Realizes y.mem
      (fun i => input.mergeSort[i.val]'(by simpa only [List.length_mergeSort] using i.isLt)) := by
  have hstack_empty : readStack input.length y = [] := by simp [readStack, hsp]
  have hsorted : (memSlice 1 (input.length + 1) y.mem).Pairwise (· ≤ ·) :=
    List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
      simp only [length_memSlice, Nat.add_sub_cancel_right] at hi hj
      rw [getElem_memSlice (by omega), getElem_memSlice (by omega)]
      exact hI.no_ext_inv (1 + i) (1 + j) (by omega) (by omega) (by omega) fun p hp => by
        simp [hstack_empty] at hp
  have hslice_eq : memSlice 1 (input.length + 1) y.mem = input.mergeSort :=
    (hI.perm.trans (List.mergeSort_perm input _).symm).eq_of_pairwise' hsorted
      (List.pairwise_mergeSort' (· ≤ ·) input)
  refine ⟨hsorted, fun i => ?_⟩
  have hlt : i.val < input.length := i.isLt
  have := getElem_memSlice (a := 1) (b := input.length + 1) (mem := y.mem)
    (by omega : i.val < input.length + 1 - 1)
  simpa [Block.read, hslice_eq] using this.symm

/-- **In-place randomized quicksort: correctness, worst-case bounds, `rand`-call bound, and
`O(n log n)` expected running time.**

For any `input : List ℕ` of length `n` and word size `w ≥ logWidth 3 n` with `InputFits w input`:
1. `program` halts without faulting within `worstCaseTime n = 20 * n ^ 2 + 8 * n + 32` instructions
   on every execution path (`RandHaltsWithin`);
2. Every execution path makes at most `n - 1` `rand` calls (`RandCallsBounded`);
3. On every supported halting configuration `.halted 0 y`, `y.Bounded w` holds,
   `memSlice 1 (n + 1) y.mem` is a sorted permutation of `input`, `Block.mk 1 n` realizes
   `input.mergeSort`, and memory outside `Finset.Ico 1 (3 * n + 1)` is untouched (`Modifies`);
4. The expected instruction count satisfies
   `expectedTime w program (.init input) ≤ expectedTimeBound n = 120 * n * (⌊log₂ n⌋ + 1) + 32`
   unconditionally (even when `input` contains duplicate elements). -/
theorem quicksort_correct_and_bounds {w : ℕ} {input : List ℕ}
    (hw : logWidth 3 input.length ≤ w) (hfit : InputFits w input) :
    RandHaltsWithin w program (.init input) (worstCaseTime input.length) ∧
    RandCallsBounded w program (.init input) (worstCaseTime input.length) (input.length - 1) ∧
    (∀ cfg ∈ (runRand w program (worstCaseTime input.length) (.running (.init input))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧
        y.Bounded w ∧
        (memSlice 1 (input.length + 1) y.mem).Perm input ∧
        (memSlice 1 (input.length + 1) y.mem).Pairwise (· ≤ ·) ∧
        (Block.mk 1 input.length).Realizes y.mem
          (fun i => input.mergeSort[i.val]'(by simpa only [List.length_mergeSort] using i.isLt)) ∧
        Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem y.mem) ∧
    expectedTime w program (.init input) ≤ (expectedTimeBound input.length : ℝ≥0∞) := by
  set n := input.length
  obtain ⟨x_init, t_s, he_setup, hts_le, hI_init, hstack_init⟩ := setup_spec hw
  have hstep_init : stepPotential n x_init ≤ 20 * n ^ 2 := by
    rw [stepPotential, hstack_init]; split_ifs <;> simp [n]
  have hcall_init : callPotential n x_init ≤ n - 1 := by
    rw [callPotential, hstack_init]; split_ifs <;> simp [n]
  have hloop_wc := (ExecRandWithin.loop_potential (OuterInv w input) (stepPotential n)
    (callPotential n) (fun _ hs hc =>
      let ⟨T_b, h⟩ := outerBody_worstCase_step hs hc; ⟨T_b, 1, h⟩) hI_init).mono
      (fun _ h => h) (by omega : stepPotential n x_init + 2 ≤ 20 * n ^ 2 + 2) hcall_init
  obtain ⟨hHalts, hCalls, hPost⟩ :=
    ((((ExecWithin.mono he_setup.within hts_le).execRandWithin rfl).seq
      fun _ hy => hy ▸ hloop_wc).mono (fun _ h => h) (by omega) (by omega) :
      ExecRandWithin w code (Data.init input) _ (20 * n ^ 2 + 8 * n + 31) (n - 1)).program
      zero (T' := worstCaseTime n) (by simp only [worstCaseTime]; omega)
  obtain ⟨⟨m_loop, hm_loop⟩, hloop_exp⟩ := expectedCodeTime_loop_le_of_drift
    (OuterInv w input) (callPotential n) (expPotential n) hI_init
    fun _ hs hc => outerBody_drift_step hs hc
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, ?_⟩
  · obtain ⟨y, hcfg_eq, hIy, hnc⟩ := hPost cfg hcfg
    rw [hIy.zero_eq] at hcfg_eq
    have hsp_zero : y.regs sp = 0 := by simp only [Cond.holds_lt, hIy.zero_eq] at hnc; omega
    obtain ⟨hsorted, hrealizes⟩ := halted_sorted_realizes hIy hsp_zero
    have hb := runRand_bounded_init hfit hcfg
    exact ⟨y, hcfg_eq, (hcfg_eq ▸ hb).2, hIy.perm, hsorted, hrealizes, hIy.modifies⟩
  · have hexec_code : ExecRand w code (Data.init input)
        ((fun z => (z.1, t_s + z.2)) <$> m_loop) := he_setup.seqRand hm_loop
    rw [program, State.init, expectedCodeTime_program hexec_code zero, code,
      expectedCodeTime_seq_of_exec he_setup]
    have ht : (t_s : ℝ≥0∞) ≤ (8 * n + 29 : ℕ) := by exact_mod_cast hts_le
    calc (t_s : ℝ≥0∞) + expectedCodeTime w _ x_init + 1
        ≤ (t_s : ℝ≥0∞) + (expPotential n x_init + 2) + 1 := by gcongr
      _ ≤ ((8 * n + 29 : ℕ) : ℝ≥0∞) +
            (((112 * n * (Nat.log 2 n + 1) : ℕ) : ℝ≥0∞) + 2) + 1 := by
          gcongr; exact expPotential_init_le hstack_init
      _ = ((8 * n + 29 + (112 * n * (Nat.log 2 n + 1) + 2) + 1 : ℕ) : ℝ≥0∞) := by norm_cast
      _ ≤ _ := by
          norm_cast; simp only [expectedTimeBound]; nlinarith [show 1 ≤ Nat.log 2 n + 1 by omega]

end Cslib.Algorithms.WordRAM.Quicksort
