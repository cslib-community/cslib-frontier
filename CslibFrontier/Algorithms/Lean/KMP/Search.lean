/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.KMP.Basic
import Mathlib.Data.List.Sort

/-!
# Knuth–Morris–Pratt Failure Table Construction and Exact String Matching

This module implements the Knuth–Morris–Pratt (`[KnuthMorrisPratt1977]`, Sections 1–2;
`[CLRS2009]`, Section 32.4) failure-table construction (`computePrefix`) and exact string matcher
(`kmpSearchWithPrefix`, `kmpMatches`, `kmpMatchesList`) as pure functions over arbitrary alphabets
`[DecidableEq α]`, proving soundness, completeness, and strict output ordering.

Linear `O(|p|)` and `O(|p| + |t|)` machine-level running-time bounds on word arrays are proved in
`CslibFrontier.Algorithms.WordRAM.KMP`.

## Source Conventions

* **Indexing:** arrays are `0`-indexed, so `pi[j] = borderLen p.toList (j + 1)` (`0 ≤ j < p.size`)
  stores `[CLRS2009]`'s `1`-indexed prefix table $\pi[1..m]$ at `j = q - 1`. Reported match shifts
  `s` are `0`-based (`t.extract s (s + p.size) = p`), matching `[CLRS2009]`'s shift
  $s \in \{0, \dots, n - m\}$.
* **Alphabet and empty pattern:** all operations are universe-polymorphic over any
  `[DecidableEq α]` in `Type*` (rather than a fixed finite alphabet $\Sigma$) and handle empty
  patterns `p.size = 0` unconditionally by returning `List.range (t.size + 1)` (whereas
  `[CLRS2009]` assumes $m \ge 1$).

## Main definitions

* `Cslib.Algorithms.Lean.KMP.IsPrefixTableFor`: `pi.size ≤ p.size` and
  `pi[j] = borderLen p.toList (j + 1)` for `j < pi.size`.
* `Cslib.Algorithms.Lean.KMP.IsDecreasingTable`: fallback bound `pi[j] ≤ j` for `j < pi.size`.
* `Cslib.Algorithms.Lean.KMP.IsMatchAt`: exact occurrence `s + p.size ≤ t.size` and
  `t.extract s (s + p.size) = p`.
* `Cslib.Algorithms.Lean.KMP.advance`: single-character KMP automaton transition.
* `Cslib.Algorithms.Lean.KMP.computePrefix`: failure-table construction on `Array α`.
* `Cslib.Algorithms.Lean.KMP.kmpSearchWithPrefix`, `kmpMatches`: exact string matching on
  `Array α` returning all match shifts in strictly increasing order.
* `Cslib.Algorithms.Lean.KMP.kmpMatchesList`: list wrapper returning all shifts `s ≤ t.length`
  where `p <+: t.drop s`.

## Main results

* `Cslib.Algorithms.Lean.KMP.advance_eq_nextLen` and
  `advance_eq_maxPrefixSuffixUpTo_take_succ`: under a valid failure table, `advance` agrees with
  `nextLen` and updates the matched prefix length on `t.take (i + 1)`.
* `Cslib.Algorithms.Lean.KMP.computePrefix_eq_ofFn`, `computePrefix_size`, and
  `getElem_computePrefix`: `computePrefix p` has size `p.size` and entry `q` equal to
  `borderLen p.toList (q + 1)`.
* `Cslib.Algorithms.Lean.KMP.mem_kmpMatches_iff`: `s ∈ kmpMatches p t ↔ IsMatchAt p t s`
  (unconditionally for all `p` and `t`, including empty patterns and overlapping matches).
* `Cslib.Algorithms.Lean.KMP.pairwise_lt_kmpMatches` and `nodup_kmpMatches`: match shifts are
  strictly increasing and duplicate-free.
* `Cslib.Algorithms.Lean.KMP.mem_kmpMatchesList_iff` and `kmpMatchesList_eq_filter_range`:
  `s ∈ kmpMatchesList p t ↔ s ≤ t.length ∧ p <+: t.drop s`, giving a kernel-decidable closed form
  `(List.range (t.length + 1)).filter (fun s => decide (p <+: t.drop s))`.

## References

* [D. E. Knuth, J. H. Morris, Jr., and V. R. Pratt, *Fast Pattern Matching in
  Strings*][KnuthMorrisPratt1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*,
  3rd ed., Section 32.4][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.KMP

/-! ## Prefix-table and exact-match specifications -/

/-- `pi` is a valid partial KMP failure table for `p` if `pi.size ≤ p.size` and each entry `pi[j]`
equals `borderLen p.toList (j + 1)`. -/
@[expose] def IsPrefixTableFor {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ) : Prop :=
  pi.size ≤ p.size ∧ ∀ (j : ℕ) (hj : j < pi.size), pi[j]'hj = borderLen p.toList (j + 1)

/-- Structural fallback bound `pi[j] ≤ j` for every `j < pi.size`. -/
@[expose] def IsDecreasingTable (pi : Array ℕ) : Prop :=
  ∀ (j : ℕ) (hj : j < pi.size), pi[j]'hj ≤ j

theorem IsPrefixTableFor.isDecreasingTable {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} (h : IsPrefixTableFor p pi) : IsDecreasingTable pi := by
  intro j hj
  have hp : p.toList ≠ [] := by
    have := h.1
    rw [← List.length_pos_iff, Array.length_toList]
    omega
  exact Nat.le_of_lt_succ (h.2 j hj ▸ borderLen_lt (by omega) hp)

/-- Pattern `p` occurs in text `t` at shift `s` (`0`-indexed). -/
@[expose] def IsMatchAt {α : Type*} (p t : Array α) (s : ℕ) : Prop :=
  s + p.size ≤ t.size ∧ t.extract s (s + p.size) = p

theorem isMatchAt_iff_toList {α : Type*} {p t : Array α} {s : ℕ} :
    IsMatchAt p t s ↔ s + p.size ≤ t.size ∧ p.toList <+: t.toList.drop s := by
  unfold IsMatchAt
  refine and_congr_right fun _ => ?_
  rw [← Array.toList_inj, Array.toList_extract, List.extract_eq_take_drop,
    show s + p.size - s = p.size by omega, List.prefix_iff_eq_take, Array.length_toList, eq_comm]

/-- For `i < t.size`, `p.toList` is a suffix of `t.toList.take (i + 1)` iff
`p.size ≤ i + 1` and `p` matches `t` at shift `i + 1 - p.size`. -/
theorem toList_isSuffix_take_iff_isMatchAt {α : Type*} {p t : Array α} {i : ℕ}
    (hit : i < t.size) :
    p.toList <:+ t.toList.take (i + 1) ↔
      p.size ≤ i + 1 ∧ IsMatchAt p t (i + 1 - p.size) := by
  rw [isMatchAt_iff_toList]
  constructor
  · intro hsuf
    have hlen_le : p.size ≤ i + 1 := by
      have h := hsuf.length_le
      rwa [Array.length_toList, List.length_take_of_le (by rw [Array.length_toList]; omega)] at h
    refine ⟨hlen_le, ⟨by omega, ?_⟩⟩
    rw [show i + 1 = i + 1 - p.size + p.size by omega, List.take_add] at hsuf
    obtain ⟨u, hu⟩ := hsuf
    rw [List.prefix_iff_eq_take, Array.length_toList]
    exact (List.append_inj' hu (by simp [List.length_take, List.length_drop]; omega)).2
  · rintro ⟨hlen_le, _, hpref⟩
    have htake_eq : p.toList = (t.toList.drop (i + 1 - p.size)).take p.size := by
      simpa only [Array.length_toList] using List.prefix_iff_eq_take.mp hpref
    rw [show i + 1 = i + 1 - p.size + p.size by omega, List.take_add, ← htake_eq]
    exact ⟨_, rfl⟩

/-! ## KMP automaton transition (`advance`) -/

/-- Single-character transition of the KMP automaton on pattern `p` with failure table `pi`. -/
@[expose] def advance {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ) (k : ℕ)
    (c : α) : ℕ :=
  if hk : k < p.size then
    if p[k]'hk = c then k + 1
    else if k = 0 then 0
    else if hpi : k - 1 < pi.size then
      if _hlt : pi[k - 1]'hpi < k then
        advance p pi (pi[k - 1]'hpi) c
      else 0
    else 0
  else 0
termination_by k

/-- Under a valid partial prefix table `IsPrefixTableFor p pi` covering `k ≤ pi.size` with
`k < p.size`, `advance` computes `nextLen p.toList k c`. -/
theorem advance_eq_nextLen {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} {k : ℕ} (c : α)
    (htab : IsPrefixTableFor p pi) (hkpi : k ≤ pi.size) (hkp : k < p.size) :
    advance p pi k c = nextLen p.toList k c := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have hklist : k < p.toList.length := by simpa only [Array.length_toList] using hkp
    rw [advance, nextLen]
    simp only [hkp, hklist, ↓reduceDIte, (Array.getElem_toList hkp).symm]
    split_ifs with hmatch hk0 hpi hlt
    · rfl
    · rfl
    · have hval := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0) ▸ htab.2 (k - 1) hpi
      rw [← hval]
      exact ih _ hlt (by omega) (by omega)
    · have hval := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0) ▸ htab.2 (k - 1) hpi
      exact (hlt (hval ▸ borderLen_lt (by omega) (by grind))).elim
    · omega

/-! ## Failure-table construction (`computePrefix`) -/

private def computePrefixLoop {α : Type*} [DecidableEq α] (p : Array α)
    (q : ℕ) (k : ℕ) (pi : Array ℕ) : Array ℕ :=
  if hq : q < p.size then
    let k' := advance p pi k (p[q]'hq)
    computePrefixLoop p (q + 1) k' (pi.push k')
  else
    pi
termination_by p.size - q

/-- Construct the KMP failure table of `p` (`[KnuthMorrisPratt1977]`; `[CLRS2009]`,
Section 32.4). -/
def computePrefix {α : Type*} [DecidableEq α] (p : Array α) : Array ℕ :=
  if p.size = 0 then
    #[]
  else
    computePrefixLoop p 1 0 #[0]

private theorem computePrefixLoop_spec {α : Type*} [DecidableEq α]
    {p : Array α} {q k : ℕ} {pi : Array ℕ}
    (hq1 : 1 ≤ q) (hqp : q ≤ p.size) (hsize : pi.size = q)
    (htab : IsPrefixTableFor p pi) (hk : k = borderLen p.toList q) :
    (computePrefixLoop p q k pi).size = p.size ∧
      IsPrefixTableFor p (computePrefixLoop p q k pi) := by
  fun_induction computePrefixLoop p q k pi with
  | case2 q k pi hq => exact ⟨hsize.trans (by omega), htab⟩
  | case1 q k pi hqlt k' ih =>
    have hqlist : q < p.toList.length := by simpa only [Array.length_toList] using hqlt
    have hpne : p.toList ≠ [] := List.length_pos_iff.mp (by omega)
    have hklt_q : k < q := hk ▸ borderLen_lt (by omega) hpne
    have hadv_eq : k' = borderLen p.toList (q + 1) := by
      dsimp only [k']
      rw [advance_eq_nextLen (p[q]'hqlt) htab (by omega) (by omega), hk,
        (Array.getElem_toList hqlt).symm, ← borderLen_succ hq1 hqlist]
    refine ih (by omega) (by omega) (by simp only [Array.size_push, hsize])
      ⟨by simp only [Array.size_push]; omega, fun j hj => ?_⟩ hadv_eq
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa [hsize] using hj)) with hjlt | rfl
    · exact Array.getElem_push_lt (hsize ▸ hjlt) ▸ htab.2 j (hsize ▸ hjlt)
    · subst j
      rwa [Array.getElem_push_eq]

theorem isPrefixTableFor_computePrefix {α : Type*} [DecidableEq α] (p : Array α) :
    (computePrefix p).size = p.size ∧ IsPrefixTableFor p (computePrefix p) := by
  unfold computePrefix
  split_ifs with hp0
  · exact ⟨hp0.symm, Nat.zero_le _, fun _ hj => by simp at hj⟩
  · refine computePrefixLoop_spec (Nat.le_refl 1) (by omega) rfl
      ⟨Nat.pos_of_ne_zero hp0, fun j hj => ?_⟩ (borderLen_one p.toList).symm
    obtain rfl : j = 0 := by simpa using hj
    exact (borderLen_one p.toList).symm

@[simp]
theorem computePrefix_size {α : Type*} [DecidableEq α] (p : Array α) :
    (computePrefix p).size = p.size :=
  (isPrefixTableFor_computePrefix p).1

theorem getElem_computePrefix {α : Type*} [DecidableEq α] (p : Array α)
    (q : ℕ) (hq : q < (computePrefix p).size) :
    (computePrefix p)[q]'hq = borderLen p.toList (q + 1) :=
  (isPrefixTableFor_computePrefix p).2.2 q hq

theorem computePrefix_eq_ofFn {α : Type*} [DecidableEq α] (p : Array α) :
    computePrefix p = Array.ofFn (n := p.size) fun q => borderLen p.toList (q.val + 1) := by
  apply Array.ext (by simp only [computePrefix_size, Array.size_ofFn])
  intro q h1 h2
  rw [getElem_computePrefix p q h1, Array.getElem_ofFn]

theorem isDecreasingTable_computePrefix {α : Type*} [DecidableEq α] (p : Array α) :
    IsDecreasingTable (computePrefix p) :=
  (isPrefixTableFor_computePrefix p).2.isDecreasingTable

/-! ## KMP exact string matching (`kmpSearchWithPrefix`, `kmpMatches`, `kmpMatchesList`) -/

private def resetFullMatch (pSize : ℕ) (pi : Array ℕ) : ℕ :=
  if h : pSize - 1 < pi.size then pi[pSize - 1]'h else 0

private def kmpSearchLoop {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ)
    (t : Array α) (i : ℕ) (k : ℕ) : List ℕ :=
  if hi : i < t.size then
    let k' := advance p pi k (t[i]'hi)
    if k' = p.size then
      (i + 1 - p.size) :: kmpSearchLoop p pi t (i + 1) (resetFullMatch p.size pi)
    else
      kmpSearchLoop p pi t (i + 1) k'
  else
    []
termination_by t.size - i

/-- Exact KMP string matching using a precomputed failure table `pi`
(`[KnuthMorrisPratt1977]`; `[CLRS2009]`, Section 32.4).
Returns all `0`-indexed match shifts in strictly increasing order; when `p.size = 0`, returns
`List.range (t.size + 1)`. -/
def kmpSearchWithPrefix {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ)
    (t : Array α) : List ℕ :=
  if p.size = 0 then
    List.range (t.size + 1)
  else
    kmpSearchLoop p pi t 0 0

/-- Pure KMP exact string matcher returning all `0`-indexed match shifts of `p` in `t` in strictly
increasing order (`[KnuthMorrisPratt1977]`, Sections 1–2; `[CLRS2009]`, Section 32.4). -/
def kmpMatches {α : Type*} [DecidableEq α] (p t : Array α) : List ℕ :=
  kmpSearchWithPrefix p (computePrefix p) t

/-- Pure KMP exact string matcher on `List α`. -/
@[expose] def kmpMatchesList {α : Type*} [DecidableEq α] (p t : List α) : List ℕ :=
  kmpMatches p.toArray t.toArray

/-- Reading `t[i]` through `advance` updates the longest matched prefix of `p` at the end of
`t.toList.take i` (bounded by `p.size - 1`) to the longest matched prefix at `t.toList.take (i + 1)`
(bounded by `p.size`). -/
theorem advance_eq_maxPrefixSuffixUpTo_take_succ {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} {t : Array α} {i k : ℕ}
    (hp : 0 < p.size) (hp_pi : pi.size = p.size) (htab : IsPrefixTableFor p pi)
    (hilt : i < t.size)
    (hk : k = maxPrefixSuffixUpTo p.toList (t.toList.take i) (p.size - 1)) :
    advance p pi k (t[i]'hilt) = maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.size := by
  have hilt_list : i < t.toList.length := by simpa only [Array.length_toList] using hilt
  have hkp : k < p.size := by
    have := maxPrefixSuffixUpTo_le_bound p.toList (t.toList.take i) (p.size - 1)
    omega
  rw [advance_eq_nextLen (t[i]'hilt) htab (by omega) hkp, hk, (Array.getElem_toList hilt).symm,
    List.take_add_one, getElem?_pos t.toList i hilt_list, Option.toList_some,
    ← show p.size - 1 + 1 = p.size by omega]
  exact (maxPrefixSuffixUpTo_append_singleton p.toList (t.toList.take i)
    (t.toList[i]'hilt_list) (B := p.size - 1) (by rw [Array.length_toList]; omega)).symm

private theorem kmpSearchLoop_spec {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} {t : Array α} {i k : ℕ}
    (hp : 0 < p.size) (hp_pi : pi.size = p.size) (htab : IsPrefixTableFor p pi)
    (hit : i ≤ t.size)
    (hk : k = maxPrefixSuffixUpTo p.toList (t.toList.take i) (p.size - 1)) :
    (∀ s, s ∈ kmpSearchLoop p pi t i k ↔ i + 1 ≤ s + p.size ∧ IsMatchAt p t s) ∧
      (kmpSearchLoop p pi t i k).Pairwise (· < ·) := by
  fun_induction kmpSearchLoop p pi t i k with
  | case3 i k hi =>
    simp only [List.not_mem_nil, false_iff, List.Pairwise.nil, and_true]
    rintro s ⟨_, hs_le, _⟩
    omega
  | case1 i k hilt k' hfull ihFull =>
    have hplist : 0 < p.toList.length := by simpa only [Array.length_toList] using hp
    have hadv_eq : k' = maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.size :=
      advance_eq_maxPrefixSuffixUpTo_take_succ hp hp_pi htab hilt hk
    have hfull_max : maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.toList.length =
        p.toList.length := by
      simpa only [Array.length_toList, hadv_eq.symm] using hfull
    have hpsuf : p.toList <:+ t.toList.take (i + 1) := by
      simpa only [hfull_max, List.take_length] using
        take_maxPrefixSuffixUpTo_isSuffix p.toList (t.toList.take (i + 1)) p.toList.length
    obtain ⟨hple_i1, hmatch_here⟩ := (toList_isSuffix_take_iff_isMatchAt hilt).mp hpsuf
    have hpi_idx : p.size - 1 < pi.size := by omega
    have hkNext_eq : resetFullMatch p.size pi =
        maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) (p.size - 1) := by
      simp only [resetFullMatch, hpi_idx, ↓reduceDIte, htab.2 (p.size - 1) hpi_idx]
      rw [show p.size - 1 + 1 = p.toList.length by rw [Array.length_toList]; omega,
        ← maxPrefixSuffixUpTo_pred_of_eq_length hplist hfull_max, Array.length_toList]
    obtain ⟨hmem_rest, hpw_rest⟩ := ihFull (by omega) hkNext_eq
    refine ⟨fun s => ?_, List.Pairwise.cons (fun s hs => ?_) hpw_rest⟩
    · simp only [List.mem_cons, hmem_rest]
      refine ⟨?_, fun ⟨hge, hm⟩ =>
        (Nat.eq_or_lt_of_le hge).imp (fun _ => by omega) fun _ => ⟨by omega, hm⟩⟩
      rintro (rfl | ⟨_, hm⟩)
      · exact ⟨by omega, hmatch_here⟩
      · exact ⟨by omega, hm⟩
    · have := ((hmem_rest s).mp hs).1
      omega
  | case2 i k hilt k' hnotfull ih =>
    have hadv_eq : k' = maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.size :=
      advance_eq_maxPrefixSuffixUpTo_take_succ hp hp_pi htab hilt hk
    have hk'_lt : maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.toList.length <
        p.toList.length :=
      lt_of_le_of_ne (maxPrefixSuffixUpTo_le_length _ _ _)
        (by simpa only [Array.length_toList, hadv_eq] using hnotfull)
    have hk'_pred : k' = maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) (p.size - 1) := by
      simpa only [Array.length_toList, ← hadv_eq] using
        (maxPrefixSuffixUpTo_pred_of_lt_length hk'_lt).symm
    have hnot_suf : ¬ (p.toList <:+ t.toList.take (i + 1)) := fun hsuf => by
      have := le_maxPrefixSuffixUpTo (B := p.toList.length) (Nat.le_refl _) (Nat.le_refl _)
        (by simpa only [List.take_length] using hsuf)
      omega
    obtain ⟨hmem_rest, hpw_rest⟩ := ih (by omega) hk'_pred
    refine ⟨fun s => ?_, hpw_rest⟩
    rw [hmem_rest]
    refine ⟨fun ⟨hge, hm⟩ => ⟨by omega, hm⟩, fun ⟨hge, hm⟩ => ?_⟩
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · obtain rfl : s = i + 1 - p.size := by omega
      exact (hnot_suf ((toList_isSuffix_take_iff_isMatchAt hilt).mpr ⟨by omega, hm⟩)).elim
    · exact ⟨by omega, hm⟩

theorem kmpSearchWithPrefix_spec {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} (t : Array α)
    (hsize : pi.size = p.size) (htab : IsPrefixTableFor p pi) :
    (∀ s, s ∈ kmpSearchWithPrefix p pi t ↔ IsMatchAt p t s) ∧
      (kmpSearchWithPrefix p pi t).Pairwise (· < ·) := by
  unfold kmpSearchWithPrefix
  split_ifs with hp0
  · obtain rfl : p = #[] := Array.eq_empty_of_size_eq_zero hp0
    refine ⟨fun s => ?_, List.pairwise_lt_range⟩
    simp only [List.mem_range, IsMatchAt, Array.size_empty, Nat.add_zero]
    exact ⟨fun hlt => ⟨by omega, Array.extract_empty_of_stop_le_start (Nat.le_refl s)⟩,
      fun ⟨hle, _⟩ => by omega⟩
  · have hk0 : 0 = maxPrefixSuffixUpTo p.toList (t.toList.take 0) (p.size - 1) :=
      eq_maxPrefixSuffixUpTo_iff.mpr ⟨Nat.zero_le _, Nat.zero_le _, List.nil_suffix,
        fun _ _ _ _ hsuf => by
          have h := hsuf.length_le
          simp only [List.take_zero, List.length_take, List.length_nil] at h
          omega⟩
    obtain ⟨hmem, hpw⟩ := kmpSearchLoop_spec (by omega) hsize htab (Nat.zero_le _) hk0
    exact ⟨fun s => (hmem s).trans ⟨And.right, fun hm => ⟨by omega, hm⟩⟩, hpw⟩

/-- Unconditional soundness and completeness of `kmpMatches` (`[KnuthMorrisPratt1977]`,
Sections 1–2; `[CLRS2009]`, Section 32.4):
`s ∈ kmpMatches p t` iff `p` occurs in `t` at shift `s`. -/
theorem mem_kmpMatches_iff {α : Type*} [DecidableEq α] (p t : Array α) (s : ℕ) :
    s ∈ kmpMatches p t ↔ IsMatchAt p t s :=
  let ⟨hsize, htab⟩ := isPrefixTableFor_computePrefix p
  (kmpSearchWithPrefix_spec t hsize htab).1 s

/-- `kmpMatches p t` lists all match shifts in strictly increasing order. -/
theorem pairwise_lt_kmpMatches {α : Type*} [DecidableEq α] (p t : Array α) :
    (kmpMatches p t).Pairwise (· < ·) :=
  let ⟨hsize, htab⟩ := isPrefixTableFor_computePrefix p
  (kmpSearchWithPrefix_spec t hsize htab).2

/-- `kmpMatches p t` contains no duplicate shifts. -/
theorem nodup_kmpMatches {α : Type*} [DecidableEq α] (p t : Array α) :
    (kmpMatches p t).Nodup :=
  (pairwise_lt_kmpMatches p t).imp (fun h => Nat.ne_of_lt h)

/-- Soundness and completeness of `kmpMatchesList` on `List α`. -/
theorem mem_kmpMatchesList_iff {α : Type*} [DecidableEq α] (p t : List α) (s : ℕ) :
    s ∈ kmpMatchesList p t ↔ s ≤ t.length ∧ p <+: t.drop s := by
  rw [kmpMatchesList, mem_kmpMatches_iff, isMatchAt_iff_toList]
  simp only [List.size_toArray]
  refine ⟨fun ⟨hs, hpref⟩ => ⟨by omega, hpref⟩, fun ⟨hs, hpref⟩ => ⟨?_, hpref⟩⟩
  have hlen := hpref.length_le
  rw [List.length_drop] at hlen
  omega

theorem pairwise_lt_kmpMatchesList {α : Type*} [DecidableEq α] (p t : List α) :
    (kmpMatchesList p t).Pairwise (· < ·) :=
  pairwise_lt_kmpMatches p.toArray t.toArray

theorem nodup_kmpMatchesList {α : Type*} [DecidableEq α] (p t : List α) :
    (kmpMatchesList p t).Nodup :=
  nodup_kmpMatches p.toArray t.toArray

/-- Explicit filter characterization of `kmpMatchesList`, useful for kernel `decide` evaluation in
downstream `module` clients without unfolding the KMP search loop. -/
theorem kmpMatchesList_eq_filter_range {α : Type*} [DecidableEq α] (p t : List α) :
    kmpMatchesList p t = (List.range (t.length + 1)).filter fun s => decide (p <+: t.drop s) :=
  (pairwise_lt_kmpMatchesList p t).eq_of_mem_iff (List.pairwise_lt_range.filter _) fun s => by
    rw [mem_kmpMatchesList_iff, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun ⟨hle, hp⟩ => ⟨Nat.lt_succ_of_le hle, hp⟩,
      fun ⟨hlt, hp⟩ => ⟨Nat.le_of_lt_succ hlt, hp⟩⟩

end Cslib.Algorithms.Lean.KMP
