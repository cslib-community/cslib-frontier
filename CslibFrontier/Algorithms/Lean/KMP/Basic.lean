/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Word Borders, Periods, and the KMP Prefix Function

This module develops the combinatorics of word borders, periods, and the Knuth–Morris–Pratt
prefix (failure) function over lists with decidable equality (`[KnuthMorrisPratt1977]`;
`[CLRS2009]`, Section 32.4).

A length `k < w.length` is a *proper border length* of a word `w` (`IsProperBorderLen w k`) when
the prefix `w.take k` is also a suffix of `w`. Equivalently, `d = w.length - k` is a positive
*period* of `w` (`IsPeriod w d`), meaning `w[i] = w[i + d]` whenever `i + d < w.length`.

To treat failure-table construction and text scanning uniformly, we define
`maxPrefixSuffixUpTo p t B` as the largest length `k ≤ B` with `k ≤ p.length` such that `p.take k`
is a suffix of `t`. Specializing `t = w` and `B = w.length - 1` yields the maximum proper border
length `maxBorderLen w` and the KMP prefix function `borderLen p q = maxBorderLen (p.take q)`
(corresponding to $\pi[q]$ in `[CLRS2009]`, Section 32.4 for $1 \le q \le |p|$).

## Main definitions

* `Cslib.Algorithms.Lean.KMP.IsProperBorderLen`: `k < w.length` and `w.take k <:+ w`.
* `Cslib.Algorithms.Lean.KMP.IsPeriod`: period `d` of `w` (`w[i] = w[i + d]` for `i + d < |w|`).
* `Cslib.Algorithms.Lean.KMP.maxPrefixSuffixUpTo`: largest `k ≤ B` with `k ≤ |p|` and
  `p.take k <:+ t`.
* `Cslib.Algorithms.Lean.KMP.maxBorderLen`: maximum proper border length of `w` (`0` on `[]`).
* `Cslib.Algorithms.Lean.KMP.minPeriod`: minimum positive period `w.length - maxBorderLen w`.
* `Cslib.Algorithms.Lean.KMP.borderLen`: KMP prefix value `maxBorderLen (p.take q)`.
* `Cslib.Algorithms.Lean.KMP.borderChain`: strictly decreasing list of all proper border lengths
  of `p.take q` obtained by iterating `k ↦ borderLen p k`.
* `Cslib.Algorithms.Lean.KMP.nextLen`: pure KMP automaton transition updating a matched prefix
  length `k < p.length` upon reading character `c`.

## Main results

* `Cslib.Algorithms.Lean.KMP.isProperBorderLen_iff_isPeriod`: `IsProperBorderLen w k` holds iff
  `k < w.length` and `IsPeriod w (w.length - k)`.
* `Cslib.Algorithms.Lean.KMP.IsProperBorderLen.trans` and `IsProperBorderLen.to_take`: proper
  borders of `w` strictly shorter than a proper border `k` are exactly the proper borders of
  `w.take k`.
* `Cslib.Algorithms.Lean.KMP.mem_borderChain_iff` and `pairwise_gt_borderChain`: iterating
  `k ↦ borderLen p k` enumerates all proper border lengths of `p.take q` in strictly decreasing
  order (`[CLRS2009]`, Lemma 32.5).
* `Cslib.Algorithms.Lean.KMP.maxPrefixSuffixUpTo_append_singleton`: extending `t` by one character
  `c` updates `maxPrefixSuffixUpTo p t B` (`B < p.length`) via `nextLen p · c`, specializing both
  to `borderLen_succ` (`[CLRS2009]`, Lemma 32.6 and Corollary 32.7) and to the KMP text-scanning
  step.

## References

* [D. E. Knuth, J. H. Morris, Jr., and V. R. Pratt, *Fast Pattern Matching in
  Strings*][KnuthMorrisPratt1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*,
  3rd ed., Section 32.4][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.KMP

/-! ## One-character suffix extension -/

/-- Appending a single element preserves suffixes iff the base lists are suffixes and the
appended elements agree. -/
private theorem append_singleton_isSuffix_iff {α : Type*} {u t : List α} {a c : α} :
    u ++ [a] <:+ t ++ [c] ↔ u <:+ t ∧ a = c := by
  constructor
  · rintro ⟨s, hs⟩
    rw [← List.append_assoc] at hs
    have hlen : (s ++ u).length = t.length := by grind [List.length_append, List.length_singleton]
    obtain ⟨hsu, hac⟩ := List.append_inj hs hlen
    exact ⟨⟨s, hsu⟩, List.singleton_inj.mp hac⟩
  · rintro ⟨⟨s, rfl⟩, rfl⟩
    exact ⟨s, (List.append_assoc s u [a]).symm⟩

/-- Extending a prefix `p.take j` (`j < p.length`) to `p.take (j + 1)` matches a suffix of
`t ++ [c]` iff `p.take j <:+ t` and `p[j] = c`. -/
private theorem take_succ_isSuffix_append_iff {α : Type*} {p t : List α} {c : α} {j : ℕ}
    (hj : j < p.length) :
    p.take (j + 1) <:+ t ++ [c] ↔ p.take j <:+ t ∧ p[j] = c := by
  rw [List.take_add_one, getElem?_pos p j hj, Option.toList_some, append_singleton_isSuffix_iff]

/-! ## Proper borders and periods -/

/-- `k` is a proper border length of `w` if `k < w.length` and the length-`k` prefix `w.take k`
is also a suffix of `w`. -/
@[expose] def IsProperBorderLen {α : Type*} (w : List α) (k : ℕ) : Prop :=
  k < w.length ∧ w.take k <:+ w

/-- `d` is a period of `w` if characters at distance `d` agree throughout `w`. -/
@[expose] def IsPeriod {α : Type*} (w : List α) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (h : i + d < w.length), w[i]'(by omega) = w[i + d]'h

theorem isProperBorderLen_zero {α : Type*} {w : List α} (hw : 0 < w.length) :
    IsProperBorderLen w 0 :=
  ⟨hw, List.nil_suffix⟩

theorem not_isProperBorderLen_nil {α : Type*} (k : ℕ) : ¬ IsProperBorderLen ([] : List α) k := by
  rintro ⟨hk, _⟩
  exact Nat.not_lt_zero k hk

theorem isProperBorderLen_iff_take_eq_drop {α : Type*} {w : List α} {k : ℕ} :
    IsProperBorderLen w k ↔ k < w.length ∧ w.take k = w.drop (w.length - k) := by
  constructor
  · rintro ⟨hk, s, hs⟩
    have hslen : s.length = w.length - k := by grind
    refine ⟨hk, ?_⟩
    simpa only [hs, hslen] using (List.drop_left (l₁ := s) (l₂ := w.take k)).symm
  · rintro ⟨hk, heq⟩
    exact ⟨hk, heq ▸ List.drop_suffix (w.length - k) w⟩

theorem isProperBorderLen_iff_exists_border {α : Type*} {w : List α} {k : ℕ} :
    IsProperBorderLen w k ↔
      ∃ b : List α, b.length = k ∧ b.length < w.length ∧ b <+: w ∧ b <:+ w := by
  constructor
  · rintro ⟨hk, hsuf⟩
    refine ⟨w.take k, ?_, ?_, List.take_prefix k w, hsuf⟩ <;>
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk), hk]
  · rintro ⟨b, rfl, hk, hpref, hsuf⟩
    have htake : b = w.take b.length := List.prefix_iff_eq_take.mp hpref
    exact ⟨hk, htake ▸ hsuf⟩

/-- Border-period duality: `k < w.length` is a proper border length of `w` iff `w.length - k` is
a period of `w`. -/
theorem isProperBorderLen_iff_isPeriod {α : Type*} {w : List α} {k : ℕ} :
    IsProperBorderLen w k ↔ k < w.length ∧ IsPeriod w (w.length - k) := by
  rw [isProperBorderLen_iff_take_eq_drop]
  refine and_congr_right fun hk => ⟨fun heq i hi => ?_, fun hper => ?_⟩
  · have h : (w.take k)[i]'(by simp only [List.length_take]; omega) =
        (w.drop (w.length - k))[i]'(by simp only [List.length_drop]; omega) := by simp only [heq]
    rw [List.getElem_take, List.getElem_drop] at h
    simpa only [Nat.add_comm] using h
  · refine List.ext_getElem (by simp only [List.length_take, List.length_drop]; omega)
      fun i h1 _ => ?_
    rw [List.getElem_take, List.getElem_drop]
    simpa only [Nat.add_comm] using hper i (by simp only [List.length_take] at h1; omega)

/-- A proper border of a proper border of `w` is itself a proper border of `w`. -/
theorem IsProperBorderLen.trans {α : Type*} {w : List α} {j k : ℕ}
    (hjk : IsProperBorderLen (w.take k) j) (hkw : IsProperBorderLen w k) :
    IsProperBorderLen w j := by
  rcases hkw with ⟨hk, hsufk⟩
  rcases hjk with ⟨hj, hsufj⟩
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hj
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hsufj
  exact ⟨Nat.lt_trans hj hk, hsufj.trans hsufk⟩

/-- Any proper border of `w` strictly shorter than a proper border `k` of `w` is a proper border
of `w.take k`. -/
theorem IsProperBorderLen.to_take {α : Type*} {w : List α} {j k : ℕ}
    (hjw : IsProperBorderLen w j) (hkw : IsProperBorderLen w k) (hlt : j < k) :
    IsProperBorderLen (w.take k) j := by
  rcases hjw with ⟨hj, hsufj⟩
  rcases hkw with ⟨hk, hsufk⟩
  refine ⟨by simp only [List.length_take]; omega, ?_⟩
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  exact List.suffix_of_suffix_length_le hsufj hsufk (by simp only [List.length_take]; omega)

/-! ## Maximum prefix-suffix lengths, maximum borders, and minimum periods -/

/-- Largest length `k ≤ B` with `k ≤ p.length` such that `p.take k <:+ t`. -/
@[expose] def maxPrefixSuffixUpTo {α : Type*} [DecidableEq α] (p t : List α) : ℕ → ℕ
  | 0 => 0
  | B + 1 =>
    if B + 1 ≤ p.length ∧ p.take (B + 1) <:+ t then B + 1
    else maxPrefixSuffixUpTo p t B

theorem maxPrefixSuffixUpTo_le_bound {α : Type*} [DecidableEq α] (p t : List α) (B : ℕ) :
    maxPrefixSuffixUpTo p t B ≤ B := by
  fun_induction maxPrefixSuffixUpTo p t B <;> omega

theorem maxPrefixSuffixUpTo_le_length {α : Type*} [DecidableEq α] (p t : List α) (B : ℕ) :
    maxPrefixSuffixUpTo p t B ≤ p.length := by
  fun_induction maxPrefixSuffixUpTo p t B <;> omega

theorem take_maxPrefixSuffixUpTo_isSuffix {α : Type*} [DecidableEq α] (p t : List α) (B : ℕ) :
    p.take (maxPrefixSuffixUpTo p t B) <:+ t := by
  fun_induction maxPrefixSuffixUpTo p t B <;> simp_all

theorem le_maxPrefixSuffixUpTo {α : Type*} [DecidableEq α] {p t : List α} {B k : ℕ}
    (hkB : k ≤ B) (hkp : k ≤ p.length) (hsuf : p.take k <:+ t) :
    k ≤ maxPrefixSuffixUpTo p t B := by
  fun_induction maxPrefixSuffixUpTo p t B with
  | case1 | case2 => exact hkB
  | case3 B h ih =>
    rcases Nat.eq_or_lt_of_le hkB with rfl | hlt
    · exact absurd ⟨hkp, hsuf⟩ h
    · exact ih (by omega)

theorem eq_maxPrefixSuffixUpTo_iff {α : Type*} [DecidableEq α] {p t : List α} {B m : ℕ} :
    m = maxPrefixSuffixUpTo p t B ↔
      m ≤ B ∧ m ≤ p.length ∧ p.take m <:+ t ∧
        ∀ k, m < k → k ≤ B → k ≤ p.length → ¬ (p.take k <:+ t) := by
  constructor
  · rintro rfl
    refine ⟨maxPrefixSuffixUpTo_le_bound p t B, maxPrefixSuffixUpTo_le_length p t B,
      take_maxPrefixSuffixUpTo_isSuffix p t B, fun k hlt hkB hkp hsuf => ?_⟩
    have hle := le_maxPrefixSuffixUpTo hkB hkp hsuf
    omega
  · rintro ⟨hmB, hmp, hmsuf, hmax⟩
    refine Nat.le_antisymm (le_maxPrefixSuffixUpTo hmB hmp hmsuf) (not_lt.mp fun hlt => ?_)
    exact hmax _ hlt (maxPrefixSuffixUpTo_le_bound p t B) (maxPrefixSuffixUpTo_le_length p t B)
      (take_maxPrefixSuffixUpTo_isSuffix p t B)

/-- Maximum proper border length of `w` (`0` when `w = []`). -/
@[expose] def maxBorderLen {α : Type*} [DecidableEq α] (w : List α) : ℕ :=
  maxPrefixSuffixUpTo w w (w.length - 1)

/-- Minimum positive period of a nonempty word `w` (`0` when `w = []`). -/
@[expose] def minPeriod {α : Type*} [DecidableEq α] (w : List α) : ℕ :=
  w.length - maxBorderLen w

/-- The KMP prefix function $\pi[q]$: maximum proper border length of the prefix `p.take q`. -/
@[expose] def borderLen {α : Type*} [DecidableEq α] (p : List α) (q : ℕ) : ℕ :=
  maxBorderLen (p.take q)

@[simp]
theorem maxBorderLen_nil {α : Type*} [DecidableEq α] : maxBorderLen ([] : List α) = 0 := rfl

@[simp]
theorem maxBorderLen_singleton {α : Type*} [DecidableEq α] (a : α) : maxBorderLen [a] = 0 := rfl

theorem maxBorderLen_le_pred {α : Type*} [DecidableEq α] (w : List α) :
    maxBorderLen w ≤ w.length - 1 :=
  maxPrefixSuffixUpTo_le_bound w w (w.length - 1)

theorem maxBorderLen_lt_length {α : Type*} [DecidableEq α] {w : List α} (hw : 0 < w.length) :
    maxBorderLen w < w.length := by
  have h := maxBorderLen_le_pred w
  omega

theorem isProperBorderLen_maxBorderLen {α : Type*} [DecidableEq α] {w : List α}
    (hw : 0 < w.length) : IsProperBorderLen w (maxBorderLen w) :=
  ⟨maxBorderLen_lt_length hw, take_maxPrefixSuffixUpTo_isSuffix w w (w.length - 1)⟩

theorem le_maxBorderLen_of_isProperBorderLen {α : Type*} [DecidableEq α] {w : List α} {k : ℕ}
    (h : IsProperBorderLen w k) : k ≤ maxBorderLen w :=
  le_maxPrefixSuffixUpTo (by have := h.1; omega) (Nat.le_of_lt h.1) h.2

theorem minPeriod_add_maxBorderLen {α : Type*} [DecidableEq α] (w : List α) :
    minPeriod w + maxBorderLen w = w.length := by
  have := maxBorderLen_le_pred w
  rw [minPeriod]; omega

theorem minPeriod_pos {α : Type*} [DecidableEq α] {w : List α} (hw : 0 < w.length) :
    0 < minPeriod w := by
  have := maxBorderLen_lt_length hw
  rw [minPeriod]; omega

theorem isPeriod_minPeriod {α : Type*} [DecidableEq α] {w : List α} (hw : 0 < w.length) :
    IsPeriod w (minPeriod w) :=
  (isProperBorderLen_iff_isPeriod.mp (isProperBorderLen_maxBorderLen hw)).2

theorem minPeriod_le_of_isPeriod {α : Type*} [DecidableEq α] {w : List α} {d : ℕ}
    (hd0 : 0 < d) (hper : IsPeriod w d) :
    minPeriod w ≤ d := by
  by_cases hdlen : d ≤ w.length
  · have hborder : IsProperBorderLen w (w.length - d) :=
      isProperBorderLen_iff_isPeriod.mpr ⟨by omega, (Nat.sub_sub_self hdlen).symm ▸ hper⟩
    have := le_maxBorderLen_of_isProperBorderLen hborder
    rw [minPeriod]; omega
  · have := maxBorderLen_le_pred w
    rw [minPeriod]; omega

@[simp]
theorem borderLen_zero {α : Type*} [DecidableEq α] (p : List α) : borderLen p 0 = 0 := rfl

@[simp]
theorem borderLen_one {α : Type*} [DecidableEq α] (p : List α) : borderLen p 1 = 0 := by
  cases p <;> rfl

theorem borderLen_lt {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hq : 0 < q) (hp : p ≠ []) : borderLen p q < q :=
  (maxBorderLen_lt_length (by grind)).trans_le (List.length_take_le q p)

theorem borderLen_eq_maxPrefixSuffixUpTo {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hqp : q ≤ p.length) :
    borderLen p q = maxPrefixSuffixUpTo p (p.take q) (q - 1) := by
  apply eq_maxPrefixSuffixUpTo_iff.mpr
  have hlen : (p.take q).length = q := List.length_take_of_le hqp
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp only [borderLen_zero, Nat.zero_le, List.take_zero, List.nil_suffix, true_and]
    omega
  · have hb : IsProperBorderLen (p.take q) (borderLen p q) :=
      isProperBorderLen_maxBorderLen (by rw [hlen]; exact hqpos)
    have hblt := hb.1
    have htake_eq : p.take (borderLen p q) = (p.take q).take (borderLen p q) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    refine ⟨by omega, by omega, htake_eq ▸ hb.2, fun k hlt hkB _ hsuf => not_le.mpr hlt ?_⟩
    exact le_maxBorderLen_of_isProperBorderLen
      ⟨by omega, by rwa [List.take_take, Nat.min_eq_left (by omega)]⟩

/-! ## Prefix-function iteration (`[CLRS2009]`, Lemma 32.5) -/

/-- Strictly decreasing list of all proper border lengths of `p.take q` (empty when `q = 0` or
`p = []`), computed by iterating `k ↦ borderLen p k` (`[CLRS2009]`, Lemma 32.5). -/
def borderChain {α : Type*} [DecidableEq α] (p : List α) (q : ℕ) : List ℕ :=
  if _h : q = 0 ∨ p = [] then []
  else
    let k := borderLen p q
    if k = 0 then [0]
    else k :: borderChain p k
termination_by q
decreasing_by
  have hq : 0 < q := by omega
  have hp : p ≠ [] := fun hp0 => _h (Or.inr hp0)
  exact borderLen_lt hq hp

/-- Prefix-function iteration theorem (`[CLRS2009]`, Lemma 32.5): for `1 ≤ q ≤ p.length`,
`borderChain p q` contains exactly the proper border lengths of `p.take q`. -/
theorem mem_borderChain_iff {α : Type*} [DecidableEq α] {p : List α} {q j : ℕ}
    (hq1 : 1 ≤ q) (hqp : q ≤ p.length) :
    j ∈ borderChain p q ↔ IsProperBorderLen (p.take q) j := by
  fun_induction borderChain p q with
  | case1 => grind
  | case2 q _ k hk0 =>
    have hlen : (p.take q).length = q := List.length_take_of_le hqp
    simp only [List.mem_singleton]
    constructor
    · rintro rfl
      exact isProperBorderLen_zero (by rw [hlen]; omega)
    · intro hj
      have hle : j ≤ k := le_maxBorderLen_of_isProperBorderLen hj
      omega
  | case3 q hcond k hk0 ih =>
    have hlen : (p.take q).length = q := List.length_take_of_le hqp
    have hb_proper : IsProperBorderLen (p.take q) k :=
      isProperBorderLen_maxBorderLen (by rw [hlen]; omega)
    have hklt : k < q := borderLen_lt (by omega) fun hp0 => hcond (Or.inr hp0)
    have hkp : k ≤ p.length := by omega
    have htake_k : (p.take q).take k = p.take k := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hklt)]
    simp only [List.mem_cons, ih (by omega) hkp]
    constructor
    · rintro (rfl | hj)
      · exact hb_proper
      · exact (htake_k.symm ▸ hj).trans hb_proper
    · intro hj
      have hle : j ≤ k := le_maxBorderLen_of_isProperBorderLen hj
      rcases Nat.eq_or_lt_of_le hle with rfl | hjlt
      · exact Or.inl rfl
      · exact Or.inr (htake_k ▸ hj.to_take hb_proper hjlt)

/-- `borderChain p q` lists proper border lengths in strictly decreasing order. -/
theorem pairwise_gt_borderChain {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hqp : q ≤ p.length) :
    (borderChain p q).Pairwise (· > ·) := by
  fun_induction borderChain p q with
  | case1 => exact List.Pairwise.nil
  | case2 => exact List.pairwise_singleton _ _
  | case3 q hcond k hk0 ih =>
    have hklt : k < q := borderLen_lt (by omega) fun hp0 => hcond (Or.inr hp0)
    have hkp : k ≤ p.length := by omega
    refine List.Pairwise.cons (fun j hj => ?_) (ih hkp)
    simpa only [List.length_take_of_le hkp] using ((mem_borderChain_iff (by omega) hkp).mp hj).1

/-! ## Pure KMP automaton transition and master step theorem -/

/-- Pure KMP transition: given a matched prefix length `k < p.length` (or `0` when `p = []`) and
input character `c`, falls back along `borderLen p` until matching `p[k] = c` or exhausting
borders. -/
@[expose] def nextLen {α : Type*} [DecidableEq α] (p : List α) (k : ℕ) (c : α) : ℕ :=
  if hk : k < p.length then
    if p[k]'hk = c then k + 1
    else if k = 0 then 0
    else nextLen p (borderLen p k) c
  else 0
termination_by k
decreasing_by
  have hp : p ≠ [] := by grind
  exact borderLen_lt (by omega) hp

theorem nextLen_le_succ {α : Type*} [DecidableEq α] (p : List α) (k : ℕ) (c : α) :
    nextLen p k c ≤ k + 1 := by
  fun_induction nextLen p k c with
  | case3 k hk _ hk0 ih =>
    have hlt : borderLen p k < k := borderLen_lt (by omega) (List.ne_nil_of_length_pos (by omega))
    omega
  | _ => omega

theorem nextLen_le_length {α : Type*} [DecidableEq α] (p : List α) (k : ℕ) (c : α) :
    nextLen p k c ≤ p.length := by
  fun_induction nextLen p k c <;> omega

/-- `maxPrefixSuffixUpTo p t B` depends only on which positive lengths `j + 1 ≤ p.length` are
admissible, that is, at most the bound and naming a prefix of `p` that is a suffix of the word. -/
private theorem maxPrefixSuffixUpTo_congr {α : Type*} [DecidableEq α] {p t t' : List α}
    {B B' : ℕ}
    (h : ∀ j, j + 1 ≤ p.length →
      (j + 1 ≤ B ∧ p.take (j + 1) <:+ t ↔ j + 1 ≤ B' ∧ p.take (j + 1) <:+ t')) :
    maxPrefixSuffixUpTo p t B = maxPrefixSuffixUpTo p t' B' := by
  have h' : ∀ k, k ≤ p.length → (k ≤ B ∧ p.take k <:+ t ↔ k ≤ B' ∧ p.take k <:+ t') := by
    rintro (_ | j) hk
    · simp only [Nat.zero_le, List.take_zero, List.nil_suffix, and_self]
    · exact h j hk
  apply eq_maxPrefixSuffixUpTo_iff.mpr
  have hm := (h' _ (maxPrefixSuffixUpTo_le_length p t B)).mp
    ⟨maxPrefixSuffixUpTo_le_bound p t B, take_maxPrefixSuffixUpTo_isSuffix p t B⟩
  refine ⟨hm.1, maxPrefixSuffixUpTo_le_length p t B, hm.2, fun k hlt hkB hkp hsuf => ?_⟩
  obtain ⟨hkB', hsuf'⟩ := (h' k hkp).mpr ⟨hkB, hsuf⟩
  have := le_maxPrefixSuffixUpTo hkB' hkp hsuf'
  omega

/-- For `B ≤ p.length`, prefixes of `p` of length `j ≤ B` that are suffixes of `t` are exactly
those of length `j ≤ k` that are suffixes of `p.take k`, where `k = maxPrefixSuffixUpTo p t B`. -/
private theorem le_and_take_isSuffix_iff {α : Type*} [DecidableEq α] {p t : List α} {B j : ℕ}
    (hB : B ≤ p.length) :
    j ≤ B ∧ p.take j <:+ t ↔
      j ≤ maxPrefixSuffixUpTo p t B ∧ p.take j <:+ p.take (maxPrefixSuffixUpTo p t B) := by
  have hkB := maxPrefixSuffixUpTo_le_bound p t B
  have hksuf := take_maxPrefixSuffixUpTo_isSuffix p t B
  constructor
  · rintro ⟨hjB, hjsuf⟩
    have hjk := le_maxPrefixSuffixUpTo hjB (by omega) hjsuf
    exact ⟨hjk, List.suffix_of_suffix_length_le hjsuf hksuf
      (by simp only [List.length_take]; omega)⟩
  · rintro ⟨hjk, hjsuf⟩
    exact ⟨by omega, hjsuf.trans hksuf⟩

private theorem nextLen_eq_maxPrefixSuffixUpTo {α : Type*} [DecidableEq α]
    (p : List α) (m : ℕ) (c : α) (hm : m < p.length) :
    nextLen p m c = maxPrefixSuffixUpTo p (p.take m ++ [c]) (m + 1) := by
  fun_induction nextLen p m c with
  | case1 m hm hmatch =>
    apply eq_maxPrefixSuffixUpTo_iff.mpr
    refine ⟨Nat.le_refl _, by omega, ?_, fun s hslt hs_le _ _ => by omega⟩
    rw [take_succ_isSuffix_append_iff hm]
    exact ⟨List.suffix_rfl, hmatch⟩
  | case2 hm hmatch =>
    apply eq_maxPrefixSuffixUpTo_iff.mpr
    refine ⟨Nat.zero_le _, Nat.zero_le _, List.nil_suffix, fun s hslt hs_le _ hssuf => ?_⟩
    obtain rfl : s = 1 := by omega
    exact hmatch ((take_succ_isSuffix_append_iff hm).mp hssuf).2
  | case3 m hm hmatch hm0 ih =>
    have hblt : borderLen p m < m :=
      borderLen_lt (by omega) (List.ne_nil_of_length_pos (by omega))
    rw [ih (by omega), borderLen_eq_maxPrefixSuffixUpTo (Nat.le_of_lt hm)]
    refine maxPrefixSuffixUpTo_congr fun j hj => ?_
    rw [take_succ_isSuffix_append_iff (by omega), take_succ_isSuffix_append_iff (by omega),
      Nat.add_le_add_iff_right, Nat.add_le_add_iff_right, ← and_assoc, ← and_assoc,
      ← le_and_take_isSuffix_iff (by omega)]
    exact and_congr_left fun hjc => and_congr_left fun _ =>
      ⟨by omega, fun hjm => by
        have : j ≠ m := fun h => hmatch (h ▸ hjc)
        omega⟩
  | case4 m hm' => exact absurd hm hm'

/-- Master KMP step theorem: for any bound `B < p.length` and word `t`, extending `t` by one
character `c` updates `maxPrefixSuffixUpTo p t B` via `nextLen p · c`. -/
theorem maxPrefixSuffixUpTo_append_singleton {α : Type*} [DecidableEq α]
    (p t : List α) (c : α) {B : ℕ} (hB : B < p.length) :
    maxPrefixSuffixUpTo p (t ++ [c]) (B + 1) =
      nextLen p (maxPrefixSuffixUpTo p t B) c := by
  have hkp : maxPrefixSuffixUpTo p t B < p.length :=
    Nat.lt_of_le_of_lt (maxPrefixSuffixUpTo_le_bound p t B) hB
  rw [nextLen_eq_maxPrefixSuffixUpTo p _ c hkp]
  refine maxPrefixSuffixUpTo_congr fun j hj => ?_
  rw [take_succ_isSuffix_append_iff (by omega), take_succ_isSuffix_append_iff (by omega),
    Nat.add_le_add_iff_right, Nat.add_le_add_iff_right, ← and_assoc, ← and_assoc,
    le_and_take_isSuffix_iff (Nat.le_of_lt hB)]

/-- Recurrence for the KMP prefix function (`[CLRS2009]`, Lemma 32.6 and Corollary 32.7): for
`1 ≤ q < p.length`, `borderLen p (q + 1) = nextLen p (borderLen p q) p[q]`. -/
theorem borderLen_succ {α : Type*} [DecidableEq α] {p : List α} {q : ℕ}
    (hq1 : 1 ≤ q) (hqp : q < p.length) :
    borderLen p (q + 1) = nextLen p (borderLen p q) (p[q]'hqp) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [borderLen_eq_maxPrefixSuffixUpTo (Nat.succ_le_of_lt hqp),
    borderLen_eq_maxPrefixSuffixUpTo (Nat.le_of_lt hqp),
    List.take_add_one, getElem?_pos p (r + 1) hqp, Option.toList_some,
    Nat.succ_sub_one, Nat.add_sub_cancel,
    maxPrefixSuffixUpTo_append_singleton p (p.take (r + 1)) (p[r + 1]'hqp) (by omega)]

/-- Resetting a full pattern match `m = p.length` (`0 < p.length`) to `borderLen p p.length`
recovers the longest proper prefix of `p` that is a suffix of `t`. -/
theorem maxPrefixSuffixUpTo_pred_of_eq_length {α : Type*} [DecidableEq α]
    {p t : List α} (_hp : 0 < p.length)
    (hfull : maxPrefixSuffixUpTo p t p.length = p.length) :
    maxPrefixSuffixUpTo p t (p.length - 1) = borderLen p p.length := by
  have hpsuf : p <:+ t := by
    simpa only [hfull, List.take_length] using take_maxPrefixSuffixUpTo_isSuffix p t p.length
  rw [borderLen, maxBorderLen, List.take_length]
  exact maxPrefixSuffixUpTo_congr fun j _ => and_congr_right fun _ =>
    ⟨fun hsuf => List.suffix_of_suffix_length_le hsuf hpsuf (List.length_take_le' _ _),
      (·.trans hpsuf)⟩

/-- When `maxPrefixSuffixUpTo p t p.length < p.length`, restricting the bound to `p.length - 1`
leaves the value unchanged. -/
theorem maxPrefixSuffixUpTo_pred_of_lt_length {α : Type*} [DecidableEq α]
    {p t : List α} (hlt : maxPrefixSuffixUpTo p t p.length < p.length) :
    maxPrefixSuffixUpTo p t (p.length - 1) = maxPrefixSuffixUpTo p t p.length := by
  refine maxPrefixSuffixUpTo_congr fun j hj => ⟨fun ⟨_, hsuf⟩ => ⟨hj, hsuf⟩, fun ⟨_, hsuf⟩ => ?_⟩
  have := le_maxPrefixSuffixUpTo hj hj hsuf
  exact ⟨by omega, hsuf⟩

end Cslib.Algorithms.Lean.KMP
