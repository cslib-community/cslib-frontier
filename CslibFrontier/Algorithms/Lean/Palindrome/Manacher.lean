/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Palindrome.Basic

/-!
# Manacher's Algorithm: Maximal Palindromic Radii at All Centers

This module implements Manacher's algorithm (`[Manacher1975]`; all-centers formulation as in
`[ApostolicoBreslauerGalil1995]`, Section 1) as a pure function over arrays `w : Array α` with
`[DecidableEq α]`: `manacher w` computes `radius w.toList c` for each of the `2 * w.size + 1`
centers `c`, and `longestPalindromeSpan w` extracts the half-open index interval `[start, stop)`
of `longestPalindrome w.toList`.

The algorithm scans the centers left to right, maintaining the center `C` whose maximal palindrome
reaches furthest right, ending at `R`. At a new center `c`, the mirror lemma `min_radius_mirror`
says that the radius about `c` agrees with the already computed radius `m` about `2 * C - c` up to
`b = R - (c + 1) / 2`. If `m < b`, the radius about `c` is `m` immediately; otherwise `extend`
grows the palindrome of radius `b` about `c` outward letter by letter.

Linear `O(|w|)` machine-level running time for both all-centers radii and the longest palindromic
factor on word arrays is proved in `CslibFrontier.Algorithms.WordRAM.Manacher`.
For distinct palindromic words, `List.card_palindromicFactors_le` counts the empty factor as
well. The palindromic tree uses this result in `Eertree.vertexCount_le` to bound its number of
vertices, including both roots.

## Source Conventions

* **Centers:** the centers and radii are those of `CslibFrontier.Algorithms.Lean.Palindrome.Basic`
  (`[ApostolicoBreslauerGalil1995]`, Section 1, translated to `0`-indexed centers
  `c = 0, …, 2 * n`), with letters only: no sentinel symbols are interleaved, and the extension
  phase stops at the ends of `w`.
* **Off-line formulation:** `manacher` reads the whole array and returns all radii. Manacher's
  original algorithm is *on-line*, reporting the palindromic prefixes of the input read so far;
  that formulation is not modeled here. The palindromic prefixes are read off the radii by
  `palindrome_take_iff`.

## Main definitions

* `Cslib.Algorithms.Lean.Palindrome.extend`: one outward extension phase from `[l, r)`.
* `Cslib.Algorithms.Lean.Palindrome.manacher`: Manacher's algorithm returning the array of all
  `2 * w.size + 1` maximal palindromic radii.
* `Cslib.Algorithms.Lean.Palindrome.Span`, `longestPalindromeSpan`: the half-open position interval
  `[start, stop)` of `longestPalindrome w.toList`.

## Main results

* `Cslib.Algorithms.Lean.Palindrome.add_extend`: extending from any palindromic radius
  `k ≤ radius w.toList c` reaches `radius w.toList c`.
* `Cslib.Algorithms.Lean.Palindrome.manacher_eq`: `manacher w` is the array `radius w.toList c`
  for `c < 2 * w.size + 1`.
* `Cslib.Algorithms.Lean.Palindrome.extract_longestPalindromeSpan`: extracting
  `longestPalindromeSpan w` from `w.toList` yields `longestPalindrome w.toList`.

## References

* [G. Manacher, *A New Linear-Time "On-Line" Algorithm for Finding the Smallest Initial
  Palindrome of a String*][Manacher1975]
* [A. Apostolico, D. Breslauer, and Z. Galil, *Parallel detection of all palindromes in a
  string*][ApostolicoBreslauerGalil1995]
-/

public section

namespace Cslib.Algorithms.Lean.Palindrome

variable {α : Type*} [DecidableEq α]

/-! ## The extension phase -/

/-- One extension phase: starting from the factor `[l, r)`, compare `w[l - 1]` with `w[r]` and grow
the factor while they agree, stopping at the ends of `w`. Returns the number of successful
extensions. -/
@[expose] def extend (w : Array α) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | l + 1, r =>
    if h : r < w.size ∧ l < w.size then
      if w[l]'h.2 = w[r]'h.1 then extend w l (r + 1) + 1 else 0
    else 0

/-- An extension phase makes at most `l` steps before reaching the start of `w`. -/
theorem extend_le (w : Array α) (l r : ℕ) : extend w l r ≤ l := by
  induction l generalizing r with
  | zero => simp only [extend, le_refl]
  | succ l ih =>
    simp only [extend]
    split_ifs with h hEq
    · have := ih (r + 1); omega
    · omega
    · omega

/-- An extension phase never moves the right end past the end of `w`. -/
theorem add_extend_le (w : Array α) (l : ℕ) {r : ℕ} (hr : r ≤ w.size) :
    r + extend w l r ≤ w.size := by
  induction l generalizing r with
  | zero => simp only [extend, Nat.add_zero]; exact hr
  | succ l ih =>
    simp only [extend]
    split_ifs with h hEq
    · have := ih (r := r + 1) (by omega); omega
    · omega
    · omega

/-- From any palindromic radius `k ≤ radius w.toList c`, the extension phase reaches the maximal
radius about `c`. -/
theorem add_extend {w : Array α} {c k : ℕ} (hk : k ≤ radius w.toList c) :
    k + extend w (c / 2 - k) ((c + 1) / 2 + k) = radius w.toList c := by
  have hhalf := radius_le_half w.toList c
  generalize hl : c / 2 - k = l
  induction l generalizing k with
  | zero =>
    simp only [extend]
    omega
  | succ l ih =>
    simp only [extend]
    split_ifs with h hEq
    · have hc : c ≤ 2 * w.toList.length := by simp only [Array.length_toList]; omega
      have hpr : IsPalRadius w.toList c (k + 1) := by
        rw [isPalRadius_succ_iff ((isPalRadius_iff_le_radius hc).mpr hk) (by omega)
          (by simp only [Array.length_toList]; omega)]
        rw [show c / 2 - k - 1 = l by omega, Array.getElem?_toList, Array.getElem?_toList,
          Array.getElem?_eq_getElem h.2, Array.getElem?_eq_getElem h.1, hEq]
      have hk1 := (isPalRadius_iff_le_radius hc).mp hpr
      have := ih hk1 (by omega)
      rw [show (c + 1) / 2 + (k + 1) = (c + 1) / 2 + k + 1 by omega] at this
      omega
    · by_contra hne
      have hpr := isPalRadius_succ_of_lt_radius (w := w.toList) (c := c) (k := k) (by omega)
      have hlen := hpr.2.1
      rw [isPalRadius_succ_iff ((isPalRadius_iff_le_radius (by omega)).mpr hk)
          (by omega) (by omega),
        show c / 2 - k - 1 = l by omega, Array.getElem?_toList, Array.getElem?_toList,
        Array.getElem?_eq_getElem h.2, Array.getElem?_eq_getElem h.1] at hpr
      exact hEq (Option.some_inj.mp hpr)
    · by_contra hne
      have h1 := (isPalRadius_succ_of_lt_radius (w := w.toList) (c := c) (k := k) (by omega)).2.1
      simp only [Array.length_toList] at h1
      omega

/-! ## The main loop -/

/-- The main loop of Manacher's algorithm. `rad` holds the radii of the centers `< c`, and `R` is
the right end of the maximal palindrome about `C`, the one reaching furthest right so far. -/
private def loop (w : Array α) : ℕ → ℕ → ℕ → ℕ → Array ℕ → Array ℕ
  | 0, _, _, _, rad => rad
  | fuel + 1, c, C, R, rad =>
    let m := rad.getD (2 * C - c) 0
    let b := R - (c + 1) / 2
    if m < b then
      loop w fuel (c + 1) C R (rad.push m)
    else
      let e := extend w (c / 2 - b) ((c + 1) / 2 + b)
      loop w fuel (c + 1) c ((c + 1) / 2 + b + e) (rad.push (b + e))

/-- **Manacher's algorithm**: the maximal palindromic radius about each of the `2 * w.size + 1`
centers of `w`. -/
def manacher (w : Array α) : Array ℕ :=
  loop w (2 * w.size) 1 0 0 #[0]

private theorem loop_spec (w : Array α) (fuel c C R : ℕ) (rad : Array ℕ)
    (hc : c + fuel = 2 * w.size + 1) (hsize : rad.size = c)
    (hrad : ∀ i (hi : i < rad.size), rad[i] = radius w.toList i) (hCc : C < c)
    (hR : R = (C + 1) / 2 + radius w.toList C) :
    loop w fuel c C R rad = Array.ofFn (n := 2 * w.size + 1) (radius w.toList ·) := by
  induction fuel generalizing c C R rad with
  | zero =>
    simp only [loop]
    apply Array.ext (by simp only [Array.size_ofFn]; omega)
    intro i h1 h2
    rw [hrad i h1, Array.getElem_ofFn]
  | succ fuel ih =>
    have hRn : R ≤ w.toList.length := by
      rw [hR]; exact add_radius_le_length _ (by simp only [Array.length_toList]; omega)
    have hmirror := min_radius_mirror (w := w.toList) (c := c) (by omega) hR hRn
    have hm : rad.getD (2 * C - c) 0 = radius w.toList (2 * C - c) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
        hrad]
    have hpush {v : ℕ} (hv : v = radius w.toList c) :
        ∀ i (hi : i < (rad.push v).size), (rad.push v)[i] = radius w.toList i := by
      intro i hi
      rw [Array.getElem_push]
      split_ifs with hi'
      · exact hrad i hi'
      · simp only [Array.size_push] at hi
        rw [show i = c by omega, hv]
    simp only [loop]
    split_ifs with hlt
    · rw [hm] at hlt ⊢
      exact ih (c + 1) C R _ (by omega) (by simp only [Array.size_push]; omega)
        (hpush (by omega)) (by omega) hR
    · rw [hm] at hlt
      have hext := add_extend (w := w) (c := c) (by omega : R - (c + 1) / 2 ≤ radius w.toList c)
      exact ih (c + 1) c _ _ (by omega) (by simp only [Array.size_push]; omega)
        (hpush hext) (by omega) (by omega)

/-- **Correctness of Manacher's algorithm**: it returns the maximal palindromic radii about all
`2 * w.size + 1` centers of `w`. -/
theorem manacher_eq (w : Array α) :
    manacher w = Array.ofFn (n := 2 * w.size + 1) (radius w.toList ·) := by
  have h0 : radius w.toList 0 = 0 := Nat.eq_zero_of_le_zero (radius_le_half w.toList 0)
  refine loop_spec w _ 1 0 0 #[0] (by omega) rfl (fun i hi => ?_) Nat.zero_lt_one (by omega)
  have hi0 : i = 0 := by simp only [List.size_toArray, List.length_singleton] at hi; omega
  subst hi0
  simpa only [List.getElem_toArray, List.getElem_singleton] using h0.symm

theorem size_manacher (w : Array α) : (manacher w).size = 2 * w.size + 1 := by
  rw [manacher_eq, Array.size_ofFn]

theorem getElem_manacher (w : Array α) {c : ℕ} (hc : c < (manacher w).size) :
    (manacher w)[c] = radius w.toList c := by
  simp only [manacher_eq, Array.getElem_ofFn]

theorem getD_manacher (w : Array α) (c : ℕ) : (manacher w).getD c 0 = radius w.toList c := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hc : c < (manacher w).size
  · rw [Array.getElem?_eq_getElem hc, Option.getD_some, getElem_manacher]
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none,
      radius_eq_zero_of_length_lt
        (by rw [size_manacher] at hc; simp only [Array.length_toList]; omega)]

/-! ## Longest palindromic factor -/

/-- Half-open position interval `[start, stop)` of a factor in a word. -/
structure Span where
  /-- Inclusive start position. -/
  start : ℕ
  /-- Exclusive end position. -/
  stop : ℕ
  deriving DecidableEq, Repr

/-- The interval `[start, stop)` of `longestPalindrome w.toList`, read off `manacher w`. -/
def longestPalindromeSpan (w : Array α) : Span :=
  let rad := manacher w
  let c := ((List.range rad.size).argmax fun c => 2 * rad.getD c 0 + c % 2).getD 0
  let k := rad.getD c 0
  ⟨c / 2 - k, (c + 1) / 2 + k⟩

theorem start_longestPalindromeSpan (w : Array α) :
    (longestPalindromeSpan w).start =
      bestCenter w.toList / 2 - radius w.toList (bestCenter w.toList) := by
  simp only [longestPalindromeSpan, size_manacher, getD_manacher, Array.length_toList, bestCenter]

theorem stop_longestPalindromeSpan (w : Array α) :
    (longestPalindromeSpan w).stop =
      (bestCenter w.toList + 1) / 2 + radius w.toList (bestCenter w.toList) := by
  simp only [longestPalindromeSpan, size_manacher, getD_manacher, Array.length_toList, bestCenter]

theorem longestPalindromeSpan_le (w : Array α) :
    (longestPalindromeSpan w).start ≤ (longestPalindromeSpan w).stop ∧
      (longestPalindromeSpan w).stop ≤ w.size := by
  rw [start_longestPalindromeSpan, stop_longestPalindromeSpan]
  have hc := bestCenter_le w.toList
  have h1 := radius_le_half w.toList (bestCenter w.toList)
  have h2 := add_radius_le_length w.toList hc
  simp only [Array.length_toList] at h2
  omega

/-- `longestPalindromeSpan w` gives the endpoints of `longestPalindrome w.toList`, a longest
palindromic factor of `w` (`length_le_longestPalindrome`). -/
theorem extract_longestPalindromeSpan (w : Array α) :
    w.toList.extract (longestPalindromeSpan w).start (longestPalindromeSpan w).stop =
      longestPalindrome w.toList := by
  rw [start_longestPalindromeSpan, stop_longestPalindromeSpan, longestPalindrome, maxPalindrome]

end Cslib.Algorithms.Lean.Palindrome
