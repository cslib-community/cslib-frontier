/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Palindrome.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Palindrome

/-!
# Palindromic factors of lists

Index characterizations of Mathlib's `List.Palindrome`, for whole lists
(`List.Palindrome.iff_getElem?`) and for factors `l.extract a b` (`List.palindrome_extract_iff`),
and the three facts about palindromic factors that center-based palindrome algorithms use:
shrinking a palindromic factor symmetrically keeps it a palindrome
(`List.Palindrome.extract_of_le`), a palindromic factor extends by one letter on each side iff those
two letters agree (`List.palindrome_extract_sub_one_add_one_iff`), and palindromic factors inside a
palindromic factor reflect to palindromic factors (`List.Palindrome.extract_reflect`).

`List.palindromicFactors` collects distinct palindromic words occurring as contiguous factors,
including the empty word. Prepending a letter introduces at most one new palindrome.

## Main results

* `List.Palindrome.iff_getElem?`: `l` is a palindrome iff `l[i]? = l[l.length - 1 - i]?` for
  every `i < l.length`.
* `List.palindrome_extract_iff`: for `b ≤ l.length`, the factor `l.extract a b` is a palindrome iff
  `l[i]? = l[a + b - 1 - i]?` for every `a ≤ i < b`.
* `List.Palindrome.extract_of_le`: shrinking a palindromic factor symmetrically about its center
  keeps it a palindrome.
* `List.palindrome_extract_sub_one_add_one_iff`: `l.extract (a - 1) (b + 1)` is a palindrome iff
  `l.extract a b` is and `l[a - 1]? = l[b]?`.
* `List.Palindrome.extract_reflect`: if `l.extract L R` and `l.extract a b` are palindromes with
  `L ≤ a ≤ b ≤ R`, then so is the mirror image `l.extract (L + R - b) (L + R - a)`.
* `List.card_palindromicFactors_le`: a word of length `n` has at most `n + 1` distinct palindromic
  factors [Glen, Justin, Widmer and Zamboni][GlenJustinWidmerZamboni2009], Proposition 2.1.
-/

public section

namespace List

variable {α : Type*}

/-- Index characterization of palindromes. -/
theorem Palindrome.iff_getElem? {l : List α} :
    Palindrome l ↔ ∀ i < l.length, l[i]? = l[l.length - 1 - i]? := by
  rw [Palindrome.iff_reverse_eq]
  refine ⟨fun h i hi => by rw [← getElem?_reverse hi, h], fun h => ext_getElem? fun i => ?_⟩
  by_cases hi : i < l.length
  · rw [getElem?_reverse hi, h i hi]
  · rw [getElem?_eq_none (by simpa only [length_reverse] using Nat.le_of_not_lt hi),
      getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- A factor `l.extract a b` with `b ≤ l.length` is a palindrome iff the letters at positions
symmetric about the midpoint of `[a, b)` agree. -/
theorem palindrome_extract_iff {l : List α} {a b : ℕ} (hb : b ≤ l.length) :
    Palindrome (l.extract a b) ↔ ∀ i, a ≤ i → i < b → l[i]? = l[a + b - 1 - i]? := by
  have hlen : (l.extract a b).length = b - a := by
    simp only [extract_eq_take_drop, length_take, length_drop]; omega
  have hget (j : ℕ) (hj : j < b - a) : (l.extract a b)[j]? = l[a + j]? := by
    simp only [extract_eq_take_drop, getElem?_take, getElem?_drop, hj, ↓reduceIte]
  rw [Palindrome.iff_getElem?, hlen]
  refine ⟨fun h i hai hib => ?_, fun h j hj => ?_⟩
  · have := h (i - a) (by omega)
    rw [hget _ (by omega), hget _ (by omega)] at this
    exact (congrArg (l[·]?) (by omega)).trans (this.trans (congrArg (l[·]?) (by omega)))
  · rw [hget _ hj, hget _ (by omega), h (a + j) (by omega) (by omega)]
    exact congrArg (l[·]?) (by omega)

/-- Shrinking a palindromic factor symmetrically about its center keeps it a palindrome. -/
theorem Palindrome.extract_of_le {l : List α} {a b a' b' : ℕ}
    (h : (l.extract a b).Palindrome) (hb : b ≤ l.length) (ha : a ≤ a') (hb' : b' ≤ b)
    (hsum : a' + b' = a + b) : (l.extract a' b').Palindrome := by
  rw [palindrome_extract_iff hb] at h
  exact (palindrome_extract_iff (by omega)).mpr fun i hi hi' => hsum ▸ h i (by omega) (by omega)

/-- A palindromic factor extends by one letter on each side iff those two letters agree. -/
theorem palindrome_extract_sub_one_add_one_iff {l : List α} {a b : ℕ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < l.length) :
    (l.extract (a - 1) (b + 1)).Palindrome ↔ (l.extract a b).Palindrome ∧ l[a - 1]? = l[b]? := by
  rw [palindrome_extract_iff (by omega), palindrome_extract_iff (by omega)]
  refine ⟨fun h => ⟨fun i hi hi' =>
      (h i (by omega) (by omega)).trans (congrArg (l[·]?) (by omega)),
    (h (a - 1) le_rfl (by omega)).trans (congrArg (l[·]?) (by omega))⟩,
    fun ⟨h, hab'⟩ i hi hi' => ?_⟩
  rcases eq_or_ne i (a - 1) with rfl | hlo
  · exact hab'.trans (congrArg (l[·]?) (by omega))
  rcases eq_or_ne i b with rfl | hhi
  · exact hab'.symm.trans (congrArg (l[·]?) (by omega))
  exact (h i (by omega) (by omega)).trans (congrArg (l[·]?) (by omega))

/-- Palindromes reflect inside a palindrome: if `l.extract L R` is a palindrome and
`L ≤ a ≤ b ≤ R`, then the factor `l.extract a b` is a palindrome iff its mirror image
`l.extract (L + R - b) (L + R - a)` is; this is the forward direction. -/
theorem Palindrome.extract_reflect {l : List α} {L R a b : ℕ}
    (hbig : (l.extract L R).Palindrome) (h : (l.extract a b).Palindrome) (hR : R ≤ l.length)
    (hL : L ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
    (l.extract (L + R - b) (L + R - a)).Palindrome := by
  rw [palindrome_extract_iff hR] at hbig
  rw [palindrome_extract_iff (by omega)] at h
  rw [palindrome_extract_iff (by omega)]
  intro i hi hi'
  -- Reflect `i` into `[a, b)` across the center of `[L, R)`, use `h` there, and reflect back.
  rw [hbig i (by omega) (by omega), h (L + R - 1 - i) (by omega) (by omega),
    hbig (a + b - 1 - (L + R - 1 - i)) (by omega) (by omega)]
  exact congrArg (l[·]?) (by omega)

/-! ## Counting distinct palindromic factors -/

variable [DecidableEq α]

/-- The distinct palindromic factors of a finite word, including the empty word. -/
@[expose] def palindromicFactors (w : List α) : Finset (List α) :=
  (w.tails.flatMap inits).toFinset.filter Palindrome

@[simp] theorem mem_palindromicFactors {p w : List α} :
    p ∈ w.palindromicFactors ↔ p <:+: w ∧ p.Palindrome := by
  simp [palindromicFactors, mem_tails, mem_inits, infix_iff_prefix_suffix, and_comm]

/-- Prepending a letter introduces at most one distinct palindrome. Any new factor is a prefix.
If two palindromic prefixes have different lengths, reflection in the longer one places the
shorter one in the old word. -/
theorem card_sdiff_palindromicFactors_cons_le_one (a : α) (w : List α) :
    ((a :: w).palindromicFactors \ w.palindromicFactors).card ≤ 1 := by
  have new_prefix {p : List α} (h : p ∈ (a :: w).palindromicFactors \ w.palindromicFactors) :
      p <+: a :: w ∧ p.Palindrome ∧ ¬ p <:+: w := by
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hi, hpal⟩ := mem_palindromicFactors.mp hp
    have hnew : ¬ p <:+: w := fun h => hn (mem_palindromicFactors.mpr ⟨h, hpal⟩)
    exact ⟨(infix_cons_iff.mp hi).resolve_right hnew, hpal, hnew⟩
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpp, hp, hn⟩ := new_prefix hp
  obtain ⟨hqp, hq, hm⟩ := new_prefix hq
  have eq_of_prefix {u v : List α} (hu : u.Palindrome) (hv : v.Palindrome)
      (hnew : ¬ u <:+: w) (hvp : v <+: a :: w) (h : u <+: v) : u = v := by
    have hs : u <:+ v := by simpa only [hu.reverse_eq, hv.reverse_eq] using reverse_suffix.mpr h
    rcases prefix_cons_iff.mp hvp with rfl | ⟨t, rfl, ht⟩
    · exact prefix_nil.mp h
    · exact (suffix_cons_iff.mp hs).resolve_right fun h => hnew (h.isInfix.trans ht.isInfix)
  exact (prefix_or_prefix_of_prefix hpp hqp).elim (eq_of_prefix hp hq hn hqp)
    (fun h => (eq_of_prefix hq hp hm hpp h).symm)

/-- A word of length `n` has at most `n + 1` distinct palindromic factors, including the empty
word. This is the Droubay–Justin–Pirillo bound as restated in [Glen, Justin, Widmer and
Zamboni][GlenJustinWidmerZamboni2009], Proposition 2.1. The alphabet need not be finite. -/
theorem card_palindromicFactors_le (w : List α) :
    w.palindromicFactors.card ≤ w.length + 1 := by
  induction w with
  | nil =>
    simpa [palindromicFactors, tails, inits] using
      Finset.card_filter_le ({[]} : Finset (List α)) Palindrome
  | cons a w ih =>
    have h := Finset.card_le_card_sdiff_add_card (s := (a :: w).palindromicFactors)
      (t := w.palindromicFactors)
    have := card_sdiff_palindromicFactors_cons_le_one a w
    simp only [length_cons]
    omega

end List
