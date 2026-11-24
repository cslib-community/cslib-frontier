/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.List.Basic

/-!
# Concatenations of self-delimiting code words

A code `c : α → List β` is *self-delimiting* when a code word followed by anything determines the
word and what follows it: `c a ++ r = c a' ++ r'` implies `a = a'` and `r = r'`. Code words that
end in a letter that occurs nowhere else, and code words of one length for an injective code, are
of this kind. A concatenation of a known number of such code words can be read back one word
after the other (`List.flatMap_inj_of_length_eq`). The number has to be known because a code
word may be empty.

## Main results

* `List.flatMap_inj_of_length_eq`: two words of the same length with the same concatenation of
  self-delimiting code words are equal.
-/

public section

/-- Two words of the same length are equal if the concatenations of the code words of their
letters are equal, for a code in which a code word followed by anything determines the letter and
what follows. -/
theorem List.flatMap_inj_of_length_eq {α β : Type*} {c : α → List β}
    (hc : ∀ a a' r r', c a ++ r = c a' ++ r' → a = a' ∧ r = r') {l l' : List α}
    (hlen : l.length = l'.length) (h : l.flatMap c = l'.flatMap c) : l = l' := by
  induction l generalizing l' with
  | nil => exact (List.length_eq_zero_iff.1 hlen.symm).symm
  | cons a l ih =>
    obtain _ | ⟨a', l'⟩ := l'
    · simp at hlen
    · obtain ⟨rfl, h'⟩ := hc a a' _ _ (by simpa using h)
      rw [ih (by simpa using hlen) h']
