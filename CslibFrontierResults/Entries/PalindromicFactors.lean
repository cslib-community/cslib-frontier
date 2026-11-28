/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Data.List.Palindrome

/-!
# Distinct palindromic factors of a finite word
-/

register_result "distinct-palindromic-factors" where
  title := "A word of length n has at most n + 1 distinct palindromic factors"
  topic := "combinatorics on words"
  sources := [
    { paper := GlenJustinWidmerZamboni2009, theorem := "Proposition 2.1 (Droubay–Justin–Pirillo)",
      locator := "arXiv:0801.1656v3, §2, p. 4. Factor and palindrome conventions in §1.1, p. 3." }
  ]
  theorems := [List.card_palindromicFactors_le]
  scope := "For every finite list over an alphabet with decidable equality, count each distinct \
    contiguous palindromic word once, including the empty word. The alphabet may be infinite."
