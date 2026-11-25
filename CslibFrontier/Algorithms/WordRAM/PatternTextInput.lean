/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.ListArray

import CslibFrontier.Computability.WordRAM.InputArray

/-!
# Pattern-and-text inputs on the word RAM

Exact pattern matchers on the word RAM, such as Knuth–Morris–Pratt
(`Cslib.Algorithms.WordRAM.KMP`) and the Z-algorithm (`Cslib.Algorithms.WordRAM.ZFunction`), read a
pattern and a text from one initialized word sequence. This module fixes that input record and its
layout once.

## Main definitions

* `Cslib.Algorithms.WordRAM.PatternTextInput`: a pattern `pat` and a text `txt` over words.
* `Cslib.Algorithms.WordRAM.PatternTextInput.encode`: the word-sequence encoding
  `[|pat|, |txt|] ++ pat ++ txt`.

## Main results

* `Cslib.Algorithms.WordRAM.PatternTextInput.init_blocks`: in `Data.init I.encode`, the two lengths
  sit at addresses `1` and `2`, `pat ++ txt` at `[3, 3 + |pat| + |txt|)`, `pat` at
  `[3, 3 + |pat|)` and `txt` at `[3 + |pat|, 3 + |pat| + |txt|)`.
-/

public section

namespace Cslib.Algorithms.WordRAM

open Cslib.WordRAM

/-- Pattern-matching instance on the word RAM: a pattern `pat` and a text `txt` over words. -/
structure PatternTextInput where
  /-- Pattern word sequence. -/
  pat : List ℕ
  /-- Text word sequence. -/
  txt : List ℕ
  deriving DecidableEq, Repr

/-- Word-list layout `[|pat|, |txt|] ++ pat ++ txt` placed into `State.init`: `mem[1] = |pat|`,
`mem[2] = |txt|`, `pat` occupies `[3, 3 + |pat|)`, `txt` occupies `[3 + |pat|, 3 + |pat| + |txt|)`,
and `pat ++ txt` occupies `[3, 3 + |pat| + |txt|)`. -/
@[expose] def PatternTextInput.encode (I : PatternTextInput) : List ℕ :=
  I.pat.length :: I.txt.length :: (I.pat ++ I.txt)

/-- The blocks of `Data.init I.encode`, for any register count: the lengths at addresses `1` and
`2`, and the pattern, the text and their concatenation at the addresses of
`PatternTextInput.encode`. -/
theorem PatternTextInput.init_blocks {r : ℕ} (I : PatternTextInput) :
    (Data.init I.encode : Data r).mem 1 = I.pat.length ∧
      (Data.init I.encode : Data r).mem 2 = I.txt.length ∧
      Block.HoldsList 3 (I.pat ++ I.txt) (Data.init I.encode : Data r).mem ∧
      Block.HoldsList 3 I.pat (Data.init I.encode : Data r).mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt (Data.init I.encode : Data r).mem := by
  have hall : Block.HoldsList 3 (I.pat ++ I.txt) (Data.init I.encode : Data r).mem := by
    have heq : I.encode = [I.pat.length, I.txt.length] ++ ((I.pat ++ I.txt) ++ []) := by
      simp only [encode, List.cons_append, List.nil_append, List.append_nil]
    rw [heq]
    exact Data.init_realizes_append [I.pat.length, I.txt.length] (I.pat ++ I.txt) []
  obtain ⟨hpat, htxt⟩ := Block.holdsList_append_iff.mp hall
  exact ⟨by simpa only [encode, List.getD_cons_zero] using Data.init_mem_succ (r := r) I.encode 0,
    by simpa only [encode, List.getD_cons_succ, List.getD_cons_zero] using
      Data.init_mem_succ (r := r) I.encode 1,
    hall, hpat, htxt⟩

end Cslib.Algorithms.WordRAM
