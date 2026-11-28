/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Algorithms.Lean.EditDistance.Unit
public import CslibFrontier.Algorithms.WordRAM.EditDistance

/-!
# Edit distance and longest common subsequence: worked examples

Kernel-checked examples (`decide`, no `native_decide`) for the Wagner–Fischer edit distance, its
traceback, the longest-common-subsequence table and its traceback, and the Word-RAM programs and
running-time certificates of `CslibFrontier.Algorithms.WordRAM.EditDistance`. The examples include
the textbook pairs kitten/sitting and flaw/lawn, the strings of the running example of
[CLRS, Section 15.4][CLRS2009], empty words, and letter costs that are neither unit nor symmetric.
-/

public section

namespace CslibFrontierTests.EditDistance

open scoped List
open Cslib.Algorithms.Lean.EditDistance
open Cslib.Algorithms.WordRAM.EditDistance
open Cslib.WordRAM

/-- `kitten`. -/
@[expose] def kitten : List Char := ['k', 'i', 't', 't', 'e', 'n']
/-- `sitting`. -/
@[expose] def sitting : List Char := ['s', 'i', 't', 't', 'i', 'n', 'g']
/-- `flaw`. -/
@[expose] def flaw : List Char := ['f', 'l', 'a', 'w']
/-- `lawn`. -/
@[expose] def lawn : List Char := ['l', 'a', 'w', 'n']

/-! ### Unit costs (Levenshtein) -/

example : editDist Costs.unit kitten sitting = 3 := by decide
example : editDist Costs.unit flaw lawn = 2 := by decide
example : editDist Costs.unit kitten kitten = 0 := by decide

/-- The traceback on kitten/sitting: two replacements and an insertion. -/
example : optScript Costs.unit kitten sitting =
    [.sub 'k' 's', .sub 'i' 'i', .sub 't' 't', .sub 't' 't', .sub 'e' 'i', .sub 'n' 'n',
      .ins 'g'] := by decide

/-- The traceback on flaw/lawn: a deletion and an insertion. -/
example : optScript Costs.unit flaw lawn =
    [.del 'f', .sub 'l' 'l', .sub 'a' 'a', .sub 'w' 'w', .ins 'n'] := by decide

/-- A script of cost `3` from kitten to sitting is optimal: no script costs less. -/
example (s : EditScript Char) (hs : s.src = kitten) (ht : s.tgt = sitting) :
    3 ≤ s.cost Costs.unit := by
  have h := (isLeast_editDist Costs.unit kitten sitting).2 ⟨s, hs, ht, rfl⟩
  rwa [show editDist Costs.unit kitten sitting = 3 by decide] at h

-- Edit the newly inserted letter at an interior position and then delete it.
example : Relation.RelatesInSteps SingleEdit [1, 3] [1, 3] 3 := by
  have ins : SingleEdit [1, 3] [1, 2, 3] := .cons 1 (.ins 2 [3])
  have sub : SingleEdit [1, 2, 3] [1, 4, 3] := .cons 1 (.sub (by decide) [3])
  have del : SingleEdit [1, 4, 3] [1, 3] := .cons 1 (.del 4 [3])
  exact ((Relation.RelatesInSteps.single ins).tail _ _ _ _ sub).tail _ _ _ _ del

-- Even sequences that revisit positions need at least three edits from kitten to sitting.
example {n : ℕ} (h : Relation.RelatesInSteps SingleEdit kitten sitting n) : 3 ≤ n := by
  have bound := (isLeast_editDist_unit kitten sitting).2 h
  rwa [show editDist Costs.unit kitten sitting = 3 by decide] at bound

/-! ### Empty words -/

example : editDist Costs.unit ([] : List Char) [] = 0 := by decide
example : editDist Costs.unit [] sitting = 7 := by decide
example : editDist Costs.unit kitten [] = 6 := by decide
example : optScript Costs.unit [] ['a', 'b'] = [.ins 'a', .ins 'b'] := by decide
example : optScript Costs.unit ['a', 'b'] [] = [.del 'a', .del 'b'] := by decide

/-! ### Costs that are neither unit nor symmetric -/

/-- Deleting costs `3`, inserting costs `2`, and replacing by a different letter costs `4`. -/
@[expose] def skewed : Costs Char where
  del _ := 3
  ins _ := 2
  sub a b := if a = b then 0 else 4

/-- A replacement (`4`) is cheaper than a deletion and an insertion (`5`). -/
example : editDist skewed ['a'] ['b'] = 4 := by decide
/-- Swapping two letters: insert, keep, delete (`5`) beats two replacements (`8`). -/
example : editDist skewed ['a', 'b'] ['b', 'a'] = 5 := by decide
example : optScript skewed ['a', 'b'] ['b', 'a'] = [.del 'a', .sub 'b' 'b', .ins 'a'] := by
  decide
/-- The distance is not symmetric for these costs. -/
example : editDist skewed ['a'] [] = 3 ∧ editDist skewed [] ['a'] = 2 := by decide

/-! ### Longest common subsequence -/

/-- `ABCBDAB`, from the running example of [CLRS, Section 15.4][CLRS2009]. -/
@[expose] def clrsX : List Char := ['A', 'B', 'C', 'B', 'D', 'A', 'B']
/-- `BDCABA`, from the running example of [CLRS, Section 15.4][CLRS2009]. -/
@[expose] def clrsY : List Char := ['B', 'D', 'C', 'A', 'B', 'A']

example : lcsLength clrsX clrsY = 4 := by decide
/-- The traceback prefers dropping a letter of the first word on ties, so it returns `BDAB`;
the CLRS traceback returns `BCBA`. Both are longest common subsequences. -/
example : lcs clrsX clrsY = ['B', 'D', 'A', 'B'] := by decide
example : ['B', 'C', 'B', 'A'] <+ clrsX ∧ ['B', 'C', 'B', 'A'] <+ clrsY := by decide
example : lcsLength kitten sitting = 4 := by decide
example : lcsLength ([] : List Char) clrsY = 0 := by decide
example : lcsLength ['a', 'b'] ['c', 'd'] = 0 := by decide

/-- No common subsequence of the CLRS strings is longer than `4`. -/
example (z : List Char) (hx : z <+ clrsX) (hy : z <+ clrsY) : z.length ≤ 4 := by
  have h := length_le_lcsLength hx hy
  rwa [show lcsLength clrsX clrsY = 4 by decide] at h

/-- The duality `editDist Costs.indel x y + 2 · lcsLength x y = |x| + |y|`: `5 + 2 · 4 = 7 + 6`. -/
example : editDist Costs.indel clrsX clrsY = 5 := by decide
example : editDist Costs.indel kitten sitting = 5 := by
  have h := editDist_indel_add_two_mul kitten sitting
  rw [show lcsLength kitten sitting = 4 by decide] at h
  simpa [kitten, sitting] using h

/-- `optScript Costs.indel` may return a replacement by a different letter, at cost `2`; a script
without one (delete, then insert) costs the same. -/
example : optScript Costs.indel ['a'] ['b'] = [.sub 'a' 'b'] := by decide
example : ∃ s : EditScript Char, s.IsIndel ∧ s.src = ['a'] ∧ s.tgt = ['b'] ∧
    s.cost Costs.indel = 2 := by
  have h := (isLeast_editDist_indel ['a'] ['b']).1
  rwa [show editDist Costs.indel ['a'] ['b'] = 2 by decide] at h

/-! ### Word-RAM execution and running-time certificates -/

/-- Word-encoded kitten/sitting pair. -/
@[expose] def kittenSittingWords : WordSeqPair where
  src := kitten.map Char.toNat
  tgt := sitting.map Char.toNat

/-- Word-encoded CLRS LCS pair. -/
@[expose] def clrsWords : WordSeqPair where
  src := clrsX.map Char.toNat
  tgt := clrsY.map Char.toNat

/-- Empty word pair. -/
@[expose] def emptyWords : WordSeqPair where
  src := []
  tgt := []

/-- Asymmetric letter costs over `Fin 2`: `del = 3`, `ins = 2`, `sub a b = if a = b then 0 else 4`
on `[0, 1]` vs `[1, 0]`, witnessing non-unit asymmetric Wagner–Fischer on the Word-RAM. -/
@[expose] def skewedSwapInst : WeightedInstance where
  sigma := 2
  costs := ⟨fun _ => 3, fun _ => 2, fun a b => if a = b then 0 else 4⟩
  src := [0, 1]
  tgt := [1, 0]

/-- Empty-alphabet edge case (`sigma = 0`) for general-cost Wagner–Fischer on the Word-RAM. -/
@[expose] def zeroSigmaInst : WeightedInstance where
  sigma := 0
  costs := ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a⟩
  src := []
  tgt := []

/-- One-sided empty source/target instances with `del = 3 ≠ 2 = ins`, distinguishing the `m > 0,
n = 0` and `m = 0, n > 0` border loops. -/
@[expose] def asymDelOnlyInst : WeightedInstance where
  sigma := 1
  costs := ⟨fun _ => 3, fun _ => 2, fun _ _ => 0⟩
  src := [0]
  tgt := []

/-- Asymmetric insertion-only counterpart (`src = []`, `tgt = [0]`, cost `2`). -/
@[expose] def asymInsOnlyInst : WeightedInstance where
  sigma := 1
  costs := ⟨fun _ => 3, fun _ => 2, fun _ _ => 0⟩
  src := []
  tgt := [0]

/-- Asymmetric substitution table (`sub 0 1 = 1`, `sub 1 0 = 4`, `del = ins = 5`), witnessing
row-major `a * σ + b` vs `b * σ + a` indexing of `WeightedInstance.subTable`. -/
@[expose] def asymSubFwdInst : WeightedInstance where
  sigma := 2
  costs := ⟨fun _ => 5, fun _ => 5, fun a b =>
    if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then 4 else 0⟩
  src := [0]
  tgt := [1]

/-- Transposed query (`src = [1]`, `tgt = [0]`, cost `4`) on the same asymmetric `sub` table. -/
@[expose] def asymSubRevInst : WeightedInstance where
  sigma := 2
  costs := asymSubFwdInst.costs
  src := [1]
  tgt := [0]

-- Checked Word-RAM execution and flat-interpreter (`Cslib.WordRAM.run`) certificates on concrete
-- fitting widths, including empty-word and empty-alphabet boundary cases.
example : ∃ n ≤ 26 * 7 * 8,
    Executes 8 unitEditDistProgram (.init kittenSittingWords.encode) 3 n ∧
      Cslib.WordRAM.run 8 unitEditDistProgram (26 * 7 * 8) (.init kittenSittingWords.encode) =
        some (3, n) := by
  obtain ⟨n, hexec, hle⟩ :=
    computesInTime_unitEditDist kittenSittingWords 8 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : editDist Costs.unit kittenSittingWords.src kittenSittingWords.tgt = 3 := by decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 26,
    Executes 3 unitEditDistProgram (.init emptyWords.encode) 0 n ∧
      Cslib.WordRAM.run 3 unitEditDistProgram 26 (.init emptyWords.encode) = some (0, n) := by
  obtain ⟨n, hexec, hle⟩ := computesInTime_unitEditDist emptyWords 3 (by decide) (by decide)
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 20 * 8 * 7,
    Executes 8 lcsLengthProgram (.init clrsWords.encode) 4 n ∧
      Cslib.WordRAM.run 8 lcsLengthProgram (20 * 8 * 7) (.init clrsWords.encode) =
        some (4, n) := by
  obtain ⟨n, hexec, hle⟩ := computesInTime_lcsLength clrsWords 8 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : lcsLength clrsWords.src clrsWords.tgt = 4 := by decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 28 * 3 * 3,
    Executes 5 weightedEditDistProgram (.init skewedSwapInst.encode) 5 n ∧
      Cslib.WordRAM.run 5 weightedEditDistProgram (28 * 3 * 3) (.init skewedSwapInst.encode) =
        some (5, n) := by
  obtain ⟨n, hexec, hle⟩ :=
    computesInTime_weightedEditDist skewedSwapInst 5 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : editDist skewedSwapInst.costs skewedSwapInst.src skewedSwapInst.tgt = 5 := by decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 28,
    Executes 3 weightedEditDistProgram (.init zeroSigmaInst.encode) 0 n ∧
      Cslib.WordRAM.run 3 weightedEditDistProgram 28 (.init zeroSigmaInst.encode) =
        some (0, n) := by
  have hw : zeroSigmaInst.FitsWidth 3 := by decide
  obtain ⟨n, hexec, hle⟩ := computesInTime_weightedEditDist zeroSigmaInst 3 hw hw.inputFits
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 28 * 2 * 1,
    Executes 4 weightedEditDistProgram (.init asymDelOnlyInst.encode) 3 n ∧
      Cslib.WordRAM.run 4 weightedEditDistProgram (28 * 2 * 1) (.init asymDelOnlyInst.encode) =
        some (3, n) := by
  have hw : asymDelOnlyInst.FitsWidth 4 := by decide
  obtain ⟨n, hexec, hle⟩ := computesInTime_weightedEditDist asymDelOnlyInst 4 hw hw.inputFits
  dsimp only at hexec hle
  have hval : editDist asymDelOnlyInst.costs asymDelOnlyInst.src asymDelOnlyInst.tgt = 3 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 28 * 1 * 2,
    Executes 4 weightedEditDistProgram (.init asymInsOnlyInst.encode) 2 n ∧
      Cslib.WordRAM.run 4 weightedEditDistProgram (28 * 1 * 2) (.init asymInsOnlyInst.encode) =
        some (2, n) := by
  have hw : asymInsOnlyInst.FitsWidth 4 := by decide
  obtain ⟨n, hexec, hle⟩ := computesInTime_weightedEditDist asymInsOnlyInst 4 hw hw.inputFits
  dsimp only at hexec hle
  have hval : editDist asymInsOnlyInst.costs asymInsOnlyInst.src asymInsOnlyInst.tgt = 2 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 28 * 2 * 2,
    Executes 5 weightedEditDistProgram (.init asymSubFwdInst.encode) 1 n ∧
      Cslib.WordRAM.run 5 weightedEditDistProgram (28 * 2 * 2) (.init asymSubFwdInst.encode) =
        some (1, n) := by
  have hw : asymSubFwdInst.FitsWidth 5 := by decide
  obtain ⟨n, hexec, hle⟩ := computesInTime_weightedEditDist asymSubFwdInst 5 hw hw.inputFits
  dsimp only at hexec hle
  have hval : editDist asymSubFwdInst.costs asymSubFwdInst.src asymSubFwdInst.tgt = 1 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 28 * 2 * 2,
    Executes 5 weightedEditDistProgram (.init asymSubRevInst.encode) 4 n ∧
      Cslib.WordRAM.run 5 weightedEditDistProgram (28 * 2 * 2) (.init asymSubRevInst.encode) =
        some (4, n) := by
  have hw : asymSubRevInst.FitsWidth 5 := by decide
  obtain ⟨n, hexec, hle⟩ := computesInTime_weightedEditDist asymSubRevInst 5 hw hw.inputFits
  dsimp only at hexec hle
  have hval : editDist asymSubRevInst.costs asymSubRevInst.src asymSubRevInst.tgt = 4 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

end CslibFrontierTests.EditDistance
