/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.KMP.Search
public import CslibFrontier.Computability.WordRAM.ListOutput

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Knuth–Morris–Pratt String Matching in Linear Time on the Word RAM

This module implements the Knuth–Morris–Pratt (`[KnuthMorrisPratt1977]`, Sections 1–2;
`[CLRS2009]`, Section 32.4) failure-table construction and exact pattern matcher as fixed
`Basis.standard` word-RAM programs over word sequences, proving linear `O(|p|)` and
`O(|p| + |t|)` instruction bounds:

* `prefixCode` and `prefixProgram` take a pattern `p : List ℕ` in `State.init p` layout and write
  the length-prefixed failure table `(computePrefix p.toArray).toList` at address `|p| + 1` within
  `31 * |p| + 10` instructions (`31 * |p| + 9` before `halt`) whenever `Fits w (2 * |p| + 1)` and
  `InputFits w p` hold.
* `searchCode` and `searchProgram` take a `SearchInput` `(pat, txt)` encoded as
  `[|pat|, |txt|] ++ pat ++ txt` in `State.init`, construct the failure table at
  `3 + |pat| + |txt|` when `pat ≠ []`, and write the length-prefixed list of all exact match shifts
  `kmpMatchesList pat txt` at address `3 + 2 * |pat| + |txt|` within
  `31 * |pat| + 37 * |txt| + 23` instructions (`+ 22` before `halt`) whenever
  `Fits w (2 * |pat| + 2 * |txt| + 4)` and `InputFits w I.encode` hold.

Every index calculation, memory load and store, character comparison, fallback transition, match
recording step, loop test, and final `halt` is charged by the machine semantics. Both the
failure-table loop and the text-scanning loop use `ExecWithin.loop_potential` with matched-prefix
potential `10 * k`, charging each `10`-instruction fallback step against the strict decrease
`pi[k - 1] ≤ k - 1`.

## Main definitions

* `Cslib.Algorithms.WordRAM.KMP.Reg.out`: output register (`Fin 15`) holding the returned
  length-prefixed array address.
* `Cslib.Algorithms.WordRAM.KMP.SearchInput`, `SearchInput.encode`: pattern-matching instance
  `(pat, txt)` and its word-sequence encoding `[|pat|, |txt|] ++ pat ++ txt`.
* `Cslib.Algorithms.WordRAM.KMP.prefixCode`, `prefixProgram`: structured and flat programs
  computing `(computePrefix p.toArray).toList`.
* `Cslib.Algorithms.WordRAM.KMP.searchCode`, `searchProgram`: structured and flat programs
  computing `kmpMatchesList I.pat I.txt`.

## Main results

* `Cslib.Algorithms.WordRAM.KMP.prefixCode_exec`, `prefixProgram_computesListInTime`: failure-table
  construction in `31 * |p| + 10` word-RAM instructions at widths fitting `2 * |p| + 1`.
* `Cslib.Algorithms.WordRAM.KMP.searchCode_exec`, `searchProgram_computesListInTime`: end-to-end
  KMP pattern search in `31 * |pat| + 37 * |txt| + 23` word-RAM instructions at widths fitting
  `2 * |pat| + 2 * |txt| + 4`.

## References

* [D. E. Knuth, J. H. Morris, Jr., and V. R. Pratt, *Fast Pattern Matching in
  Strings*][KnuthMorrisPratt1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*,
  3rd ed., Section 32.4][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.KMP

open Cslib.WordRAM
open Cslib.Algorithms.Lean.KMP

/-! ## Input encoding and registers -/

/-- Pattern-matching instance on the word RAM: a pattern `pat` and a text `txt` over `w`-bit
words. -/
structure SearchInput where
  /-- Pattern word sequence. -/
  pat : List ℕ
  /-- Text word sequence. -/
  txt : List ℕ
  deriving DecidableEq, Repr

/-- Word-list layout `[|pat|, |txt|] ++ pat ++ txt` placed into `State.init`: `mem[1] = |pat|`,
`mem[2] = |txt|`, `pat` occupies `[3, 3 + |pat|)`, and `txt` occupies
`[3 + |pat|, 3 + |pat| + |txt|)`. -/
@[expose] def SearchInput.encode (I : SearchInput) : List ℕ :=
  I.pat.length :: I.txt.length :: (I.pat ++ I.txt)

namespace Reg

private abbrev zero : Fin 15 := 0
private abbrev one : Fin 15 := 1
private abbrev patBase : Fin 15 := 2
private abbrev patLen : Fin 15 := 3
private abbrev txtBase : Fin 15 := 4
private abbrev txtLen : Fin 15 := 5
private abbrev piBase : Fin 15 := 6
private abbrev regidx : Fin 15 := 7
private abbrev regk : Fin 15 := 8
private abbrev regch : Fin 15 := 9
private abbrev outCnt : Fin 15 := 10
private abbrev go : Fin 15 := 11
private abbrev t0 : Fin 15 := 12
private abbrev t1 : Fin 15 := 13
/-- Address register `out` of the length-prefixed output array. -/
abbrev out : Fin 15 := 14

end Reg

open Reg

/-! ## Programs -/

/-- One iteration of the KMP fallback loop: stops when `regk = 0` or `pat[regk] = regch`, and
otherwise replaces `regk` with `pi[regk - 1]`. -/
private def fallbackBody : Code .standard 15 := ram[
  if zero < regk then [
    t0 ← patBase + regk;
    t0 ← *t0;
    if t0 = regch then [
      go ← #0
    ] else [
      t0 ← regk - one;
      t0 ← piBase + t0;
      regk ← *t0
    ]
  ] else [
    go ← #0
  ] ]

/-- Shared KMP automaton step updating `regk` on character `regch`. -/
private def advanceCode : Code .standard 15 := ram[
  go ← #1;
  while zero < go do [ ⟪fallbackBody⟫ ];
  t0 ← patBase + regk;
  t0 ← *t0;
  if t0 = regch then [
    regk ← regk + one
  ] else [
    regk ← #0
  ] ]

/-- One step of failure-table construction at pattern index `regidx` (`1 ≤ regidx < patLen`). -/
private def prefixBody : Code .standard 15 :=
  .seq (ram[ t0 ← patBase + regidx; regch ← *t0 ])
    (.seq advanceCode (ram[ t0 ← piBase + regidx; *t0 ← regk; regidx ← regidx + one ]))

/-- Construct the failure table of a nonempty pattern `pat` (`0 < patLen`) at `piBase`. -/
private def buildPrefixNonempty : Code .standard 15 :=
  .seq (ram[ *piBase ← zero; regidx ← one; regk ← zero ])
    (.loop (.lt regidx patLen) prefixBody)

/-- Structured program computing `(computePrefix p.toArray).toList` as a length-prefixed array at
`out = |p| + 1` from `Data.init p`. -/
def prefixCode : Code .standard 15 :=
  .seq (ram[
    zero ← #0;
    one ← #1;
    patLen ← *zero;
    patBase ← one;
    out ← patLen + one;
    *out ← patLen ])
  (.branch (.lt zero patLen)
    (.seq (ram[ piBase ← out + one ]) buildPrefixNonempty)
    (ram[ regk ← zero ]))

/-- Flat program computing `(computePrefix p.toArray).toList` via `ExecutesList`. -/
def prefixProgram : Program .standard 15 := prefixCode.program out

/-- Body writing `List.range (txtLen + 1)` at `out + 1` when the pattern is empty. -/
private def emptyPatBody : Code .standard 15 := ram[
  t0 ← out + one;
  t0 ← t0 + regidx;
  *t0 ← regidx;
  regidx ← regidx + one ]

/-- Empty-pattern branch writing `List.range (txtLen + 1)` as a length-prefixed array at `out`. -/
private def emptyPatCode : Code .standard 15 :=
  .seq (ram[ t1 ← txtLen + one; *out ← t1; regidx ← zero ])
    (.loop (.lt regidx t1) emptyPatBody)

/-- Post-advance match check and state update in `searchBody`. -/
private def searchPostBranch : Code .standard 15 := ram[
  if regk = patLen then [
    regidx ← regidx + one;
    t0 ← regidx - patLen;
    outCnt ← outCnt + one;
    t1 ← out + outCnt;
    *t1 ← t0;
    t0 ← patLen - one;
    t0 ← piBase + t0;
    regk ← *t0
  ] else [
    regidx ← regidx + one
  ] ]

/-- One step of the KMP text scan at text index `regidx` (`0 ≤ regidx < txtLen`). -/
private def searchBody : Code .standard 15 :=
  .seq (ram[ t0 ← txtBase + regidx; regch ← *t0 ])
    (.seq advanceCode searchPostBranch)

/-- Nonempty-pattern KMP search: build `pi` at `piBase`, scan `txt`, and write `outCnt` at `out`. -/
private def nonemptyPatCode : Code .standard 15 :=
  .seq buildPrefixNonempty <|
  .seq (ram[ outCnt ← zero; regidx ← zero; regk ← zero ]) <|
  .seq (.loop (.lt regidx txtLen) searchBody)
    (ram[ *out ← outCnt ])

/-- Setup pointers and lengths from `Data.init I.encode`. -/
private def searchSetup : Code .standard 15 := ram[
  zero ← #0;
  one ← #1;
  patLen ← *one;
  t0 ← #2;
  txtLen ← *t0;
  patBase ← #3;
  txtBase ← patBase + patLen;
  piBase ← txtBase + txtLen;
  out ← piBase + patLen ]

/-- Structured program computing `kmpMatchesList I.pat I.txt` as a length-prefixed array at
`out = 3 + 2 * |I.pat| + |I.txt|` from `Data.init I.encode`. -/
def searchCode : Code .standard 15 :=
  .seq searchSetup (.branch (.lt zero patLen) nonemptyPatCode emptyPatCode)

/-- Flat program computing `kmpMatchesList I.pat I.txt` via `ExecutesList`. -/
def searchProgram : Program .standard 15 := searchCode.program out

/-! ## Amortized execution of `advanceCode` -/

private theorem while_fallback_spec {w : ℕ} (pat : List ℕ) (pi : Array ℕ)
    (hdec : IsDecreasingTable pi) (k : ℕ) :
    ∀ x : Data 15,
      x.regs zero = 0 →
      x.regs one = 1 →
      x.regs go = 1 →
      x.regs regk = k →
      k < pat.length →
      k ≤ pi.size →
      Fits w (x.regs patBase + pat.length) →
      Fits w (x.regs piBase + pi.size) →
      Block.HoldsList (x.regs patBase) pat x.mem →
      Block.HoldsList (x.regs piBase) pi.toList x.mem →
      ∃ y T, ExecWithin w (.loop (.lt zero go) fallbackBody) x y T ∧
        T + 10 * y.regs regk ≤ 10 * k + 9 ∧
        ∃ hk' : y.regs regk < pat.length,
          (if pat[y.regs regk]'hk' = x.regs regch then y.regs regk + 1 else 0) =
            advance pat.toArray pi k (x.regs regch) ∧
          y.mem = x.mem ∧
          (∀ r : Fin 15, r ≠ regk → r ≠ go → r ≠ t0 → y.regs r = x.regs r) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro x hz ho hgo hk hk_lt hk_pi hf_pat hf_pi hpat hpi
    have hc : (Cond.lt zero go).Holds x := by simp only [Cond.holds_lt, hz, hgo]; omega
    have hsz : pat.toArray.size = pat.length := List.size_toArray
    by_cases hk0 : k = 0
    · subst hk0
      let x₁ := x.set go 0
      have hb : ExecWithin w fallbackBody x x₁ 3 := by
        unfold fallbackBody
        wram_exec [hz, hk]
      have hstop : ¬(Cond.lt zero go).Holds x₁ := by simp +decide [Cond.holds_lt, x₁, hz]
      have hx₁_k : x₁.regs regk = 0 := by simp +decide [x₁, hk]
      have hx₁_ch : x₁.regs regch = x.regs regch := by simp +decide [x₁]
      refine ⟨x₁, 7, ExecWithin.loop_once hc hb hstop, by rw [hx₁_k]; omega,
        by rw [hx₁_k]; exact hk_lt, ?_, rfl, fun r hr1 hr2 hr3 => ?_⟩
      · simp only [hx₁_k]
        rw [advance]
        have hk_arr : 0 < pat.toArray.size := by omega
        have hget_arr : pat.toArray[0]'hk_arr = pat[0]'hk_lt := List.getElem_toArray _
        simp only [hk_arr, ↓reduceDIte, hget_arr, ↓reduceIte]
      · simp only [x₁, Data.set_regs, Function.update_of_ne hr2]
    · have hk_pos : 0 < k := by omega
      have hread_pat : x.mem (x.regs patBase + k) = pat[k] := hpat.get k hk_lt
      have hf_pk : Fits w (x.regs patBase + k) := hf_pat.of_le (by omega)
      have hk_arr : k < pat.toArray.size := by omega
      have hget_arr : pat.toArray[k]'hk_arr = pat[k]'hk_lt := List.getElem_toArray _
      by_cases hmatch : pat[k] = x.regs regch
      · let x₁ := ((x.set t0 (x.regs patBase + k)).set t0 pat[k]).set go 0
        have hb : ExecWithin w fallbackBody x x₁ 5 := by
          unfold fallbackBody
          wram_exec [hz, hk, hk_pos, hread_pat, hmatch, hf_pk]
          rw [← hmatch]
        have hstop : ¬(Cond.lt zero go).Holds x₁ := by simp +decide [Cond.holds_lt, x₁, hz]
        have hx₁_k : x₁.regs regk = k := by simp +decide [x₁, hk]
        have hx₁_ch : x₁.regs regch = x.regs regch := by simp +decide [x₁]
        refine ⟨x₁, 9, ExecWithin.loop_once hc hb hstop, by rw [hx₁_k]; omega,
          by rw [hx₁_k]; exact hk_lt, ?_, rfl, fun r hr1 hr2 hr3 => ?_⟩
        · simp only [hx₁_k, hmatch, ↓reduceIte]
          rw [advance]
          simp only [hk_arr, ↓reduceDIte, hget_arr, hmatch, ↓reduceIte]
        · simp only [x₁, Data.set_regs, Function.update_of_ne hr2, Function.update_of_ne hr3]
      · have hpi_idx : k - 1 < pi.size := by omega
        have hpi_list : k - 1 < pi.toList.length := by
          simpa only [Array.length_toList] using hpi_idx
        have hread_pi : x.mem (x.regs piBase + (k - 1)) = pi[k - 1]'hpi_idx := by
          have h1 := hpi.get (k - 1) hpi_list
          rwa [Array.getElem_toList] at h1
        have hf_km1 : Fits w (k - 1) := hf_pat.of_le (by omega)
        have hf_pik : Fits w (x.regs piBase + (k - 1)) := hf_pi.of_le (by omega)
        let k' := pi[k - 1]'hpi_idx
        have hk'_le : k' ≤ k - 1 := hdec (k - 1) hpi_idx
        have hk'_lt : k' < k := by omega
        let x₁ := ((((x.set t0 (x.regs patBase + k)).set t0 pat[k]).set t0 (k - 1)).set
          t0 (x.regs piBase + (k - 1))).set regk k'
        have hb : ExecWithin w fallbackBody x x₁ 8 := by
          unfold fallbackBody
          wram_exec [hz, ho, hk, hk_pos, hread_pat, hmatch, hread_pi, hf_pk, hf_km1, hf_pik]
        have hx₁_pb : x₁.regs patBase = x.regs patBase := by simp +decide [x₁]
        have hx₁_pib : x₁.regs piBase = x.regs piBase := by simp +decide [x₁]
        have hx₁_ch : x₁.regs regch = x.regs regch := by simp +decide [x₁]
        obtain ⟨y, T', hy_exec, hy_pot, hk_y, hy_adv, hy_mem, hy_fr⟩ := ih k' hk'_lt x₁
          (by simp +decide [x₁, hz])
          (by simp +decide [x₁, ho])
          (by simp +decide [x₁, hgo])
          (by simp +decide [x₁])
          (by omega)
          (by omega)
          (by rwa [hx₁_pb])
          (by rwa [hx₁_pib])
          (by rw [hx₁_pb]; exact hpat)
          (by rw [hx₁_pib]; exact hpi)
        refine ⟨y, 8 + T' + 2, ExecWithin.loop_iter hc hb hy_exec, by omega, hk_y, ?_, hy_mem,
          fun r hr1 hr2 hr3 => ?_⟩
        · rw [hx₁_ch] at hy_adv
          rw [hy_adv]
          have hlt_pi : pi[k - 1]'hpi_idx < k := hk'_lt
          conv_rhs => rw [advance]
          simp only [hk_arr, ↓reduceDIte, hget_arr, hmatch, ↓reduceIte, hk0, hpi_idx, hlt_pi]
          rfl
        · rw [hy_fr r hr1 hr2 hr3]
          simp only [x₁, Data.set_regs, Function.update_of_ne hr1, Function.update_of_ne hr3]

private theorem advanceCode_spec {w : ℕ} (pat : List ℕ) (pi : Array ℕ)
    (hdec : IsDecreasingTable pi) (x : Data 15)
    (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hk_lt : x.regs regk < pat.length) (hk_pi : x.regs regk ≤ pi.size)
    (hf_pat : Fits w (x.regs patBase + pat.length))
    (hf_pi : Fits w (x.regs piBase + pi.size))
    (hpat : Block.HoldsList (x.regs patBase) pat x.mem)
    (hpi : Block.HoldsList (x.regs piBase) pi.toList x.mem) :
    ∃ y T, ExecWithin w advanceCode x y T ∧
      y.regs regk = advance pat.toArray pi (x.regs regk) (x.regs regch) ∧
      T + 10 * y.regs regk ≤ 10 * x.regs regk + 24 ∧
      y.mem = x.mem ∧
      (∀ r : Fin 15, r ≠ regk → r ≠ go → r ≠ t0 → y.regs r = x.regs r) := by
  have hf_1 : Fits w 1 := hf_pat.of_le (by omega)
  let x₀ := x.set go 1
  have hx₀_go : ExecWithin (B := .standard) w (ram[ go ← #1 ]) x x₀ 1 := ExecWithin.const hf_1
  have hx₀_pb : x₀.regs patBase = x.regs patBase := by simp +decide [x₀]
  have hx₀_pib : x₀.regs piBase = x.regs piBase := by simp +decide [x₀]
  have hx₀_ch : x₀.regs regch = x.regs regch := by simp +decide [x₀]
  obtain ⟨y₁, T₁, hloop, hpot₁, hk₁_lt, hadv₁, hmem₁, hfr₁⟩ :=
    while_fallback_spec pat pi hdec (x.regs regk) x₀
      (by simp +decide [x₀, hz])
      (by simp +decide [x₀, ho])
      (by simp +decide [x₀])
      (by simp +decide [x₀])
      hk_lt hk_pi
      (by rwa [hx₀_pb])
      (by rwa [hx₀_pib])
      (by rw [hx₀_pb]; exact hpat)
      (by rw [hx₀_pib]; exact hpi)
  rw [hx₀_ch] at hadv₁
  have hy₁_one : y₁.regs one = 1 :=
    (hfr₁ one (by decide) (by decide) (by decide)).trans (by simp +decide [x₀, ho])
  have hy₁_pb : y₁.regs patBase = x.regs patBase :=
    (hfr₁ patBase (by decide) (by decide) (by decide)).trans hx₀_pb
  have hy₁_ch : y₁.regs regch = x.regs regch :=
    (hfr₁ regch (by decide) (by decide) (by decide)).trans hx₀_ch
  have hread₁ : y₁.mem (y₁.regs patBase + y₁.regs regk) = pat[y₁.regs regk] := by
    rw [hmem₁, hy₁_pb]
    exact hpat.get (y₁.regs regk) hk₁_lt
  have hf_pk₁ : Fits w (y₁.regs patBase + y₁.regs regk) := by
    rw [hy₁_pb]; exact hf_pat.of_le (by omega)
  have hf_k1 : Fits w (y₁.regs regk + 1) := hf_pat.of_le (by omega)
  let tail : Code .standard 15 := ram[
    t0 ← patBase + regk;
    t0 ← *t0;
    if t0 = regch then [
      regk ← regk + one
    ] else [
      regk ← #0
    ] ]
  have hcode_eq : advanceCode = .seq (ram[ go ← #1 ])
      (.seq (.loop (.lt zero go) fallbackBody) tail) := by
    rfl
  rw [hcode_eq]
  by_cases hm : pat[y₁.regs regk] = x.regs regch
  · let y := ((y₁.set t0 (y₁.regs patBase + y₁.regs regk)).set t0 pat[y₁.regs regk]).set
        regk (y₁.regs regk + 1)
    have htail : ExecWithin w tail y₁ y 4 := by
      unfold tail
      wram_exec [hy₁_one, hy₁_ch, hread₁, hm, hf_pk₁, hf_k1]
      rw [← hm]
    have hy_k : y.regs regk = y₁.regs regk + 1 := by simp +decide [y]
    refine ⟨y, 1 + (T₁ + 4), hx₀_go.seq (hloop.seq htail), ?_, by rw [hy_k]; omega, hmem₁,
      by regs_frame⟩
    rw [hy_k, ← hadv₁]
    simp only [hm, ↓reduceIte]
  · let y := ((y₁.set t0 (y₁.regs patBase + y₁.regs regk)).set t0 pat[y₁.regs regk]).set regk 0
    have htail : ExecWithin w tail y₁ y 5 := by
      unfold tail
      wram_exec [hy₁_ch, hread₁, hm, hf_pk₁]
    have hy_k : y.regs regk = 0 := by simp +decide [y]
    refine ⟨y, 1 + (T₁ + 5), hx₀_go.seq (hloop.seq htail), ?_, by rw [hy_k]; omega, hmem₁,
      by regs_frame⟩
    rw [hy_k, ← hadv₁]
    simp only [hm, ↓reduceIte]

/-! ## Execution of `buildPrefixNonempty` and `prefixCode` -/

private def prefixPotential (m : ℕ) (s : Data 15) : ℕ :=
  10 * s.regs regk + 31 * (m - s.regs regidx)

private theorem buildPrefixNonempty_spec {w : ℕ} (pat : List ℕ) (hpos : 0 < pat.length)
    (x : Data 15)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hlen : x.regs patLen = pat.length)
    (hf_pat : Fits w (x.regs patBase + pat.length))
    (hf_pi : Fits w (x.regs piBase + (pat.length - 1)))
    (hpat : Block.HoldsList (x.regs patBase) pat x.mem)
    (hdisj : x.regs patBase + pat.length ≤ x.regs piBase) :
    ∃ y, ExecWithin w buildPrefixNonempty x y (31 * (pat.length - 1) + 5) ∧
      Block.HoldsList (x.regs piBase) (computePrefix pat.toArray).toList y.mem ∧
      (∀ a, (a < x.regs piBase ∨ x.regs piBase + pat.length ≤ a) → y.mem a = x.mem a) ∧
      (∀ r : Fin 15,
        r ≠ regidx → r ≠ regk → r ≠ regch → r ≠ go → r ≠ t0 → y.regs r = x.regs r) := by
  let pb := x.regs patBase
  let pib := x.regs piBase
  let I (s : Data 15) : Prop :=
    s.regs zero = 0 ∧ s.regs one = 1 ∧ s.regs patBase = pb ∧ s.regs patLen = pat.length ∧
      s.regs piBase = pib ∧ 1 ≤ s.regs regidx ∧ s.regs regidx ≤ pat.length ∧
      s.regs regk = borderLen pat (s.regs regidx) ∧
      (∀ j < s.regs regidx, s.mem (pib + j) = borderLen pat (j + 1)) ∧
      (∀ a, (a < pib ∨ pib + pat.length ≤ a) → s.mem a = x.mem a) ∧
      (∀ r : Fin 15,
        r ≠ regidx → r ≠ regk → r ≠ regch → r ≠ go → r ≠ t0 → s.regs r = x.regs r)
  let x₀ := ((x.write pib 0).set regidx 1).set regk 0
  have hinit : ExecWithin (B := .standard) w
      (ram[ *piBase ← zero; regidx ← one; regk ← zero ]) x x₀ 3 := by
    wram_exec [pib, hz, ho]
  have hx₀_I : I x₀ := by
    have hx₀_idx : x₀.regs regidx = 1 := by simp +decide [x₀]
    refine ⟨by simp +decide [x₀, hz], by simp +decide [x₀, ho], by simp +decide [x₀, pb],
      by simp +decide [x₀, hlen], by simp +decide [x₀, pib], by rw [hx₀_idx],
      by rw [hx₀_idx]; exact hpos, ?_, ?_, ?_, ?_⟩
    · rw [hx₀_idx]; simp +decide [x₀, borderLen_one]
    · intro j hj
      rw [hx₀_idx] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [x₀, Data.set_mem, Data.write_mem, Nat.add_zero, Function.update_self,
        Nat.zero_add, borderLen_one]
    · intro a ha
      simp only [x₀, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne (by omega)]
    · intro r hr1 hr2 _ _ _
      simp only [x₀, Data.set_regs, Data.write_regs, Function.update_of_ne hr2,
        Function.update_of_ne hr1]
  have hbody : ∀ s, I s → (Cond.lt regidx patLen).Holds s →
      ∃ z T, ExecWithin w prefixBody s z T ∧ I z ∧
        T + 2 + prefixPotential pat.length z ≤ prefixPotential pat.length s := by
    intro s ⟨sz, so, spb, splen, spib, sq_pos, sq_le, sk, spi_holds, smem_fr, sreg_fr⟩ hc
    let q := s.regs regidx
    have hq_lt : q < pat.length := by simpa only [Cond.holds_lt, splen, q] using hc
    have hpne : pat ≠ [] := List.ne_nil_of_length_pos hpos
    have hk_lt_q : s.regs regk < q := sk ▸ borderLen_lt (by omega) hpne
    have hs_pat : Block.HoldsList pb pat s.mem :=
      hpat.frame fun a ha1 ha2 => smem_fr a (Or.inl (by omega))
    let pi_q : Array ℕ := Array.ofFn (n := q) fun j => borderLen pat (j.val + 1)
    have hpi_q_sz : pi_q.size = q := Array.size_ofFn
    have hpi_q_tab : IsPrefixTableFor pat.toArray pi_q := by
      refine ⟨by rw [hpi_q_sz, List.size_toArray]; omega, fun j hj => ?_⟩
      rw [Array.getElem_ofFn, List.toList_toArray]
    have hpi_q_dec : IsDecreasingTable pi_q := hpi_q_tab.isDecreasingTable
    have hs_pi : Block.HoldsList pib pi_q.toList s.mem := by
      intro i
      have hi_q : i.val < q := by simpa only [Array.length_toList, hpi_q_sz] using i.isLt
      change s.mem (pib + i.val) = pi_q.toList[i.val]
      rw [spi_holds i.val hi_q, Array.getElem_toList, Array.getElem_ofFn]
    have hf_pbq : Fits w (pb + q) := hf_pat.of_le (by omega)
    have hread_q : s.mem (pb + q) = pat[q] := hs_pat.get q hq_lt
    let s₁ := (s.set t0 (pb + q)).set regch pat[q]
    have hpre : ExecWithin w (ram[ t0 ← patBase + regidx; regch ← *t0 ]) s s₁ 2 := by
      wram_exec [spb, q, hread_q, hf_pbq]
    have hs₁_pb : s₁.regs patBase = pb := by simp +decide [s₁, spb]
    have hs₁_pib : s₁.regs piBase = pib := by simp +decide [s₁, spib]
    have hs₁_k : s₁.regs regk = s.regs regk := by simp +decide [s₁]
    have hs₁_ch : s₁.regs regch = pat[q] := by simp +decide [s₁]
    obtain ⟨s₂, T_adv, hadv_exec, hadv_k, hadv_pot, hadv_mem, hadv_fr⟩ :=
      advanceCode_spec pat pi_q hpi_q_dec s₁
        (by simp +decide [s₁, sz])
        (by simp +decide [s₁, so])
        (by rw [hs₁_k]; omega)
        (by rw [hs₁_k, hpi_q_sz]; omega)
        (by rw [hs₁_pb]; exact hf_pat)
        (by rw [hs₁_pib, hpi_q_sz]; exact hf_pi.of_le (by omega))
        (by rw [hs₁_pb]; exact hs_pat)
        (by rw [hs₁_pib]; exact hs_pi)
    rw [hs₁_k, hs₁_ch] at hadv_k
    rw [hs₁_k] at hadv_pot
    have hk'_eq : advance pat.toArray pi_q (s.regs regk) pat[q] = borderLen pat (q + 1) := by
      rw [advance_eq_nextLen pat[q] hpi_q_tab (by rw [hpi_q_sz]; omega)
        (by rw [List.size_toArray]; omega), List.toList_toArray, sk, ← borderLen_succ sq_pos hq_lt]
    have hs₂_k : s₂.regs regk = borderLen pat (q + 1) := hadv_k.trans hk'_eq
    have hs₂_one : s₂.regs one = 1 :=
      (hadv_fr one (by decide) (by decide) (by decide)).trans (by simp +decide [s₁, so])
    have hs₂_pib : s₂.regs piBase = pib :=
      (hadv_fr piBase (by decide) (by decide) (by decide)).trans hs₁_pib
    have hs₂_idx : s₂.regs regidx = q :=
      (hadv_fr regidx (by decide) (by decide) (by decide)).trans (by simp +decide [s₁, q])
    have hf_pibq : Fits w (pib + q) := hf_pi.of_le (by omega)
    have hf_q1 : Fits w (q + 1) := hf_pat.of_le (by omega)
    let z := ((s₂.set t0 (pib + q)).write (pib + q) (s₂.regs regk)).set regidx (q + 1)
    have hpost : ExecWithin w (ram[ t0 ← piBase + regidx; *t0 ← regk; regidx ← regidx + one ])
        s₂ z 3 := by
      wram_exec [hs₂_pib, hs₂_idx, hs₂_one, hf_pibq, hf_q1]
    unfold prefixBody
    have hz_idx : z.regs regidx = q + 1 := by simp +decide [z]
    have hz_k : z.regs regk = s₂.regs regk := by simp +decide [z]
    refine ⟨z, 2 + (T_adv + 3), hpre.seq (hadv_exec.seq hpost), ?_, ?_⟩
    · refine ⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        by rw [hz_idx]; omega, by rw [hz_idx]; omega,
        by rw [hz_k, hz_idx, hs₂_k], ?_, ?_, by regs_frame⟩
      · intro j hj
        rw [hz_idx] at hj
        simp only [z, Data.set_mem, Data.write_mem]
        by_cases hjq : j = q
        · subst hjq
          rw [Function.update_self, hs₂_k]
        · rw [Function.update_of_ne (by omega), hadv_mem]
          exact spi_holds j (by omega)
      · intro a ha
        simp only [z, Data.set_mem, Data.write_mem]
        rw [Function.update_of_ne (by omega), hadv_mem]
        exact smem_fr a ha
    · unfold prefixPotential
      rw [hz_k, hz_idx, hs₂_k, ← hk'_eq, ← hadv_k]
      change 2 + (T_adv + 3) + 2 + (10 * s₂.regs regk + 31 * (pat.length - (q + 1))) ≤
        10 * s.regs regk + 31 * (pat.length - q)
      omega
  obtain ⟨y, hloop, hy_I, hstop⟩ := ExecWithin.loop_potential
    (cond := .lt regidx patLen) (body := prefixBody) I (prefixPotential pat.length) hbody hx₀_I
  obtain ⟨_, _, _, hy_plen, _, _, hy_q_le, _, hy_pi_holds, hy_mem_fr, hy_reg_fr⟩ := hy_I
  have hy_q_eq : y.regs regidx = pat.length := by
    simp only [Cond.holds_lt, hy_plen] at hstop
    omega
  have hpot₀ : prefixPotential pat.length x₀ = 31 * (pat.length - 1) := by
    unfold prefixPotential
    simp +decide [x₀]
  refine ⟨y, (hinit.seq hloop).mono (by rw [hpot₀]; omega), ?_, hy_mem_fr, hy_reg_fr⟩
  intro ⟨iv, hiv⟩
  have hi_len : iv < pat.length := by
    simpa only [Array.length_toList, computePrefix_size, List.size_toArray] using hiv
  have hi_cp : iv < (computePrefix pat.toArray).size := by
    rw [computePrefix_size, List.size_toArray]; exact hi_len
  change y.mem (pib + iv) = (computePrefix pat.toArray).toList[iv]'hiv
  rw [hy_pi_holds iv (by omega), Array.getElem_toList,
    getElem_computePrefix pat.toArray iv hi_cp, List.toList_toArray]

/-- **KMP failure-table construction on the word RAM.** Starting from `Data.init p` at any word
width `w` with `Fits w (2 * p.length + 1)`, `prefixCode` executes within `31 * p.length + 9`
instructions and writes `(computePrefix p.toArray).toList` as the length-prefixed array at
`y.regs Reg.out = p.length + 1`, preserving the input block `[1, 1 + p.length)`. -/
theorem prefixCode_exec {w : ℕ} (p : List ℕ) (hw : Fits w (2 * p.length + 1)) :
    ∃ y, ExecWithin w prefixCode (Data.init p) y (31 * p.length + 9) ∧
      outputList y.mem (y.regs out) = (computePrefix p.toArray).toList ∧
      y.regs out = p.length + 1 ∧
      Fits w (y.regs out + (computePrefix p.toArray).toList.length) ∧
      Block.HoldsList 1 p y.mem := by
  let x : Data 15 := Data.init p
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_m1 : Fits w (p.length + 1) := hw.of_le (by omega)
  have hsetup_spec : ∃ x₁, ExecWithin w (ram[
      zero ← #0;
      one ← #1;
      patLen ← *zero;
      patBase ← one;
      out ← patLen + one;
      *out ← patLen ]) x x₁ 6 ∧
    x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧ x₁.regs patLen = p.length ∧ x₁.regs patBase = 1 ∧
    x₁.regs out = p.length + 1 ∧
    x₁.mem = Function.update x.mem (p.length + 1) p.length := by
    refine WP.exists_execWithin ?_
    wram_exec [x, Data.init_regs, Data.init_mem_zero, hf_1, hf_m1]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x₁, hsetup, hz₁, ho₁, hlen₁, hpb₁, hout₁, hmem₁⟩ := hsetup_spec
  have hpat_init : Block.HoldsList 1 p x.mem := (outputList_eq_iff.mp (outputList_init p)).2
  have hpat₁ : Block.HoldsList 1 p x₁.mem :=
    hpat_init.frame fun a ha1 ha2 => by rw [hmem₁, Function.update_of_ne (by omega)]
  have hcp_len : (computePrefix p.toArray).toList.length = p.length := by
    rw [Array.length_toList, computePrefix_size, List.size_toArray]
  unfold prefixCode
  by_cases hp : 0 < p.length
  · have hc : (Cond.lt zero patLen).Holds x₁ := by simp only [Cond.holds_lt, hz₁, hlen₁]; exact hp
    have hf_m2 : Fits w (p.length + 2) := hw.of_le (by omega)
    let x₂ := x₁.set piBase (p.length + 2)
    have hpib_step : ExecWithin w (ram[ piBase ← out + one ]) x₁ x₂ 1 := by
      have h := ExecWithin.bin (w := w) (f := .add) (d := piBase) (i := out) (j := one) (x := x₁)
        (by simpa only [BinOp.eval, hout₁, ho₁, Nat.add_assoc] using hf_m2)
      simpa only [x₂, BinOp.eval, hout₁, ho₁, Nat.add_assoc] using h
    have hx₂_pb : x₂.regs patBase = 1 := by simp +decide [x₂, hpb₁]
    have hx₂_pib : x₂.regs piBase = p.length + 2 := by simp +decide [x₂]
    obtain ⟨y, hbuild, hy_pi, hy_mem_fr, hy_reg_fr⟩ :=
      buildPrefixNonempty_spec p hp x₂
        (by simp +decide [x₂, hz₁])
        (by simp +decide [x₂, ho₁])
        (by simp +decide [x₂, hlen₁])
        (by rw [hx₂_pb]; exact hw.of_le (by omega))
        (by rw [hx₂_pib]; exact hw.of_le (by omega))
        (by rw [hx₂_pb]; exact hpat₁)
        (by rw [hx₂_pb, hx₂_pib]; omega)
    rw [hx₂_pib] at hy_pi hy_mem_fr
    have hy_out : y.regs out = p.length + 1 :=
      (hy_reg_fr out (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simp +decide [x₂, hout₁])
    have hbranch : ExecWithin w (.branch (.lt zero patLen)
        (.seq (ram[ piBase ← out + one ]) buildPrefixNonempty) (ram[ regk ← zero ]))
        x₁ y (1 + (31 * (p.length - 1) + 5) + 1) :=
      ExecWithin.branch_pos hc (hpib_step.seq hbuild)
    refine ⟨y, (hsetup.seq hbranch).mono (by omega), ?_, hy_out,
      by rw [hy_out, hcp_len]; exact hw.of_le (by omega), ?_⟩
    · rw [hy_out, outputList_eq_iff]
      refine ⟨?_, hy_pi⟩
      rw [hy_mem_fr (p.length + 1) (Or.inl (by omega))]
      simp only [x₂, Data.set_mem, hmem₁, Function.update_self, hcp_len]
    · exact hpat₁.frame fun a ha1 ha2 => by
        rw [hy_mem_fr a (Or.inl (by omega))]
        rfl
  · have hp0 : p.length = 0 := by omega
    have hnil : p = [] := List.eq_nil_of_length_eq_zero hp0
    subst hnil
    have hc : ¬(Cond.lt zero patLen).Holds x₁ := by simp only [Cond.holds_lt, hz₁, hlen₁]; omega
    let y := x₁.set regk 0
    have hnoop : ExecWithin (B := .standard) w (ram[ regk ← zero ]) x₁ y 1 := by
      simpa only [y, hz₁] using ExecWithin.copy (B := .standard) (d := regk) (s := zero) (x := x₁)
    have hy_out : y.regs out = 1 := by simp +decide [y, hout₁]
    refine ⟨y, (hsetup.seq (ExecWithin.branch_neg hc hnoop)).mono (by omega), ?_, hy_out,
      by rw [hy_out, hcp_len]; exact hw.of_le (by omega), hpat₁⟩
    rw [hy_out, outputList_eq_iff]
    have hcp_nil : (computePrefix ([] : List ℕ).toArray).toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [hcp_len, List.length_nil]
    rw [hcp_nil]
    exact ⟨by simp only [y, Data.set_mem, hmem₁, List.length_nil, Function.update_self],
      Block.holdsList_nil _ _⟩

/-- `prefixProgram` computes `(computePrefix p.toArray).toList` in `31 * |p| + 10` instructions on
every fitting word array at every word width fitting `2 * |p| + 1`. -/
theorem prefixProgram_computesListInTime :
    prefixProgram.ComputesListInTime (fun _ p => p) (fun p _ => 31 * p.length + 10)
      (fun p w => Fits w (2 * p.length + 1)) (fun p => (computePrefix p.toArray).toList) :=
  prefixCode.computesListInTime_program out fun p _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _⟩ := prefixCode_exec p hw
    exact ⟨y, hexec, hout, hfit⟩

/-! ## Execution of `searchCode` -/

private theorem init_encode_blocks (I : SearchInput) :
    let x : Data 15 := Data.init I.encode
    x.mem 1 = I.pat.length ∧
      x.mem 2 = I.txt.length ∧
      Block.HoldsList 3 I.pat x.mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt x.mem := by
  dsimp only
  have hm1 : (Data.init I.encode : Data 15).mem 1 = I.pat.length := by
    simpa only [SearchInput.encode, List.getD_cons_zero] using
      Data.init_mem_succ (r := 15) I.encode 0
  have hm2 : (Data.init I.encode : Data 15).mem 2 = I.txt.length := by
    simpa only [SearchInput.encode, List.getD_cons_succ, List.getD_cons_zero] using
      Data.init_mem_succ (r := 15) I.encode 1
  have heq1 : I.encode = [I.pat.length, I.txt.length] ++ (I.pat ++ I.txt) := rfl
  have hpat : Block.HoldsList 3 I.pat (Data.init I.encode : Data 15).mem := by
    rw [heq1]
    exact Data.init_realizes_append [I.pat.length, I.txt.length] I.pat I.txt
  have htxt : Block.HoldsList (3 + I.pat.length) I.txt (Data.init I.encode : Data 15).mem := by
    have heq2 : I.encode = ([I.pat.length, I.txt.length] ++ I.pat) ++ (I.txt ++ []) := by
      simp only [SearchInput.encode, List.cons_append, List.nil_append, List.append_nil]
    have h := Data.init_realizes_append (r := 15) ([I.pat.length, I.txt.length] ++ I.pat) I.txt []
    rw [← heq2] at h
    have hbase : ([I.pat.length, I.txt.length] ++ I.pat).length + 1 = 3 + I.pat.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    intro ⟨k, hk⟩
    have hk_eq := h ⟨k, hk⟩
    change (Data.init I.encode : Data 15).mem
      (([I.pat.length, I.txt.length] ++ I.pat).length + 1 + k) = I.txt[k] at hk_eq
    change (Data.init I.encode : Data 15).mem (3 + I.pat.length + k) = I.txt[k]
    rwa [← hbase]
  exact ⟨hm1, hm2, hpat, htxt⟩

private theorem emptyPatCode_spec {w : ℕ} (txt : List ℕ) (hw : Fits w (2 * txt.length + 4))
    (x : Data 15)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hn : x.regs txtLen = txt.length)
    (hout : x.regs out = 3 + txt.length)
    (htxt : Block.HoldsList 3 txt x.mem) :
    ∃ y, ExecWithin w emptyPatCode x y (6 * txt.length + 11) ∧
      outputList y.mem (y.regs out) = kmpMatchesList [] txt ∧
      (kmpMatchesList [] txt).length = txt.length + 1 ∧
      y.regs out = 3 + txt.length ∧
      Block.HoldsList 3 txt y.mem := by
  have hf_n1 : Fits w (txt.length + 1) := hw.of_le (by omega)
  let x₀ := ((x.set t1 (txt.length + 1)).write (3 + txt.length) (txt.length + 1)).set regidx 0
  have hinit : ExecWithin w (ram[ t1 ← txtLen + one; *out ← t1; regidx ← zero ]) x x₀ 3 := by
    wram_exec [hn, ho, hout, hz, hf_n1]
  let P (j : ℕ) (s : Data 15) : Prop :=
    s.regs one = 1 ∧ s.regs out = 3 + txt.length ∧ s.regs t1 = txt.length + 1 ∧
      s.mem (3 + txt.length) = txt.length + 1 ∧
      (∀ i < j, s.mem (4 + txt.length + i) = i) ∧
      Block.HoldsList 3 txt s.mem
  have hx₀_P : P (x₀.regs regidx) x₀ := by
    refine ⟨by simp +decide [x₀, ho], by simp +decide [x₀, hout], by simp +decide [x₀],
      by simp only [x₀, Data.set_mem, Data.write_mem, Function.update_self],
      fun i hi => by simp +decide [x₀] at hi, ?_⟩
    exact htxt.frame fun a ha1 ha2 => by
      simp only [x₀, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne (by omega)]
  have hbody (s : Data 15) (hs : P (s.regs regidx) s) (hlt : s.regs regidx < txt.length + 1) :
      ∃ z, ExecWithin w emptyPatBody s z 4 ∧ P (s.regs regidx + 1) z ∧
        z.regs regidx = s.regs regidx + 1 := by
    obtain ⟨so, sout, st1, shdr, svals, stxt⟩ := hs
    let j := s.regs regidx
    have hf_o1 : Fits w (3 + txt.length + 1) := hw.of_le (by omega)
    have hf_addr : Fits w (3 + txt.length + 1 + j) := hw.of_le (by omega)
    have hf_j1 : Fits w (j + 1) := hw.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold emptyPatBody
    wram_exec [so, sout, hf_o1, hf_addr, hf_j1]
    refine ⟨⟨by wram_simp [so], by wram_simp [sout], by wram_simp [st1], ?_, ?_, ?_⟩,
      by wram_simp⟩
    · wram_simp [shdr]
    · intro i hi
      by_cases hij : i = j
      · subst hij
        wram_simp
        rfl
      · wram_simp
        exact svals i (by omega)
    · exact stxt.frame fun a ha1 ha2 => by wram_simp
  have hx₀_idx : x₀.regs regidx = 0 := by simp +decide [x₀]
  obtain ⟨y, hloop, ⟨_, hy_out, _, hy_hdr, hy_vals, hy_txt⟩, _⟩ :=
    ExecWithin.loop_count P (fun _ hs => hs.2.2.1) hbody (by rw [hx₀_idx]; omega) hx₀_P
  rw [hx₀_idx] at hloop
  have hmatches_nil : kmpMatchesList ([] : List ℕ) txt = List.range (txt.length + 1) := by
    refine (pairwise_lt_kmpMatchesList [] txt).eq_of_mem_iff List.pairwise_lt_range fun s => ?_
    rw [mem_kmpMatchesList_iff, List.mem_range]
    exact ⟨fun ⟨hle, _⟩ => by omega, fun hlt => ⟨by omega, List.nil_prefix⟩⟩
  unfold emptyPatCode
  refine ⟨y, (hinit.seq hloop).mono (by omega), ?_,
    by rw [hmatches_nil, List.length_range], hy_out, hy_txt⟩
  rw [hy_out, hmatches_nil, outputList_eq_iff]
  refine ⟨by rw [hy_hdr, List.length_range], fun i => ?_⟩
  have hi : i.val < txt.length + 1 := by simpa only [List.length_range] using i.isLt
  change y.mem (3 + txt.length + 1 + i.val) = (List.range (txt.length + 1))[i.val]
  rw [show 3 + txt.length + 1 + i.val = 4 + txt.length + i.val by omega, hy_vals i.val hi,
    List.getElem_range]

private def searchPotential (n : ℕ) (s : Data 15) : ℕ :=
  10 * s.regs regk + 37 * (n - s.regs regidx)

private theorem maxPrefixSuffixUpTo_take_zero (pat txt : List ℕ) (B : ℕ) :
    0 = maxPrefixSuffixUpTo pat (txt.take 0) B := by
  apply eq_maxPrefixSuffixUpTo_iff.mpr
  refine ⟨Nat.zero_le _, Nat.zero_le _, List.nil_suffix, fun k hk_pos _ _ hsuf => ?_⟩
  simp only [List.take_zero] at hsuf
  have hlen := hsuf.length_le
  simp only [List.length_take, List.length_nil] at hlen
  omega

private structure SearchRegs (I : SearchInput) (s : Data 15) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  pb_eq : s.regs patBase = 3
  pm_eq : s.regs patLen = I.pat.length
  tb_eq : s.regs txtBase = 3 + I.pat.length
  tn_eq : s.regs txtLen = I.txt.length
  pib_eq : s.regs piBase = 3 + I.pat.length + I.txt.length
  out_eq : s.regs out = 3 + 2 * I.pat.length + I.txt.length

private structure SearchInv (I : SearchInput) (pi : Array ℕ) (s : Data 15) : Prop where
  regs_ok : SearchRegs I s
  idx_le : s.regs regidx ≤ I.txt.length
  oc_le : s.regs outCnt ≤ s.regs regidx
  k_eq : s.regs regk = maxPrefixSuffixUpTo I.pat (I.txt.take (s.regs regidx)) (I.pat.length - 1)
  pat_holds : Block.HoldsList 3 I.pat s.mem
  txt_holds : Block.HoldsList (3 + I.pat.length) I.txt s.mem
  pi_holds : Block.HoldsList (3 + I.pat.length + I.txt.length) pi.toList s.mem
  matches_ex : ∃ ms : List ℕ, s.regs outCnt = ms.length ∧
    Block.HoldsList (3 + 2 * I.pat.length + I.txt.length + 1) ms s.mem ∧
    ms.Pairwise (· < ·) ∧
    (∀ sh, sh ∈ ms ↔ sh + I.pat.length ≤ s.regs regidx ∧ IsMatchAt I.pat.toArray I.txt.toArray sh)

private theorem searchPostBranch_full_step {w : ℕ} (I : SearchInput) (hp : 0 < I.pat.length)
    (hw : Fits w (2 * I.pat.length + 2 * I.txt.length + 4))
    (pi : Array ℕ) (hpi_idx : I.pat.length - 1 < pi.size)
    (s₂ : Data 15) (hr₂ : SearchRegs I s₂)
    (hi_lt : s₂.regs regidx < I.txt.length)
    (hoc_le : s₂.regs outCnt ≤ s₂.regs regidx)
    (hfull : s₂.regs regk = I.pat.length)
    (hm_le_i1 : I.pat.length ≤ s₂.regs regidx + 1)
    (hread_pi_last : s₂.mem (3 + I.pat.length + I.txt.length + (I.pat.length - 1)) =
      pi[I.pat.length - 1]'hpi_idx) :
    ∃ z, ExecWithin w searchPostBranch s₂ z 9 ∧
      SearchRegs I z ∧
      z.regs regidx = s₂.regs regidx + 1 ∧
      z.regs outCnt = s₂.regs outCnt + 1 ∧
      z.regs regk = pi[I.pat.length - 1]'hpi_idx ∧
      z.mem = Function.update s₂.mem
        (3 + 2 * I.pat.length + I.txt.length + 1 + s₂.regs outCnt)
        (s₂.regs regidx + 1 - I.pat.length) := by
  have hf_i1 : Fits w (s₂.regs regidx + 1) := hw.of_le (by omega)
  have hf_shift : Fits w (s₂.regs regidx + 1 - I.pat.length) := hw.of_le (by omega)
  have hf_oc1 : Fits w (s₂.regs outCnt + 1) := hw.of_le (by omega)
  have hf_out_oc : Fits w (3 + 2 * I.pat.length + I.txt.length + (s₂.regs outCnt + 1)) :=
    hw.of_le (by omega)
  have hf_mm1 : Fits w (I.pat.length - 1) := hw.of_le (by omega)
  have hf_pibm : Fits w (3 + I.pat.length + I.txt.length + (I.pat.length - 1)) :=
    hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold searchPostBranch
  wram_exec [hr₂.one_eq, hr₂.pm_eq, hr₂.pib_eq, hr₂.out_eq, hfull, hread_pi_last,
    hf_i1, hf_shift, hf_oc1, hf_out_oc, hf_mm1, hf_pibm]
  refine ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp, ?_⟩
  wram_simp
  congr 1
  omega

private theorem searchPostBranch_nonfull_step {w : ℕ} (I : SearchInput)
    (hw : Fits w (2 * I.pat.length + 2 * I.txt.length + 4))
    (s₂ : Data 15) (hr₂ : SearchRegs I s₂)
    (hi_lt : s₂.regs regidx < I.txt.length)
    (hkne : s₂.regs regk ≠ I.pat.length) :
    ∃ z, ExecWithin w searchPostBranch s₂ z 3 ∧
      SearchRegs I z ∧
      z.regs regidx = s₂.regs regidx + 1 ∧
      z.regs outCnt = s₂.regs outCnt ∧
      z.regs regk = s₂.regs regk ∧
      z.mem = s₂.mem := by
  have hf_i1 : Fits w (s₂.regs regidx + 1) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold searchPostBranch
  wram_exec [hr₂.one_eq, hr₂.pm_eq, hkne, hf_i1]
  exact ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩

private theorem searchBody_spec {w : ℕ} (I : SearchInput) (hp : 0 < I.pat.length)
    (hw : Fits w (2 * I.pat.length + 2 * I.txt.length + 4))
    (pi : Array ℕ) (hpi_sz : pi.size = I.pat.length)
    (hpi_tab : IsPrefixTableFor I.pat.toArray pi) (hpi_dec : IsDecreasingTable pi)
    (s : Data 15) (hs : SearchInv I pi s) (hc : (Cond.lt regidx txtLen).Holds s) :
    ∃ z T, ExecWithin w searchBody s z T ∧ SearchInv I pi z ∧
      T + 2 + searchPotential I.txt.length z ≤ searchPotential I.txt.length s := by
  obtain ⟨hrs, si_le, soc_le, sk, spat, stxt_s, spi_s,
    ⟨ms, soc_ms, sms_holds, sms_pw, sms_mem⟩⟩ := hs
  have hi_lt : s.regs regidx < I.txt.length := by simpa only [Cond.holds_lt, hrs.tn_eq] using hc
  have hi_arr : s.regs regidx < I.txt.toArray.size := by rw [List.size_toArray]; exact hi_lt
  have hk_lt_m : s.regs regk < I.pat.length := by
    rw [sk]
    exact Nat.lt_of_le_of_lt (maxPrefixSuffixUpTo_le_bound I.pat (I.txt.take (s.regs regidx))
      (I.pat.length - 1)) (Nat.sub_lt hp Nat.one_pos)
  have hf_tbi : Fits w (3 + I.pat.length + s.regs regidx) :=
    hw.of_le (by clear sk sms_mem hpi_tab hpi_dec; omega)
  have hread_txt : s.mem (3 + I.pat.length + s.regs regidx) = I.txt[s.regs regidx] :=
    stxt_s.get (s.regs regidx) hi_lt
  have hpre_ex : ∃ s₁ : Data 15,
      ExecWithin w (ram[ t0 ← txtBase + regidx; regch ← *t0 ]) s s₁ 2 ∧
      SearchRegs I s₁ ∧ s₁.regs regidx = s.regs regidx ∧
      s₁.regs outCnt = s.regs outCnt ∧ s₁.regs regk = s.regs regk ∧
      s₁.regs regch = I.txt[s.regs regidx] ∧ s₁.mem = s.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hrs.tb_eq, hread_txt, hf_tbi]
    exact ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp, by wram_simp, rfl⟩
  obtain ⟨s₁, hpre, hr₁, hs₁_idx, hs₁_oc, hs₁_k, hs₁_ch, hs₁_mem⟩ := hpre_ex
  obtain ⟨s₂, T_adv, hadv_exec, hadv_k, hadv_pot, hadv_mem, hadv_fr⟩ :=
    advanceCode_spec I.pat pi hpi_dec s₁
      hr₁.zero_eq hr₁.one_eq
      (by rw [hs₁_k]; exact hk_lt_m)
      (by rw [hs₁_k, hpi_sz]; exact Nat.le_of_lt hk_lt_m)
      (by rw [hr₁.pb_eq]; exact hw.of_le (by clear sk sms_mem hpi_tab hpi_dec hs₁_ch; omega))
      (by
        rw [hr₁.pib_eq, hpi_sz]
        exact hw.of_le (by clear sk sms_mem hpi_tab hpi_dec hs₁_ch; omega))
      (by rw [hr₁.pb_eq, hs₁_mem]; exact spat)
      (by rw [hr₁.pib_eq, hs₁_mem]; exact spi_s)
  rw [hs₁_k, hs₁_ch] at hadv_k
  rw [hs₁_k] at hadv_pot
  rw [hs₁_mem] at hadv_mem
  have hr₂ : SearchRegs I s₂ := by regs_frame
  have hs₂_idx : s₂.regs regidx = s.regs regidx := by regs_frame
  have hs₂_oc : s₂.regs outCnt = s.regs outCnt := by regs_frame
  have hk'_max : s₂.regs regk =
      maxPrefixSuffixUpTo I.pat (I.txt.take (s.regs regidx + 1)) I.pat.length := by
    rw [hadv_k]
    exact advance_eq_maxPrefixSuffixUpTo_take_succ (p := I.pat.toArray) (t := I.txt.toArray)
      (by rw [List.size_toArray]; exact hp) (by rw [List.size_toArray]; exact hpi_sz)
      hpi_tab hi_arr sk
  unfold searchBody
  by_cases hfull : s₂.regs regk = I.pat.length
  · have hpsuf : I.pat.toArray.toList <:+ I.txt.toArray.toList.take (s.regs regidx + 1) := by
      have h := take_maxPrefixSuffixUpTo_isSuffix I.pat (I.txt.take (s.regs regidx + 1))
        I.pat.length
      rwa [← hk'_max, hfull, List.take_length] at h
    obtain ⟨hm_le_i1, hmatch_here⟩ := (toList_isSuffix_take_iff_isMatchAt hi_arr).mp hpsuf
    rw [List.size_toArray] at hm_le_i1 hmatch_here
    have hpi_idx : I.pat.length - 1 < pi.size := by rw [hpi_sz]; exact Nat.sub_lt hp Nat.one_pos
    have hpi_list_idx : I.pat.length - 1 < pi.toList.length := by
      simpa only [Array.length_toList] using hpi_idx
    have hread_pi_last : s₂.mem (3 + I.pat.length + I.txt.length + (I.pat.length - 1)) =
        pi[I.pat.length - 1]'hpi_idx := by
      rw [hadv_mem]
      have h1 := spi_s.get (I.pat.length - 1) hpi_list_idx
      rwa [Array.getElem_toList] at h1
    have hk_reset_le : pi[I.pat.length - 1]'hpi_idx ≤ I.pat.length - 1 :=
      hpi_dec (I.pat.length - 1) hpi_idx
    have hk_reset_eq : pi[I.pat.length - 1]'hpi_idx =
        maxPrefixSuffixUpTo I.pat (I.txt.take (s.regs regidx + 1)) (I.pat.length - 1) := by
      rw [hpi_tab.2 (I.pat.length - 1) hpi_idx, List.toList_toArray, Nat.sub_add_cancel hp,
        ← maxPrefixSuffixUpTo_pred_of_eq_length hp (hk'_max.symm.trans hfull)]
    obtain ⟨z, hpost, hrz, zidx, zoc, zk, zmem⟩ :=
      searchPostBranch_full_step I hp hw pi hpi_idx s₂ hr₂
        (hs₂_idx ▸ hi_lt) (hs₂_oc.trans_le (hs₂_idx.symm ▸ soc_le)) hfull
        (hs₂_idx ▸ hm_le_i1) hread_pi_last
    rw [hs₂_idx] at zidx zmem
    rw [hs₂_oc] at zoc zmem
    refine ⟨z, 2 + (T_adv + 9), hpre.seq (hadv_exec.seq hpost), ?_, ?_⟩
    · refine ⟨hrz, zidx ▸ Nat.succ_le_of_lt hi_lt,
        by rw [zoc, zidx]; exact Nat.add_le_add_right soc_le 1,
        by rw [zk, zidx, hk_reset_eq], ?_, ?_, ?_,
        ⟨ms ++ [s.regs regidx + 1 - I.pat.length], ?_, ?_, ?_, ?_⟩⟩
      · exact spat.frame fun a ha1 ha2 => by
          rw [zmem, hadv_mem, Function.update_of_ne]
          clear sk hk'_max hk_reset_eq hpsuf hmatch_here sms_mem hpi_tab hpi_dec hs₁_ch hread_txt
            hadv_k
          omega
      · exact stxt_s.frame fun a ha1 ha2 => by
          rw [zmem, hadv_mem, Function.update_of_ne]
          clear sk hk'_max hk_reset_eq hpsuf hmatch_here sms_mem hpi_tab hpi_dec hs₁_ch hread_txt
            hadv_k
          omega
      · exact spi_s.frame fun a ha1 ha2 => by
          rw [Array.length_toList, hpi_sz] at ha2
          rw [zmem, hadv_mem, Function.update_of_ne]
          clear sk hk'_max hk_reset_eq hpsuf hmatch_here sms_mem hpi_tab hpi_dec hs₁_ch hread_txt
            hadv_k
          omega
      · rw [zoc, soc_ms, List.length_append, List.length_singleton]
      · rw [zmem, hadv_mem, soc_ms]
        exact sms_holds.append_one (s.regs regidx + 1 - I.pat.length)
      · rw [List.pairwise_append]
        refine ⟨sms_pw, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb
        subst hb
        obtain ⟨ha_le, _⟩ := (sms_mem a).mp ha
        clear sk hk'_max hk_reset_eq hpsuf hmatch_here sms_mem hpi_tab hpi_dec hs₁_ch hread_txt
          hadv_k
        omega
      · intro sh
        rw [zidx, List.mem_append, List.mem_singleton, sms_mem]
        constructor
        · rintro (⟨hle, hm⟩ | rfl)
          · exact ⟨Nat.le_succ_of_le hle, hm⟩
          · exact ⟨Nat.le_of_eq (Nat.sub_add_cancel hm_le_i1), hmatch_here⟩
        · rintro ⟨hle, hm⟩
          rcases Nat.eq_or_lt_of_le hle with heq | hlt
          · right
            exact Nat.eq_sub_of_add_eq heq
          · left
            exact ⟨Nat.le_of_lt_succ hlt, hm⟩
    · unfold searchPotential
      rw [zk, zidx]
      have hle_k : pi[I.pat.length - 1]'hpi_idx ≤ s₂.regs regk :=
        Nat.le_trans hk_reset_le (hfull ▸ Nat.sub_le _ _)
      clear sk hk'_max hk_reset_eq hpsuf hmatch_here sms_mem hpi_tab hpi_dec hs₁_ch hread_txt
        hadv_k hread_pi_last hk_reset_le
      omega
  · have hk'_le_m : s₂.regs regk ≤ I.pat.length := by
      rw [hk'_max]
      exact maxPrefixSuffixUpTo_le_length I.pat (I.txt.take (s.regs regidx + 1)) I.pat.length
    have hk'_lt_m : maxPrefixSuffixUpTo I.pat (I.txt.take (s.regs regidx + 1)) I.pat.length <
        I.pat.length :=
      Nat.lt_of_le_of_ne (hk'_max ▸ hk'_le_m) (hk'_max ▸ hfull)
    have hk'_pred : s₂.regs regk =
        maxPrefixSuffixUpTo I.pat (I.txt.take (s.regs regidx + 1)) (I.pat.length - 1) := by
      rw [hk'_max, maxPrefixSuffixUpTo_pred_of_lt_length hk'_lt_m]
    have hnot_suf : ¬(I.pat.toArray.toList <:+ I.txt.toArray.toList.take (s.regs regidx + 1)) := by
      intro hsuf
      have hle := le_maxPrefixSuffixUpTo (B := I.pat.length) (Nat.le_refl _) (Nat.le_refl _)
        (by simpa only [List.take_length] using hsuf)
      exact Nat.not_le.mpr hk'_lt_m hle
    obtain ⟨z, hpost, hrz, zidx, zoc, zk, zmem⟩ :=
      searchPostBranch_nonfull_step I hw s₂ hr₂ (hs₂_idx ▸ hi_lt) hfull
    rw [hs₂_idx] at zidx
    rw [hs₂_oc] at zoc
    rw [hadv_mem] at zmem
    refine ⟨z, 2 + (T_adv + 3), hpre.seq (hadv_exec.seq hpost), ?_, ?_⟩
    · refine ⟨hrz, zidx ▸ Nat.succ_le_of_lt hi_lt,
        by rw [zoc, zidx]; exact Nat.le_succ_of_le soc_le,
        by rw [zk, zidx, hk'_pred],
        zmem ▸ spat, zmem ▸ stxt_s, zmem ▸ spi_s, ⟨ms, zoc.trans soc_ms,
        zmem ▸ sms_holds, sms_pw, fun sh => ?_⟩⟩
      rw [zidx, sms_mem]
      constructor
      · rintro ⟨hle, hm⟩
        exact ⟨Nat.le_succ_of_le hle, hm⟩
      · rintro ⟨hle, hm⟩
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · exfalso
          have hm_le : I.pat.length ≤ s.regs regidx + 1 := heq ▸ Nat.le_add_left _ _
          have hsh : sh = s.regs regidx + 1 - I.pat.length := Nat.eq_sub_of_add_eq heq
          subst hsh
          exact hnot_suf ((toList_isSuffix_take_iff_isMatchAt hi_arr).mpr
            ⟨by rw [List.size_toArray]; exact hm_le, hm⟩)
        · exact ⟨Nat.le_of_lt_succ hlt, hm⟩
    · unfold searchPotential
      rw [zk, zidx]
      clear sk hk'_max hk'_lt_m hk'_pred hnot_suf sms_mem hpi_tab hpi_dec hs₁_ch hread_txt hadv_k
      omega

private theorem nonemptyPatCode_spec {w : ℕ} (I : SearchInput) (hp : 0 < I.pat.length)
    (hw : Fits w (2 * I.pat.length + 2 * I.txt.length + 4))
    (x : Data 15) (hrx : SearchRegs I x)
    (hpat : Block.HoldsList 3 I.pat x.mem)
    (htxt : Block.HoldsList (3 + I.pat.length) I.txt x.mem) :
    ∃ y, ExecWithin w nonemptyPatCode x y (31 * I.pat.length + 37 * I.txt.length + 11) ∧
      outputList y.mem (y.regs out) = kmpMatchesList I.pat I.txt ∧
      (kmpMatchesList I.pat I.txt).length ≤ I.txt.length ∧
      y.regs out = 3 + 2 * I.pat.length + I.txt.length ∧
      Block.HoldsList 3 I.pat y.mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt y.mem := by
  obtain ⟨y₁, hbuild, hpi_holds₁, hmem_fr₁, hreg_fr₁⟩ :=
    buildPrefixNonempty_spec I.pat hp x hrx.zero_eq hrx.one_eq hrx.pm_eq
      (by rw [hrx.pb_eq]; exact hw.of_le (by omega))
      (by rw [hrx.pib_eq]; exact hw.of_le (by omega))
      (by rw [hrx.pb_eq]; exact hpat)
      (by rw [hrx.pb_eq, hrx.pib_eq]; omega)
  rw [hrx.pib_eq] at hpi_holds₁ hmem_fr₁
  have hry₁ : SearchRegs I y₁ := by regs_frame
  have hpat₁ : Block.HoldsList 3 I.pat y₁.mem :=
    hpat.frame fun a ha1 ha2 => hmem_fr₁ a (Or.inl (by omega))
  have htxt₁ : Block.HoldsList (3 + I.pat.length) I.txt y₁.mem :=
    htxt.frame fun a ha1 ha2 => hmem_fr₁ a (Or.inl (by omega))
  have hprep_ex : ∃ y₂ : Data 15,
      ExecWithin (B := .standard) w
        (ram[ outCnt ← zero; regidx ← zero; regk ← zero ]) y₁ y₂ 3 ∧
      SearchRegs I y₂ ∧
      y₂.regs regidx = 0 ∧ y₂.regs outCnt = 0 ∧ y₂.regs regk = 0 ∧
      y₂.mem = y₁.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hry₁.zero_eq]
    exact ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₂, hprep, hry₂, hy₂_idx, hy₂_oc, hy₂_k, hy₂_mem⟩ := hprep_ex
  generalize hpi_def : computePrefix I.pat.toArray = pi
  rw [hpi_def] at hpi_holds₁
  have hpi_sz : pi.size = I.pat.length := by
    rw [← hpi_def, computePrefix_size, List.size_toArray]
  have hpi_tab : IsPrefixTableFor I.pat.toArray pi :=
    hpi_def ▸ (isPrefixTableFor_computePrefix _).2
  have hpi_dec : IsDecreasingTable pi := hpi_def ▸ isDecreasingTable_computePrefix _
  have hy₂_Inv : SearchInv I pi y₂ := by
    refine ⟨hry₂,
      by rw [hy₂_idx]; exact Nat.zero_le _, by rw [hy₂_oc, hy₂_idx],
      by rw [hy₂_k, hy₂_idx]; exact maxPrefixSuffixUpTo_take_zero I.pat I.txt (I.pat.length - 1),
      hy₂_mem ▸ hpat₁, hy₂_mem ▸ htxt₁, hy₂_mem ▸ hpi_holds₁,
      ⟨[], hy₂_oc, Block.holdsList_nil _ _, List.Pairwise.nil, fun sh => ?_⟩⟩
    rw [hy₂_idx]
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨hle, -⟩
    exact absurd (Nat.lt_of_lt_of_le hp (Nat.le_trans (Nat.le_add_left _ _) hle)) (Nat.lt_irrefl 0)
  obtain ⟨y₃, hloop, hy₃_Inv, hstop⟩ := ExecWithin.loop_potential
    (cond := .lt regidx txtLen) (body := searchBody) (SearchInv I pi)
    (searchPotential I.txt.length)
    (fun s hs hc => searchBody_spec I hp hw pi hpi_sz hpi_tab hpi_dec s hs hc) hy₂_Inv
  obtain ⟨hry₃, hy₃_i_le, hy₃_oc_le, _, hy₃_pat, hy₃_txt, _,
    ⟨ms, hy₃_oc, hy₃_ms_holds, hy₃_ms_pw, hy₃_ms_mem⟩⟩ := hy₃_Inv
  have hy₃_i_eq : y₃.regs regidx = I.txt.length := by
    simp only [Cond.holds_lt, hry₃.tn_eq] at hstop
    exact Nat.le_antisymm hy₃_i_le (Nat.not_lt.mp hstop)
  rw [hy₃_i_eq] at hy₃_ms_mem hy₃_oc_le
  have hms_eq : ms = kmpMatchesList I.pat I.txt := by
    refine hy₃_ms_pw.eq_of_mem_iff (pairwise_lt_kmpMatchesList I.pat I.txt) fun sh => ?_
    rw [hy₃_ms_mem, kmpMatchesList, mem_kmpMatches_iff]
    refine ⟨fun ⟨_, hm⟩ => hm, fun hm => ⟨?_, hm⟩⟩
    have hle := hm.1
    simpa only [List.size_toArray] using hle
  let outAddr := 3 + 2 * I.pat.length + I.txt.length
  let y := y₃.write outAddr (y₃.regs outCnt)
  have hfin : ExecWithin (B := .standard) w (ram[ *out ← outCnt ]) y₃ y 1 := by
    simpa only [y, hry₃.out_eq] using ExecWithin.store (B := .standard) (a := out) (s := outCnt)
      (x := y₃)
  have hpot₂ : searchPotential I.txt.length y₂ = 37 * I.txt.length := by
    unfold searchPotential
    rw [hy₂_k, hy₂_idx, Nat.sub_zero, Nat.mul_zero, Nat.zero_add]
  have htotal_time : (31 * (I.pat.length - 1) + 5) +
      (3 + ((37 * I.txt.length + 2) + 1)) ≤ 31 * I.pat.length + 37 * I.txt.length + 11 := by
    clear hpi_def hpi_tab hpi_dec hy₃_ms_mem hms_eq
    omega
  unfold nonemptyPatCode
  refine ⟨y, (hbuild.seq (hprep.seq (hloop.seq hfin))).mono (by rw [hpot₂]; exact htotal_time),
    ?_, by rw [← hms_eq, ← hy₃_oc]; exact hy₃_oc_le, by simp +decide [y, hry₃.out_eq], ?_, ?_⟩
  · simp only [y, Data.write_regs, hry₃.out_eq]
    rw [← hms_eq, outputList_eq_iff]
    refine ⟨by simp only [Data.write_mem, outAddr, Function.update_self, hy₃_oc], ?_⟩
    exact hy₃_ms_holds.frame fun a ha1 ha2 => by
      simp only [Data.write_mem, outAddr]
      rw [Function.update_of_ne]
      clear hpi_def hpi_tab hpi_dec hy₃_ms_mem hms_eq
      omega
  · exact hy₃_pat.frame fun a ha1 ha2 => by
      simp only [y, Data.write_mem, outAddr]
      rw [Function.update_of_ne]
      clear hpi_def hpi_tab hpi_dec hy₃_ms_mem hms_eq
      omega
  · exact hy₃_txt.frame fun a ha1 ha2 => by
      simp only [y, Data.write_mem, outAddr]
      rw [Function.update_of_ne]
      clear hpi_def hpi_tab hpi_dec hy₃_ms_mem hms_eq
      omega

/-- **End-to-end KMP pattern search on the word RAM.** Starting from `Data.init I.encode` at any
word width `w` with `Fits w (2 * I.pat.length + 2 * I.txt.length + 4)`, `searchCode` executes
within `31 * I.pat.length + 37 * I.txt.length + 22` instructions and writes
`kmpMatchesList I.pat I.txt` as the length-prefixed array at
`y.regs Reg.out = 3 + 2 * I.pat.length + I.txt.length`, preserving the pattern and text blocks at
`[3, 3 + I.pat.length)` and `[3 + I.pat.length, 3 + I.pat.length + I.txt.length)`. -/
theorem searchCode_exec {w : ℕ} (I : SearchInput)
    (hw : Fits w (2 * I.pat.length + 2 * I.txt.length + 4)) :
    ∃ y, ExecWithin w searchCode (Data.init I.encode) y
        (31 * I.pat.length + 37 * I.txt.length + 22) ∧
      outputList y.mem (y.regs out) = kmpMatchesList I.pat I.txt ∧
      y.regs out = 3 + 2 * I.pat.length + I.txt.length ∧
      Fits w (y.regs out + (kmpMatchesList I.pat I.txt).length) ∧
      Block.HoldsList 3 I.pat y.mem ∧
      Block.HoldsList (3 + I.pat.length) I.txt y.mem := by
  let x : Data 15 := Data.init I.encode
  obtain ⟨hm1, hm2, hpat, htxt⟩ := init_encode_blocks I
  have hf_1 : Fits w 1 := hw.of_le (by omega)
  have hf_2 : Fits w 2 := hw.of_le (by omega)
  have hf_3 : Fits w 3 := hw.of_le (by omega)
  have hf_tb : Fits w (3 + I.pat.length) := hw.of_le (by omega)
  have hf_pib : Fits w (3 + I.pat.length + I.txt.length) := hw.of_le (by omega)
  have hf_out : Fits w (3 + I.pat.length + I.txt.length + I.pat.length) := hw.of_le (by omega)
  have hsetup_spec : ∃ x₁, ExecWithin w searchSetup x x₁ 9 ∧
      SearchRegs I x₁ ∧ x₁.mem = x.mem := by
    refine WP.exists_execWithin ?_
    unfold searchSetup
    wram_exec [x, Data.init_regs, hm1, hm2, hf_1, hf_2, hf_3, hf_tb, hf_pib, hf_out]
    exact ⟨⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp; omega⟩, rfl⟩
  obtain ⟨x₁, hsetup, hrx₁, hmem₁⟩ := hsetup_spec
  unfold searchCode
  by_cases hp : 0 < I.pat.length
  · have hc : (Cond.lt zero patLen).Holds x₁ := by
      simp only [Cond.holds_lt, hrx₁.zero_eq, hrx₁.pm_eq]; exact hp
    obtain ⟨y, hne, hy_out_list, hlen_le, hy_out, hy_pat, hy_txt⟩ :=
      nonemptyPatCode_spec I hp hw x₁ hrx₁ (hmem₁ ▸ hpat) (hmem₁ ▸ htxt)
    have hfit_out : Fits w (y.regs out + (kmpMatchesList I.pat I.txt).length) := by
      rw [hy_out]
      refine hw.of_le (Nat.le_trans (Nat.add_le_add_left hlen_le _) ?_)
      clear hlen_le hy_out_list; omega
    refine ⟨y, (hsetup.seq (ExecWithin.branch_pos hc hne)).mono
      (by clear hlen_le hy_out_list hfit_out; omega),
      hy_out_list, hy_out, hfit_out, hy_pat, hy_txt⟩
  · have hp0 : I.pat.length = 0 := Nat.eq_zero_of_not_pos hp
    have hpnil : I.pat = [] := List.eq_nil_of_length_eq_zero hp0
    have hc : ¬(Cond.lt zero patLen).Holds x₁ := by
      simp only [Cond.holds_lt, hrx₁.zero_eq, hrx₁.pm_eq, hp0]; exact Nat.not_lt_zero 0
    have htxt0 : Block.HoldsList 3 I.txt x₁.mem := by
      rw [hmem₁]
      simpa only [hp0, Nat.add_zero] using htxt
    obtain ⟨y, hemp, hy_out_list, hlen_eq, hy_out, hy_txt⟩ :=
      emptyPatCode_spec I.txt (hw.of_le (by omega)) x₁ hrx₁.zero_eq hrx₁.one_eq hrx₁.tn_eq
        (by rw [hrx₁.out_eq, hp0]) htxt0
    rw [← hpnil] at hy_out_list hlen_eq
    have hy_out' : y.regs out = 3 + 2 * I.pat.length + I.txt.length := by
      rw [hy_out, hp0]
    have hy_pat : Block.HoldsList 3 I.pat y.mem := by
      rw [hpnil]; exact Block.holdsList_nil _ _
    have hy_txt' : Block.HoldsList (3 + I.pat.length) I.txt y.mem := by
      simpa only [hp0, Nat.add_zero] using hy_txt
    have hfit_out : Fits w (y.regs out + (kmpMatchesList I.pat I.txt).length) := by
      rw [hy_out', hlen_eq]
      exact hw.of_le (by clear hlen_eq hy_out_list; omega)
    refine ⟨y, (hsetup.seq (ExecWithin.branch_neg hc hemp)).mono
      (by clear hlen_eq hy_out_list hfit_out; omega),
      hy_out_list, hy_out', hfit_out, hy_pat, hy_txt'⟩

/-- `searchProgram` computes `kmpMatchesList I.pat I.txt` in
`31 * |I.pat| + 37 * |I.txt| + 23` instructions on every fitting `SearchInput` at every word width
fitting `2 * |I.pat| + 2 * |I.txt| + 4`. -/
theorem searchProgram_computesListInTime :
    searchProgram.ComputesListInTime (fun _ (I : SearchInput) => I.encode)
      (fun I _ => 31 * I.pat.length + 37 * I.txt.length + 23)
      (fun I w => Fits w (2 * I.pat.length + 2 * I.txt.length + 4))
      (fun I => kmpMatchesList I.pat I.txt) :=
  searchCode.computesListInTime_program out fun I _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _, _⟩ := searchCode_exec I hw
    exact ⟨y, hexec, hout, hfit⟩

end Cslib.Algorithms.WordRAM.KMP
