/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Palindrome.Manacher
public import CslibFrontier.Computability.WordRAM.Copy
public import CslibFrontier.Computability.WordRAM.ListOutput

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Manacher's Algorithm in Linear Time on the Word RAM

This module implements Manacher's algorithm (`[Manacher1975]`; all-centers formulation as in
`[ApostolicoBreslauerGalil1995]`, Section 1) as fixed `Basis.standard` word-RAM programs over word
arrays (`State.init xs`), proving linear `O(|xs|)` instruction bounds:

* `radiiCode` and `radiiProgram` compute the length-prefixed list of all `2 * |xs| + 1` maximal
  palindromic radii `(manacher xs.toArray).toList` at address `|xs| + 1` within `87 * |xs| + 16`
  instructions whenever `Fits w (3 * |xs| + 2)` and `InputFits w xs` hold.
* `longestCode` and `longestProgram` additionally scan the computed radii to locate
  `bestCenter xs` and `longestPalindromeSpan xs.toArray` in registers `(regl, regr)` and copy the
  factor to a length-prefixed block at address `3 * |xs| + 3`, returning `longestPalindrome xs`
  within `116 * |xs| + 37` instructions whenever `Fits w (4 * |xs| + 4)` and `InputFits w xs` hold.

Every mirror index computation, array read and write, character load and equality test, argmax
comparison, output copy, loop test, and final `halt` is charged by the machine semantics. The
linear bound for the main loop uses `ExecWithin.loop_potential` with potential
`11 * (|xs| - R) + 38 * (2 * |xs| + 1 - c)`, paying for each successful outward character match by
the strictly advancing right endpoint `R` of the furthest palindrome seen so far.

## Main definitions

* `Cslib.Algorithms.WordRAM.Manacher.Reg.regl`, `Reg.regr`, `Reg.out`: output span and
  array-header registers (`Fin 16`).
* `Cslib.Algorithms.WordRAM.Manacher.radiiCode`, `radiiProgram`: structured and flat programs
  computing all `2 * |xs| + 1` maximal palindromic radii.
* `Cslib.Algorithms.WordRAM.Manacher.longestCode`, `longestProgram`: structured and flat programs
  computing `longestPalindromeSpan xs.toArray` and `longestPalindrome xs`.

## Main results

* `Cslib.Algorithms.WordRAM.Manacher.radiiCode_exec`, `radiiProgram_computesListInTime`: all
  maximal palindromic radii in `87 * |xs| + 16` word-RAM instructions at widths fitting
  `3 * |xs| + 2`.
* `Cslib.Algorithms.WordRAM.Manacher.longestCode_exec`, `longestProgram_computesListInTime`:
  longest palindromic span and factor in `116 * |xs| + 37` word-RAM instructions at widths fitting
  `4 * |xs| + 4`.

## References

* [G. Manacher, *A New Linear-Time "On-Line" Algorithm for Finding the Smallest Initial
  Palindrome of a String*][Manacher1975]
* [A. Apostolico, D. Breslauer, and Z. Galil, *Parallel detection of all palindromes in a
  string*][ApostolicoBreslauerGalil1995]
-/

public section

namespace Cslib.Algorithms.WordRAM.Manacher

open Cslib.WordRAM
open Cslib.Algorithms.Lean.Palindrome

/-! ## Registers and programs -/

namespace Reg

/-- Constant zero (`0`). -/
private abbrev zero : Fin 16 := 0
/-- Constant one (`1`). -/
private abbrev one : Fin 16 := 1
/-- Constant two (`2`). -/
private abbrev two : Fin 16 := 2
/-- Input word length `n = |xs|`. -/
private abbrev len : Fin 16 := 3
/-- Number of centers `2 * n + 1`. -/
private abbrev limit : Fin 16 := 4
/-- Base address `n + 2` of the radii entries `rad[0 .. 2 * n]`. -/
private abbrev radBase : Fin 16 := 5
/-- Current center `c`. -/
private abbrev regc : Fin 16 := 6
/-- Center `C` whose maximal palindrome reaches furthest right so far. -/
private abbrev regC : Fin 16 := 7
/-- Right endpoint `R = (C + 1) / 2 + radius xs C` of the furthest palindrome. -/
private abbrev regR : Fin 16 := 8
/-- Left extension cursor `l` (1-indexed input address), and output span `start`. -/
abbrev regl : Fin 16 := 9
/-- Right extension cursor `r` (0-indexed input position), and output span `stop`. -/
abbrev regr : Fin 16 := 10
/-- Extension count `ext`, and best palindrome length in the argmax scan. -/
private abbrev ext : Fin 16 := 11
/-- Inner-loop flag `go`, and best center `bestCenter` in the argmax scan. -/
private abbrev go : Fin 16 := 12
/-- Scratch register `t0`. -/
private abbrev t0 : Fin 16 := 13
/-- Scratch register `t1`. -/
private abbrev t1 : Fin 16 := 14
/-- Address register `out` of the length-prefixed output array. -/
abbrev out : Fin 16 := 15

end Reg

open Reg

/-- Initialize constants, read input length `n`, write the radii header `2 * n + 1` at `n + 1`,
store `rad[0] = 0` at `n + 2`, and start at center `c = 1` with `C = 0`, `R = 0`. -/
private def radiiSetup : Code .standard 16 := ram[
  zero ← #0;
  one ← #1;
  two ← #2;
  len ← *zero;
  limit ← two * len;
  limit ← limit + one;
  out ← len + one;
  *out ← limit;
  radBase ← out + one;
  *radBase ← zero;
  regc ← one;
  regC ← zero;
  regR ← zero ]

/-- One step of the outward character-extension loop. In `Data.init xs`, `xs[l - 1]` is at address
`l` when `0 < l`, and `xs[r]` is at address `r + 1`. -/
private def extBody : Code .standard 16 := ram[
  if zero < regl then [
    if regr < len then [
      t0 ← regr + one;
      t1 ← *regl;
      t0 ← *t0;
      if t1 = t0 then [
        regl ← regl - one;
        regr ← regr + one;
        ext ← ext + one
      ] else [
        go ← #0
      ]
    ] else [
      go ← #0
    ]
  ] else [
    go ← #0
  ] ]

/-- Outward character-extension loop starting from `[regl, regr)`. -/
private def extLoop : Code .standard 16 := ram[
  ext ← #0;
  go ← #1;
  while zero < go do [ ⟪extBody⟫ ] ]

/-- Process center `regc`: compute mirror center `2 * C - c = C - (c - C)`, look up `m = rad[2C-c]`
and truncation `b = R - (c + 1) / 2`, and either copy `m` or extend outward and advance `(C, R)`. -/
private def manacherBody : Code .standard 16 := ram[
  t0 ← regc - regC;
  t0 ← regC - t0;
  ⟪readAt t1 t0 radBase t0⟫;
  t1 ← regc + one;
  t1 ← t1 / two;
  t1 ← regR - t1;
  if t0 < t1 then [
    ⟪writeAt regl radBase regc t0⟫;
    regc ← regc + one
  ] else [
    regl ← regc / two;
    regl ← regl - t1;
    regr ← regc + one;
    regr ← regr / two;
    regr ← regr + t1;
    ⟪extLoop⟫;
    t0 ← regc + one;
    t0 ← t0 / two;
    t0 ← regr - t0;
    ⟪writeAt t1 radBase regc t0⟫;
    regC ← regc;
    regR ← regr;
    regc ← regc + one
  ] ]

/-- Structured program computing all `2 * |xs| + 1` maximal palindromic radii as a length-prefixed
array at address `out = |xs| + 1`. -/
def radiiCode : Code .standard 16 :=
  .seq radiiSetup (.loop (.lt regc limit) manacherBody)

/-- Flat program returning all `2 * |xs| + 1` maximal palindromic radii via `ExecutesList`. -/
def radiiProgram : Program .standard 16 := radiiCode.program out

/-- Body of the linear scan computing `bestCenter xs` across centers `1, …, 2 * n`. -/
private def argmaxBody : Code .standard 16 := ram[
  ⟪readAt t1 t0 radBase regc⟫;
  t0 ← two * t0;
  t1 ← regc % two;
  t0 ← t0 + t1;
  if ext < t0 then [
    ext ← t0;
    go ← regc
  ] else [
    ext ← ext
  ];
  regc ← regc + one ]

/-- Injective bank embedding `ArrayCopy`'s seven registers into `Fin 16`, keeping `regl`, `regr`,
and `out` outside the bank. -/
private def copyBank : Fin 7 → Fin 16 := ![t1, regC, t0, regc, regR, ext, one]

/-- Scan the radii array at `radBase` for `bestCenter`, compute `longestPalindromeSpan` in
`(regl, regr)`, and copy `xs[regl .. regr)` to a length-prefixed block at `out = 3 * |xs| + 3`. -/
private def extractLongestCode : Code .standard 16 :=
  .seq (ram[ go ← zero; ext ← zero; regc ← one ]) <|
  .seq (.loop (.lt regc limit) argmaxBody) <|
  .seq (ram[
    ⟪readAt t1 t0 radBase go⟫;
    regl ← go / two;
    regl ← regl - t0;
    regr ← go + one;
    regr ← regr / two;
    regr ← regr + t0;
    out ← radBase + limit;
    t0 ← regr - regl;
    *out ← t0;
    t1 ← one + regl;
    regC ← out + one ])
  (ArrayCopy.program.rename copyBank)

/-- Structured program computing both `longestPalindromeSpan xs.toArray` in `(regl, regr)` and
`longestPalindrome xs` as a length-prefixed list at `out`. -/
def longestCode : Code .standard 16 := .seq radiiCode extractLongestCode

/-- Flat program returning `longestPalindrome xs` via `ExecutesList`. -/
def longestProgram : Program .standard 16 := longestCode.program out

/-! ## Execution of the extension loop -/

private theorem while_extBody_spec {w : ℕ} (xs : List ℕ) (hw : Fits w (3 * xs.length + 2))
    (l₀ : ℕ) :
    ∀ x : Data 16,
      x.regs zero = 0 →
      x.regs one = 1 →
      x.regs len = xs.length →
      x.regs go = 1 →
      x.regs regl = l₀ →
      l₀ ≤ xs.length →
      x.regs regr ≤ xs.length →
      x.regs ext + l₀ ≤ xs.length →
      Block.HoldsList 1 xs x.mem →
      ∃ y, ExecWithin w (.loop (.lt zero go) extBody) x y
          (11 * extend xs.toArray l₀ (x.regs regr) + 12) ∧
        y.regs ext = x.regs ext + extend xs.toArray l₀ (x.regs regr) ∧
        y.regs regr = x.regs regr + extend xs.toArray l₀ (x.regs regr) ∧
        y.mem = x.mem := by
  induction l₀ with
  | zero =>
    intro x hz _ _ hgo hl₀ _ _ _ _
    have hc : (Cond.lt zero go).Holds x := by simp only [Cond.holds_lt, hz, hgo]; omega
    let x₁ := x.set go 0
    have hb : ExecWithin w extBody x x₁ 3 := by
      unfold extBody
      wram_exec [hz, hl₀]
    have hstop : ¬(Cond.lt zero go).Holds x₁ := by simp +decide [Cond.holds_lt, x₁, hz]
    exact ⟨x₁, (ExecWithin.loop_once hc hb hstop).mono (by simp only [extend]; omega),
      by simp +decide [x₁, extend], by simp +decide [x₁, extend], rfl⟩
  | succ l ih =>
    intro x hz ho hlen hgo hl₀ hl_le hr_le hext_le hxs
    have hc : (Cond.lt zero go).Holds x := by simp only [Cond.holds_lt, hz, hgo]; omega
    have hsz : xs.toArray.size = xs.length := List.size_toArray
    by_cases hr : x.regs regr < xs.length
    · have hl_lt : l < xs.length := by omega
      have hreadL : x.mem (l + 1) = xs[l] := by
        simpa only [Nat.add_comm 1 l] using hxs.get l hl_lt
      have hreadR : x.mem (x.regs regr + 1) = xs[x.regs regr] := by
        simpa only [Nat.add_comm 1 (x.regs regr)] using hxs.get (x.regs regr) hr
      have hf_r1 : Fits w (x.regs regr + 1) := hw.of_le (by omega)
      have hf_l : Fits w l := hw.of_le (by omega)
      have hf_ext1 : Fits w (x.regs ext + 1) := hw.of_le (by omega)
      have harrL : xs.toArray[l]'(by omega) = xs[l] := List.getElem_toArray _
      have harrR : xs.toArray[x.regs regr]'(by omega) = xs[x.regs regr] := List.getElem_toArray _
      by_cases hEq : xs[l] = xs[x.regs regr]
      · let x₁ := (((((x.set t0 (x.regs regr + 1)).set t1 xs[l]).set t0 xs[x.regs regr]).set
            regl l).set regr (x.regs regr + 1)).set ext (x.regs ext + 1)
        have hb : ExecWithin w extBody x x₁ 9 := by
          unfold extBody
          wram_exec [hz, ho, hlen, hl₀, hr, hreadL, hreadR, hEq, hf_r1, hf_l, hf_ext1]
          dsimp only [x₁]; rw [hEq]
        have hext_eq : extend xs.toArray (l + 1) (x.regs regr) =
            extend xs.toArray l (x.regs regr + 1) + 1 := by
          simp only [extend, hsz, hr, hl_lt, and_self, ↓reduceDIte, harrL, harrR, hEq, ↓reduceIte]
        obtain ⟨y, hy, hy_ext, hy_r, hy_mem⟩ := ih x₁
          (by simp +decide [x₁, hz])
          (by simp +decide [x₁, ho])
          (by simp +decide [x₁, hlen])
          (by simp +decide [x₁, hgo])
          (by simp +decide [x₁])
          (by omega)
          (by simp +decide [x₁]; omega)
          (by simp +decide [x₁]; omega)
          hxs
        have hx₁_r : x₁.regs regr = x.regs regr + 1 := by simp +decide [x₁]
        have hx₁_e : x₁.regs ext = x.regs ext + 1 := by simp +decide [x₁]
        rw [hx₁_r] at hy hy_ext hy_r
        rw [hx₁_e] at hy_ext
        exact ⟨y, (ExecWithin.loop_iter hc hb hy).mono (by rw [hext_eq]; omega),
          by rw [hext_eq]; omega, by rw [hext_eq]; omega, hy_mem⟩
      · let x₁ := (((x.set t0 (x.regs regr + 1)).set t1 xs[l]).set t0 xs[x.regs regr]).set go 0
        have hb : ExecWithin w extBody x x₁ 8 := by
          unfold extBody
          wram_exec [hz, ho, hlen, hl₀, hr, hreadL, hreadR, hEq, hf_r1]
        have hstop : ¬(Cond.lt zero go).Holds x₁ := by simp +decide [Cond.holds_lt, x₁, hz]
        have hext_eq : extend xs.toArray (l + 1) (x.regs regr) = 0 := by
          simp only [extend, hsz, hr, hl_lt, and_self, ↓reduceDIte, harrL, harrR, hEq, ↓reduceIte]
        exact ⟨x₁, (ExecWithin.loop_once hc hb hstop).mono (by rw [hext_eq]),
          by simp +decide [x₁, hext_eq], by simp +decide [x₁, hext_eq], rfl⟩
    · let x₁ := x.set go 0
      have hb : ExecWithin w extBody x x₁ 4 := by
        unfold extBody
        wram_exec [hz, hlen, hl₀, hr]
      have hstop : ¬(Cond.lt zero go).Holds x₁ := by simp +decide [Cond.holds_lt, x₁, hz]
      have hext_eq : extend xs.toArray (l + 1) (x.regs regr) = 0 := by
        have hnot : ¬(x.regs regr < xs.toArray.size ∧ l < xs.toArray.size) := by rw [hsz]; omega
        simp only [extend, hnot, ↓reduceDIte]
      exact ⟨x₁, (ExecWithin.loop_once hc hb hstop).mono (by rw [hext_eq]; omega),
        by simp +decide [x₁, hext_eq], by simp +decide [x₁, hext_eq], rfl⟩

private theorem extLoop_spec {w : ℕ} (xs : List ℕ) (hw : Fits w (3 * xs.length + 2))
    (x : Data 16)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hlen : x.regs len = xs.length)
    (hl : x.regs regl ≤ xs.length) (hr : x.regs regr ≤ xs.length)
    (hxs : Block.HoldsList 1 xs x.mem) :
    ∃ y, ExecWithin w extLoop x y
        (11 * extend xs.toArray (x.regs regl) (x.regs regr) + 14) ∧
      y.regs ext = extend xs.toArray (x.regs regl) (x.regs regr) ∧
      y.regs regr = x.regs regr + extend xs.toArray (x.regs regl) (x.regs regr) ∧
      y.mem = x.mem := by
  have h1 : Fits w 1 := hw.of_le (by omega)
  let x₀ := (x.set ext 0).set go 1
  have hx₀_r : x₀.regs regr = x.regs regr := by simp +decide [x₀]
  have hx₀_l : x₀.regs regl = x.regs regl := by simp +decide [x₀]
  have hx₀_e : x₀.regs ext = 0 := by simp +decide [x₀]
  obtain ⟨y, hy, hy_ext, hy_r, hy_mem⟩ := while_extBody_spec xs hw (x.regs regl) x₀
    (by simp +decide [x₀, hz])
    (by simp +decide [x₀, ho])
    (by simp +decide [x₀, hlen])
    (by simp +decide [x₀])
    hx₀_l
    hl
    (by rwa [hx₀_r])
    (by rw [hx₀_e, Nat.zero_add]; exact hl)
    hxs
  rw [hx₀_r] at hy hy_ext hy_r
  rw [hx₀_e, Nat.zero_add] at hy_ext
  unfold extLoop
  exact ⟨y, ((ExecWithin.const (fits_zero w)).seq ((ExecWithin.const h1).seq hy)).mono (by omega),
    hy_ext, hy_r, hy_mem⟩

/-! ## Execution of the main Manacher loop -/

private structure RadiiInv (xs : List ℕ) (y : Data 16) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  two_eq : y.regs two = 2
  len_eq : y.regs len = xs.length
  limit_eq : y.regs limit = 2 * xs.length + 1
  out_eq : y.regs out = xs.length + 1
  radBase_eq : y.regs radBase = xs.length + 2
  c_pos : 1 ≤ y.regs regc
  c_le : y.regs regc ≤ 2 * xs.length + 1
  C_lt_c : y.regs regC < y.regs regc
  R_eq : y.regs regR = (y.regs regC + 1) / 2 + radius xs (y.regs regC)
  input_holds : Block.HoldsList 1 xs y.mem
  hdr_eq : y.mem (xs.length + 1) = 2 * xs.length + 1
  rad_holds : ∀ j < y.regs regc, y.mem (xs.length + 2 + j) = radius xs j

private theorem radiiSetup_spec {w : ℕ} (xs : List ℕ) (hw : Fits w (3 * xs.length + 2)) :
    ∃ y, ExecWithin w radiiSetup (Data.init xs) y 13 ∧ RadiiInv xs y := by
  let x : Data 16 := Data.init xs
  have h1 : Fits w 1 := hw.of_le (by omega)
  have h2 : Fits w 2 := hw.of_le (by omega)
  have h2n : Fits w (2 * xs.length) := hw.of_le (by omega)
  have h2n1 : Fits w (2 * xs.length + 1) := hw.of_le (by omega)
  have hn1 : Fits w (xs.length + 1) := hw.of_le (by omega)
  have hn2 : Fits w (xs.length + 2) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold radiiSetup
  wram_exec [x, Data.init_regs, Data.init_mem_zero, h1, h2, h2n, h2n1, hn1, hn2]
  refine ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp, by wram_simp, ?_, ?_, ?_, ?_⟩
  · wram_simp
    have := radius_le_half xs 0
    omega
  · intro i
    have hi : i.val < xs.length := i.isLt
    wram_simp [Data.write_mem, Block.read]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Nat.add_comm, Data.init_mem_succ]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; rfl
  · wram_simp [Data.write_mem]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · intro j hj
    wram_simp at hj
    obtain rfl : j = 0 := by omega
    have := radius_le_half xs 0
    wram_simp [Data.write_mem]
    rw [show xs.length + 2 + 0 = xs.length + 1 + 1 by omega, Function.update_self]
    omega

private def radiiPotential (n : ℕ) (y : Data 16) : ℕ :=
  11 * (n - y.regs regR) + 38 * (2 * n + 1 - y.regs regc)

private theorem manacherBody_spec {w : ℕ} (xs : List ℕ) (hw : Fits w (3 * xs.length + 2))
    (x : Data 16) (hx : RadiiInv xs x) (hc : (Cond.lt regc limit).Holds x) :
    ∃ y T, ExecWithin w manacherBody x y T ∧ RadiiInv xs y ∧
      T + 2 + radiiPotential xs.length y ≤ radiiPotential xs.length x := by
  have hc_lt : x.regs regc < 2 * xs.length + 1 := by
    simpa only [Cond.holds_lt, hx.limit_eq] using hc
  have hCc : x.regs regC < x.regs regc := hx.C_lt_c
  have hc_pos : 1 ≤ x.regs regc := hx.c_pos
  have hRn : x.regs regR ≤ xs.length := by
    rw [hx.R_eq]
    exact add_radius_le_length xs (by omega)
  have hmirror_idx : x.regs regC - (x.regs regc - x.regs regC) = 2 * x.regs regC - x.regs regc := by
    omega
  have hmc_lt : 2 * x.regs regC - x.regs regc < x.regs regc := by omega
  have hrad_m : x.mem (xs.length + 2 + (2 * x.regs regC - x.regs regc)) =
      radius xs (2 * x.regs regC - x.regs regc) :=
    hx.rad_holds _ hmc_lt
  have hmirror := min_radius_mirror (w := xs) (C := x.regs regC) (c := x.regs regc)
    (by omega) hx.R_eq hRn
  have hf_sub1 : Fits w (x.regs regc - x.regs regC) := hw.of_le (by omega)
  have hf_sub2 : Fits w (2 * x.regs regC - x.regs regc) := hw.of_le (by omega)
  have hf_radm : Fits w (xs.length + 2 + (2 * x.regs regC - x.regs regc)) := hw.of_le (by omega)
  have hf_c1 : Fits w (x.regs regc + 1) := hw.of_le (by omega)
  have hf_c1_div : Fits w ((x.regs regc + 1) / 2) := hw.of_le (by omega)
  have hf_b : Fits w (x.regs regR - (x.regs regc + 1) / 2) := hw.of_le (by omega)
  have hf_radc : Fits w (xs.length + 2 + x.regs regc) := hw.of_le (by omega)
  by_cases hlt : radius xs (2 * x.regs regC - x.regs regc) < x.regs regR - (x.regs regc + 1) / 2
  · have hrad_c : radius xs (x.regs regc) = radius xs (2 * x.regs regC - x.regs regc) := by omega
    refine exists_comm.mp ⟨11, WP.exists_execWithin ?_⟩
    unfold manacherBody readAt writeAt
    wram_exec [hx.one_eq, hx.two_eq, hx.radBase_eq, hmirror_idx, hrad_m, hlt,
      hf_sub1, hf_sub2, hf_radm, hf_c1, hf_c1_div, hf_b, hf_radc]
    refine ⟨⟨by wram_simp [hx.zero_eq], by wram_simp [hx.one_eq], by wram_simp [hx.two_eq],
      by wram_simp [hx.len_eq], by wram_simp [hx.limit_eq], by wram_simp [hx.out_eq],
      by wram_simp [hx.radBase_eq], by wram_simp, by wram_simp; omega,
      by wram_simp; omega, by wram_simp [hx.R_eq], ?_, ?_, ?_⟩, ?_⟩
    · exact hx.input_holds.frame fun a ha1 ha2 => by wram_simp
    · wram_simp [hx.hdr_eq]
    · intro j hj
      wram_simp at hj
      by_cases hjc : j = x.regs regc
      · subst hjc
        wram_simp [hrad_c]
      · wram_simp
        exact hx.rad_holds j (by omega)
    · unfold radiiPotential
      wram_simp
      omega
  · let b := x.regs regR - (x.regs regc + 1) / 2
    have hb_def : x.regs regR - (x.regs regc + 1) / 2 = b := rfl
    have hb_le_rad : b ≤ radius xs (x.regs regc) := by omega
    have hrad_c_le : (x.regs regc + 1) / 2 + radius xs (x.regs regc) ≤ xs.length :=
      add_radius_le_length xs (by omega)
    have hr0_le : (x.regs regc + 1) / 2 + b ≤ xs.length := by omega
    have hl0_le : x.regs regc / 2 - b ≤ xs.length := by omega
    have hf_c_div : Fits w (x.regs regc / 2) := hw.of_le (by omega)
    have hf_l0 : Fits w (x.regs regc / 2 - b) := hw.of_le (by omega)
    have hf_r0 : Fits w ((x.regs regc + 1) / 2 + b) := hw.of_le (by omega)
    let e := extend xs.toArray (x.regs regc / 2 - b) ((x.regs regc + 1) / 2 + b)
    have hbe_eq : b + e = radius xs (x.regs regc) := by
      simpa only [List.toList_toArray] using
        add_extend (w := xs.toArray) (c := x.regs regc) hb_le_rad
    have hR' : (x.regs regc + 1) / 2 + b + e =
        (x.regs regc + 1) / 2 + radius xs (x.regs regc) := by omega
    have hR'_le : (x.regs regc + 1) / 2 + b + e ≤ xs.length := by omega
    have hsub_rad : (x.regs regc + 1) / 2 + b + e - (x.regs regc + 1) / 2 =
        radius xs (x.regs regc) := by omega
    have hf_radval : Fits w (radius xs (x.regs regc)) := hw.of_le (by omega)
    refine exists_comm.mp ⟨11 * e + 36, WP.exists_execWithin ?_⟩
    unfold manacherBody readAt writeAt
    wram_exec [hx.one_eq, hx.two_eq, hx.radBase_eq, hmirror_idx, hrad_m, hlt,
      hb_def, hf_sub1, hf_sub2, hf_radm, hf_c1, hf_c1_div, hf_b, hf_c_div, hf_l0, hf_r0]
    wram_call (extLoop_spec xs hw _
      (by wram_simp [hx.zero_eq])
      (by wram_simp [hx.one_eq])
      (by wram_simp [hx.len_eq])
      (by wram_simp; exact hl0_le)
      (by wram_simp; exact hr0_le)
      hx.input_holds)
      with x₂ ⟨hx₂_ext, hx₂_r, hx₂_mem⟩
    have ⟨hx₂_zero, hx₂_one, hx₂_two, hx₂_len, hx₂_limit, hx₂_out, hx₂_radBase, hx₂_c⟩ :
        x₂.regs zero = 0 ∧ x₂.regs one = 1 ∧ x₂.regs two = 2 ∧ x₂.regs len = xs.length ∧
        x₂.regs limit = 2 * xs.length + 1 ∧ x₂.regs out = xs.length + 1 ∧
        x₂.regs radBase = xs.length + 2 ∧ x₂.regs regc = x.regs regc := by
      regs_frame
    have hx₂_r' : x₂.regs regr = (x.regs regc + 1) / 2 + b + e := by
      wram_simp at hx₂_r
      exact hx₂_r
    wram_exec [hx₂_one, hx₂_two, hx₂_radBase, hx₂_c, hx₂_r', hsub_rad,
      hf_c1, hf_c1_div, hf_radval, hf_radc]
    refine ⟨⟨by wram_simp [hx₂_zero], by wram_simp [hx₂_one], by wram_simp [hx₂_two],
        by wram_simp [hx₂_len], by wram_simp [hx₂_limit], by wram_simp [hx₂_out],
        by wram_simp [hx₂_radBase], by wram_simp [hx₂_c],
        by wram_simp [hx₂_c]; omega, by wram_simp [hx₂_c]; omega,
        by wram_simp [hx₂_c, hx₂_r', hR'], ?_, ?_, ?_⟩, ?_⟩
    · exact hx.input_holds.frame fun a ha1 ha2 => by
        wram_simp [hx₂_mem, hx₂_radBase, hx₂_c]
    · wram_simp [hx₂_mem, hx₂_radBase, hx₂_c, hx.hdr_eq]
    · intro j hj
      wram_simp [hx₂_c] at hj
      by_cases hjc : j = x.regs regc
      · subst hjc
        wram_simp [hx₂_mem, hx₂_radBase, hx₂_c]
      · wram_simp [hx₂_mem, hx₂_radBase, hx₂_c]
        exact hx.rad_holds j (by omega)
    · unfold radiiPotential
      wram_simp [hx₂_c, hx₂_r']
      omega

private theorem radiiCode_inv_exec {w : ℕ} (xs : List ℕ) (hw : Fits w (3 * xs.length + 2)) :
    ∃ y, ExecWithin w radiiCode (Data.init xs) y (87 * xs.length + 15) ∧
      RadiiInv xs y ∧ y.regs regc = 2 * xs.length + 1 := by
  obtain ⟨x₀, hsetup, hx₀⟩ := radiiSetup_spec xs hw
  obtain ⟨y, hloop, hy, hstop⟩ := ExecWithin.loop_potential
    (cond := .lt regc limit) (body := manacherBody)
    (RadiiInv xs) (radiiPotential xs.length)
    (fun s hs hc => manacherBody_spec xs hw s hs hc) hx₀
  have hc_end : y.regs regc = 2 * xs.length + 1 := by
    have := hy.c_le
    simp only [Cond.holds_lt, hy.limit_eq] at hstop
    omega
  have hpot₀ : radiiPotential xs.length x₀ ≤ 87 * xs.length := by
    have := hx₀.c_pos
    unfold radiiPotential
    omega
  exact ⟨y, (hsetup.seq hloop).mono (by omega), hy, hc_end⟩

/-- **All-centers Manacher on the word RAM.** Starting from `Data.init xs` at any word width `w`
with `Fits w (3 * xs.length + 2)`, `radiiCode` executes within `87 * xs.length + 15` instructions
and writes `(manacher xs.toArray).toList` as the length-prefixed array at
`y.regs out = xs.length + 1`, preserving the input block `[1, 1 + xs.length)`. -/
theorem radiiCode_exec {w : ℕ} (xs : List ℕ) (hw : Fits w (3 * xs.length + 2)) :
    ∃ y, ExecWithin w radiiCode (Data.init xs) y (87 * xs.length + 15) ∧
      outputList y.mem (y.regs out) = (manacher xs.toArray).toList ∧
      y.regs out = xs.length + 1 ∧
      Fits w (y.regs out + (manacher xs.toArray).toList.length) ∧
      Block.HoldsList 1 xs y.mem := by
  obtain ⟨y, hy_exec, hy, hc_end⟩ := radiiCode_inv_exec xs hw
  have hlen_rad : (manacher xs.toArray).toList.length = 2 * xs.length + 1 := by
    rw [Array.length_toList, size_manacher, List.size_toArray]
  refine ⟨y, hy_exec, ?_, hy.out_eq, by rw [hy.out_eq, hlen_rad]; exact hw.of_le (by omega),
    hy.input_holds⟩
  rw [hy.out_eq, outputList_eq_iff]
  refine ⟨by rw [hy.hdr_eq, hlen_rad], fun i => ?_⟩
  have hi : i.val < 2 * xs.length + 1 := by simpa only [hlen_rad] using i.isLt
  have hi' : i.val < (manacher xs.toArray).size := by
    rw [size_manacher, List.size_toArray]; exact hi
  change y.mem (xs.length + 1 + 1 + i.val) = (manacher xs.toArray).toList[i.val]
  rw [show xs.length + 1 + 1 + i.val = xs.length + 2 + i.val by omega,
    hy.rad_holds i.val (by omega), Array.getElem_toList, getElem_manacher xs.toArray hi']

/-- `radiiProgram` computes `(manacher xs.toArray).toList` in `87 * |xs| + 16` instructions on
every fitting word array at every word width fitting `3 * |xs| + 2`. -/
theorem radiiProgram_computesListInTime :
    radiiProgram.ComputesListInTime (fun _ xs => xs) (fun xs _ => 87 * xs.length + 16)
      (fun xs w => Fits w (3 * xs.length + 2)) (fun xs => (manacher xs.toArray).toList) :=
  radiiCode.computesListInTime_program out fun xs _ hw _ => by
    obtain ⟨y, hexec, hout, _, hfit, _⟩ := radiiCode_exec xs hw
    exact ⟨y, hexec, hout, hfit⟩

/-! ## Longest palindromic span and factor -/

private theorem copyBank_injective : Function.Injective copyBank := by decide

private theorem extractLongestCode_spec {w : ℕ} (xs : List ℕ) (hw : Fits w (4 * xs.length + 4))
    (y₁ : Data 16) (hy₁ : RadiiInv xs y₁) (hc_end : y₁.regs regc = 2 * xs.length + 1) :
    ∃ y, ExecWithin w extractLongestCode y₁ y (29 * xs.length + 21) ∧
      y.regs regl = (longestPalindromeSpan xs.toArray).start ∧
      y.regs regr = (longestPalindromeSpan xs.toArray).stop ∧
      outputList y.mem (y.regs out) = longestPalindrome xs ∧
      y.regs out = 3 * xs.length + 3 ∧
      Fits w (y.regs out + (longestPalindrome xs).length) ∧
      Block.HoldsList 1 xs y.mem := by
  let f : ℕ → ℕ := fun i => 2 * radius xs i + i % 2
  let y₂ := ((y₁.set go 0).set ext 0).set regc 1
  have hinit : ExecWithin (B := .standard) w
      (ram[ go ← zero; ext ← zero; regc ← one ]) y₁ y₂ 3 := by
    wram_exec [hy₁.zero_eq, hy₁.one_eq]
  let P (j : ℕ) (s : Data 16) : Prop :=
    s.regs one = 1 ∧ s.regs two = 2 ∧ s.regs limit = 2 * xs.length + 1 ∧
      s.regs radBase = xs.length + 2 ∧ s.mem = y₁.mem ∧
      (List.range j).argmax f = some (s.regs go) ∧
      s.regs ext = f (s.regs go)
  have hbody (s : Data 16) (hs : P (s.regs regc) s) (hlt : s.regs regc < 2 * xs.length + 1) :
      ∃ z, ExecWithin w argmaxBody s z 9 ∧ P (s.regs regc + 1) z ∧
        z.regs regc = s.regs regc + 1 := by
    obtain ⟨ho, ht2, hlim, hrb, hmem, harg, hext_eq⟩ := hs
    have hrad_j : s.mem (xs.length + 2 + s.regs regc) = radius xs (s.regs regc) := by
      rw [hmem]
      exact hy₁.rad_holds _ (by omega)
    have hhalf_j := radius_le_half xs (s.regs regc)
    have hf_addr : Fits w (xs.length + 2 + s.regs regc) := hw.of_le (by omega)
    have hf_2rad : Fits w (2 * radius xs (s.regs regc)) := hw.of_le (by omega)
    have hf_mod : Fits w (s.regs regc % 2) := hw.of_le (by omega)
    have hf_fj : Fits w (2 * radius xs (s.regs regc) + s.regs regc % 2) := hw.of_le (by omega)
    have hf_j1 : Fits w (s.regs regc + 1) := hw.of_le (by omega)
    by_cases hlt_f : s.regs ext < 2 * radius xs (s.regs regc) + s.regs regc % 2
    · refine WP.exists_execWithin ?_
      unfold argmaxBody readAt
      wram_exec [ho, ht2, hrb, hrad_j, hlt_f, hf_addr, hf_2rad, hf_mod, hf_fj, hf_j1]
      refine ⟨⟨by wram_simp [ho], by wram_simp [ht2], by wram_simp [hlim],
        by wram_simp [hrb], by wram_simp [hmem], ?_, by wram_simp; rfl⟩, by wram_simp⟩
      wram_simp
      simp [List.range_succ, List.argmax_concat, harg, ← hext_eq, hlt_f, f]
    · refine WP.exists_execWithin ?_
      unfold argmaxBody readAt
      wram_exec [ho, ht2, hrb, hrad_j, hlt_f, hf_addr, hf_2rad, hf_mod, hf_fj, hf_j1]
      refine ⟨⟨by wram_simp [ho], by wram_simp [ht2], by wram_simp [hlim],
        by wram_simp [hrb], by wram_simp [hmem], ?_, by wram_simp [hext_eq]⟩, by wram_simp⟩
      wram_simp
      simp [List.range_succ, List.argmax_concat, harg, ← hext_eq, hlt_f, f]
  have hy₂_P : P (y₂.regs regc) y₂ := by
    refine ⟨by simp +decide [y₂, hy₁.one_eq], by simp +decide [y₂, hy₁.two_eq],
      by simp +decide [y₂, hy₁.limit_eq], by simp +decide [y₂, hy₁.radBase_eq], rfl, ?_, ?_⟩
    · simp +decide [y₂]
    · have := radius_le_half xs 0
      simp +decide only [y₂, Data.set_regs, Function.update_apply, ↓reduceIte, f]
      omega
  obtain ⟨y₃, hloop, ⟨hy₃_1, hy₃_2, hy₃_lim, hy₃_rb, hy₃_mem, hy₃_arg, _⟩, _⟩ :=
    ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
      (by simp +decide [y₂]) hy₂_P
  have hbest_eq : y₃.regs go = bestCenter xs := by
    unfold bestCenter
    change y₃.regs go = ((List.range (2 * xs.length + 1)).argmax f).getD 0
    rw [hy₃_arg, Option.getD_some]
  let bc := bestCenter xs
  let bk := radius xs bc
  have hbc_le : bc ≤ 2 * xs.length := bestCenter_le xs
  have hrad_bc1 : y₁.mem (xs.length + 2 + bestCenter xs) = radius xs (bestCenter xs) :=
    hy₁.rad_holds (bestCenter xs) (by omega)
  have hrad_bc : y₃.mem (xs.length + 2 + bestCenter xs) = radius xs (bestCenter xs) := by
    rw [hy₃_mem]; exact hrad_bc1
  have hbk_half : bk ≤ bc / 2 := radius_le_half xs bc
  have hbk_len : (bc + 1) / 2 + bk ≤ xs.length := add_radius_le_length xs hbc_le
  let st := bc / 2 - bk
  let sp := (bc + 1) / 2 + bk
  have hst_eq : st = (longestPalindromeSpan xs.toArray).start := by
    rw [start_longestPalindromeSpan, List.toList_toArray]
  have hsp_eq : sp = (longestPalindromeSpan xs.toArray).stop := by
    rw [stop_longestPalindromeSpan, List.toList_toArray]
  have hst_le_sp : st ≤ sp := by omega
  have hf_rb_bc : Fits w (xs.length + 2 + bc) := hw.of_le (by omega)
  have hf_bc_div : Fits w (bc / 2) := hw.of_le (by omega)
  have hf_st : Fits w st := hw.of_le (by omega)
  have hf_bc1 : Fits w (bc + 1) := hw.of_le (by omega)
  have hf_bc1_div : Fits w ((bc + 1) / 2) := hw.of_le (by omega)
  have hf_sp : Fits w sp := hw.of_le (by omega)
  have hf_3n3 : Fits w (xs.length + 2 + (2 * xs.length + 1)) := hw.of_le (by omega)
  have hf_diff : Fits w (sp - st) := hw.of_le (by omega)
  have hf_1st : Fits w (1 + st) := hw.of_le (by omega)
  have hf_3n4 : Fits w (xs.length + 2 + (2 * xs.length + 1) + 1) := hw.of_le (by omega)
  have hprep_spec : ∃ y₄, ExecWithin w (ram[
      ⟪readAt t1 t0 radBase go⟫;
      regl ← go / two;
      regl ← regl - t0;
      regr ← go + one;
      regr ← regr / two;
      regr ← regr + t0;
      out ← radBase + limit;
      t0 ← regr - regl;
      *out ← t0;
      t1 ← one + regl;
      regC ← out + one ]) y₃ y₄ 12 ∧
    y₄.regs regl = st ∧ y₄.regs regr = sp ∧ y₄.regs out = 3 * xs.length + 3 ∧
    y₄.regs t0 = sp - st ∧ y₄.regs t1 = 1 + st ∧ y₄.regs regC = 3 * xs.length + 4 ∧
    y₄.mem = Function.update y₁.mem (3 * xs.length + 3) (sp - st) := by
    refine WP.exists_execWithin ?_
    unfold readAt
    wram_exec [hy₃_1, hy₃_2, hy₃_lim, hy₃_rb, hbest_eq, hrad_bc,
      hf_rb_bc, hf_bc_div, hf_st, hf_bc1, hf_bc1_div, hf_sp,
      hf_3n3, hf_diff, hf_1st, hf_3n4]
    refine ⟨by wram_simp [hrad_bc]; rfl, by wram_simp [hrad_bc]; rfl, by wram_simp; omega,
      by wram_simp [hrad_bc]; rfl, by wram_simp [hrad_bc]; rfl, by wram_simp; omega, ?_⟩
    wram_simp [hy₃_mem, hrad_bc, hrad_bc1]
    congr 1
    omega
  obtain ⟨y₄, hprep, hy₄_l, hy₄_r, hy₄_out, hy₄_t0, hy₄_t1, hy₄_C, hy₄_mem⟩ := hprep_spec
  have h1 : Fits w 1 := hw.of_le (by omega)
  have hbank_src : (y₄.comap copyBank).regs ArrayCopy.src = 1 + st := hy₄_t1
  have hbank_dst : (y₄.comap copyBank).regs ArrayCopy.dst = 3 * xs.length + 4 := hy₄_C
  have hbank_len : (y₄.comap copyBank).regs ArrayCopy.len = sp - st := hy₄_t0
  have hcopy_callee := ArrayCopy.exec (w := w) (y₄.comap copyBank) h1
    (by rw [hbank_src, hbank_len]; exact hw.of_le (by omega))
    (by rw [hbank_dst, hbank_len]; exact hw.of_le (by omega))
    (by rw [hbank_src, hbank_len, hbank_dst]; omega)
  obtain ⟨y, hcopy, ⟨hy_mem, _⟩, _⟩ := ExecWithin.rename_post copyBank_injective hcopy_callee
  rw [hbank_len] at hcopy
  change y.mem = ArrayCopy.copyPrefix y₄.mem _ _ _ at hy_mem
  rw [hbank_src, hbank_dst, hbank_len] at hy_mem
  have hy_regl : y.regs regl = st := by regs_frame
  have hy_regr : y.regs regr = sp := by regs_frame
  have hy_out : y.regs out = 3 * xs.length + 3 := by regs_frame
  have hy₂_c : y₂.regs regc = 1 := by simp +decide [y₂]
  rw [hy₂_c] at hloop
  have htotal : ExecWithin w extractLongestCode y₁ y (29 * xs.length + 21) :=
    (hinit.seq (hloop.seq (hprep.seq hcopy))).mono (by omega)
  have hextract_eq : xs.extract st sp = longestPalindrome xs := by
    simpa only [List.toList_toArray] using
      (hst_eq ▸ hsp_eq ▸ extract_longestPalindromeSpan xs.toArray)
  have hlen_ext : (xs.extract st sp).length = sp - st := by
    rw [List.extract_eq_take_drop, List.length_take, List.length_drop]
    omega
  have hhold_xs : Block.HoldsList 1 xs y.mem := fun i => by
    have hi : i.val < xs.length := i.isLt
    change y.mem (1 + i.val) = xs[i.val]
    rw [hy_mem, ArrayCopy.copyPrefix_outside (by omega), hy₄_mem, Function.update_of_ne (by omega)]
    exact hy₁.input_holds i
  refine ⟨y, htotal, hy_regl.trans hst_eq, hy_regr.trans hsp_eq, ?_, hy_out,
    hw.of_le (by rw [hy_out, ← hextract_eq, hlen_ext]; omega), hhold_xs⟩
  rw [hy_out, ← hextract_eq, outputList_eq_iff]
  refine ⟨?_, fun i => ?_⟩
  · rw [hy_mem, ArrayCopy.copyPrefix_outside (by omega), hy₄_mem, hlen_ext, Function.update_self]
  · have hi : i.val < sp - st := by simpa only [hlen_ext] using i.isLt
    change y.mem (3 * xs.length + 3 + 1 + i.val) = (xs.extract st sp)[i.val]
    rw [show 3 * xs.length + 3 + 1 + i.val = (3 * xs.length + 4) + i.val by omega, hy_mem,
      ArrayCopy.copyPrefix_read hi, hy₄_mem, Function.update_of_ne (by omega)]
    have hget : y₁.mem (1 + (st + i.val)) = xs[st + i.val]'(by omega) :=
      hy₁.input_holds.get (st + i.val) (by omega)
    rw [show 1 + st + i.val = 1 + (st + i.val) by omega, hget]
    simp only [List.extract_eq_take_drop, List.getElem_take, List.getElem_drop]

/-- **Longest palindromic span and factor on the word RAM.** Starting from `Data.init xs` at any
word width `w` with `Fits w (4 * xs.length + 4)`, `longestCode` executes within
`116 * xs.length + 36` instructions, leaving `(longestPalindromeSpan xs.toArray).start` in `regl`,
`(longestPalindromeSpan xs.toArray).stop` in `regr`, and `longestPalindrome xs` as the
length-prefixed array at `y.regs out = 3 * xs.length + 3`, while preserving `xs` at `1 .. |xs|`. -/
theorem longestCode_exec {w : ℕ} (xs : List ℕ) (hw : Fits w (4 * xs.length + 4)) :
    ∃ y, ExecWithin w longestCode (Data.init xs) y (116 * xs.length + 36) ∧
      y.regs regl = (longestPalindromeSpan xs.toArray).start ∧
      y.regs regr = (longestPalindromeSpan xs.toArray).stop ∧
      outputList y.mem (y.regs out) = longestPalindrome xs ∧
      y.regs out = 3 * xs.length + 3 ∧
      Fits w (y.regs out + (longestPalindrome xs).length) ∧
      Block.HoldsList 1 xs y.mem := by
  obtain ⟨y₁, hradii, hy₁, hc_end⟩ := radiiCode_inv_exec xs (hw.of_le (by omega))
  obtain ⟨y, hext, hst, hsp, hout, hout_eq, hfit, hhold⟩ :=
    extractLongestCode_spec xs hw y₁ hy₁ hc_end
  exact ⟨y, (hradii.seq hext).mono (by omega), hst, hsp, hout, hout_eq, hfit, hhold⟩

/-- `longestProgram` computes `longestPalindrome xs` in `116 * |xs| + 37` instructions on every
fitting word array at every word width fitting `4 * |xs| + 4`. -/
theorem longestProgram_computesListInTime :
    longestProgram.ComputesListInTime (fun _ xs => xs) (fun xs _ => 116 * xs.length + 37)
      (fun xs w => Fits w (4 * xs.length + 4)) longestPalindrome :=
  longestCode.computesListInTime_program out fun xs _ hw _ => by
    obtain ⟨y, hexec, _, _, hout, _, hfit, _⟩ := longestCode_exec xs hw
    exact ⟨y, hexec, hout, hfit⟩

end Cslib.Algorithms.WordRAM.Manacher
