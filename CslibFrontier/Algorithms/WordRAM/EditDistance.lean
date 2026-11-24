/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM edit distance and longest common subsequence

Checked Word-RAM implementations and `O((|x| + 1)(|y| + 1))` running-time bounds for the dynamic
programs of `CslibFrontier.Algorithms.Lean.EditDistance`:

* **General-cost Wagner–Fischer edit distance** (`weightedEditDistProgram`) over a finite alphabet
  `Fin σ` with arbitrary natural-number letter costs (`Costs (Fin σ)`), laid out in input memory as
  `[σ, |x|, |y|]`, the words `x` and `y`, the `σ`-entry `del` and `ins` tables, and the `σ²`-entry
  row-major `sub` table. The program computes `editDist I.costs I.src I.tgt` using a single working
  row of `|y| + 1` words in at most `28 (|x| + 1)(|y| + 1)` standard-basis instructions.
* **Unit-cost Levenshtein edit distance** (`unitEditDistProgram`) over arbitrary `w`-bit word
  sequences `x, y : List ℕ` (`WordSeqPair`), laid out as `[|x|, |y|] ++ x ++ y` with no alphabet
  table. The program computes `editDist Costs.unit I.src I.tgt` in at most
  `26 (|x| + 1)(|y| + 1)` instructions.
* **Longest-common-subsequence length** (`lcsLengthProgram`) over arbitrary `w`-bit word sequences
  `x, y : List ℕ` (`WordSeqPair`), computing `lcsLength I.src I.tgt` in at most
  `20 (|x| + 1)(|y| + 1)` instructions.

All three instantiate a shared private `GridDP` execution engine that fills the suffix table
`D.value (x.drop (|x| - s)) (y.drop (|y| - k))` in place across one `(n + 1)`-word row using an
explicit diagonal register. Every address calculation, table read/write, comparison, arithmetic
instruction, loop branch/jump, and final `halt` is charged by the Word-RAM semantics.

## Main definitions

* `Cslib.Algorithms.WordRAM.EditDistance.WeightedInstance`: edit-distance instance over `Fin σ`
  with general letter costs, its word layout `WeightedInstance.encode`, and word-width condition
  `WeightedInstance.FitsWidth`.
* `Cslib.Algorithms.WordRAM.EditDistance.WordSeqPair`: pair of word-encoded sequences `List ℕ`,
  its word layout `WordSeqPair.encode`, and word-width condition `WordSeqPair.FitsWidth`.
* `Cslib.Algorithms.WordRAM.EditDistance.weightedEditDistProgram`,
  `unitEditDistProgram`, `lcsLengthProgram`: fixed `Program .standard 22` programs.

## Main results

* `Cslib.Algorithms.WordRAM.EditDistance.WeightedInstance.FitsWidth.inputFits`: `FitsWidth` implies
  `InputFits w I.encode`.
* `Cslib.Algorithms.WordRAM.EditDistance.computesInTime_weightedEditDist`,
  `uniformComputableInTime_weightedEditDist`: general-cost Wagner–Fischer edit distance runs in at
  most `28 (|x| + 1)(|y| + 1)` Word-RAM instructions at fitting widths.
* `Cslib.Algorithms.WordRAM.EditDistance.computesInTime_unitEditDist`,
  `uniformComputableInTime_unitEditDist`: unit-cost Levenshtein edit distance on word sequences
  runs in at most `26 (|x| + 1)(|y| + 1)` Word-RAM instructions at fitting widths.
* `Cslib.Algorithms.WordRAM.EditDistance.computesInTime_lcsLength`,
  `uniformComputableInTime_lcsLength`: longest-common-subsequence length on word sequences runs in
  at most `20 (|x| + 1)(|y| + 1)` Word-RAM instructions at fitting widths.

## References

* [R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*][WagnerFischer1974]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.EditDistance

open Cslib.Algorithms.Lean.EditDistance
open Cslib.WordRAM

/-! ## Shared register layout and `GridDP` row engine -/

private abbrev regM : Fin 22 := 0
private abbrev regN : Fin 22 := 1
private abbrev regXBase : Fin 22 := 2
private abbrev regYBase : Fin 22 := 3
private abbrev regDPBase : Fin 22 := 4
private abbrev regSigma : Fin 22 := 5
private abbrev regDelBase : Fin 22 := 6
private abbrev regInsBase : Fin 22 := 7
private abbrev regSubBase : Fin 22 := 8
private abbrev regOne : Fin 22 := 9
private abbrev regS : Fin 22 := 10
private abbrev regT : Fin 22 := 11
private abbrev regA : Fin 22 := 12
private abbrev regB : Fin 22 := 13
private abbrev regDiag : Fin 22 := 14
private abbrev regUp : Fin 22 := 15
private abbrev regRowAux0 : Fin 22 := 16
private abbrev regRowAux1 : Fin 22 := 17
private abbrev regCur : Fin 22 := 18
private abbrev regNext : Fin 22 := 19
private abbrev regTmp0 : Fin 22 := 20
private abbrev regTmp1 : Fin 22 := 21

private structure GridFixedRegs (x₀ st : Data 22) : Prop where
  m : st.regs regM = x₀.regs regM
  n : st.regs regN = x₀.regs regN
  xb : st.regs regXBase = x₀.regs regXBase
  yb : st.regs regYBase = x₀.regs regYBase
  dpb : st.regs regDPBase = x₀.regs regDPBase
  sig : st.regs regSigma = x₀.regs regSigma
  delb : st.regs regDelBase = x₀.regs regDelBase
  insb : st.regs regInsBase = x₀.regs regInsBase
  subb : st.regs regSubBase = x₀.regs regSubBase

private def gridSetup (nilNilVal : ℕ) : Code .standard 22 :=
  ram[ regOne ← #1; regCur ← #nilNilVal; *regDPBase ← regCur; regT ← #0 ]

private def gridInitPre : Code .standard 22 :=
  ram[
    regTmp0 ← regYBase + regN;
    regTmp0 ← regTmp0 - regOne;
    regTmp0 ← regTmp0 - regT;
    regB ← *regTmp0 ]

private def gridInitPost : Code .standard 22 :=
  ram[ regT ← regT + regOne; regTmp0 ← regDPBase + regT; *regTmp0 ← regCur ]

private def gridInitBody (initCell : Code .standard 22) : Code .standard 22 :=
  .seq gridInitPre (.seq initCell gridInitPost)

private def gridOuterPre : Code .standard 22 :=
  ram[
    regTmp0 ← regXBase + regM;
    regTmp0 ← regTmp0 - regOne;
    regTmp0 ← regTmp0 - regS;
    regA ← *regTmp0;
    regDiag ← *regDPBase ]

private def gridOuterMid : Code .standard 22 :=
  ram[ *regDPBase ← regCur; regT ← #0 ]

private def gridInnerPre : Code .standard 22 :=
  ram[
    regTmp0 ← regYBase + regN;
    regTmp0 ← regTmp0 - regOne;
    regTmp0 ← regTmp0 - regT;
    regB ← *regTmp0;
    regTmp0 ← regDPBase + regT;
    regTmp0 ← regTmp0 + regOne;
    regUp ← *regTmp0 ]

private def gridInnerPost : Code .standard 22 :=
  ram[
    regTmp0 ← regDPBase + regT;
    regTmp0 ← regTmp0 + regOne;
    *regTmp0 ← regNext;
    regDiag ← regUp;
    regCur ← regNext;
    regT ← regT + regOne ]

private def gridInnerBody (innerCell : Code .standard 22) : Code .standard 22 :=
  .seq gridInnerPre (.seq innerCell gridInnerPost)

private def gridOuterBody (borderCell innerCell : Code .standard 22) : Code .standard 22 :=
  .seq gridOuterPre
    (.seq borderCell
      (.seq gridOuterMid
        (.seq (.loop (.lt regT regN) (gridInnerBody innerCell))
          (ram[ regS ← regS + regOne ]))))

private def gridFinalLoad : Code .standard 22 :=
  ram[ regTmp0 ← regDPBase + regN; regCur ← *regTmp0 ]

/-- Structured `GridDP` table evaluator parameterized by the corner constant `nilNilVal` and the
three cell-update blocks `initCell`, `borderCell`, and `innerCell`. Expects `regM = |x|`,
`regN = |y|`, `regXBase`, `regYBase`, `regDPBase` initialized by the caller, and leaves
`D.value x y` in `regCur`. -/
private def gridCode (nilNilVal : ℕ)
    (initCell borderCell innerCell : Code .standard 22) : Code .standard 22 :=
  .seq (gridSetup nilNilVal)
    (.seq (.loop (.lt regT regN) (gridInitBody initCell))
      (.seq (ram[ regS ← #0 ])
        (.seq (.loop (.lt regS regM) (gridOuterBody borderCell innerCell))
          gridFinalLoad)))

private theorem drop_sub_succ_eq_cons {α : Type*} (l : List α) {k : ℕ} (hk : k < l.length) :
    l.drop (l.length - (k + 1)) = l[l.length - 1 - k] :: l.drop (l.length - k) := by
  have hlt : l.length - 1 - k < l.length := by omega
  have h1 : l.length - (k + 1) = l.length - 1 - k := by omega
  have h2 : l.length - 1 - k + 1 = l.length - k := by omega
  rw [h1, List.drop_eq_getElem_cons hlt, h2]

private def dpInitMem {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (y : List α) (t : ℕ) (addr : ℕ) : ℕ :=
  if dpBase ≤ addr ∧ addr < dpBase + (t + 1) then
    D.value [] (y.drop (y.length - (addr - dpBase)))
  else mem₀ addr

private def dpRowMem {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s : ℕ) (addr : ℕ) : ℕ :=
  if dpBase ≤ addr ∧ addr < dpBase + (y.length + 1) then
    D.value (x.drop (x.length - s)) (y.drop (y.length - (addr - dpBase)))
  else mem₀ addr

private def dpMidMem {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s t : ℕ) (addr : ℕ) : ℕ :=
  if dpBase ≤ addr ∧ addr < dpBase + (t + 1) then
    D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - (addr - dpBase)))
  else if dpBase + (t + 1) ≤ addr ∧ addr < dpBase + (y.length + 1) then
    D.value (x.drop (x.length - s)) (y.drop (y.length - (addr - dpBase)))
  else mem₀ addr

private theorem dpInitMem_zero {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (y : List α) :
    Function.update mem₀ dpBase D.nilNil = dpInitMem mem₀ dpBase D y 0 := by
  funext addr
  rcases eq_or_ne addr dpBase with rfl | h
  · have hin : addr ≤ addr ∧ addr < addr + (0 + 1) := by omega
    rw [Function.update_self, dpInitMem, ite_eq_left hin, Nat.sub_self, Nat.sub_zero,
      List.drop_length, D.value_nil_nil]
  · rw [Function.update_of_ne h]
    have hnot : ¬(dpBase ≤ addr ∧ addr < dpBase + (0 + 1)) := by omega
    rw [dpInitMem, ite_eq_right hnot]

private theorem dpInitMem_succ {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (y : List α) {t : ℕ} (_ht : t < y.length) :
    Function.update (dpInitMem mem₀ dpBase D y t) (dpBase + (t + 1))
        (D.value [] (y.drop (y.length - (t + 1)))) =
      dpInitMem mem₀ dpBase D y (t + 1) := by
  funext addr
  rcases eq_or_ne addr (dpBase + (t + 1)) with rfl | h
  · have hsub : dpBase + (t + 1) - dpBase = t + 1 := by omega
    have hin : dpBase ≤ dpBase + (t + 1) ∧ dpBase + (t + 1) < dpBase + (t + 1 + 1) := by omega
    rw [Function.update_self, dpInitMem, ite_eq_left hin, hsub]
  · rw [Function.update_of_ne h]
    have heq : (dpBase ≤ addr ∧ addr < dpBase + (t + 1 + 1)) ↔
        (dpBase ≤ addr ∧ addr < dpBase + (t + 1)) := by omega
    simp only [dpInitMem, heq]

private theorem dpInitMem_end {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) :
    dpInitMem mem₀ dpBase D y y.length = dpRowMem mem₀ dpBase D x y 0 := by
  funext addr
  simp only [dpInitMem, dpRowMem, Nat.sub_zero, List.drop_length]

private theorem dpRowMem_read {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s k : ℕ) (hk : k ≤ y.length) :
    dpRowMem mem₀ dpBase D x y s (dpBase + k) =
      D.value (x.drop (x.length - s)) (y.drop (y.length - k)) := by
  have hin : dpBase ≤ dpBase + k ∧ dpBase + k < dpBase + (y.length + 1) := by omega
  have hsub : dpBase + k - dpBase = k := by omega
  rw [dpRowMem, ite_eq_left hin, hsub]

private theorem dpMidMem_zero {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s : ℕ) :
    Function.update (dpRowMem mem₀ dpBase D x y s) dpBase
        (D.value (x.drop (x.length - (s + 1))) []) =
      dpMidMem mem₀ dpBase D x y s 0 := by
  funext addr
  rcases eq_or_ne addr dpBase with rfl | h
  · have hin : addr ≤ addr ∧ addr < addr + (0 + 1) := by omega
    rw [Function.update_self, dpMidMem, ite_eq_left hin, Nat.sub_self, Nat.sub_zero,
      List.drop_length]
  · rw [Function.update_of_ne h]
    have hnot : ¬(dpBase ≤ addr ∧ addr < dpBase + (0 + 1)) := by omega
    have heq : (dpBase + (0 + 1) ≤ addr ∧ addr < dpBase + (y.length + 1)) ↔
        (dpBase ≤ addr ∧ addr < dpBase + (y.length + 1)) := by omega
    rw [dpMidMem, ite_eq_right hnot, dpRowMem]
    simp only [heq]

private theorem dpMidMem_read_next {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s : ℕ) {t : ℕ} (ht : t < y.length) :
    dpMidMem mem₀ dpBase D x y s t (dpBase + t + 1) =
      D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) := by
  have hnot : ¬(dpBase ≤ dpBase + t + 1 ∧ dpBase + t + 1 < dpBase + (t + 1)) := by omega
  have hin : dpBase + (t + 1) ≤ dpBase + t + 1 ∧ dpBase + t + 1 < dpBase + (y.length + 1) := by
    omega
  have hsub : dpBase + t + 1 - dpBase = t + 1 := by omega
  rw [dpMidMem, ite_eq_right hnot, ite_eq_left hin, hsub]

private theorem dpMidMem_succ {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s : ℕ) {t : ℕ} (_ht : t < y.length) :
    Function.update (dpMidMem mem₀ dpBase D x y s t) (dpBase + t + 1)
        (D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - (t + 1)))) =
      dpMidMem mem₀ dpBase D x y s (t + 1) := by
  funext addr
  rcases eq_or_ne addr (dpBase + t + 1) with rfl | h
  · have hin : dpBase ≤ dpBase + t + 1 ∧ dpBase + t + 1 < dpBase + (t + 1 + 1) := by omega
    have hsub : dpBase + t + 1 - dpBase = t + 1 := by omega
    rw [Function.update_self, dpMidMem, ite_eq_left hin, hsub]
  · rw [Function.update_of_ne h]
    by_cases h1 : dpBase ≤ addr ∧ addr < dpBase + (t + 1)
    · have h1' : dpBase ≤ addr ∧ addr < dpBase + (t + 1 + 1) := by omega
      rw [dpMidMem, ite_eq_left h1, dpMidMem, ite_eq_left h1']
    · have h1' : ¬(dpBase ≤ addr ∧ addr < dpBase + (t + 1 + 1)) := by omega
      have h2eq : (dpBase + (t + 1 + 1) ≤ addr ∧ addr < dpBase + (y.length + 1)) ↔
          (dpBase + (t + 1) ≤ addr ∧ addr < dpBase + (y.length + 1)) := by omega
      rw [dpMidMem, ite_eq_right h1, dpMidMem, ite_eq_right h1']
      simp only [h2eq]

private theorem dpMidMem_end {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s : ℕ) :
    dpMidMem mem₀ dpBase D x y s y.length = dpRowMem mem₀ dpBase D x y (s + 1) := by
  funext addr
  have h2 : ¬(dpBase + (y.length + 1) ≤ addr ∧ addr < dpBase + (y.length + 1)) := by omega
  by_cases h1 : dpBase ≤ addr ∧ addr < dpBase + (y.length + 1)
  · rw [dpMidMem, ite_eq_left h1, dpRowMem, ite_eq_left h1]
  · rw [dpMidMem, ite_eq_right h1, ite_eq_right h2, dpRowMem, ite_eq_right h1]

private theorem dpInitMem_lt {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (y : List α) (t addr : ℕ) (ha : addr < dpBase) :
    dpInitMem mem₀ dpBase D y t addr = mem₀ addr := by
  have hnot : ¬(dpBase ≤ addr ∧ addr < dpBase + (t + 1)) := by omega
  rw [dpInitMem, ite_eq_right hnot]

private theorem dpRowMem_lt {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s addr : ℕ) (ha : addr < dpBase) :
    dpRowMem mem₀ dpBase D x y s addr = mem₀ addr := by
  have hnot : ¬(dpBase ≤ addr ∧ addr < dpBase + (y.length + 1)) := by omega
  rw [dpRowMem, ite_eq_right hnot]

private theorem dpMidMem_lt {α : Type*} (mem₀ : ℕ → ℕ) (dpBase : ℕ) (D : GridDP α ℕ)
    (x y : List α) (s t addr : ℕ) (ha : addr < dpBase) :
    dpMidMem mem₀ dpBase D x y s t addr = mem₀ addr := by
  have h1 : ¬(dpBase ≤ addr ∧ addr < dpBase + (t + 1)) := by omega
  have h2 : ¬(dpBase + (t + 1) ≤ addr ∧ addr < dpBase + (y.length + 1)) := by omega
  rw [dpMidMem, ite_eq_right h1, ite_eq_right h2]

/-- Execute `gridCode` on any `GridDP α ℕ` whose corner, border, and interior updates are
implemented by `initCell`, `borderCell`, and `innerCell`. -/
private theorem exec_gridCode {α : Type*} {w : ℕ} (Ti Tb Tc : ℕ)
    (D : GridDP α ℕ) (encSym : α → ℕ)
    (x y : List α) (x₀ : Data 22)
    (initCell borderCell innerCell : Code .standard 22)
    (RowInv : α → Data 22 → Prop)
    (hm : x₀.regs regM = x.length)
    (hn : x₀.regs regN = y.length)
    (hxdisj : x₀.regs regXBase + x.length ≤ x₀.regs regDPBase)
    (hydisj : x₀.regs regYBase + y.length ≤ x₀.regs regDPBase)
    (hxmem : ∀ i (hi : i < x.length), x₀.mem (x₀.regs regXBase + i) = encSym x[i])
    (hymem : ∀ j (hj : j < y.length), x₀.mem (x₀.regs regYBase + j) = encSym y[j])
    (hfit1 : Fits w 1)
    (hfitNil : Fits w D.nilNil)
    (hfitDP : Fits w (x₀.regs regDPBase + y.length + 1))
    (hfitM : Fits w (x.length + 1))
    (hinit : ∀ (t : ℕ) (ht : t < y.length) (st : Data 22),
      GridFixedRegs x₀ st →
      st.regs regOne = 1 →
      (∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr) →
      st.regs regB = encSym y[y.length - 1 - t] →
      st.regs regCur = D.value [] (y.drop (y.length - t)) →
      ∃ st', ExecWithin w initCell st st' Ti ∧
        st'.mem = st.mem ∧
        GridFixedRegs x₀ st' ∧
        st'.regs regOne = 1 ∧
        st'.regs regT = st.regs regT ∧
        st'.regs regCur = D.nilCons y[y.length - 1 - t] (D.value [] (y.drop (y.length - t))))
    (hborder : ∀ (s : ℕ) (hs : s < x.length) (st : Data 22),
      GridFixedRegs x₀ st →
      st.regs regOne = 1 →
      (∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr) →
      st.regs regA = encSym x[x.length - 1 - s] →
      st.regs regDiag = D.value (x.drop (x.length - s)) [] →
      ∃ st', ExecWithin w borderCell st st' Tb ∧
        st'.mem = st.mem ∧
        GridFixedRegs x₀ st' ∧
        st'.regs regOne = 1 ∧
        st'.regs regS = st.regs regS ∧
        st'.regs regA = st.regs regA ∧
        st'.regs regDiag = st.regs regDiag ∧
        RowInv x[x.length - 1 - s] st' ∧
        st'.regs regCur = D.consNil x[x.length - 1 - s] (D.value (x.drop (x.length - s)) []))
    (hRowInv_frame : ∀ (a : α) (st st' : Data 22),
      st'.regs regRowAux0 = st.regs regRowAux0 →
      st'.regs regRowAux1 = st.regs regRowAux1 →
      RowInv a st → RowInv a st')
    (hinner : ∀ (s t : ℕ) (hs : s < x.length) (ht : t < y.length) (st : Data 22),
      GridFixedRegs x₀ st →
      st.regs regOne = 1 →
      (∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr) →
      RowInv x[x.length - 1 - s] st →
      st.regs regA = encSym x[x.length - 1 - s] →
      st.regs regB = encSym y[y.length - 1 - t] →
      st.regs regDiag = D.value (x.drop (x.length - s)) (y.drop (y.length - t)) →
      st.regs regUp = D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) →
      st.regs regCur = D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t)) →
      ∃ st', ExecWithin w innerCell st st' Tc ∧
        st'.mem = st.mem ∧
        GridFixedRegs x₀ st' ∧
        st'.regs regOne = 1 ∧
        st'.regs regS = st.regs regS ∧
        st'.regs regT = st.regs regT ∧
        st'.regs regA = st.regs regA ∧
        st'.regs regUp = st.regs regUp ∧
        RowInv x[x.length - 1 - s] st' ∧
        st'.regs regNext = D.consCons x[x.length - 1 - s] y[y.length - 1 - t]
          (D.value (x.drop (x.length - s)) (y.drop (y.length - t)))
          (D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))))
          (D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t)))) :
    ∃ xf, ExecWithin w (gridCode D.nilNil initCell borderCell innerCell) x₀ xf
      (x.length * y.length * (Tc + 15) + x.length * (Tb + 12) + y.length * (Ti + 9) + 11) ∧
      xf.regs regCur = D.value x y := by
  let dpBase := x₀.regs regDPBase
  have hy_len : x₀.regs regN = y.length := hn
  have hx_len : x₀.regs regM = x.length := hm
  have read_y_rev : ∀ (m : ℕ → ℕ) (t : ℕ) (_ht : t < y.length),
      (∀ addr < x₀.regs regDPBase, m addr = x₀.mem addr) →
      m (x₀.regs regYBase + y.length - 1 - t) = encSym y[y.length - 1 - t] := by
    intro m t ht hlt
    rw [show x₀.regs regYBase + y.length - 1 - t = x₀.regs regYBase + (y.length - 1 - t) by omega,
      hlt _ (by omega)]
    exact hymem (y.length - 1 - t) (by omega)
  have hfix₀ : GridFixedRegs x₀ x₀ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  let Pinit (t : ℕ) (st : Data 22) : Prop :=
    GridFixedRegs x₀ st ∧ st.regs regOne = 1 ∧
      st.regs regCur = D.value [] (y.drop (y.length - t)) ∧
      st.mem = dpInitMem x₀.mem dpBase D y t
  have hsetup : ∃ x₁, ExecWithin w (gridSetup D.nilNil) x₀ x₁ 4 ∧
      x₁.regs regT = 0 ∧ Pinit 0 x₁ := by
    unfold gridSetup
    wram_exec * [hfit1, hfitNil]
    refine ⟨by wram_simp *, by regs_frame, by wram_simp *, ?_, ?_⟩
    · wram_simp *
      rw [List.drop_length, D.value_nil_nil]
    · rw [Data.set_mem, Data.write_mem]
      exact dpInitMem_zero x₀.mem dpBase D y
  obtain ⟨x₁, hsetup_ex, hx₁_t0, hx₁_P0⟩ := hsetup
  have hinitBody : ∀ st, Pinit (st.regs regT) st → st.regs regT < y.length →
      ∃ st', ExecWithin w (gridInitBody initCell) st st' (Ti + 7) ∧
        Pinit (st.regs regT + 1) st' ∧ st'.regs regT = st.regs regT + 1 := by
    intro st ⟨hfix, hone, hcur, hmem⟩ ht
    set t := st.regs regT with ht_def
    have ht_reg : st.regs regT = t := ht_def.symm
    have hreadB_mem := read_y_rev st.mem t ht
      (fun addr ha => by rw [hmem, dpInitMem_lt _ _ _ _ _ _ ha])
    have hpre : ∃ stA, ExecWithin w gridInitPre st stA 4 ∧
        stA.mem = st.mem ∧ GridFixedRegs x₀ stA ∧ stA.regs regOne = 1 ∧
        stA.regs regT = t ∧ stA.regs regB = encSym y[y.length - 1 - t] ∧
        stA.regs regCur = D.value [] (y.drop (y.length - t)) := by
      unfold gridInitPre
      wram_exec * [hy_len]
      refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, ?_, by wram_simp *⟩
      wram_simp * [hy_len, hreadB_mem]
    obtain ⟨stA, hpre_ex, hstA_mem, hstA_fix, hstA_one, hstA_t, hstA_b, hstA_cur⟩ := hpre
    obtain ⟨stB, hcell, hstB_mem, hstB_fix, hstB_one, hstB_t, hstB_cur⟩ :=
      hinit t ht stA hstA_fix hstA_one
        (fun addr ha => by rw [hstA_mem, hmem, dpInitMem_lt _ _ _ _ _ _ ha])
        hstA_b hstA_cur
    have hstB_t' : stB.regs regT = t := hstB_t.trans hstA_t
    have hval_next : D.nilCons y[y.length - 1 - t] (D.value [] (y.drop (y.length - t))) =
        D.value [] (y.drop (y.length - (t + 1))) := by
      rw [drop_sub_succ_eq_cons y ht, D.value_nil_cons]
    have hpost : ∃ stC, ExecWithin w gridInitPost stB stC 3 ∧
        Pinit (t + 1) stC ∧ stC.regs regT = t + 1 := by
      unfold gridInitPost
      wram_exec *
      refine ⟨⟨by regs_frame, by wram_simp *, ?_, ?_⟩, by wram_simp *⟩
      · wram_simp *; exact hval_next
      · rw [Data.write_mem, Data.set_mem, Data.set_mem, hstB_mem, hstA_mem, hmem, hval_next]
        exact dpInitMem_succ x₀.mem dpBase D y ht
    obtain ⟨stC, hpost_ex, hstC_P, hstC_t⟩ := hpost
    exact ⟨stC, (hpre_ex.seq (hcell.seq hpost_ex)).mono (by omega), hstC_P, hstC_t⟩
  obtain ⟨x₂, hinitLoop, ⟨hx₂_fix, hx₂_one, _, hx₂_mem⟩, _⟩ :=
    ExecWithin.loop_count Pinit
      (fun _ h => h.1.n.trans hn)
      hinitBody (hx₁_t0.symm ▸ Nat.zero_le y.length) (hx₁_t0.symm ▸ hx₁_P0)
  rw [hx₁_t0, Nat.sub_zero] at hinitLoop
  let x₃ := x₂.set regS 0
  have hsetS : ExecWithin w (ram[ regS ← #0 ] : Code .standard 22) x₂ x₃ 1 := by wram_exec
  let Pouter (s : ℕ) (st : Data 22) : Prop :=
    GridFixedRegs x₀ st ∧ st.regs regOne = 1 ∧ st.mem = dpRowMem x₀.mem dpBase D x y s
  have houterBody : ∀ st, Pouter (st.regs regS) st → st.regs regS < x.length →
      ∃ st', ExecWithin w (gridOuterBody borderCell innerCell) st st'
          (y.length * (Tc + 15) + Tb + 10) ∧
        Pouter (st.regs regS + 1) st' ∧ st'.regs regS = st.regs regS + 1 := by
    intro st ⟨hfix, hone, hmem⟩ hs
    set s := st.regs regS with hs_def
    have hs_reg : st.regs regS = s := hs_def.symm
    have hreadA_mem : st.mem (x₀.regs regXBase + x.length - 1 - s) =
        encSym x[x.length - 1 - s] := by
      rw [show x₀.regs regXBase + x.length - 1 - s =
        x₀.regs regXBase + (x.length - 1 - s) by omega,
        hmem, dpRowMem_lt _ _ _ _ _ _ _ (by omega)]
      exact hxmem (x.length - 1 - s) (by omega)
    have hreadDiag_mem : st.mem (x₀.regs regDPBase) = D.value (x.drop (x.length - s)) [] := by
      rw [hmem]
      simpa only [Nat.add_zero, Nat.sub_zero, List.drop_length] using
        dpRowMem_read x₀.mem dpBase D x y s 0 (Nat.zero_le _)
    have hpreOut : ∃ st1, ExecWithin w gridOuterPre st st1 5 ∧
        st1.mem = st.mem ∧ GridFixedRegs x₀ st1 ∧ st1.regs regOne = 1 ∧ st1.regs regS = s ∧
        st1.regs regA = encSym x[x.length - 1 - s] ∧
        st1.regs regDiag = D.value (x.drop (x.length - s)) [] := by
      unfold gridOuterPre
      wram_exec * [hx_len]
      refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, ?_, ?_⟩
      · wram_simp * [hx_len, hreadA_mem]
      · wram_simp * [hreadDiag_mem]
    obtain ⟨st1, hpreOut_ex, hst1_mem, hst1_fix, hst1_one, hst1_s, hst1_a, hst1_diag⟩ := hpreOut
    obtain ⟨st2, hbord, hst2_mem, hst2_fix, hst2_one, hst2_s, hst2_a, hst2_diag, hst2_inv,
        hst2_cur⟩ :=
      hborder s hs st1 hst1_fix hst1_one
        (fun addr ha => by rw [hst1_mem, hmem, dpRowMem_lt _ _ _ _ _ _ _ ha])
        hst1_a hst1_diag
    have hst2_s' : st2.regs regS = s := hst2_s.trans hst1_s
    have hst2_a' : st2.regs regA = encSym x[x.length - 1 - s] := hst2_a.trans hst1_a
    have hst2_diag' : st2.regs regDiag = D.value (x.drop (x.length - s)) [] :=
      hst2_diag.trans hst1_diag
    have hval_s0 : D.consNil x[x.length - 1 - s] (D.value (x.drop (x.length - s)) []) =
        D.value (x.drop (x.length - (s + 1))) [] := by
      rw [drop_sub_succ_eq_cons x hs, D.value_cons_nil]
    let Pinner (t : ℕ) (q : Data 22) : Prop :=
      GridFixedRegs x₀ q ∧ q.regs regOne = 1 ∧ q.regs regS = s ∧
        q.regs regA = encSym x[x.length - 1 - s] ∧
        RowInv x[x.length - 1 - s] q ∧
        q.regs regDiag = D.value (x.drop (x.length - s)) (y.drop (y.length - t)) ∧
        q.regs regCur = D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t)) ∧
        q.mem = dpMidMem x₀.mem dpBase D x y s t
    have hmid : ∃ st3, ExecWithin w gridOuterMid st2 st3 2 ∧
        st3.regs regT = 0 ∧ Pinner 0 st3 := by
      unfold gridOuterMid
      wram_exec *
      refine ⟨by wram_simp *, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
        hRowInv_frame _ st2 _ (by wram_simp) (by wram_simp) hst2_inv, ?_, ?_, ?_⟩
      · wram_simp *; rw [List.drop_length]
      · wram_simp *; rw [hval_s0, List.drop_length]
      · rw [Data.set_mem, Data.write_mem, hst2_mem, hst1_mem, hmem, hval_s0]
        exact dpMidMem_zero x₀.mem dpBase D x y s
    obtain ⟨st3, hmid_ex, hst3_t0, hst3_P0⟩ := hmid
    have hinnerBody : ∀ q, Pinner (q.regs regT) q → q.regs regT < y.length →
        ∃ q', ExecWithin w (gridInnerBody innerCell) q q' (Tc + 13) ∧
          Pinner (q.regs regT + 1) q' ∧ q'.regs regT = q.regs regT + 1 := by
      intro q ⟨hq_fix, hq_one, hq_s, hq_a, hq_inv, hq_diag, hq_cur, hq_mem⟩ ht
      set t := q.regs regT with ht_def
      have ht_reg : q.regs regT = t := ht_def.symm
      have hreadB_in := read_y_rev q.mem t ht
        (fun addr ha => by rw [hq_mem, dpMidMem_lt _ _ _ _ _ _ _ _ ha])
      have hreadUp_in : q.mem (x₀.regs regDPBase + t + 1) =
          D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) := by
        rw [hq_mem]; exact dpMidMem_read_next x₀.mem dpBase D x y s ht
      have hpreIn : ∃ q1, ExecWithin w gridInnerPre q q1 7 ∧
          q1.mem = q.mem ∧ GridFixedRegs x₀ q1 ∧ q1.regs regOne = 1 ∧ q1.regs regS = s ∧
          q1.regs regT = t ∧ q1.regs regA = encSym x[x.length - 1 - s] ∧
          q1.regs regB = encSym y[y.length - 1 - t] ∧
          RowInv x[x.length - 1 - s] q1 ∧
          q1.regs regDiag = D.value (x.drop (x.length - s)) (y.drop (y.length - t)) ∧
          q1.regs regUp = D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) ∧
          q1.regs regCur = D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t)) := by
        unfold gridInnerPre
        wram_exec * [hy_len]
        refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
          by wram_simp *, ?_,
          hRowInv_frame _ q _ (by wram_simp) (by wram_simp) hq_inv,
          by wram_simp *, ?_, by wram_simp *⟩
        · wram_simp * [hy_len, hreadB_in]
        · wram_simp * [hreadUp_in]
      obtain ⟨q1, hpreIn_ex, hq1_mem, hq1_fix, hq1_one, hq1_s, hq1_t, hq1_a, hq1_b, hq1_inv,
          hq1_diag, hq1_up, hq1_cur⟩ := hpreIn
      obtain ⟨q2, hinCell, hq2_mem, hq2_fix, hq2_one, hq2_s, hq2_t, hq2_a, hq2_up, hq2_inv,
          hq2_next⟩ :=
        hinner s t hs ht q1 hq1_fix hq1_one
          (fun addr ha => by rw [hq1_mem, hq_mem, dpMidMem_lt _ _ _ _ _ _ _ _ ha])
          hq1_inv hq1_a hq1_b hq1_diag hq1_up hq1_cur
      have hq2_s' : q2.regs regS = s := hq2_s.trans hq1_s
      have hq2_t' : q2.regs regT = t := hq2_t.trans hq1_t
      have hq2_a' : q2.regs regA = encSym x[x.length - 1 - s] := hq2_a.trans hq1_a
      have hq2_up' : q2.regs regUp =
          D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) := hq2_up.trans hq1_up
      have hval_st : D.consCons x[x.length - 1 - s] y[y.length - 1 - t]
          (D.value (x.drop (x.length - s)) (y.drop (y.length - t)))
          (D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))))
          (D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t))) =
          D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - (t + 1))) := by
        rw [drop_sub_succ_eq_cons x hs, drop_sub_succ_eq_cons y ht, D.value_cons_cons]
      have hpostIn : ∃ q3, ExecWithin w gridInnerPost q2 q3 6 ∧
          Pinner (t + 1) q3 ∧ q3.regs regT = t + 1 := by
        unfold gridInnerPost
        wram_exec *
        refine ⟨⟨by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
          hRowInv_frame _ q2 _ (by wram_simp) (by wram_simp) hq2_inv,
          by wram_simp *, ?_, ?_⟩, by wram_simp *⟩
        · wram_simp *; exact hval_st
        · rw [Data.set_mem, Data.set_mem, Data.set_mem, Data.write_mem,
            Data.set_mem, Data.set_mem, hq2_mem, hq1_mem, hq_mem, hval_st]
          exact dpMidMem_succ x₀.mem dpBase D x y s ht
      obtain ⟨q3, hpostIn_ex, hq3_P, hq3_t⟩ := hpostIn
      exact ⟨q3, (hpreIn_ex.seq (hinCell.seq hpostIn_ex)).mono (by omega), hq3_P, hq3_t⟩
    obtain ⟨st4, hinLoop, ⟨hst4_fix, hst4_one, hst4_s, _, _, _, _, hst4_mem⟩, _⟩ :=
      ExecWithin.loop_count Pinner
        (fun _ h => h.1.n.trans hn)
        hinnerBody (hst3_t0.symm ▸ Nat.zero_le y.length) (hst3_t0.symm ▸ hst3_P0)
    rw [hst3_t0, Nat.sub_zero] at hinLoop
    have hincS : ExecWithin w (ram[ regS ← regS + regOne ]) st4 (st4.set regS (s + 1)) 1 := by
      wram_exec *
    refine ⟨st4.set regS (s + 1),
      (hpreOut_ex.seq (hbord.seq (hmid_ex.seq (hinLoop.seq hincS)))).mono (le_of_eq (by ring)),
      ⟨by regs_frame, Data.set_regs_of_ne (by decide) (s + 1) |>.trans hst4_one, ?_⟩,
      Data.set_regs_self st4 regS (s + 1)⟩
    rw [Data.set_mem, hst4_mem, dpMidMem_end]
  have hx₃_s0 : x₃.regs regS = 0 := rfl
  have hx₃_P0 : Pouter 0 x₃ := ⟨by regs_frame,
    Data.set_regs_of_ne (by decide) 0 |>.trans hx₂_one,
    by rw [Data.set_mem, hx₂_mem, dpInitMem_end]⟩
  obtain ⟨x₄, houterLoop, ⟨hx₄_fix, _, hx₄_mem⟩, _⟩ :=
    ExecWithin.loop_count Pouter
      (fun _ h => h.1.m.trans hm)
      houterBody (hx₃_s0.symm ▸ Nat.zero_le x.length) (hx₃_s0.symm ▸ hx₃_P0)
  rw [hx₃_s0, Nat.sub_zero] at houterLoop
  have hy_len : x₀.regs regN = y.length := hn
  have hfin : ∃ xf, ExecWithin w gridFinalLoad x₄ xf 2 ∧ xf.regs regCur = D.value x y := by
    unfold gridFinalLoad
    wram_exec * [hy_len]
    wram_simp * [hy_len, hx₄_mem]
    rw [dpRowMem_read x₀.mem dpBase D x y x.length y.length le_rfl]
    simp
  obtain ⟨xf, hfin_ex, hres⟩ := hfin
  exact ⟨xf, (hsetup_ex.seq (hinitLoop.seq (hsetS.seq (houterLoop.seq hfin_ex)))).mono
    (le_of_eq (by ring)), hres⟩

/-! ## Shared three-way minimum tail -/

/-- Set `regNext` to `min (regs regNext) (min (regs regTmp0) (regs regTmp1))` in `≤ 6` steps,
modifying only `regNext` and `regTmp0`. -/
private def min3Tail : Code .standard 22 :=
  .seq
    (.branch (.lt regTmp0 regTmp1)
      (ram[ regTmp0 ← regTmp0 ])
      (ram[ regTmp0 ← regTmp1 ]))
    (.branch (.lt regNext regTmp0)
      (ram[ regNext ← regNext ])
      (ram[ regNext ← regTmp0 ]))

private theorem exec_min3Tail {w : ℕ} (st : Data 22) :
    ∃ st', ExecWithin w min3Tail st st' 6 ∧
      st'.mem = st.mem ∧
      (∀ i : Fin 22, i.val < 19 → st'.regs i = st.regs i) ∧
      st'.regs regNext = min (st.regs regNext) (min (st.regs regTmp0) (st.regs regTmp1)) := by
  unfold min3Tail
  wram_exec
  all_goals refine ⟨rfl, fun i hi => ?_, by wram_simp; omega⟩
  all_goals
    rw [Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
      Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide))]

/-! ## Word-encoded sequence pairs: LCS length and unit-cost edit distance -/

/-- A pair of word-encoded sequences `src, tgt : List ℕ` for longest-common-subsequence length and
unit-cost Levenshtein edit distance on the Word-RAM. Letters may be arbitrary `w`-bit words. -/
structure WordSeqPair where
  /-- Source sequence `x`. -/
  src : List ℕ
  /-- Target sequence `y`. -/
  tgt : List ℕ

namespace WordSeqPair

/-- Word-RAM input layout `[|src|, |tgt|] ++ src ++ tgt` of length `2 + |src| + |tgt|`. -/
@[expose] def encode (I : WordSeqPair) : List ℕ :=
  [I.src.length, I.tgt.length] ++ I.src ++ I.tgt

@[simp]
theorem length_encode (I : WordSeqPair) : I.encode.length = 2 + I.src.length + I.tgt.length := by
  simp [encode]
  omega

/-- Word-width condition for `WordSeqPair`: one-past-end working-row addresses and all DP entries
fit in `w` bits. -/
abbrev FitsWidth (I : WordSeqPair) (w : ℕ) : Prop :=
  Fits w (I.src.length + 2 * I.tgt.length + 4)

/-- Every `WordSeqPair` admits a fitting word width. -/
theorem inputAdmissible : InputAdmissible (fun _ => encode) FitsWidth := by
  intro I
  obtain ⟨w, hw, hfit⟩ := InputFits.exists_width I.encode (I.src.length + 2 * I.tgt.length + 4)
  exact ⟨w, (fits_self _).mono hw, hfit⟩

end WordSeqPair

private def seqPairSetup : Code .standard 22 :=
  ram[
    regTmp0 ← #1; regM ← *regTmp0;
    regTmp0 ← #2; regN ← *regTmp0;
    regXBase ← #3;
    regYBase ← regXBase + regM;
    regDPBase ← regYBase + regN ]

private theorem exec_seqPairSetup {w : ℕ} (I : WordSeqPair) (hw : I.FitsWidth w) :
    ∃ x₀, ExecWithin w seqPairSetup (.init I.encode) x₀ 7 ∧
      x₀.mem = (Data.init I.encode : Data 22).mem ∧
      x₀.regs regM = I.src.length ∧
      x₀.regs regN = I.tgt.length ∧
      x₀.regs regXBase = 3 ∧
      x₀.regs regYBase = 3 + I.src.length ∧
      x₀.regs regDPBase = 3 + I.src.length + I.tgt.length := by
  have hm1 : (Data.init I.encode : Data 22).mem 1 = I.src.length := by simp [WordSeqPair.encode]
  have hm2 : (Data.init I.encode : Data 22).mem 2 = I.tgt.length := by simp [WordSeqPair.encode]
  unfold seqPairSetup
  wram_exec *
  · exact ⟨rfl, by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *⟩
  all_goals exact hw.of_le (by omega)

private theorem seqPair_read_src (I : WordSeqPair) {i : ℕ} (hi : i < I.src.length) :
    (Data.init I.encode : Data 22).mem (3 + i) = I.src[i] := by
  have h := Data.init_realizes_append (r := 22) [I.src.length, I.tgt.length] I.src I.tgt ⟨i, hi⟩
  change (Data.init ([I.src.length, I.tgt.length] ++ (I.src ++ I.tgt)) : Data 22).mem (2 + 1 + i) =
    I.src[i] at h
  rwa [← List.append_assoc] at h

private theorem seqPair_read_tgt (I : WordSeqPair) {j : ℕ} (hj : j < I.tgt.length) :
    (Data.init I.encode : Data 22).mem (3 + I.src.length + j) = I.tgt[j] := by
  have h := Data.init_realizes_append (r := 22) ([I.src.length, I.tgt.length] ++ I.src) I.tgt []
    ⟨j, hj⟩
  change (Data.init (([I.src.length, I.tgt.length] ++ I.src) ++ (I.tgt ++ [])) : Data 22).mem
    (([I.src.length, I.tgt.length] ++ I.src).length + 1 + j) = I.tgt[j] at h
  have haddr : ([I.src.length, I.tgt.length] ++ I.src).length + 1 + j = 3 + I.src.length + j := by
    simp; omega
  rwa [List.append_nil, haddr] at h

/-- Shared execution of `.seq seqPairSetup (gridCode 0 initCell borderCell innerCell)` for
`WordSeqPair` programs with `D.nilNil = 0` and no per-row auxiliary invariant. -/
private theorem exec_seqPairGrid {w : ℕ} (Ti Tb Tc : ℕ) (D : GridDP ℕ ℕ)
    (hNil : D.nilNil = 0) (I : WordSeqPair) (hw : I.FitsWidth w)
    (initCell borderCell innerCell : Code .standard 22)
    (hinit : ∀ (t : ℕ) (_ht : t < I.tgt.length) (st : Data 22),
      st.regs regOne = 1 →
      st.regs regCur = D.value [] (I.tgt.drop (I.tgt.length - t)) →
      ∃ st', ExecWithin w initCell st st' Ti ∧
        st'.mem = st.mem ∧
        (∀ i : Fin 22, i ≠ regCur → st'.regs i = st.regs i) ∧
        st'.regs regCur =
          D.nilCons I.tgt[I.tgt.length - 1 - t] (D.value [] (I.tgt.drop (I.tgt.length - t))))
    (hborder : ∀ (s : ℕ) (_hs : s < I.src.length) (st : Data 22),
      st.regs regOne = 1 →
      st.regs regDiag = D.value (I.src.drop (I.src.length - s)) [] →
      ∃ st', ExecWithin w borderCell st st' Tb ∧
        st'.mem = st.mem ∧
        (∀ i : Fin 22, i ≠ regCur → st'.regs i = st.regs i) ∧
        st'.regs regCur =
          D.consNil I.src[I.src.length - 1 - s] (D.value (I.src.drop (I.src.length - s)) []))
    (hinner : ∀ (s t : ℕ) (_hs : s < I.src.length) (_ht : I.tgt.length > t) (st : Data 22),
      st.regs regOne = 1 →
      st.regs regA = I.src[I.src.length - 1 - s] →
      st.regs regB = I.tgt[I.tgt.length - 1 - t] →
      st.regs regDiag = D.value (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - t)) →
      st.regs regUp =
        D.value (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - (t + 1))) →
      st.regs regCur =
        D.value (I.src.drop (I.src.length - (s + 1))) (I.tgt.drop (I.tgt.length - t)) →
      ∃ st', ExecWithin w innerCell st st' Tc ∧
        st'.mem = st.mem ∧
        (∀ i : Fin 22, i.val < 19 → st'.regs i = st.regs i) ∧
        st'.regs regNext = D.consCons I.src[I.src.length - 1 - s] I.tgt[I.tgt.length - 1 - t]
          (D.value (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - t)))
          (D.value (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - (t + 1))))
          (D.value (I.src.drop (I.src.length - (s + 1))) (I.tgt.drop (I.tgt.length - t)))) :
    ∃ xf, ExecWithin w (.seq seqPairSetup (gridCode 0 initCell borderCell innerCell))
        (.init I.encode) xf
        (I.src.length * I.tgt.length * (Tc + 15) + I.src.length * (Tb + 12) +
          I.tgt.length * (Ti + 9) + 18) ∧
      xf.regs regCur = D.value I.src I.tgt := by
  obtain ⟨x₀, hsetup, hmem0, hm, hn, hxb, hyb, hdpb⟩ := exec_seqPairSetup I hw
  have hgrid := exec_gridCode Ti Tb Tc D id I.src I.tgt x₀
    initCell borderCell innerCell (fun _ _ => True)
    hm hn (by omega) (by omega)
    (fun i hi => by rw [hmem0, hxb]; exact seqPair_read_src I hi)
    (fun j hj => by rw [hmem0, hyb]; exact seqPair_read_tgt I hj)
    (hw.of_le (by omega)) (hNil ▸ fits_zero w)
    (by rw [hdpb]; exact hw.of_le (by omega))
    (hw.of_le (by omega))
    (fun t ht st hfix hone _ _ hcur => by
      obtain ⟨st', hex, hmem', hfr, hcur'⟩ := hinit t ht st hone hcur
      exact ⟨st', hex, hmem', by regs_frame, by regs_frame, by regs_frame, hcur'⟩)
    (fun s hs st hfix hone _ _ hdiag => by
      obtain ⟨st', hex, hmem', hfr, hcur'⟩ := hborder s hs st hone hdiag
      exact ⟨st', hex, hmem', by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        by regs_frame, trivial, hcur'⟩)
    (fun _ _ _ _ _ _ => trivial)
    (fun s t hs ht st hfix hone _ _ ha hb hdiag hup hcur => by
      obtain ⟨st', hex, hmem', hfr, hnext'⟩ := hinner s t hs ht st hone ha hb hdiag hup hcur
      exact ⟨st', hex, hmem',
        ⟨(hfr _ (by decide)).trans hfix.m, (hfr _ (by decide)).trans hfix.n,
         (hfr _ (by decide)).trans hfix.xb, (hfr _ (by decide)).trans hfix.yb,
         (hfr _ (by decide)).trans hfix.dpb, (hfr _ (by decide)).trans hfix.sig,
         (hfr _ (by decide)).trans hfix.delb, (hfr _ (by decide)).trans hfix.insb,
         (hfr _ (by decide)).trans hfix.subb⟩,
        (hfr _ (by decide)).trans hone, hfr _ (by decide), hfr _ (by decide),
        hfr _ (by decide), hfr _ (by decide), trivial, hnext'⟩)
  rw [hNil] at hgrid
  obtain ⟨xf, hexec, hres⟩ := hgrid
  exact ⟨xf, (hsetup.seq hexec).mono (by omega), hres⟩

/-! ### Longest common subsequence on the Word-RAM -/

private def lcsInnerCell : Code .standard 22 :=
  .branch (.eq regA regB)
    (ram[ regNext ← regDiag + regOne ])
    (.branch (.lt regUp regCur)
      (ram[ regNext ← regCur ])
      (ram[ regNext ← regUp ]))

private def lcsLengthCode : Code .standard 22 :=
  .seq seqPairSetup
    (gridCode 0 (ram[ regCur ← regCur ]) (ram[ regCur ← regDiag ]) lcsInnerCell)

/-- Fixed standard-basis Word-RAM program computing `lcsLength I.src I.tgt` on `I : WordSeqPair`. -/
def lcsLengthProgram : Program .standard 22 :=
  lcsLengthCode.program regCur

private theorem exec_lcsLengthCode {w : ℕ} (I : WordSeqPair) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w lcsLengthCode (.init I.encode) xf
        (20 * I.src.length * I.tgt.length + 13 * I.src.length + 10 * I.tgt.length + 18) ∧
      xf.regs regCur = lcsLength I.src I.tgt := by
  obtain ⟨xf, hexec, hres⟩ := exec_seqPairGrid 1 1 5 (lcsTable (α := ℕ)) rfl I hw
    (ram[ regCur ← regCur ]) (ram[ regCur ← regDiag ]) lcsInnerCell
    (fun _ _ st _ hcur => by
      wram_exec *
      exact ⟨rfl, fun i hi => Data.set_regs_of_ne hi _, by wram_simp *; rfl⟩)
    (fun _ _ st _ hdiag => by
      wram_exec *
      exact ⟨rfl, fun i hi => Data.set_regs_of_ne hi _, by wram_simp *; rfl⟩)
    (fun s t hs _ht st hone ha hb hdiag hup hcur => by
      have hd_le : lcsLength (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - t)) ≤ s := by
        have := lcsLength_le_left (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - t))
        simp only [List.length_drop] at this; omega
      unfold lcsInnerCell
      wram_exec *
      · refine ⟨rfl,
          fun i hi => Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)) _, ?_⟩
        wram_simp *
        change _ = if I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] then _ + 1 else _
        rw [ite_eq_left hc]
      · rename_i hc1
        refine ⟨rfl,
          fun i hi => Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)) _, ?_⟩
        wram_simp *
        change _ = if I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] then _ else max _ _
        rw [ite_eq_right hc1]; omega
      · rename_i hc1
        refine ⟨rfl,
          fun i hi => Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)) _, ?_⟩
        wram_simp *
        change _ = if I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] then _ else max _ _
        rw [ite_eq_right hc1]; omega
      · change Fits w (lcsLength (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - t)) + 1)
        exact hw.of_le (by omega))
  exact ⟨xf, hexec.mono (le_of_eq (by ring)), hres⟩

/-- **Word-RAM running time of longest common subsequence.** The fixed standard-basis program
`lcsLengthProgram` computes `lcsLength I.src I.tgt` in at most `20 (|x| + 1)(|y| + 1)`
instructions (including input header reads and `halt`) at every fitting word width `w`. -/
theorem computesInTime_lcsLength :
    lcsLengthProgram.ComputesInTime (fun _ => WordSeqPair.encode)
      (fun I _ => 20 * (I.src.length + 1) * (I.tgt.length + 1))
      WordSeqPair.FitsWidth (fun I => lcsLength I.src I.tgt) := by
  refine (lcsLengthCode.computesInTime_program regCur
    (time := fun I _ =>
      20 * I.src.length * I.tgt.length + 13 * I.src.length + 10 * I.tgt.length + 18) ?_).mono ?_
    (fun _ _ h => h)
  · intro I w hw _
    exact exec_lcsLengthCode I hw
  · intro I _
    nlinarith

/-- Uniform Word-RAM computability of longest-common-subsequence length in
`20 (|x| + 1)(|y| + 1)` instructions, bundling width admissibility
(`WordSeqPair.inputAdmissible`). -/
theorem uniformComputableInTime_lcsLength :
    UniformComputableInTime .standard (fun I : WordSeqPair => lcsLength I.src I.tgt)
      (fun _ => WordSeqPair.encode)
      (fun I _ => 20 * (I.src.length + 1) * (I.tgt.length + 1))
      WordSeqPair.FitsWidth :=
  ⟨22, lcsLengthProgram, computesInTime_lcsLength, WordSeqPair.inputAdmissible⟩

/-! ### Unit-cost Levenshtein edit distance on the Word-RAM -/

private def unitInnerCell : Code .standard 22 :=
  .seq
    (.seq
      (.branch (.eq regA regB)
        (ram[ regNext ← regDiag ])
        (ram[ regNext ← regDiag + regOne ]))
      (ram[ regTmp0 ← regUp + regOne; regTmp1 ← regCur + regOne ]))
    min3Tail

private def unitEditDistCode : Code .standard 22 :=
  .seq seqPairSetup
    (gridCode 0
      (ram[ regCur ← regCur + regOne ])
      (ram[ regCur ← regDiag + regOne ])
      unitInnerCell)

/-- Fixed standard-basis Word-RAM program computing `editDist Costs.unit I.src I.tgt` on
`I : WordSeqPair`. -/
def unitEditDistProgram : Program .standard 22 :=
  unitEditDistCode.program regCur

private theorem exec_unitEditDistCode {w : ℕ} (I : WordSeqPair) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w unitEditDistCode (.init I.encode) xf
        (26 * I.src.length * I.tgt.length + 13 * I.src.length + 10 * I.tgt.length + 18) ∧
      xf.regs regCur = editDist Costs.unit I.src I.tgt := by
  obtain ⟨xf, hexec, hres⟩ := exec_seqPairGrid 1 1 11 (wagnerFischer (Costs.unit (α := ℕ))) rfl I hw
    (ram[ regCur ← regCur + regOne ]) (ram[ regCur ← regDiag + regOne ]) unitInnerCell
    (fun t ht st hone hcur => by
      have hle : editDist Costs.unit [] (I.tgt.drop (I.tgt.length - t)) ≤ t := by
        have := editDist_unit_le_add ([] : List ℕ) (I.tgt.drop (I.tgt.length - t))
        simp only [List.length_nil, List.length_drop] at this; omega
      wram_exec *
      · refine ⟨rfl, fun i hi => Data.set_regs_of_ne hi _, ?_⟩
        wram_simp *; change _ = 1 + _; omega
      · change Fits w (editDist Costs.unit [] (I.tgt.drop (I.tgt.length - t)) + 1)
        exact hw.of_le (by omega))
    (fun s hs st hone hdiag => by
      have hle : editDist Costs.unit (I.src.drop (I.src.length - s)) [] ≤ s := by
        have := editDist_unit_le_add (I.src.drop (I.src.length - s)) ([] : List ℕ)
        simp only [List.length_nil, List.length_drop] at this; omega
      wram_exec *
      · refine ⟨rfl, fun i hi => Data.set_regs_of_ne hi _, ?_⟩
        wram_simp *; change _ = 1 + _; omega
      · change Fits w (editDist Costs.unit (I.src.drop (I.src.length - s)) [] + 1)
        exact hw.of_le (by omega))
    (fun s t hs ht st hone ha hb hdiag hup hcur => by
      have hd_le : editDist Costs.unit (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - t)) ≤ s + t := by
        have := editDist_unit_le_add (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - t))
        simp only [List.length_drop] at this; omega
      have hu_le : editDist Costs.unit (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - (t + 1))) ≤ s + t + 1 := by
        have := editDist_unit_le_add (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - (t + 1)))
        simp only [List.length_drop] at this; omega
      have hl_le : editDist Costs.unit (I.src.drop (I.src.length - (s + 1)))
          (I.tgt.drop (I.tgt.length - t)) ≤ s + 1 + t := by
        have := editDist_unit_le_add (I.src.drop (I.src.length - (s + 1)))
          (I.tgt.drop (I.tgt.length - t))
        simp only [List.length_drop] at this; omega
      have hpre : ∃ s1, ExecWithin w
          (.seq
            (.branch (.eq regA regB) (ram[ regNext ← regDiag ])
              (ram[ regNext ← regDiag + regOne ]))
            (ram[ regTmp0 ← regUp + regOne; regTmp1 ← regCur + regOne ])) st s1 5 ∧
          s1.mem = st.mem ∧
          (∀ i : Fin 22, i.val < 19 → s1.regs i = st.regs i) ∧
          s1.regs regNext = (Costs.unit (α := ℕ)).sub I.src[I.src.length - 1 - s]
            I.tgt[I.tgt.length - 1 - t] + st.regs regDiag ∧
          s1.regs regTmp0 = 1 + st.regs regUp ∧
          s1.regs regTmp1 = 1 + st.regs regCur := by
        wram_exec *
        · refine ⟨rfl, fun i hi => ?_, ?_, by wram_simp *; omega, by wram_simp *; omega⟩
          · rw [Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
              Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
              Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide))]
          · wram_simp *; rw [Costs.unit_sub, ite_eq_left hc, Nat.zero_add]
        · refine ⟨rfl, fun i hi => ?_, ?_, by wram_simp *; omega, by wram_simp *; omega⟩
          · rw [Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
              Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
              Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide))]
          · wram_simp *; rw [Costs.unit_sub, ite_eq_right hc, Nat.add_comm]
        all_goals
          first
          | (change Fits w (editDist Costs.unit (I.src.drop (I.src.length - s))
              (I.tgt.drop (I.tgt.length - (t + 1))) + 1); exact hw.of_le (by omega))
          | (change Fits w (editDist Costs.unit (I.src.drop (I.src.length - (s + 1)))
              (I.tgt.drop (I.tgt.length - t)) + 1); exact hw.of_le (by omega))
          | (change Fits w (editDist Costs.unit (I.src.drop (I.src.length - s))
              (I.tgt.drop (I.tgt.length - t)) + 1); exact hw.of_le (by omega))
      obtain ⟨s1, he1, hm1, hr1, hv1, hv0, hvt1⟩ := hpre
      obtain ⟨s2, he2, hm2, hr2, hv2⟩ := exec_min3Tail (w := w) s1
      exact ⟨s2, (he1.seq he2).mono (by omega), hm2.trans hm1,
        fun i hi => (hr2 i hi).trans (hr1 i hi),
        by rw [hv2, hv1, hv0, hvt1, hdiag, hup, hcur]; rfl⟩)
  exact ⟨xf, hexec.mono (le_of_eq (by ring)), hres⟩

/-- **Word-RAM running time of unit-cost edit distance (Levenshtein).** The fixed standard-basis
program `unitEditDistProgram` computes `editDist Costs.unit I.src I.tgt` in at most
`26 (|x| + 1)(|y| + 1)` instructions at every fitting word width `w`. -/
theorem computesInTime_unitEditDist :
    unitEditDistProgram.ComputesInTime (fun _ => WordSeqPair.encode)
      (fun I _ => 26 * (I.src.length + 1) * (I.tgt.length + 1))
      WordSeqPair.FitsWidth (fun I => editDist Costs.unit I.src I.tgt) := by
  refine (unitEditDistCode.computesInTime_program regCur
    (time := fun I _ =>
      26 * I.src.length * I.tgt.length + 13 * I.src.length + 10 * I.tgt.length + 18) ?_).mono ?_
    (fun _ _ h => h)
  · intro I w hw _
    exact exec_unitEditDistCode I hw
  · intro I _
    nlinarith

/-- Uniform Word-RAM computability of unit-cost Levenshtein edit distance in
`26 (|x| + 1)(|y| + 1)` instructions, bundling width admissibility
(`WordSeqPair.inputAdmissible`). -/
theorem uniformComputableInTime_unitEditDist :
    UniformComputableInTime .standard (fun I : WordSeqPair => editDist Costs.unit I.src I.tgt)
      (fun _ => WordSeqPair.encode)
      (fun I _ => 26 * (I.src.length + 1) * (I.tgt.length + 1))
      WordSeqPair.FitsWidth :=
  ⟨22, unitEditDistProgram, computesInTime_unitEditDist, WordSeqPair.inputAdmissible⟩

/-! ## General-cost Wagner–Fischer edit distance on the Word-RAM -/

/-- An edit-distance instance over a finite integer alphabet `Fin sigma` with arbitrary
natural-number letter costs (`Costs (Fin sigma)`). -/
structure WeightedInstance where
  /-- Alphabet size `σ`. -/
  sigma : ℕ
  /-- Deletion, insertion, and substitution costs over `Fin sigma`. -/
  costs : Costs (Fin sigma)
  /-- Source word `x`. -/
  src : List (Fin sigma)
  /-- Target word `y`. -/
  tgt : List (Fin sigma)

namespace WeightedInstance

/-- Flattened row-major `σ × σ` substitution-cost table `[costs.sub a b | a, b < σ]`. -/
@[expose] def subTable (I : WeightedInstance) : List ℕ :=
  List.ofFn fun idx : Fin (I.sigma * I.sigma) =>
    I.costs.sub ⟨idx.val / I.sigma, Nat.div_lt_of_lt_mul idx.isLt⟩
      ⟨idx.val % I.sigma, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt idx.isLt))⟩

/-- All `2σ + σ²` letter-operation cost entries of `I`. -/
@[expose] def opCosts (I : WeightedInstance) : List ℕ :=
  List.ofFn I.costs.del ++ List.ofFn I.costs.ins ++ I.subTable

/-- Word-RAM input layout `[σ, |src|, |tgt|] ++ src ++ tgt ++ del ++ ins ++ sub` of length
`3 + |src| + |tgt| + 2σ + σ²`. -/
@[expose] def encode (I : WeightedInstance) : List ℕ :=
  [I.sigma, I.src.length, I.tgt.length] ++
    I.src.map Fin.val ++ I.tgt.map Fin.val ++ I.opCosts

@[simp]
theorem length_subTable (I : WeightedInstance) : I.subTable.length = I.sigma * I.sigma := by
  simp [subTable]

@[simp]
theorem length_encode (I : WeightedInstance) :
    I.encode.length = 3 + I.src.length + I.tgt.length + 2 * I.sigma + I.sigma * I.sigma := by
  simp [encode, opCosts]
  omega

/-- Largest single letter-operation cost entry in `I`. -/
@[expose] def maxOpCost (I : WeightedInstance) : ℕ :=
  I.opCosts.foldr max 0

/-- Upper bound on all DP entries and candidate sums during Wagner–Fischer execution on `I`:
deleting all of `src` plus inserting all of `tgt`, plus `maxOpCost`. -/
@[expose] def valueBound (I : WeightedInstance) : ℕ :=
  (I.src.map I.costs.del).sum + (I.tgt.map I.costs.ins).sum + I.maxOpCost

/-- Word-width condition for `WeightedInstance`: working-row addresses and all candidate DP sums
fit in `w` bits. -/
abbrev FitsWidth (I : WeightedInstance) (w : ℕ) : Prop :=
  Fits w (I.encode.length + I.tgt.length + 4) ∧ Fits w I.valueBound

/-- `FitsWidth` already bounds the length, header words, `< σ` symbols, and `≤ maxOpCost` cost
entries of `I.encode`, so callers need not discharge `InputFits` separately. -/
theorem FitsWidth.inputFits {I : WeightedInstance} {w : ℕ} (hw : I.FitsWidth w) :
    InputFits w I.encode := by
  obtain ⟨hwAddr, hwVal⟩ := hw
  dsimp only [WeightedInstance.valueBound] at hwVal
  have hlen := I.length_encode
  refine ⟨hwAddr.of_le (by omega), fun v hv => ?_⟩
  simp only [encode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hv
  rcases hv with (((rfl | rfl | rfl) | ⟨a, _, rfl⟩) | ⟨b, _, rfl⟩) | hcost
  · exact hwAddr.of_le (by omega)
  · exact hwAddr.of_le (by omega)
  · exact hwAddr.of_le (by omega)
  · exact hwAddr.of_le (by have := a.isLt; omega)
  · exact hwAddr.of_le (by have := b.isLt; omega)
  · have hle : v ≤ I.maxOpCost := List.le_max_of_le' 0 hcost le_rfl
    exact hwVal.of_le (by omega)

/-- Every `WeightedInstance` admits a fitting word width. -/
theorem inputAdmissible : InputAdmissible (fun _ => encode) FitsWidth := by
  intro I
  let B := max (I.encode.length + I.tgt.length + 4) I.valueBound
  obtain ⟨w, hw0, _⟩ := InputFits.exists_width I.encode B
  have hwB : Fits w B := (fits_self B).mono hw0
  have hw : I.FitsWidth w := ⟨hwB.of_le (le_max_left _ _), hwB.of_le (le_max_right _ _)⟩
  exact ⟨w, hw, hw.inputFits⟩

end WeightedInstance

private theorem sum_map_drop_le {α : Type*} (f : α → ℕ) (l : List α) (k : ℕ) :
    ((l.drop k).map f).sum ≤ (l.map f).sum := by
  conv_rhs => rw [← List.take_append_drop k l, List.map_append, List.sum_append]
  omega

private theorem subTable_getElem (I : WeightedInstance) (a b : Fin I.sigma) :
    I.subTable[a.val * I.sigma + b.val]'(by
      rw [WeightedInstance.length_subTable]
      have ha : a.val + 1 ≤ I.sigma := a.isLt
      have hb : b.val < I.sigma := b.isLt
      nlinarith) = I.costs.sub a b := by
  have hpos : 0 < I.sigma := Nat.zero_lt_of_lt a.isLt
  have hdiv : (a.val * I.sigma + b.val) / I.sigma = a.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  have hmod : (a.val * I.sigma + b.val) % I.sigma = b.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  simp only [WeightedInstance.subTable, List.getElem_ofFn]
  congr 1 <;> exact Fin.ext (by assumption)

private theorem del_le_maxOpCost (I : WeightedInstance) (a : Fin I.sigma) :
    I.costs.del a ≤ I.maxOpCost :=
  List.le_max_of_le' 0
    (by simp only [WeightedInstance.opCosts, List.mem_append];
        exact Or.inl (Or.inl (List.mem_ofFn.2 ⟨a, rfl⟩))) le_rfl

private theorem ins_le_maxOpCost (I : WeightedInstance) (b : Fin I.sigma) :
    I.costs.ins b ≤ I.maxOpCost :=
  List.le_max_of_le' 0
    (by simp only [WeightedInstance.opCosts, List.mem_append];
        exact Or.inl (Or.inr (List.mem_ofFn.2 ⟨b, rfl⟩))) le_rfl

private theorem sub_le_maxOpCost (I : WeightedInstance) (a b : Fin I.sigma) :
    I.costs.sub a b ≤ I.maxOpCost :=
  List.le_max_of_le' 0
    (by simp only [WeightedInstance.opCosts, List.mem_append];
        refine Or.inr ?_; rw [← subTable_getElem I a b]; exact List.getElem_mem _) le_rfl

private def weightedSetup : Code .standard 22 :=
  ram[
    regTmp0 ← #1; regSigma ← *regTmp0;
    regTmp0 ← #2; regM ← *regTmp0;
    regTmp0 ← #3; regN ← *regTmp0;
    regXBase ← #4;
    regYBase ← regXBase + regM;
    regDelBase ← regYBase + regN;
    regInsBase ← regDelBase + regSigma;
    regSubBase ← regInsBase + regSigma;
    regTmp0 ← #0; regDPBase ← *regTmp0;
    regOne ← #1; regDPBase ← regDPBase + regOne ]

private def weightedInitCell : Code .standard 22 :=
  ram[
    regTmp0 ← regInsBase + regB;
    regTmp0 ← *regTmp0;
    regCur ← regTmp0 + regCur ]

private def weightedBorderCell : Code .standard 22 :=
  ram[
    regTmp0 ← regDelBase + regA;
    regRowAux0 ← *regTmp0;
    regCur ← regRowAux0 + regDiag;
    regTmp0 ← regA * regSigma;
    regRowAux1 ← regSubBase + regTmp0 ]

private def weightedInnerCell : Code .standard 22 :=
  .seq
    (ram[
      regTmp0 ← regRowAux1 + regB;
      regTmp0 ← *regTmp0;
      regNext ← regTmp0 + regDiag;
      regTmp0 ← regInsBase + regB;
      regTmp1 ← *regTmp0;
      regTmp1 ← regTmp1 + regCur;
      regTmp0 ← regRowAux0 + regUp ])
    min3Tail

private def weightedEditDistCode : Code .standard 22 :=
  .seq weightedSetup
    (gridCode 0 weightedInitCell weightedBorderCell weightedInnerCell)

/-- Fixed standard-basis Word-RAM program computing `editDist I.costs I.src I.tgt` on
`I : WeightedInstance`. -/
def weightedEditDistProgram : Program .standard 22 :=
  weightedEditDistCode.program regCur

private theorem weighted_read_src (I : WeightedInstance) {i : ℕ} (hi : i < I.src.length) :
    (Data.init I.encode : Data 22).mem (4 + i) = (I.src[i]).val := by
  have hi' : i < (I.src.map Fin.val).length := by simp [hi]
  have h := Data.init_realizes_append (r := 22) [I.sigma, I.src.length, I.tgt.length]
    (I.src.map Fin.val) (I.tgt.map Fin.val ++ I.opCosts) ⟨i, hi'⟩
  change (Data.init ([I.sigma, I.src.length, I.tgt.length] ++
      (I.src.map Fin.val ++ (I.tgt.map Fin.val ++ I.opCosts))) : Data 22).mem (3 + 1 + i) =
    (I.src.map Fin.val)[i] at h
  simpa [WeightedInstance.encode, List.append_assoc] using h

private theorem weighted_read_tgt (I : WeightedInstance) {j : ℕ} (hj : j < I.tgt.length) :
    (Data.init I.encode : Data 22).mem (4 + I.src.length + j) = (I.tgt[j]).val := by
  have hj' : j < (I.tgt.map Fin.val).length := by simp [hj]
  have h := Data.init_realizes_append (r := 22)
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val)
    (I.tgt.map Fin.val) I.opCosts ⟨j, hj'⟩
  change (Data.init (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val) ++
      (I.tgt.map Fin.val ++ I.opCosts)) : Data 22).mem
    (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val).length + 1 + j) =
    (I.tgt.map Fin.val)[j] at h
  have haddr : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val).length + 1 + j =
      4 + I.src.length + j := by simp; omega
  rw [haddr] at h
  simpa [WeightedInstance.encode, List.append_assoc] using h

private theorem weighted_read_del (I : WeightedInstance) (a : Fin I.sigma) :
    (Data.init I.encode : Data 22).mem (4 + I.src.length + I.tgt.length + a.val) =
      I.costs.del a := by
  have ha : a.val < (List.ofFn I.costs.del).length := by simp
  have h := Data.init_realizes_append (r := 22)
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val)
    (List.ofFn I.costs.del) (List.ofFn I.costs.ins ++ I.subTable) ⟨a.val, ha⟩
  change (Data.init (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val) ++ (List.ofFn I.costs.del ++ (List.ofFn I.costs.ins ++ I.subTable))) :
    Data 22).mem
    (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val).length +
      1 + a.val) = (List.ofFn I.costs.del)[a.val] at h
  have haddr : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val).length + 1 + a.val = 4 + I.src.length + I.tgt.length + a.val := by
    simp; omega
  rw [haddr] at h
  simpa [WeightedInstance.encode, WeightedInstance.opCosts, List.append_assoc] using h

private theorem weighted_read_ins (I : WeightedInstance) (b : Fin I.sigma) :
    (Data.init I.encode : Data 22).mem (4 + I.src.length + I.tgt.length + I.sigma + b.val) =
      I.costs.ins b := by
  have hb : b.val < (List.ofFn I.costs.ins).length := by simp
  have h := Data.init_realizes_append (r := 22)
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del)
    (List.ofFn I.costs.ins) I.subTable ⟨b.val, hb⟩
  change (Data.init (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val ++ List.ofFn I.costs.del) ++ (List.ofFn I.costs.ins ++ I.subTable)) :
    Data 22).mem
    (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del).length + 1 + b.val) = (List.ofFn I.costs.ins)[b.val] at h
  have haddr : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val ++ List.ofFn I.costs.del).length + 1 + b.val =
      4 + I.src.length + I.tgt.length + I.sigma + b.val := by simp; omega
  rw [haddr] at h
  simpa [WeightedInstance.encode, WeightedInstance.opCosts, List.append_assoc] using h

private theorem weighted_read_sub (I : WeightedInstance) (a b : Fin I.sigma) :
    (Data.init I.encode : Data 22).mem
        (4 + I.src.length + I.tgt.length + 2 * I.sigma + a.val * I.sigma + b.val) =
      I.costs.sub a b := by
  have hab : a.val * I.sigma + b.val < I.subTable.length := by
    rw [WeightedInstance.length_subTable]
    have ha : a.val + 1 ≤ I.sigma := a.isLt
    have hb : b.val < I.sigma := b.isLt
    nlinarith
  have h := Data.init_realizes_append (r := 22)
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del ++ List.ofFn I.costs.ins)
    I.subTable [] ⟨a.val * I.sigma + b.val, hab⟩
  change (Data.init (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val ++ List.ofFn I.costs.del ++ List.ofFn I.costs.ins) ++
      (I.subTable ++ [])) : Data 22).mem
    (([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del ++ List.ofFn I.costs.ins).length + 1 + (a.val * I.sigma + b.val)) =
    I.subTable[a.val * I.sigma + b.val] at h
  have haddr : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val ++ List.ofFn I.costs.del ++ List.ofFn I.costs.ins).length + 1 +
      (a.val * I.sigma + b.val) =
      4 + I.src.length + I.tgt.length + 2 * I.sigma + a.val * I.sigma + b.val := by simp; omega
  have henc : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++
      I.tgt.map Fin.val ++ List.ofFn I.costs.del ++ List.ofFn I.costs.ins) ++ I.subTable =
      I.encode := by simp [WeightedInstance.encode, WeightedInstance.opCosts, List.append_assoc]
  rw [List.append_nil, haddr, henc, subTable_getElem I a b] at h
  exact h

private theorem weighted_entry_le (I : WeightedInstance) (k₁ k₂ : ℕ) :
    (wagnerFischer I.costs).value (I.src.drop k₁) (I.tgt.drop k₂) ≤
      (I.src.map I.costs.del).sum + (I.tgt.map I.costs.ins).sum := by
  have h := editDist_le_sum_del_ins I.costs (I.src.drop k₁) (I.tgt.drop k₂)
  have h1 := sum_map_drop_le I.costs.del I.src k₁
  have h2 := sum_map_drop_le I.costs.ins I.tgt k₂
  dsimp only [editDist] at h
  omega

private theorem exec_weightedSetup {w : ℕ} (I : WeightedInstance)
    (hwAddr : Fits w (I.encode.length + I.tgt.length + 4)) :
    ∃ x₀, ExecWithin w weightedSetup (.init I.encode) x₀ 15 ∧
      x₀.mem = (Data.init I.encode : Data 22).mem ∧
      x₀.regs regM = I.src.length ∧
      x₀.regs regN = I.tgt.length ∧
      x₀.regs regXBase = 4 ∧
      x₀.regs regYBase = 4 + I.src.length ∧
      x₀.regs regDPBase = I.encode.length + 1 ∧
      x₀.regs regSigma = I.sigma ∧
      x₀.regs regDelBase = 4 + I.src.length + I.tgt.length ∧
      x₀.regs regInsBase = 4 + I.src.length + I.tgt.length + I.sigma ∧
      x₀.regs regSubBase = 4 + I.src.length + I.tgt.length + 2 * I.sigma := by
  have hlen := I.length_encode
  have hm0 : (Data.init I.encode : Data 22).mem 0 = I.encode.length := rfl
  have hm1 : (Data.init I.encode : Data 22).mem 1 = I.sigma := by simp [WeightedInstance.encode]
  have hm2 : (Data.init I.encode : Data 22).mem 2 = I.src.length := by
    simp [WeightedInstance.encode]
  have hm3 : (Data.init I.encode : Data 22).mem 3 = I.tgt.length := by
    simp [WeightedInstance.encode]
  unfold weightedSetup
  wram_exec *
  refine ⟨rfl, by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *,
    by wram_simp *, by wram_simp *, by wram_simp *, ?_⟩
  wram_simp *; omega

private theorem mul_lt_sq {σ a : ℕ} (ha : a < σ) : a * σ < σ * σ := by
  have ha1 : a + 1 ≤ σ := ha
  nlinarith

private def WeightedRowInv (I : WeightedInstance) (a : Fin I.sigma) (st : Data 22) : Prop :=
  st.regs regRowAux0 = I.costs.del a ∧
    st.regs regRowAux1 = 4 + I.src.length + I.tgt.length + 2 * I.sigma + a.val * I.sigma

private theorem exec_weightedInitCell {w : ℕ} (I : WeightedInstance) (x₀ : Data 22)
    (hwAddr : Fits w (I.encode.length + I.tgt.length + 4))
    (hwVal : Fits w I.valueBound)
    (hx₀_mem : x₀.mem = (Data.init I.encode : Data 22).mem)
    (hdpb : x₀.regs regDPBase = I.encode.length + 1)
    (hinsb : x₀.regs regInsBase = 4 + I.src.length + I.tgt.length + I.sigma)
    (t : ℕ) (ht : t < I.tgt.length) (st : Data 22)
    (hfix : GridFixedRegs x₀ st) (hone : st.regs regOne = 1)
    (hmemlt : ∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr)
    (hb : st.regs regB = (I.tgt[I.tgt.length - 1 - t]).val)
    (hcur : st.regs regCur = (wagnerFischer I.costs).value [] (I.tgt.drop (I.tgt.length - t))) :
    ∃ st', ExecWithin w weightedInitCell st st' 3 ∧
      st'.mem = st.mem ∧ GridFixedRegs x₀ st' ∧ st'.regs regOne = 1 ∧
      st'.regs regT = st.regs regT ∧
      st'.regs regCur = (wagnerFischer I.costs).nilCons I.tgt[I.tgt.length - 1 - t]
        ((wagnerFischer I.costs).value [] (I.tgt.drop (I.tgt.length - t))) := by
  dsimp only [WeightedInstance.valueBound] at hwVal
  have hlen := I.length_encode
  have hb_lt : (I.tgt[I.tgt.length - 1 - t]).val < I.sigma :=
    (I.tgt[I.tgt.length - 1 - t]).isLt
  have hread_ins :
      st.mem (4 + I.src.length + I.tgt.length + I.sigma + (I.tgt[I.tgt.length - 1 - t]).val) =
      I.costs.ins I.tgt[I.tgt.length - 1 - t] := by
    rw [hmemlt _ (by rw [hdpb]; omega), hx₀_mem]
    exact weighted_read_ins I I.tgt[I.tgt.length - 1 - t]
  have h1 := ins_le_maxOpCost I I.tgt[I.tgt.length - 1 - t]
  have h2 := weighted_entry_le I I.src.length (I.tgt.length - t)
  rw [List.drop_length] at h2
  unfold weightedInitCell
  wram_exec * [hinsb, hread_ins]
  refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, ?_⟩
  wram_simp * [hinsb, hread_ins]
  rfl

private theorem exec_weightedBorderCell {w : ℕ} (I : WeightedInstance) (x₀ : Data 22)
    (hwAddr : Fits w (I.encode.length + I.tgt.length + 4))
    (hwVal : Fits w I.valueBound)
    (hx₀_mem : x₀.mem = (Data.init I.encode : Data 22).mem)
    (hdpb : x₀.regs regDPBase = I.encode.length + 1)
    (hsig : x₀.regs regSigma = I.sigma)
    (hdelb : x₀.regs regDelBase = 4 + I.src.length + I.tgt.length)
    (hsubb : x₀.regs regSubBase = 4 + I.src.length + I.tgt.length + 2 * I.sigma)
    (s : ℕ) (hs : s < I.src.length) (st : Data 22)
    (hfix : GridFixedRegs x₀ st) (hone : st.regs regOne = 1)
    (hmemlt : ∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr)
    (ha : st.regs regA = (I.src[I.src.length - 1 - s]).val)
    (hdiag : st.regs regDiag = (wagnerFischer I.costs).value (I.src.drop (I.src.length - s)) []) :
    ∃ st', ExecWithin w weightedBorderCell st st' 5 ∧
      st'.mem = st.mem ∧ GridFixedRegs x₀ st' ∧ st'.regs regOne = 1 ∧
      st'.regs regS = st.regs regS ∧ st'.regs regA = st.regs regA ∧
      st'.regs regDiag = st.regs regDiag ∧
      WeightedRowInv I I.src[I.src.length - 1 - s] st' ∧
      st'.regs regCur = (wagnerFischer I.costs).consNil I.src[I.src.length - 1 - s]
        ((wagnerFischer I.costs).value (I.src.drop (I.src.length - s)) []) := by
  dsimp only [WeightedInstance.valueBound] at hwVal
  have hlen := I.length_encode
  have ha_lt : (I.src[I.src.length - 1 - s]).val < I.sigma :=
    (I.src[I.src.length - 1 - s]).isLt
  have hmul_lt : (I.src[I.src.length - 1 - s]).val * I.sigma < I.sigma * I.sigma :=
    mul_lt_sq ha_lt
  have hread_del :
      st.mem (4 + I.src.length + I.tgt.length + (I.src[I.src.length - 1 - s]).val) =
      I.costs.del I.src[I.src.length - 1 - s] := by
    rw [hmemlt _ (by rw [hdpb]; omega), hx₀_mem]
    exact weighted_read_del I I.src[I.src.length - 1 - s]
  have h1 := del_le_maxOpCost I I.src[I.src.length - 1 - s]
  have h2 := weighted_entry_le I (I.src.length - s) I.tgt.length
  rw [List.drop_length] at h2
  unfold weightedBorderCell
  wram_exec * [hdelb, hsig, hsubb, hread_del]
  refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
    by wram_simp *, ⟨?_, ?_⟩, ?_⟩
  · wram_simp * [hdelb, hread_del]
  · wram_simp * [hsig, hsubb]
  · wram_simp * [hdelb, hread_del]; rfl

private theorem exec_weightedInnerCell {w : ℕ} (I : WeightedInstance) (x₀ : Data 22)
    (hwAddr : Fits w (I.encode.length + I.tgt.length + 4))
    (hwVal : Fits w I.valueBound)
    (hx₀_mem : x₀.mem = (Data.init I.encode : Data 22).mem)
    (hdpb : x₀.regs regDPBase = I.encode.length + 1)
    (hinsb : x₀.regs regInsBase = 4 + I.src.length + I.tgt.length + I.sigma)
    (s t : ℕ) (hs : s < I.src.length) (ht : t < I.tgt.length) (st : Data 22)
    (hfix : GridFixedRegs x₀ st) (hone : st.regs regOne = 1)
    (hmemlt : ∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr)
    (hinv : WeightedRowInv I I.src[I.src.length - 1 - s] st)
    (_ha : st.regs regA = (I.src[I.src.length - 1 - s]).val)
    (hb : st.regs regB = (I.tgt[I.tgt.length - 1 - t]).val)
    (hdiag : st.regs regDiag =
      (wagnerFischer I.costs).value (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - t)))
    (hup : st.regs regUp =
      (wagnerFischer I.costs).value (I.src.drop (I.src.length - s))
        (I.tgt.drop (I.tgt.length - (t + 1))))
    (hcur : st.regs regCur =
      (wagnerFischer I.costs).value (I.src.drop (I.src.length - (s + 1)))
        (I.tgt.drop (I.tgt.length - t))) :
    ∃ st', ExecWithin w weightedInnerCell st st' 13 ∧
      st'.mem = st.mem ∧ GridFixedRegs x₀ st' ∧ st'.regs regOne = 1 ∧
      st'.regs regS = st.regs regS ∧ st'.regs regT = st.regs regT ∧
      st'.regs regA = st.regs regA ∧ st'.regs regUp = st.regs regUp ∧
      WeightedRowInv I I.src[I.src.length - 1 - s] st' ∧
      st'.regs regNext = (wagnerFischer I.costs).consCons I.src[I.src.length - 1 - s]
        I.tgt[I.tgt.length - 1 - t]
        ((wagnerFischer I.costs).value (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - t)))
        ((wagnerFischer I.costs).value (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - (t + 1))))
        ((wagnerFischer I.costs).value (I.src.drop (I.src.length - (s + 1)))
          (I.tgt.drop (I.tgt.length - t))) := by
  obtain ⟨hra0, hra1⟩ := hinv
  dsimp only [WeightedInstance.valueBound] at hwVal
  have hlen := I.length_encode
  have hb_lt : (I.tgt[I.tgt.length - 1 - t]).val < I.sigma :=
    (I.tgt[I.tgt.length - 1 - t]).isLt
  have hprod_lt : (I.src[I.src.length - 1 - s]).val * I.sigma +
      (I.tgt[I.tgt.length - 1 - t]).val < I.sigma * I.sigma :=
    List.mul_add_lt_sq (I.src[I.src.length - 1 - s]).isLt hb_lt
  have hread_sub :
      st.mem (4 + I.src.length + I.tgt.length + 2 * I.sigma +
        (I.src[I.src.length - 1 - s]).val * I.sigma +
        (I.tgt[I.tgt.length - 1 - t]).val) =
      I.costs.sub I.src[I.src.length - 1 - s] I.tgt[I.tgt.length - 1 - t] := by
    rw [hmemlt _ (by rw [hdpb]; omega), hx₀_mem]
    simpa only [Nat.add_assoc] using
      weighted_read_sub I I.src[I.src.length - 1 - s] I.tgt[I.tgt.length - 1 - t]
  have hread_ins :
      st.mem (4 + I.src.length + I.tgt.length + I.sigma +
        (I.tgt[I.tgt.length - 1 - t]).val) =
      I.costs.ins I.tgt[I.tgt.length - 1 - t] := by
    rw [hmemlt _ (by rw [hdpb]; omega), hx₀_mem]
    exact weighted_read_ins I I.tgt[I.tgt.length - 1 - t]
  have hs_max := sub_le_maxOpCost I I.src[I.src.length - 1 - s] I.tgt[I.tgt.length - 1 - t]
  have hd_max := del_le_maxOpCost I I.src[I.src.length - 1 - s]
  have hi_max := ins_le_maxOpCost I I.tgt[I.tgt.length - 1 - t]
  have he_d := weighted_entry_le I (I.src.length - s) (I.tgt.length - t)
  have he_u := weighted_entry_le I (I.src.length - s) (I.tgt.length - (t + 1))
  have he_l := weighted_entry_le I (I.src.length - (s + 1)) (I.tgt.length - t)
  have hpre : ∃ s1, ExecWithin w (ram[
        regTmp0 ← regRowAux1 + regB;
        regTmp0 ← *regTmp0;
        regNext ← regTmp0 + regDiag;
        regTmp0 ← regInsBase + regB;
        regTmp1 ← *regTmp0;
        regTmp1 ← regTmp1 + regCur;
        regTmp0 ← regRowAux0 + regUp ]) st s1 7 ∧
      s1.mem = st.mem ∧
      (∀ i : Fin 22, i.val < 19 → s1.regs i = st.regs i) ∧
      s1.regs regNext = I.costs.sub I.src[I.src.length - 1 - s]
        I.tgt[I.tgt.length - 1 - t] + st.regs regDiag ∧
      s1.regs regTmp0 = I.costs.del I.src[I.src.length - 1 - s] + st.regs regUp ∧
      s1.regs regTmp1 = I.costs.ins I.tgt[I.tgt.length - 1 - t] + st.regs regCur := by
    wram_exec * [hinsb, hread_sub, hread_ins]
    refine ⟨rfl, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
        Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
        Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
        Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
        Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
        Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide)),
        Data.set_regs_of_ne (fun h => by subst h; exact absurd hi (by decide))]
    · wram_simp * [hread_sub]
    · wram_simp *
    · wram_simp * [hinsb, hread_ins]
  obtain ⟨s1, he1, hm1, hr1, hvNext, hvT0, hvT1⟩ := hpre
  obtain ⟨s2, he2, hm2, hr2, hv2⟩ := exec_min3Tail (w := w) s1
  unfold weightedInnerCell
  have hr12 : ∀ i : Fin 22, i.val < 19 → s2.regs i = st.regs i :=
    fun i hi => (hr2 i hi).trans (hr1 i hi)
  refine ⟨s2, (he1.seq he2).mono (by omega), hm2.trans hm1,
    ⟨(hr12 _ (by decide)).trans hfix.m, (hr12 _ (by decide)).trans hfix.n,
     (hr12 _ (by decide)).trans hfix.xb, (hr12 _ (by decide)).trans hfix.yb,
     (hr12 _ (by decide)).trans hfix.dpb, (hr12 _ (by decide)).trans hfix.sig,
     (hr12 _ (by decide)).trans hfix.delb, (hr12 _ (by decide)).trans hfix.insb,
     (hr12 _ (by decide)).trans hfix.subb⟩,
    (hr12 _ (by decide)).trans hone,
    hr12 _ (by decide), hr12 _ (by decide), hr12 _ (by decide), hr12 _ (by decide),
    ⟨(hr12 _ (by decide)).trans hra0, (hr12 _ (by decide)).trans hra1⟩, ?_⟩
  rw [hv2, hvNext, hvT0, hvT1, hdiag, hup, hcur]
  rfl

private theorem exec_weightedEditDistCode {w : ℕ} (I : WeightedInstance) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w weightedEditDistCode (.init I.encode) xf
        (28 * I.src.length * I.tgt.length + 17 * I.src.length + 12 * I.tgt.length + 26) ∧
      xf.regs regCur = editDist I.costs I.src I.tgt := by
  obtain ⟨hwAddr, hwVal⟩ := hw
  have hlen := I.length_encode
  obtain ⟨x₀, hsetup, hx₀_mem, hm, hn, hxb, hyb, hdpb, hsig, hdelb, hinsb, hsubb⟩ :=
    exec_weightedSetup I hwAddr
  have hgrid := exec_gridCode 3 5 13 (wagnerFischer I.costs) Fin.val I.src I.tgt x₀
    weightedInitCell weightedBorderCell weightedInnerCell (WeightedRowInv I)
    hm hn
    (by rw [hxb, hdpb]; omega)
    (by rw [hyb, hdpb]; omega)
    (fun i hi => by rw [hx₀_mem, hxb]; exact weighted_read_src I hi)
    (fun j hj => by rw [hx₀_mem, hyb]; exact weighted_read_tgt I hj)
    (hwAddr.of_le (by omega)) (fits_zero w)
    (by rw [hdpb]; exact hwAddr.of_le (by omega))
    (hwAddr.of_le (by omega))
    (exec_weightedInitCell I x₀ hwAddr hwVal hx₀_mem hdpb hinsb)
    (exec_weightedBorderCell I x₀ hwAddr hwVal hx₀_mem hdpb hsig hdelb hsubb)
    (fun _ _ _ h0 h1 ⟨ha0, ha1⟩ => ⟨h0.trans ha0, h1.trans ha1⟩)
    (exec_weightedInnerCell I x₀ hwAddr hwVal hx₀_mem hdpb hinsb)
  obtain ⟨xf, hexec, hres⟩ := hgrid
  refine ⟨xf, (hsetup.seq hexec).mono ?_, hres⟩
  nlinarith

/-- **Word-RAM running time of Wagner–Fischer edit distance under arbitrary letter costs.** The
fixed standard-basis program `weightedEditDistProgram` computes `editDist I.costs I.src I.tgt`
in at most `28 (|x| + 1)(|y| + 1)` instructions (including input header reads and `halt`) at
every fitting word width `w`. -/
theorem computesInTime_weightedEditDist :
    weightedEditDistProgram.ComputesInTime (fun _ => WeightedInstance.encode)
      (fun I _ => 28 * (I.src.length + 1) * (I.tgt.length + 1))
      WeightedInstance.FitsWidth (fun I => editDist I.costs I.src I.tgt) := by
  refine (weightedEditDistCode.computesInTime_program regCur
    (time := fun I _ =>
      28 * I.src.length * I.tgt.length + 17 * I.src.length + 12 * I.tgt.length + 26) ?_).mono ?_
    (fun _ _ h => h)
  · intro I w hw _
    exact exec_weightedEditDistCode I hw
  · intro I _
    nlinarith

/-- Uniform Word-RAM computability of general-cost Wagner–Fischer edit distance in
`28 (|x| + 1)(|y| + 1)` instructions, bundling width admissibility
(`WeightedInstance.inputAdmissible`). -/
theorem uniformComputableInTime_weightedEditDist :
    UniformComputableInTime .standard (fun I : WeightedInstance => editDist I.costs I.src I.tgt)
      (fun _ => WeightedInstance.encode)
      (fun I _ => 28 * (I.src.length + 1) * (I.tgt.length + 1))
      WeightedInstance.FitsWidth :=
  ⟨22, weightedEditDistProgram, computesInTime_weightedEditDist,
    WeightedInstance.inputAdmissible⟩

end Cslib.Algorithms.WordRAM.EditDistance
