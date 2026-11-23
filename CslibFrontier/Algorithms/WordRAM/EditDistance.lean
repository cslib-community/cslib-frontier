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
import CslibFrontier.Computability.WordRAM.Notation
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

private theorem regs_set_lt {x : Data 22} {r : Fin 22} {v k : ℕ} (hr : k ≤ r.val)
    {i : Fin 22} (hi : i.val < k) : (x.set r v).regs i = x.regs i := by
  rw [Data.set_regs]
  exact Function.update_of_ne (fun h : i = r => by rw [h] at hi; omega) v x.regs

private theorem regs_set_ne {x : Data 22} {r i : Fin 22} {v : ℕ} (hne : i ≠ r) :
    (x.set r v).regs i = x.regs i := by
  rw [Data.set_regs]
  exact Function.update_of_ne hne v x.regs

private theorem regs_set_self (x : Data 22) (r : Fin 22) (v : ℕ) :
    (x.set r v).regs r = v := by
  rw [Data.set_regs, Function.update_self]

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
      (∀ i : Fin 22, i.val < 9 → st.regs i = x₀.regs i) →
      st.regs regOne = 1 →
      (∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr) →
      st.regs regB = encSym y[y.length - 1 - t] →
      st.regs regCur = D.value [] (y.drop (y.length - t)) →
      ∃ st', ExecWithin w initCell st st' Ti ∧
        st'.mem = st.mem ∧
        (∀ i : Fin 22, i.val < 18 → st'.regs i = st.regs i) ∧
        st'.regs regCur = D.nilCons y[y.length - 1 - t] (D.value [] (y.drop (y.length - t))))
    (hborder : ∀ (s : ℕ) (hs : s < x.length) (st : Data 22),
      (∀ i : Fin 22, i.val < 9 → st.regs i = x₀.regs i) →
      st.regs regOne = 1 →
      (∀ addr < x₀.regs regDPBase, st.mem addr = x₀.mem addr) →
      st.regs regA = encSym x[x.length - 1 - s] →
      st.regs regDiag = D.value (x.drop (x.length - s)) [] →
      ∃ st', ExecWithin w borderCell st st' Tb ∧
        st'.mem = st.mem ∧
        (∀ i : Fin 22, i.val < 16 → st'.regs i = st.regs i) ∧
        RowInv x[x.length - 1 - s] st' ∧
        st'.regs regCur = D.consNil x[x.length - 1 - s] (D.value (x.drop (x.length - s)) []))
    (hRowInv_frame : ∀ (a : α) (st st' : Data 22),
      st'.regs regRowAux0 = st.regs regRowAux0 →
      st'.regs regRowAux1 = st.regs regRowAux1 →
      RowInv a st → RowInv a st')
    (hinner : ∀ (s t : ℕ) (hs : s < x.length) (ht : t < y.length) (st : Data 22),
      (∀ i : Fin 22, i.val < 9 → st.regs i = x₀.regs i) →
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
        (∀ i : Fin 22, i.val < 19 → st'.regs i = st.regs i) ∧
        st'.regs regNext = D.consCons x[x.length - 1 - s] y[y.length - 1 - t]
          (D.value (x.drop (x.length - s)) (y.drop (y.length - t)))
          (D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))))
          (D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t)))) :
    ∃ xf, ExecWithin w (gridCode D.nilNil initCell borderCell innerCell) x₀ xf
      (x.length * y.length * (Tc + 15) + x.length * (Tb + 12) + y.length * (Ti + 9) + 11) ∧
      xf.regs regCur = D.value x y := by
  let dpBase := x₀.regs regDPBase
  let x₁ := (((x₀.set regOne 1).set regCur D.nilNil).write dpBase D.nilNil).set regT 0
  have hsetup : ExecWithin w (gridSetup D.nilNil) x₀ x₁ 4 := by
    ram_eval [gridSetup, x₁, dpBase, hfit1, hfitNil]
  let Pinit (t : ℕ) (st : Data 22) : Prop :=
    (∀ i : Fin 22, i.val < 9 → st.regs i = x₀.regs i) ∧
      st.regs regOne = 1 ∧
      st.regs regCur = D.value [] (y.drop (y.length - t)) ∧
      st.mem = dpInitMem x₀.mem dpBase D y t
  have hinitBody : ∀ st, Pinit (st.regs regT) st → st.regs regT < y.length →
      ∃ st', ExecWithin w (gridInitBody initCell) st st' (Ti + 7) ∧
        Pinit (st.regs regT + 1) st' ∧ st'.regs regT = st.regs regT + 1 := by
    intro st ⟨hregs, hone, hcur, hmem⟩ ht
    have hyb : st.regs regYBase = x₀.regs regYBase := hregs regYBase (by decide)
    have hyn : st.regs regN = y.length := (hregs regN (by decide)).trans hn
    have hyaddr_fit : Fits w (st.regs regYBase + st.regs regN) := by
      rw [hyb, hyn]; exact hfitDP.of_le (by omega)
    let stA := (((st.set regTmp0 (st.regs regYBase + st.regs regN)).set regTmp0
        (st.regs regYBase + st.regs regN - 1)).set regTmp0
        (st.regs regYBase + st.regs regN - 1 - st.regs regT)).set regB
        (st.mem (st.regs regYBase + st.regs regN - 1 - st.regs regT))
    have hpre : ExecWithin w gridInitPre st stA 4 := by
      ram_eval [gridInitPre, stA, hone, hyaddr_fit]
    have haddr_eq : st.regs regYBase + st.regs regN - 1 - st.regs regT =
        x₀.regs regYBase + (y.length - 1 - st.regs regT) := by
      rw [hyb, hyn]; omega
    have hreadB : stA.regs regB = encSym y[y.length - 1 - st.regs regT] := by
      change st.mem (st.regs regYBase + st.regs regN - 1 - st.regs regT) = _
      rw [haddr_eq, hmem, dpInitMem_lt _ _ _ _ _ _ (by omega)]
      exact hymem (y.length - 1 - st.regs regT) (by omega)
    have hstA_regs : ∀ i : Fin 22, i.val < 9 → stA.regs i = x₀.regs i := by
      intro i hi
      dsimp only [stA]
      rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
        regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
      exact hregs i hi
    have hstA_one : stA.regs regOne = 1 := by
      dsimp only [stA]
      rw [regs_set_lt (by decide : 10 ≤ regB.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide)]
      exact hone
    have hstA_cur : stA.regs regCur = D.value [] (y.drop (y.length - st.regs regT)) := by
      dsimp only [stA]
      rw [regs_set_ne (by decide : regCur ≠ regB),
        regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide)]
      exact hcur
    obtain ⟨stB, hcell, hcell_mem, hcell_regs, hcell_cur⟩ :=
      hinit (st.regs regT) ht stA hstA_regs hstA_one
        (fun addr ha => by rw [show stA.mem = st.mem from rfl, hmem, dpInitMem_lt _ _ _ _ _ _ ha])
        hreadB hstA_cur
    have hstA_t : stA.regs regT = st.regs regT := by
      dsimp only [stA]
      rw [regs_set_lt (by decide : 12 ≤ regB.val) (by decide),
        regs_set_lt (by decide : 12 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 12 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 12 ≤ regTmp0.val) (by decide)]
    have hstB_t : stB.regs regT = st.regs regT :=
      (hcell_regs regT (by decide)).trans hstA_t
    have hstB_one : stB.regs regOne = 1 :=
      (hcell_regs regOne (by decide)).trans hstA_one
    have hstB_dpb : stB.regs regDPBase = dpBase :=
      (hcell_regs regDPBase (by decide)).trans (hstA_regs regDPBase (by decide))
    have ht1_fit : Fits w (stB.regs regT + 1) := by
      rw [hstB_t]; exact hfitDP.of_le (by omega)
    have hdp1_fit : Fits w (stB.regs regDPBase + (stB.regs regT + 1)) := by
      rw [hstB_dpb, hstB_t]; exact hfitDP.of_le (by omega)
    let stC := ((stB.set regT (stB.regs regT + 1)).set regTmp0
        (stB.regs regDPBase + (stB.regs regT + 1))).write
        (stB.regs regDPBase + (stB.regs regT + 1)) (stB.regs regCur)
    have hpost : ExecWithin w gridInitPost stB stC 3 := by
      ram_eval [gridInitPost, stC, hstB_one, ht1_fit, hdp1_fit]
    have hval_next : D.nilCons y[y.length - 1 - st.regs regT]
        (D.value [] (y.drop (y.length - st.regs regT))) =
        D.value [] (y.drop (y.length - (st.regs regT + 1))) := by
      rw [drop_sub_succ_eq_cons y ht, D.value_nil_cons]
    refine ⟨stC, (hpre.seq (hcell.seq hpost)).mono (by omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      dsimp only [stC]
      rw [Data.write_regs, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
      exact (hcell_regs i (by omega)).trans (hstA_regs i hi)
    · dsimp only [stC]
      rw [Data.write_regs, regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regT.val) (by decide)]
      exact hstB_one
    · dsimp only [stC]
      rw [Data.write_regs, regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
        regs_set_ne (by decide : regCur ≠ regT), hcell_cur, hval_next]
    · change
        Function.update stB.mem (stB.regs regDPBase + (stB.regs regT + 1)) (stB.regs regCur) = _
      rw [hcell_mem, show stA.mem = st.mem from rfl, hmem, hstB_dpb, hstB_t, hcell_cur, hval_next]
      exact dpInitMem_succ x₀.mem dpBase D y ht
    · dsimp only [stC]
      rw [Data.write_regs, regs_set_lt (by decide : 12 ≤ regTmp0.val) (by decide),
        regs_set_self, hstB_t]
  have hx₁_init : Pinit (x₁.regs regT) x₁ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · intro i hi
      dsimp only [x₁]
      rw [regs_set_lt (by decide) hi, Data.write_regs, regs_set_lt (by decide) hi,
        regs_set_lt (by decide) hi]
    · change D.nilNil = D.value [] (y.drop (y.length - 0))
      rw [Nat.sub_zero, List.drop_length, D.value_nil_nil]
    · exact dpInitMem_zero x₀.mem dpBase D y
  obtain ⟨x₂, hinitLoop, ⟨hx₂_regs, hx₂_one, _, hx₂_mem⟩, _⟩ :=
    ExecWithin.loop_count Pinit
      (fun st h => (h.1 regN (by decide)).trans hn)
      hinitBody (Nat.zero_le _) hx₁_init
  let x₃ := x₂.set regS 0
  have hsetS : ExecWithin w (ram[ regS ← #0 ] : Code .standard 22) x₂ x₃ 1 := by ram_eval [x₃]
  let Pouter (s : ℕ) (st : Data 22) : Prop :=
    (∀ i : Fin 22, i.val < 9 → st.regs i = x₀.regs i) ∧
      st.regs regOne = 1 ∧
      st.mem = dpRowMem x₀.mem dpBase D x y s
  have houterBody : ∀ st, Pouter (st.regs regS) st → st.regs regS < x.length →
      ∃ st', ExecWithin w (gridOuterBody borderCell innerCell) st st'
          (y.length * (Tc + 15) + Tb + 10) ∧
        Pouter (st.regs regS + 1) st' ∧ st'.regs regS = st.regs regS + 1 := by
    intro st ⟨hregs, hone, hmem⟩ hs
    let s := st.regs regS
    have hxb : st.regs regXBase = x₀.regs regXBase := hregs regXBase (by decide)
    have hxm : st.regs regM = x.length := (hregs regM (by decide)).trans hm
    have hdpb : st.regs regDPBase = dpBase := hregs regDPBase (by decide)
    have hxaddr_fit : Fits w (st.regs regXBase + st.regs regM) := by
      rw [hxb, hxm]; exact hfitDP.of_le (by omega)
    let st1 := ((((st.set regTmp0 (st.regs regXBase + st.regs regM)).set regTmp0
        (st.regs regXBase + st.regs regM - 1)).set regTmp0
        (st.regs regXBase + st.regs regM - 1 - s)).set regA
        (st.mem (st.regs regXBase + st.regs regM - 1 - s))).set regDiag
        (st.mem (st.regs regDPBase))
    have hpreOut : ExecWithin w gridOuterPre st st1 5 := by
      ram_eval [gridOuterPre, st1, s, hone, hxaddr_fit]
    have hxaddr_eq : st.regs regXBase + st.regs regM - 1 - s =
        x₀.regs regXBase + (x.length - 1 - s) := by
      rw [hxb, hxm]; omega
    have hreadA : st1.regs regA = encSym x[x.length - 1 - s] := by
      dsimp only [st1]
      rw [regs_set_lt (by decide : 13 ≤ regDiag.val) (by decide), Data.set_regs,
        Function.update_self, hxaddr_eq, hmem, dpRowMem_lt _ _ _ _ _ _ _ (by omega)]
      exact hxmem (x.length - 1 - s) (by omega)
    have hreadDiag0 : st1.regs regDiag = D.value (x.drop (x.length - s)) [] := by
      dsimp only [st1]
      rw [Data.set_regs, Function.update_self, hdpb, hmem]
      simpa only [Nat.add_zero, Nat.sub_zero, List.drop_length] using
        dpRowMem_read x₀.mem dpBase D x y s 0 (Nat.zero_le _)
    have hst1_regs : ∀ i : Fin 22, i.val < 9 → st1.regs i = x₀.regs i := by
      intro i hi
      dsimp only [st1]
      rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
        regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
      exact hregs i hi
    have hst1_one : st1.regs regOne = 1 := by
      dsimp only [st1]
      rw [regs_set_lt (by decide : 10 ≤ regDiag.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regA.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 10 ≤ regTmp0.val) (by decide)]
      exact hone
    have hst1_s : st1.regs regS = s := by
      dsimp only [st1]
      rw [regs_set_lt (by decide : 11 ≤ regDiag.val) (by decide),
        regs_set_lt (by decide : 11 ≤ regA.val) (by decide),
        regs_set_lt (by decide : 11 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 11 ≤ regTmp0.val) (by decide),
        regs_set_lt (by decide : 11 ≤ regTmp0.val) (by decide)]
    obtain ⟨st2, hbord, hbord_mem, hbord_regs, hbord_inv, hbord_cur⟩ :=
      hborder s hs st1 hst1_regs hst1_one
        (fun addr ha => by
          rw [show st1.mem = st.mem from rfl, hmem, dpRowMem_lt _ _ _ _ _ _ _ ha])
        hreadA hreadDiag0
    have hst2_dpb : st2.regs regDPBase = dpBase :=
      (hbord_regs regDPBase (by decide)).trans (hst1_regs regDPBase (by decide))
    let st3 := (st2.write (st2.regs regDPBase) (st2.regs regCur)).set regT 0
    have hpostBord : ExecWithin w gridOuterMid st2 st3 2 := by
      ram_eval [gridOuterMid, st3]
    have hval_s0 : D.consNil x[x.length - 1 - s] (D.value (x.drop (x.length - s)) []) =
        D.value (x.drop (x.length - (s + 1))) [] := by
      rw [drop_sub_succ_eq_cons x hs, D.value_cons_nil]
    let Pinner (t : ℕ) (q : Data 22) : Prop :=
      (∀ i : Fin 22, i.val < 9 → q.regs i = x₀.regs i) ∧
        q.regs regOne = 1 ∧
        q.regs regS = s ∧
        q.regs regA = encSym x[x.length - 1 - s] ∧
        RowInv x[x.length - 1 - s] q ∧
        q.regs regDiag = D.value (x.drop (x.length - s)) (y.drop (y.length - t)) ∧
        q.regs regCur = D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t)) ∧
        q.mem = dpMidMem x₀.mem dpBase D x y s t
    have hinnerBody : ∀ q, Pinner (q.regs regT) q → q.regs regT < y.length →
        ∃ q', ExecWithin w (gridInnerBody innerCell) q q' (Tc + 13) ∧
          Pinner (q.regs regT + 1) q' ∧ q'.regs regT = q.regs regT + 1 := by
      intro q ⟨hq_regs, hq_one, hq_s, hq_a, hq_inv, hq_diag, hq_cur, hq_mem⟩ ht
      let t := q.regs regT
      have hq_yb : q.regs regYBase = x₀.regs regYBase := hq_regs regYBase (by decide)
      have hq_yn : q.regs regN = y.length := (hq_regs regN (by decide)).trans hn
      have hq_dpb : q.regs regDPBase = dpBase := hq_regs regDPBase (by decide)
      have hy_fit : Fits w (q.regs regYBase + q.regs regN) := by
        rw [hq_yb, hq_yn]; exact hfitDP.of_le (by omega)
      have hdpt_fit : Fits w (q.regs regDPBase + t + 1) := by
        rw [hq_dpb]; exact hfitDP.of_le (by omega)
      let q1 := ((((((q.set regTmp0 (q.regs regYBase + q.regs regN)).set regTmp0
          (q.regs regYBase + q.regs regN - 1)).set regTmp0
          (q.regs regYBase + q.regs regN - 1 - t)).set regB
          (q.mem (q.regs regYBase + q.regs regN - 1 - t))).set regTmp0
          (q.regs regDPBase + t)).set regTmp0
          (q.regs regDPBase + t + 1)).set regUp
          (q.mem (q.regs regDPBase + t + 1))
      have hpreIn : ExecWithin w gridInnerPre q q1 7 := by
        ram_eval [gridInnerPre, q1, t, hq_one, hy_fit, hdpt_fit]
      have hyaddr_eq : q.regs regYBase + q.regs regN - 1 - t =
          x₀.regs regYBase + (y.length - 1 - t) := by
        rw [hq_yb, hq_yn]; omega
      have hq1_b : q1.regs regB = encSym y[y.length - 1 - t] := by
        dsimp only [q1]
        rw [regs_set_lt (by decide : 14 ≤ regUp.val) (by decide),
          regs_set_lt (by decide : 14 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 14 ≤ regTmp0.val) (by decide),
          Data.set_regs, Function.update_self, hyaddr_eq, hq_mem,
          dpMidMem_lt _ _ _ _ _ _ _ _ (by omega)]
        exact hymem (y.length - 1 - t) (by omega)
      have hq1_up : q1.regs regUp =
          D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) := by
        dsimp only [q1]
        rw [Data.set_regs, Function.update_self, hq_dpb, hq_mem]
        exact dpMidMem_read_next x₀.mem dpBase D x y s ht
      have hq1_low : ∀ i : Fin 22, i.val < 13 → q1.regs i = q.regs i := by
        intro i hi
        dsimp only [q1]
        rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
          regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
          regs_set_lt (by decide) hi]
      have hq1_regs : ∀ i : Fin 22, i.val < 9 → q1.regs i = x₀.regs i :=
        fun i hi => (hq1_low i (by omega)).trans (hq_regs i hi)
      have hq1_diag : q1.regs regDiag = q.regs regDiag := by
        dsimp only [q1]
        rw [regs_set_lt (by decide : 15 ≤ regUp.val) (by decide),
          regs_set_lt (by decide : 15 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 15 ≤ regTmp0.val) (by decide),
          regs_set_ne (by decide : regDiag ≠ regB),
          regs_set_lt (by decide : 15 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 15 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 15 ≤ regTmp0.val) (by decide)]
      have hq1_ra0 : q1.regs regRowAux0 = q.regs regRowAux0 := by
        dsimp only [q1]
        rw [regs_set_ne (by decide : regRowAux0 ≠ regUp),
          regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide),
          regs_set_ne (by decide : regRowAux0 ≠ regB),
          regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide)]
      have hq1_ra1 : q1.regs regRowAux1 = q.regs regRowAux1 := by
        dsimp only [q1]
        rw [regs_set_ne (by decide : regRowAux1 ≠ regUp),
          regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide),
          regs_set_ne (by decide : regRowAux1 ≠ regB),
          regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide)]
      have hq1_cur : q1.regs regCur = q.regs regCur := by
        dsimp only [q1]
        rw [regs_set_ne (by decide : regCur ≠ regUp),
          regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
          regs_set_ne (by decide : regCur ≠ regB),
          regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide)]
      have hq1_inv : RowInv x[x.length - 1 - s] q1 :=
        hRowInv_frame _ q q1 hq1_ra0 hq1_ra1 hq_inv
      obtain ⟨q2, hinCell, hin_mem, hin_regs, hin_next⟩ :=
        hinner s t hs ht q1 hq1_regs ((hq1_low regOne (by decide)).trans hq_one)
          (fun addr ha => by
            rw [show q1.mem = q.mem from rfl, hq_mem, dpMidMem_lt _ _ _ _ _ _ _ _ ha])
          hq1_inv ((hq1_low regA (by decide)).trans hq_a) hq1_b
          (hq1_diag.trans hq_diag) hq1_up (hq1_cur.trans hq_cur)
      have hq2_t : q2.regs regT = t :=
        (hin_regs regT (by decide)).trans (hq1_low regT (by decide))
      have hq2_one : q2.regs regOne = 1 :=
        (hin_regs regOne (by decide)).trans ((hq1_low regOne (by decide)).trans hq_one)
      have hq2_dpb : q2.regs regDPBase = dpBase :=
        (hin_regs regDPBase (by decide)).trans (hq1_regs regDPBase (by decide))
      have hq2_up : q2.regs regUp =
          D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))) :=
        (hin_regs regUp (by decide)).trans hq1_up
      have hq2_dpt_fit : Fits w (q2.regs regDPBase + q2.regs regT + 1) := by
        rw [hq2_dpb, hq2_t]; exact hfitDP.of_le (by omega)
      have hq2_t1_fit : Fits w (q2.regs regT + 1) := by
        rw [hq2_t]; exact hfitDP.of_le (by omega)
      let q3 := (((((q2.set regTmp0 (q2.regs regDPBase + q2.regs regT)).set regTmp0
          (q2.regs regDPBase + q2.regs regT + 1)).write
          (q2.regs regDPBase + q2.regs regT + 1) (q2.regs regNext)).set regDiag
          (q2.regs regUp)).set regCur (q2.regs regNext)).set regT (q2.regs regT + 1)
      have hpostIn : ExecWithin w gridInnerPost q2 q3 6 := by
        ram_eval [gridInnerPost, q3, hq2_one, hq2_dpt_fit, hq2_t1_fit]
      have hval_st : D.consCons x[x.length - 1 - s] y[y.length - 1 - t]
          (D.value (x.drop (x.length - s)) (y.drop (y.length - t)))
          (D.value (x.drop (x.length - s)) (y.drop (y.length - (t + 1))))
          (D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - t))) =
          D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - (t + 1))) := by
        dsimp only [s, t]
        rw [drop_sub_succ_eq_cons x hs, drop_sub_succ_eq_cons y ht, D.value_cons_cons]
      have hq3_low : ∀ i : Fin 22, i.val < 11 → q3.regs i = q2.regs i := by
        intro i hi
        dsimp only [q3]
        rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
          Data.write_regs, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
      refine ⟨q3, (hpreIn.seq (hinCell.seq hpostIn)).mono (by omega),
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi
        exact (hq3_low i (by omega)).trans ((hin_regs i (by omega)).trans (hq1_regs i hi))
      · exact (hq3_low regOne (by decide)).trans hq2_one
      · exact (hq3_low regS (by decide)).trans
          ((hin_regs regS (by decide)).trans ((hq1_low regS (by decide)).trans hq_s))
      · have hq3_a : q3.regs regA = q2.regs regA := by
          dsimp only [q3]
          rw [regs_set_ne (by decide : regA ≠ regT),
            regs_set_lt (by decide : 13 ≤ regCur.val) (by decide),
            regs_set_lt (by decide : 13 ≤ regDiag.val) (by decide), Data.write_regs,
            regs_set_lt (by decide : 13 ≤ regTmp0.val) (by decide),
            regs_set_lt (by decide : 13 ≤ regTmp0.val) (by decide)]
        exact hq3_a.trans
          ((hin_regs regA (by decide)).trans ((hq1_low regA (by decide)).trans hq_a))
      · have hq3_ra0 : q3.regs regRowAux0 = q2.regs regRowAux0 := by
          dsimp only [q3]
          rw [regs_set_ne (by decide : regRowAux0 ≠ regT),
            regs_set_lt (by decide : 17 ≤ regCur.val) (by decide),
            regs_set_ne (by decide : regRowAux0 ≠ regDiag), Data.write_regs,
            regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide),
            regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide)]
        have hq3_ra1 : q3.regs regRowAux1 = q2.regs regRowAux1 := by
          dsimp only [q3]
          rw [regs_set_ne (by decide : regRowAux1 ≠ regT),
            regs_set_lt (by decide : 18 ≤ regCur.val) (by decide),
            regs_set_ne (by decide : regRowAux1 ≠ regDiag), Data.write_regs,
            regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide),
            regs_set_lt (by decide : 18 ≤ regTmp0.val) (by decide)]
        refine hRowInv_frame _ q2 q3 hq3_ra0 hq3_ra1 ?_
        exact hRowInv_frame _ q1 q2 (hin_regs regRowAux0 (by decide))
          (hin_regs regRowAux1 (by decide)) hq1_inv
      · dsimp only [q3]
        rw [regs_set_ne (by decide : regDiag ≠ regT),
          regs_set_lt (by decide : 15 ≤ regCur.val) (by decide),
          regs_set_self, hq2_up]
      · dsimp only [q3]
        rw [regs_set_ne (by decide : regCur ≠ regT),
          regs_set_self, hin_next, hval_st]
      · change Function.update q2.mem (q2.regs regDPBase + q2.regs regT + 1) (q2.regs regNext) = _
        rw [hin_mem, show q1.mem = q.mem from rfl, hq_mem, hq2_dpb, hq2_t, hin_next, hval_st]
        exact dpMidMem_succ x₀.mem dpBase D x y s ht
      · dsimp only [q3]
        rw [regs_set_self, hq2_t]
    have hst3_inner : Pinner (st3.regs regT) st3 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        dsimp only [st3]
        rw [regs_set_lt (by decide) hi, Data.write_regs]
        exact (hbord_regs i (by omega)).trans (hst1_regs i hi)
      · dsimp only [st3]
        rw [regs_set_lt (by decide : 10 ≤ regT.val) (by decide), Data.write_regs]
        exact (hbord_regs regOne (by decide)).trans hst1_one
      · dsimp only [st3]
        rw [regs_set_lt (by decide : 11 ≤ regT.val) (by decide), Data.write_regs]
        exact (hbord_regs regS (by decide)).trans hst1_s
      · dsimp only [st3]
        rw [regs_set_ne (by decide : regA ≠ regT), Data.write_regs]
        exact (hbord_regs regA (by decide)).trans hreadA
      · refine hRowInv_frame _ st2 st3 ?_ ?_ hbord_inv
        · dsimp only [st3]
          rw [regs_set_ne (by decide : regRowAux0 ≠ regT), Data.write_regs]
        · dsimp only [st3]
          rw [regs_set_ne (by decide : regRowAux1 ≠ regT), Data.write_regs]
      · change st3.regs regDiag = D.value (x.drop (x.length - s)) (y.drop (y.length - 0))
        dsimp only [st3]
        rw [regs_set_ne (by decide : regDiag ≠ regT), Data.write_regs,
          hbord_regs regDiag (by decide), hreadDiag0, Nat.sub_zero, List.drop_length]
      · change st3.regs regCur = D.value (x.drop (x.length - (s + 1))) (y.drop (y.length - 0))
        dsimp only [st3]
        rw [regs_set_ne (by decide : regCur ≠ regT), Data.write_regs,
          hbord_cur, hval_s0, Nat.sub_zero, List.drop_length]
      · change Function.update st2.mem (st2.regs regDPBase) (st2.regs regCur) =
          dpMidMem x₀.mem dpBase D x y s 0
        rw [hbord_mem, show st1.mem = st.mem from rfl, hmem, hst2_dpb, hbord_cur, hval_s0]
        exact dpMidMem_zero x₀.mem dpBase D x y s
    obtain ⟨st4, hinLoop, ⟨hst4_regs, hst4_one, hst4_s, _, _, _, _, hst4_mem⟩, _⟩ :=
      ExecWithin.loop_count Pinner
        (fun q h => (h.1 regN (by decide)).trans hn)
        hinnerBody (Nat.zero_le _) hst3_inner
    have hs1_fit : Fits w (st4.regs regS + 1) := by
      rw [hst4_s]; exact hfitM.of_le (by omega)
    let st5 := st4.set regS (st4.regs regS + 1)
    have hincS : ExecWithin w (ram[ regS ← regS + regOne ]) st4 st5 1 := by
      ram_eval [st5, hst4_one, hs1_fit]
    have ht3 : st3.regs regT = 0 := rfl
    rw [ht3, Nat.sub_zero] at hinLoop
    refine ⟨st5,
      (hpreOut.seq (hbord.seq (hpostBord.seq (hinLoop.seq hincS)))).mono (le_of_eq (by ring)),
      ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      dsimp only [st5]
      rw [regs_set_lt (by decide) hi]
      exact hst4_regs i hi
    · dsimp only [st5]
      rw [regs_set_lt (by decide : 10 ≤ regS.val) (by decide)]
      exact hst4_one
    · change st4.mem = dpRowMem x₀.mem dpBase D x y (s + 1)
      rw [hst4_mem, dpMidMem_end]
    · dsimp only [st5]
      rw [Data.set_regs, Function.update_self, hst4_s]
  have hx₃_outer : Pouter (x₃.regs regS) x₃ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      dsimp only [x₃]
      rw [regs_set_lt (by decide) hi]
      exact hx₂_regs i hi
    · dsimp only [x₃]
      rw [regs_set_lt (by decide : 10 ≤ regS.val) (by decide)]
      exact hx₂_one
    · change x₂.mem = dpRowMem x₀.mem dpBase D x y 0
      rw [hx₂_mem, dpInitMem_end]
  obtain ⟨x₄, houterLoop, ⟨hx₄_regs, _, hx₄_mem⟩, _⟩ :=
    ExecWithin.loop_count Pouter
      (fun st h => (h.1 regM (by decide)).trans hm)
      houterBody (Nat.zero_le _) hx₃_outer
  have hx₄_dpb : x₄.regs regDPBase = dpBase := hx₄_regs regDPBase (by decide)
  have hx₄_n : x₄.regs regN = y.length := (hx₄_regs regN (by decide)).trans hn
  have hfin_fit : Fits w (x₄.regs regDPBase + x₄.regs regN) := by
    rw [hx₄_dpb, hx₄_n]; exact hfitDP.of_le (by omega)
  let xf := (x₄.set regTmp0 (x₄.regs regDPBase + x₄.regs regN)).set regCur
      (x₄.mem (x₄.regs regDPBase + x₄.regs regN))
  have hfin : ExecWithin w gridFinalLoad x₄ xf 2 := by
    ram_eval [gridFinalLoad, xf, hfin_fit]
  have ht1 : x₁.regs regT = 0 := rfl
  have hs3 : x₃.regs regS = 0 := rfl
  rw [ht1, Nat.sub_zero] at hinitLoop
  rw [hs3, Nat.sub_zero] at houterLoop
  refine ⟨xf, ?_, ?_⟩
  · exact (hsetup.seq (hinitLoop.seq (hsetS.seq (houterLoop.seq hfin)))).mono (le_of_eq (by ring))
  · dsimp only [xf]
    rw [Data.set_regs, Function.update_self, hx₄_dpb, hx₄_n, hx₄_mem,
      dpRowMem_read x₀.mem dpBase D x y x.length y.length le_rfl]
    simp

/-! ## Shared three-way minimum tail and `Data.init` read helper -/

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
  have h1 : ∃ s1, ExecWithin (B := .standard) w
      (.branch (.lt regTmp0 regTmp1) (ram[ regTmp0 ← regTmp0 ]) (ram[ regTmp0 ← regTmp1 ]))
      st s1 3 ∧ s1.mem = st.mem ∧
      (∀ i : Fin 22, i.val < 20 → s1.regs i = st.regs i) ∧
      s1.regs regTmp0 = min (st.regs regTmp0) (st.regs regTmp1) := by
    by_cases hlt : st.regs regTmp0 < st.regs regTmp1
    · refine ⟨st.set regTmp0 (st.regs regTmp0), ?_, rfl,
        fun i hi => regs_set_lt (by decide) hi, ?_⟩
      · exact (ExecWithin.branch_pos (by simpa only [Cond.holds_lt] using hlt)
          ExecWithin.copy).mono (by omega)
      · rw [Data.set_regs, Function.update_self]; omega
    · refine ⟨st.set regTmp0 (st.regs regTmp1), ?_, rfl,
        fun i hi => regs_set_lt (by decide) hi, ?_⟩
      · exact (ExecWithin.branch_neg (by simpa only [Cond.holds_lt] using hlt)
          ExecWithin.copy).mono (by omega)
      · rw [Data.set_regs, Function.update_self]; omega
  obtain ⟨s1, he1, hm1, hr1, hv1⟩ := h1
  have hs1_next : s1.regs regNext = st.regs regNext := hr1 regNext (by decide)
  by_cases hlt2 : s1.regs regNext < s1.regs regTmp0
  · refine ⟨s1.set regNext (s1.regs regNext), ?_, hm1,
      fun i hi => (regs_set_lt (by decide) hi).trans (hr1 i (by omega)), ?_⟩
    · exact (he1.seq (ExecWithin.branch_pos (by simpa only [Cond.holds_lt] using hlt2)
        ExecWithin.copy)).mono (by omega)
    · rw [Data.set_regs, Function.update_self, hs1_next]
      rw [hs1_next, hv1] at hlt2
      omega
  · refine ⟨s1.set regNext (s1.regs regTmp0), ?_, hm1,
      fun i hi => (regs_set_lt (by decide) hi).trans (hr1 i (by omega)), ?_⟩
    · exact (he1.seq (ExecWithin.branch_neg (by simpa only [Cond.holds_lt] using hlt2)
        ExecWithin.copy)).mono (by omega)
    · rw [Data.set_regs, Function.update_self, hv1]
      rw [hs1_next, hv1] at hlt2
      omega

private theorem init_mem_slice (pre mid post : List ℕ) {i : ℕ} (hi : i < mid.length) :
    (Data.init (pre ++ mid ++ post) : Data 22).mem (pre.length + 1 + i) = mid[i] := by
  have heq : pre.length + 1 + i = (pre.length + i) + 1 := by omega
  rw [heq, Data.init_mem_succ, List.getD_eq_getElem?_getD]
  have hlt1 : pre.length + i < (pre ++ mid).length := by simp [List.length_append]; omega
  have hlt2 : pre.length + i < (pre ++ mid ++ post).length := by simp [List.length_append]; omega
  rw [List.getElem?_eq_getElem hlt2, Option.getD_some,
    List.getElem_append_left hlt1,
    List.getElem_append_right (Nat.le_add_right _ _)]
  simp

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
  have hf3 : Fits w 3 := hw.of_le (by omega)
  have hfy : Fits w (3 + I.src.length) := hw.of_le (by omega)
  have hfdp : Fits w (3 + I.src.length + I.tgt.length) := hw.of_le (by omega)
  have hm1 : (Data.init I.encode : Data 22).mem 1 = I.src.length := by
    simp [WordSeqPair.encode]
  have hm2 : (Data.init I.encode : Data 22).mem 2 = I.tgt.length := by
    simp [WordSeqPair.encode]
  let d0 : Data 22 := Data.init I.encode
  let x₀ := ((((((d0.set regTmp0 1).set regM I.src.length).set regTmp0 2).set regN
      I.tgt.length).set regXBase 3).set regYBase (3 + I.src.length)).set regDPBase
      (3 + I.src.length + I.tgt.length)
  have he : ExecWithin w seqPairSetup d0 x₀ 7 := by
    ram_eval [seqPairSetup, x₀, d0, hm1, hm2, hf3, hfy, hfdp]
  exact ⟨x₀, he, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem seqPair_read_src (I : WordSeqPair) {i : ℕ} (hi : i < I.src.length) :
    (Data.init I.encode : Data 22).mem (3 + i) = I.src[i] := by
  have h := init_mem_slice [I.src.length, I.tgt.length] I.src I.tgt hi
  simpa [WordSeqPair.encode, List.append_assoc] using h

private theorem seqPair_read_tgt (I : WordSeqPair) {j : ℕ} (hj : j < I.tgt.length) :
    (Data.init I.encode : Data 22).mem (3 + I.src.length + j) = I.tgt[j] := by
  have h := init_mem_slice ([I.src.length, I.tgt.length] ++ I.src) I.tgt [] hj
  simpa [WordSeqPair.encode, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using h

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

private theorem lcsLength_le_left {α : Type*} [DecidableEq α] (x y : List α) :
    lcsLength x y ≤ x.length := by
  obtain ⟨hx, _, hlen⟩ := lcs_spec x y
  rw [← hlen]
  exact hx.length_le

private theorem exec_lcsLengthCode {w : ℕ} (I : WordSeqPair) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w lcsLengthCode (.init I.encode) xf
        (20 * I.src.length * I.tgt.length + 13 * I.src.length + 10 * I.tgt.length + 18) ∧
      xf.regs regCur = lcsLength I.src I.tgt := by
  obtain ⟨x₀, hsetup, hmem0, hm, hn, hxb, hyb, hdpb⟩ := exec_seqPairSetup I hw
  have hgrid := exec_gridCode 1 1 5 (lcsTable (α := ℕ)) id I.src I.tgt x₀
    (ram[ regCur ← regCur ]) (ram[ regCur ← regDiag ]) lcsInnerCell (fun _ _ => True)
    hm hn (by omega) (by omega)
    (fun i hi => by rw [hmem0, hxb]; exact seqPair_read_src I hi)
    (fun j hj => by rw [hmem0, hyb]; exact seqPair_read_tgt I hj)
    (hw.of_le (by omega)) (fits_zero w)
    (by rw [hdpb]; exact hw.of_le (by omega))
    (hw.of_le (by omega))
    (fun _ _ st _ _ _ _ hcur =>
      ⟨st.set regCur (st.regs regCur), ExecWithin.copy, rfl,
        fun i hi => regs_set_lt (by decide) hi,
        by rw [regs_set_self, hcur]; rfl⟩)
    (fun _ _ st _ _ _ _ hdiag =>
      ⟨st.set regCur (st.regs regDiag), ExecWithin.copy, rfl,
        fun i hi => regs_set_lt (by decide) hi, trivial,
        by rw [regs_set_self, hdiag]; rfl⟩)
    (fun _ _ _ _ _ _ => trivial)
    (fun s t hs _ st _ hone _ _ ha hb hdiag hup hcur => by
      by_cases hab : st.regs regA = st.regs regB
      · have hab' : I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] := by
          simpa [ha, hb] using hab
        have hd_le : lcsLength (I.src.drop (I.src.length - s))
            (I.tgt.drop (I.tgt.length - t)) ≤ s := by
          have := lcsLength_le_left (I.src.drop (I.src.length - s))
            (I.tgt.drop (I.tgt.length - t))
          simp only [List.length_drop] at this
          omega
        have hd1_fit : Fits w (st.regs regDiag + 1) := by
          rw [hdiag]; change Fits w (lcsLength _ _ + 1); exact hw.of_le (by omega)
        let st' := st.set regNext (st.regs regDiag + 1)
        have hstep : ExecWithin w (ram[ regNext ← regDiag + regOne ]) st st' 1 := by
          ram_eval [st', hone, hd1_fit]
        refine ⟨st', (ExecWithin.branch_pos (by simpa only [Cond.holds_eq] using hab) hstep).mono
            (by omega), rfl, fun i hi => regs_set_lt (by decide) hi, ?_⟩
        dsimp only [st']
        rw [regs_set_self, hdiag]
        change _ = if I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] then _ + 1 else _
        rw [ite_eq_left hab']
      · have hab' : I.src[I.src.length - 1 - s] ≠ I.tgt[I.tgt.length - 1 - t] := by
          intro h; exact hab (by simp [ha, hb, h])
        by_cases hlt : st.regs regUp < st.regs regCur
        · refine ⟨st.set regNext (st.regs regCur),
            (ExecWithin.branch_neg (by simpa only [Cond.holds_eq] using hab)
              (ExecWithin.branch_pos (by simpa only [Cond.holds_lt] using hlt)
                ExecWithin.copy)).mono (by omega),
            rfl, fun i hi => regs_set_lt (by decide) hi, ?_⟩
          rw [regs_set_self, hcur]
          rw [hup, hcur] at hlt
          change _ =
            if I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] then _ else max _ _
          rw [ite_eq_right hab']
          omega
        · refine ⟨st.set regNext (st.regs regUp),
            (ExecWithin.branch_neg (by simpa only [Cond.holds_eq] using hab)
              (ExecWithin.branch_neg (by simpa only [Cond.holds_lt] using hlt)
                ExecWithin.copy)).mono (by omega),
            rfl, fun i hi => regs_set_lt (by decide) hi, ?_⟩
          rw [regs_set_self, hup]
          rw [hup, hcur] at hlt
          change _ =
            if I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] then _ else max _ _
          rw [ite_eq_right hab']
          omega)
  obtain ⟨xf, hexec, hres⟩ := hgrid
  refine ⟨xf, (hsetup.seq hexec).mono ?_, hres⟩
  nlinarith

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
    (.branch (.eq regA regB)
      (ram[ regNext ← regDiag ])
      (ram[ regNext ← regDiag + regOne ]))
    (.seq
      (ram[ regTmp0 ← regUp + regOne; regTmp1 ← regCur + regOne ])
      min3Tail)

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

private theorem editDist_le_sum_del_ins {α : Type*} (C : Costs α) (x y : List α) :
    editDist C x y ≤ (x.map C.del).sum + (y.map C.ins).sum := by
  induction x with
  | nil => rw [editDist_nil_left]; simp
  | cons a x ih =>
    have h := editDist_cons_left_le C a x y
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem editDist_unit_le_add {α : Type*} [DecidableEq α] (x y : List α) :
    editDist Costs.unit x y ≤ x.length + y.length := by
  have h := editDist_le_sum_del_ins (Costs.unit (α := α)) x y
  have h1 : (x.map (Costs.unit (α := α)).del).sum = x.length := by simp [Costs.unit]
  have h2 : (y.map (Costs.unit (α := α)).ins).sum = y.length := by simp [Costs.unit]
  omega

private theorem exec_unitEditDistCode {w : ℕ} (I : WordSeqPair) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w unitEditDistCode (.init I.encode) xf
        (26 * I.src.length * I.tgt.length + 13 * I.src.length + 10 * I.tgt.length + 18) ∧
      xf.regs regCur = editDist Costs.unit I.src I.tgt := by
  obtain ⟨x₀, hsetup, hmem0, hm, hn, hxb, hyb, hdpb⟩ := exec_seqPairSetup I hw
  have hgrid := exec_gridCode 1 1 11 (wagnerFischer (Costs.unit (α := ℕ))) id I.src I.tgt x₀
    (ram[ regCur ← regCur + regOne ]) (ram[ regCur ← regDiag + regOne ]) unitInnerCell
    (fun _ _ => True)
    hm hn (by omega) (by omega)
    (fun i hi => by rw [hmem0, hxb]; exact seqPair_read_src I hi)
    (fun j hj => by rw [hmem0, hyb]; exact seqPair_read_tgt I hj)
    (hw.of_le (by omega)) (fits_zero w)
    (by rw [hdpb]; exact hw.of_le (by omega))
    (hw.of_le (by omega))
    (fun t ht st _ hone _ _ hcur => by
      have hle : editDist Costs.unit [] (I.tgt.drop (I.tgt.length - t)) ≤ t := by
        have := editDist_unit_le_add ([] : List ℕ) (I.tgt.drop (I.tgt.length - t))
        simp only [List.length_nil, List.length_drop] at this
        omega
      have hc1_fit : Fits w (st.regs regCur + 1) := by
        rw [hcur]
        change Fits w (editDist Costs.unit [] (I.tgt.drop (I.tgt.length - t)) + 1)
        exact hw.of_le (by omega)
      let st' := st.set regCur (st.regs regCur + 1)
      have hstep : ExecWithin w (ram[ regCur ← regCur + regOne ]) st st' 1 := by
        ram_eval [st', hone, hc1_fit]
      refine ⟨st', hstep, rfl, fun i hi => regs_set_lt (by decide) hi, ?_⟩
      dsimp only [st']
      rw [regs_set_self, hcur]
      change _ = 1 + _
      omega)
    (fun s hs st _ hone _ _ hdiag => by
      have hle : editDist Costs.unit (I.src.drop (I.src.length - s)) [] ≤ s := by
        have := editDist_unit_le_add (I.src.drop (I.src.length - s)) ([] : List ℕ)
        simp only [List.length_nil, List.length_drop] at this
        omega
      have hd1_fit : Fits w (st.regs regDiag + 1) := by
        rw [hdiag]
        change Fits w (editDist Costs.unit (I.src.drop (I.src.length - s)) [] + 1)
        exact hw.of_le (by omega)
      let st' := st.set regCur (st.regs regDiag + 1)
      have hstep : ExecWithin w (ram[ regCur ← regDiag + regOne ]) st st' 1 := by
        ram_eval [st', hone, hd1_fit]
      refine ⟨st', hstep, rfl, fun i hi => regs_set_lt (by decide) hi, trivial, ?_⟩
      dsimp only [st']
      rw [regs_set_self, hdiag]
      change _ = 1 + _
      omega)
    (fun _ _ _ _ _ _ => trivial)
    (fun s t hs ht st _ hone _ _ ha hb hdiag hup hcur => by
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
      have hd1_fit : Fits w (st.regs regDiag + 1) := by
        rw [hdiag]
        change Fits w (editDist Costs.unit (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - t)) + 1)
        exact hw.of_le (by omega)
      have hu1_fit : Fits w (st.regs regUp + 1) := by
        rw [hup]
        change Fits w (editDist Costs.unit (I.src.drop (I.src.length - s))
          (I.tgt.drop (I.tgt.length - (t + 1))) + 1)
        exact hw.of_le (by omega)
      have hl1_fit : Fits w (st.regs regCur + 1) := by
        rw [hcur]
        change Fits w (editDist Costs.unit (I.src.drop (I.src.length - (s + 1)))
          (I.tgt.drop (I.tgt.length - t)) + 1)
        exact hw.of_le (by omega)
      have hsubStep : ∃ s1, ExecWithin w
          (.branch (.eq regA regB) (ram[ regNext ← regDiag ])
            (ram[ regNext ← regDiag + regOne ])) st s1 3 ∧
          s1.mem = st.mem ∧
          (∀ i : Fin 22, i.val < 19 → s1.regs i = st.regs i) ∧
          s1.regs regNext = (Costs.unit (α := ℕ)).sub I.src[I.src.length - 1 - s]
            I.tgt[I.tgt.length - 1 - t] + st.regs regDiag := by
        by_cases hab : st.regs regA = st.regs regB
        · have hab' : I.src[I.src.length - 1 - s] = I.tgt[I.tgt.length - 1 - t] := by
            simpa [ha, hb] using hab
          refine ⟨st.set regNext (st.regs regDiag),
            (ExecWithin.branch_pos (by simpa only [Cond.holds_eq] using hab)
              ExecWithin.copy).mono (by omega),
            rfl, fun i hi => regs_set_lt (by decide) hi, ?_⟩
          rw [regs_set_self, Costs.unit_sub, ite_eq_left hab', Nat.zero_add]
        · have hab' : I.src[I.src.length - 1 - s] ≠ I.tgt[I.tgt.length - 1 - t] := by
            intro h; exact hab (by simp [ha, hb, h])
          let s1 := st.set regNext (st.regs regDiag + 1)
          have hadd : ExecWithin w (ram[ regNext ← regDiag + regOne ]) st s1 1 := by
            ram_eval [s1, hone, hd1_fit]
          refine ⟨s1, (ExecWithin.branch_neg (by simpa only [Cond.holds_eq] using hab) hadd).mono
            (by omega), rfl, fun i hi => regs_set_lt (by decide) hi, ?_⟩
          dsimp only [s1]
          rw [regs_set_self, Costs.unit_sub, ite_eq_right hab', Nat.add_comm]
      obtain ⟨s1, he1, hm1, hr1, hv1⟩ := hsubStep
      have hs1_one : s1.regs regOne = 1 := (hr1 regOne (by decide)).trans hone
      have hs1_up : s1.regs regUp = st.regs regUp := hr1 regUp (by decide)
      have hs1_cur : s1.regs regCur = st.regs regCur := hr1 regCur (by decide)
      have hs1_u_fit : Fits w (s1.regs regUp + 1) := by rw [hs1_up]; exact hu1_fit
      have hs1_l_fit : Fits w (s1.regs regCur + 1) := by rw [hs1_cur]; exact hl1_fit
      let s2 := (s1.set regTmp0 (s1.regs regUp + 1)).set regTmp1 (s1.regs regCur + 1)
      have he2 : ExecWithin w (ram[ regTmp0 ← regUp + regOne; regTmp1 ← regCur + regOne ])
          s1 s2 2 := by
        ram_eval [s2, hs1_one, hs1_u_fit, hs1_l_fit]
      obtain ⟨s3, he3, hm3, hr3, hv3⟩ := exec_min3Tail (w := w) s2
      refine ⟨s3, (he1.seq (he2.seq he3)).mono (by omega), hm3.trans hm1, ?_, ?_⟩
      · intro i hi
        have hs2_i : s2.regs i = s1.regs i := by
          dsimp only [s2]
          rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
        exact (hr3 i hi).trans (hs2_i.trans (hr1 i hi))
      · have hs2_next : s2.regs regNext = s1.regs regNext := by
          dsimp only [s2]
          rw [regs_set_lt (by decide : 20 ≤ regTmp1.val) (by decide),
            regs_set_lt (by decide : 20 ≤ regTmp0.val) (by decide)]
        have hs2_t0 : s2.regs regTmp0 = s1.regs regUp + 1 := by
          dsimp only [s2]
          rw [regs_set_lt (by decide : 21 ≤ regTmp1.val) (by decide), regs_set_self]
        have hs2_t1 : s2.regs regTmp1 = s1.regs regCur + 1 := by
          dsimp only [s2]
          rw [regs_set_self]
        rw [hs2_next, hs2_t0, hs2_t1, hv1, hs1_up, hs1_cur, hdiag, hup, hcur] at hv3
        rw [hv3]
        change min _ (min (_ + 1) (_ + 1)) = min _ (min (1 + _) (1 + _))
        rw [Nat.add_comm 1, Nat.add_comm 1])
  obtain ⟨xf, hexec, hres⟩ := hgrid
  refine ⟨xf, (hsetup.seq hexec).mono ?_, hres⟩
  nlinarith

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
    have hpos : 0 < I.sigma := by
      by_contra h
      have h0 : I.sigma * I.sigma = 0 := by
        have : I.sigma = 0 := by omega
        simp [this]
      exact Fin.elim0 (h0 ▸ idx)
    I.costs.sub ⟨idx.val / I.sigma, Nat.div_lt_of_lt_mul idx.isLt⟩
      ⟨idx.val % I.sigma, Nat.mod_lt _ hpos⟩

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

/-- Every `WeightedInstance` admits a fitting word width. -/
theorem inputAdmissible : InputAdmissible (fun _ => encode) FitsWidth := by
  intro I
  let B := max (I.encode.length + I.tgt.length + 4) I.valueBound
  obtain ⟨w, hw, hfit⟩ := InputFits.exists_width I.encode B
  have hB : Fits w B := (fits_self B).mono hw
  exact ⟨w, ⟨hB.of_le (le_max_left _ _), hB.of_le (le_max_right _ _)⟩, hfit⟩

end WeightedInstance

private theorem le_foldr_max_of_mem {v : ℕ} {l : List ℕ} (h : v ∈ l) :
    v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.1 h with rfl | hmem
    · exact le_max_left _ _
    · exact (ih hmem).trans (le_max_right _ _)

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
    I.costs.del a ≤ I.maxOpCost := by
  apply le_foldr_max_of_mem
  simp only [WeightedInstance.opCosts, List.mem_append]
  exact Or.inl (Or.inl (List.mem_ofFn.2 ⟨a, rfl⟩))

private theorem ins_le_maxOpCost (I : WeightedInstance) (b : Fin I.sigma) :
    I.costs.ins b ≤ I.maxOpCost := by
  apply le_foldr_max_of_mem
  simp only [WeightedInstance.opCosts, List.mem_append]
  exact Or.inl (Or.inr (List.mem_ofFn.2 ⟨b, rfl⟩))

private theorem sub_le_maxOpCost (I : WeightedInstance) (a b : Fin I.sigma) :
    I.costs.sub a b ≤ I.maxOpCost := by
  apply le_foldr_max_of_mem
  simp only [WeightedInstance.opCosts, List.mem_append]
  refine Or.inr ?_
  rw [← subTable_getElem I a b]
  exact List.getElem_mem _

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
  have h := init_mem_slice [I.sigma, I.src.length, I.tgt.length] (I.src.map Fin.val)
    (I.tgt.map Fin.val ++ I.opCosts) hi'
  simpa [WeightedInstance.encode, List.append_assoc] using h

private theorem weighted_read_tgt (I : WeightedInstance) {j : ℕ} (hj : j < I.tgt.length) :
    (Data.init I.encode : Data 22).mem (4 + I.src.length + j) = (I.tgt[j]).val := by
  have hj' : j < (I.tgt.map Fin.val).length := by simp [hj]
  have h := init_mem_slice ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val)
    (I.tgt.map Fin.val) I.opCosts hj'
  simpa [WeightedInstance.encode, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using h

private theorem weighted_read_del (I : WeightedInstance) (a : Fin I.sigma) :
    (Data.init I.encode : Data 22).mem (4 + I.src.length + I.tgt.length + a.val) =
      I.costs.del a := by
  have ha : a.val < (List.ofFn I.costs.del).length := by simp
  have h := init_mem_slice
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val)
    (List.ofFn I.costs.del) (List.ofFn I.costs.ins ++ I.subTable) ha
  simpa [WeightedInstance.encode, WeightedInstance.opCosts, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem weighted_read_ins (I : WeightedInstance) (b : Fin I.sigma) :
    (Data.init I.encode : Data 22).mem (4 + I.src.length + I.tgt.length + I.sigma + b.val) =
      I.costs.ins b := by
  have hb : b.val < (List.ofFn I.costs.ins).length := by simp
  have h := init_mem_slice
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del)
    (List.ofFn I.costs.ins) I.subTable hb
  simpa [WeightedInstance.encode, WeightedInstance.opCosts, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem weighted_read_sub (I : WeightedInstance) (a b : Fin I.sigma) :
    (Data.init I.encode : Data 22).mem
        (4 + I.src.length + I.tgt.length + 2 * I.sigma + a.val * I.sigma + b.val) =
      I.costs.sub a b := by
  have hab : a.val * I.sigma + b.val < I.subTable.length := by
    rw [WeightedInstance.length_subTable]
    have ha : a.val + 1 ≤ I.sigma := a.isLt
    have hb : b.val < I.sigma := b.isLt
    nlinarith
  have h := init_mem_slice
    ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del ++ List.ofFn I.costs.ins)
    I.subTable [] hab
  have hlen : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del ++ List.ofFn I.costs.ins).length + 1 + (a.val * I.sigma + b.val) =
      4 + I.src.length + I.tgt.length + 2 * I.sigma + a.val * I.sigma + b.val := by
    simp; omega
  have henc : ([I.sigma, I.src.length, I.tgt.length] ++ I.src.map Fin.val ++ I.tgt.map Fin.val ++
      List.ofFn I.costs.del ++ List.ofFn I.costs.ins) ++ I.subTable ++ [] = I.encode := by
    simp [WeightedInstance.encode, WeightedInstance.opCosts, List.append_assoc]
  rw [hlen, henc, subTable_getElem I a b] at h
  exact h

private theorem weighted_entry_le (I : WeightedInstance) (k₁ k₂ : ℕ) :
    editDist I.costs (I.src.drop k₁) (I.tgt.drop k₂) ≤
      (I.src.map I.costs.del).sum + (I.tgt.map I.costs.ins).sum := by
  have h := editDist_le_sum_del_ins I.costs (I.src.drop k₁) (I.tgt.drop k₂)
  have h1 := sum_map_drop_le I.costs.del I.src k₁
  have h2 := sum_map_drop_le I.costs.ins I.tgt k₂
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
  have hm1 : (Data.init I.encode : Data 22).mem 1 = I.sigma := by
    simp [WeightedInstance.encode]
  have hm2 : (Data.init I.encode : Data 22).mem 2 = I.src.length := by
    simp [WeightedInstance.encode]
  have hm3 : (Data.init I.encode : Data 22).mem 3 = I.tgt.length := by
    simp [WeightedInstance.encode]
  let d0 : Data 22 := Data.init I.encode
  let yBase := 4 + I.src.length
  let delBase := yBase + I.tgt.length
  let insBase := delBase + I.sigma
  let subBase := insBase + I.sigma
  let dpBase := I.encode.length + 1
  have hf4 : Fits w 4 := hwAddr.of_le (by omega)
  have hfy : Fits w yBase := hwAddr.of_le (by dsimp [yBase]; omega)
  have hfdel : Fits w delBase := hwAddr.of_le (by dsimp [delBase, yBase]; omega)
  have hfins : Fits w insBase := hwAddr.of_le (by dsimp [insBase, delBase, yBase]; omega)
  have hfsub : Fits w subBase := hwAddr.of_le (by dsimp [subBase, insBase, delBase, yBase]; omega)
  have hfdp : Fits w dpBase := hwAddr.of_le (by dsimp [dpBase]; omega)
  let x₀ := ((((((((((((((d0.set regTmp0 1).set regSigma I.sigma).set regTmp0 2).set regM
      I.src.length).set regTmp0 3).set regN I.tgt.length).set regXBase 4).set regYBase
      yBase).set regDelBase delBase).set regInsBase insBase).set regSubBase subBase).set regTmp0
      0).set regDPBase I.encode.length).set regOne 1).set regDPBase dpBase
  have hsetup : ExecWithin w weightedSetup d0 x₀ 15 := by
    ram_eval [weightedSetup, x₀, d0, yBase, delBase, insBase, subBase, dpBase,
      hm0, hm1, hm2, hm3, hf4, hfy, hfdel, hfins, hfsub, hfdp]
  exact ⟨x₀, hsetup, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by change subBase = _; dsimp [subBase, insBase, delBase, yBase]; omega⟩

private theorem mul_add_lt_sq {σ a b : ℕ} (ha : a < σ) (hb : b < σ) :
    a * σ + b < σ * σ := by
  have ha1 : a + 1 ≤ σ := ha
  nlinarith

private theorem mul_lt_sq {σ a : ℕ} (ha : a < σ) : a * σ < σ * σ := by
  have ha1 : a + 1 ≤ σ := ha
  nlinarith

private theorem exec_weightedEditDistCode {w : ℕ} (I : WeightedInstance) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w weightedEditDistCode (.init I.encode) xf
        (28 * I.src.length * I.tgt.length + 17 * I.src.length + 12 * I.tgt.length + 26) ∧
      xf.regs regCur = editDist I.costs I.src I.tgt := by
  obtain ⟨hwAddr, hwVal⟩ := hw
  have hlen := I.length_encode
  obtain ⟨x₀, hsetup, hx₀_mem, hm, hn, hxb, hyb, hdpb, hsig, hdelb, hinsb, hsubb⟩ :=
    exec_weightedSetup I hwAddr
  let subBase := 4 + I.src.length + I.tgt.length + 2 * I.sigma
  let RowInv (a : Fin I.sigma) (st : Data 22) : Prop :=
    st.regs regRowAux0 = I.costs.del a ∧ st.regs regRowAux1 = subBase + a.val * I.sigma
  have hgrid := exec_gridCode 3 5 13 (wagnerFischer I.costs) Fin.val I.src I.tgt x₀
    weightedInitCell weightedBorderCell weightedInnerCell RowInv
    hm hn
    (by rw [hxb, hdpb]; omega)
    (by rw [hyb, hdpb]; omega)
    (fun i hi => by rw [hx₀_mem, hxb]; exact weighted_read_src I hi)
    (fun j hj => by rw [hx₀_mem, hyb]; exact weighted_read_tgt I hj)
    (hwAddr.of_le (by omega)) (fits_zero w)
    (by rw [hdpb]; exact hwAddr.of_le (by omega))
    (hwAddr.of_le (by omega))
    (fun t ht st hregs _ hmemlt hb hcur => by
      let b : Fin I.sigma := I.tgt[I.tgt.length - 1 - t]
      have hinsb_reg : st.regs regInsBase = 4 + I.src.length + I.tgt.length + I.sigma :=
        (hregs regInsBase (by decide)).trans hinsb
      have hb_lt : b.val < I.sigma := b.isLt
      have haddr_lt : st.regs regInsBase + st.regs regB < x₀.regs regDPBase := by
        rw [hinsb_reg, hb, hdpb]; dsimp only [b] at hb_lt; omega
      have haddr_fit : Fits w (st.regs regInsBase + st.regs regB) := by
        rw [hinsb_reg, hb]; dsimp only [b] at hb_lt; exact hwAddr.of_le (by omega)
      have hread_ins : st.mem (st.regs regInsBase + st.regs regB) = I.costs.ins b := by
        rw [hmemlt _ haddr_lt, hx₀_mem, hinsb_reg, hb]
        exact weighted_read_ins I b
      have hsum_fit : Fits w (I.costs.ins b + st.regs regCur) := by
        rw [hcur]
        have h1 := ins_le_maxOpCost I b
        have h2 := weighted_entry_le I I.src.length (I.tgt.length - t)
        rw [List.drop_length] at h2
        change Fits w (I.costs.ins b + editDist I.costs [] (I.tgt.drop (I.tgt.length - t)))
        exact hwVal.of_le (by dsimp [WeightedInstance.valueBound]; omega)
      let st' := ((st.set regTmp0 (st.regs regInsBase + st.regs regB)).set regTmp0
          (I.costs.ins b)).set regCur (I.costs.ins b + st.regs regCur)
      have hstep : ExecWithin w weightedInitCell st st' 3 := by
        ram_eval [weightedInitCell, st', haddr_fit, hread_ins, hsum_fit]
      refine ⟨st', hstep, rfl, ?_, ?_⟩
      · intro i hi
        dsimp only [st']
        rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
      · dsimp only [st']
        rw [regs_set_self, hcur]
        rfl)
    (fun s hs st hregs _ hmemlt ha hdiag => by
      let a : Fin I.sigma := I.src[I.src.length - 1 - s]
      have hdel_reg : st.regs regDelBase = 4 + I.src.length + I.tgt.length :=
        (hregs regDelBase (by decide)).trans hdelb
      have hsig_reg : st.regs regSigma = I.sigma :=
        (hregs regSigma (by decide)).trans hsig
      have hsub_reg : st.regs regSubBase = subBase :=
        (hregs regSubBase (by decide)).trans hsubb
      have ha_lt : (I.src[I.src.length - 1 - s]).val < I.sigma := a.isLt
      have hmul_lt : (I.src[I.src.length - 1 - s]).val * I.sigma < I.sigma * I.sigma :=
        mul_lt_sq ha_lt
      have hdel_lt : st.regs regDelBase + st.regs regA < x₀.regs regDPBase := by
        rw [hdel_reg, ha, hdpb]; omega
      have hdel_fit : Fits w (st.regs regDelBase + st.regs regA) := by
        rw [hdel_reg, ha]; exact hwAddr.of_le (by omega)
      have hread_del : st.mem (st.regs regDelBase + st.regs regA) = I.costs.del a := by
        rw [hmemlt _ hdel_lt, hx₀_mem, hdel_reg, ha]
        exact weighted_read_del I a
      have hcur_fit : Fits w (I.costs.del a + st.regs regDiag) := by
        rw [hdiag]
        have h1 := del_le_maxOpCost I a
        have h2 := weighted_entry_le I (I.src.length - s) I.tgt.length
        rw [List.drop_length] at h2
        change Fits w (I.costs.del a + editDist I.costs (I.src.drop (I.src.length - s)) [])
        exact hwVal.of_le (by dsimp [WeightedInstance.valueBound]; omega)
      have hmul_fit : Fits w (st.regs regA * I.sigma) := by
        rw [ha]; exact hwAddr.of_le (by omega)
      have hsub_fit : Fits w (subBase + st.regs regA * I.sigma) := by
        rw [ha]; exact hwAddr.of_le (by dsimp only [subBase]; omega)
      let st' := ((((st.set regTmp0 (st.regs regDelBase + st.regs regA)).set regRowAux0
          (I.costs.del a)).set regCur (I.costs.del a + st.regs regDiag)).set regTmp0
          (st.regs regA * I.sigma)).set regRowAux1 (subBase + st.regs regA * I.sigma)
      have hstep : ExecWithin w weightedBorderCell st st' 5 := by
        ram_eval [weightedBorderCell, st', hsig_reg, hsub_reg, hdel_fit, hread_del,
          hcur_fit, hmul_fit, hsub_fit]
      refine ⟨st', hstep, rfl, ?_, ?_, ?_⟩
      · intro i hi
        dsimp only [st']
        rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
          regs_set_lt (by decide) hi, regs_set_lt (by decide) hi]
      · refine ⟨?_, by dsimp only [st']; rw [regs_set_self, ha]⟩
        dsimp only [st']
        rw [regs_set_lt (by decide : 17 ≤ regRowAux1.val) (by decide),
          regs_set_lt (by decide : 17 ≤ regTmp0.val) (by decide),
          regs_set_lt (by decide : 17 ≤ regCur.val) (by decide),
          regs_set_self]
      · dsimp only [st']
        rw [regs_set_ne (by decide : regCur ≠ regRowAux1),
          regs_set_lt (by decide : 19 ≤ regTmp0.val) (by decide),
          regs_set_self, hdiag]
        rfl)
    (fun a st st' h0 h1 ⟨ha0, ha1⟩ => ⟨h0.trans ha0, h1.trans ha1⟩)
    (fun s t hs ht st hregs _ hmemlt ⟨hra0, hra1⟩ ha hb hdiag hup hcur => by
      let a : Fin I.sigma := I.src[I.src.length - 1 - s]
      let b : Fin I.sigma := I.tgt[I.tgt.length - 1 - t]
      have hins_reg : st.regs regInsBase = 4 + I.src.length + I.tgt.length + I.sigma :=
        (hregs regInsBase (by decide)).trans hinsb
      have hb_lt : (I.tgt[I.tgt.length - 1 - t]).val < I.sigma := b.isLt
      have hprod_lt : (I.src[I.src.length - 1 - s]).val * I.sigma +
          (I.tgt[I.tgt.length - 1 - t]).val < I.sigma * I.sigma :=
        mul_add_lt_sq a.isLt hb_lt
      have hsub_lt : st.regs regRowAux1 + st.regs regB < x₀.regs regDPBase := by
        rw [hra1, hb, hdpb]; dsimp only [subBase] at *; omega
      have hins_lt : st.regs regInsBase + st.regs regB < x₀.regs regDPBase := by
        rw [hins_reg, hb, hdpb]; omega
      have hsub_addr_fit : Fits w (st.regs regRowAux1 + st.regs regB) := by
        rw [hra1, hb]; dsimp only [subBase] at *; exact hwAddr.of_le (by omega)
      have hins_addr_fit : Fits w (st.regs regInsBase + st.regs regB) := by
        rw [hins_reg, hb]; exact hwAddr.of_le (by omega)
      have hread_sub : st.mem (st.regs regRowAux1 + st.regs regB) = I.costs.sub a b := by
        rw [hmemlt _ hsub_lt, hx₀_mem, hra1, hb]
        simpa only [subBase, a, b, Nat.add_assoc] using weighted_read_sub I a b
      have hread_ins : st.mem (st.regs regInsBase + st.regs regB) = I.costs.ins b := by
        rw [hmemlt _ hins_lt, hx₀_mem, hins_reg, hb]
        exact weighted_read_ins I b
      have hc1_fit : Fits w (I.costs.sub a b + st.regs regDiag) := by
        rw [hdiag]
        have h1 := sub_le_maxOpCost I a b
        have h2 := weighted_entry_le I (I.src.length - s) (I.tgt.length - t)
        change Fits w (I.costs.sub a b +
          editDist I.costs (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - t)))
        exact hwVal.of_le (by dsimp [WeightedInstance.valueBound]; omega)
      have hc2_fit : Fits w (I.costs.del a + st.regs regUp) := by
        rw [hup]
        have h1 := del_le_maxOpCost I a
        have h2 := weighted_entry_le I (I.src.length - s) (I.tgt.length - (t + 1))
        change Fits w (I.costs.del a +
          editDist I.costs (I.src.drop (I.src.length - s)) (I.tgt.drop (I.tgt.length - (t + 1))))
        exact hwVal.of_le (by dsimp [WeightedInstance.valueBound]; omega)
      have hc3_fit : Fits w (I.costs.ins b + st.regs regCur) := by
        rw [hcur]
        have h1 := ins_le_maxOpCost I b
        have h2 := weighted_entry_le I (I.src.length - (s + 1)) (I.tgt.length - t)
        change Fits w (I.costs.ins b +
          editDist I.costs (I.src.drop (I.src.length - (s + 1))) (I.tgt.drop (I.tgt.length - t)))
        exact hwVal.of_le (by dsimp [WeightedInstance.valueBound]; omega)
      let s1 := ((((((st.set regTmp0 (st.regs regRowAux1 + st.regs regB)).set regTmp0
          (I.costs.sub a b)).set regNext (I.costs.sub a b + st.regs regDiag)).set regTmp0
          (st.regs regInsBase + st.regs regB)).set regTmp1 (I.costs.ins b)).set regTmp1
          (I.costs.ins b + st.regs regCur)).set regTmp0 (I.costs.del a + st.regs regUp)
      have he1 : ExecWithin w (ram[
          regTmp0 ← regRowAux1 + regB;
          regTmp0 ← *regTmp0;
          regNext ← regTmp0 + regDiag;
          regTmp0 ← regInsBase + regB;
          regTmp1 ← *regTmp0;
          regTmp1 ← regTmp1 + regCur;
          regTmp0 ← regRowAux0 + regUp ]) st s1 7 := by
        ram_eval [s1, a, b, hra0, hsub_addr_fit, hins_addr_fit, hread_sub, hread_ins,
          hc1_fit, hc2_fit, hc3_fit]
      obtain ⟨s2, he2, hm2, hr2, hv2⟩ := exec_min3Tail (w := w) s1
      refine ⟨s2, (he1.seq he2).mono (by omega), hm2, ?_, ?_⟩
      · intro i hi
        have hs1_i : s1.regs i = st.regs i := by
          dsimp only [s1]
          rw [regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
            regs_set_lt (by decide) hi, regs_set_lt (by decide) hi, regs_set_lt (by decide) hi,
            regs_set_lt (by decide) hi]
        exact (hr2 i hi).trans hs1_i
      · have hs1_next : s1.regs regNext = I.costs.sub a b + st.regs regDiag := by
          dsimp only [s1]
          rw [regs_set_lt (by decide : 20 ≤ regTmp0.val) (by decide),
            regs_set_lt (by decide : 20 ≤ regTmp1.val) (by decide),
            regs_set_lt (by decide : 20 ≤ regTmp1.val) (by decide),
            regs_set_lt (by decide : 20 ≤ regTmp0.val) (by decide),
            regs_set_self]
        have hs1_t0 : s1.regs regTmp0 = I.costs.del a + st.regs regUp := by
          dsimp only [s1]
          rw [regs_set_self]
        have hs1_t1 : s1.regs regTmp1 = I.costs.ins b + st.regs regCur := by
          dsimp only [s1]
          rw [regs_set_ne (by decide : regTmp1 ≠ regTmp0),
            regs_set_self]
        rw [hs1_next, hs1_t0, hs1_t1, hdiag, hup, hcur] at hv2
        exact hv2)
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
