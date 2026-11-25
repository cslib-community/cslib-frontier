/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.OptimalBST.Knuth
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
# Word-RAM optimal binary search trees and Knuth's quadratic speedup

Checked Word-RAM implementations and `O(n³)` / `O(n²)` running-time bounds for the dynamic programs
of `CslibFrontier.Algorithms.Lean.OptimalBST.Knuth`:

* **Cubic optimal BST** (`plainBSTProgram`): fills the interval cost and root tables by increasing
  interval length `d + 1 = 1, …, n`, scanning every candidate root `k ∈ [i + 1, j]`. Computes
  `(plainBST I.weightFn I.numKeys).cost = optCost I.weightFn 0 I.numKeys` for **every** encoded
  weight table `I : OptimalBSTInstance` in at most `17 (n + 1)³` standard-basis instructions.
* **Knuth's window optimal BST** (`knuthBSTProgram`): restricts each cell `(i, j]` with `i + 1 < j`
  to the candidate-root window `[root(i, j - 1), root(i + 1, j)]` read from the previous diagonal in
  memory. Whenever `I.weightFn` satisfies `QuadrangleIneq` and `MonotoneOnIntervals`
  (`OptimalBSTInstance.IsKnuthValid`), the windows along each diagonal telescope
  (`sum_knuth_window_le`) and `knuthBSTProgram` computes `(knuthBST I.weightFn I.numKeys).cost` in
  at most `58 (n + 1)²` instructions.

Both programs instantiate a shared private dynamic-programming engine parameterized by the
candidate-window subprogram. Every header read, row-major address calculation, table lookup,
candidate comparison, memory store, loop branch/jump, and final `halt` is charged by the Word-RAM
semantics.

## Main definitions

* `Cslib.Algorithms.WordRAM.OptimalBST.OptimalBSTInstance`: an `n`-key instance carrying the
  `(n + 1) × (n + 1)` interval weight matrix `weights`, its clamped extension
  `OptimalBSTInstance.weightFn`, its flat word layout `OptimalBSTInstance.encode`, its word-width
  condition `OptimalBSTInstance.FitsWidth`, and the quadrangle/monotonicity predicate
  `OptimalBSTInstance.IsKnuthValid`.
* `Cslib.Algorithms.WordRAM.OptimalBST.OptimalBSTInstance.ofWeight`: restricts any interval weight
  `w : ℕ → ℕ → ℕ` to keys `1, …, n` while preserving `QuadrangleIneq` and `MonotoneOnIntervals`.
* `Cslib.Algorithms.WordRAM.OptimalBST.plainBSTProgram`, `knuthBSTProgram`: fixed
  `Program .standard 22` programs for the cubic and Knuth window algorithms.

## Main results

* `Cslib.Algorithms.WordRAM.OptimalBST.computesInTime_plainBST`,
  `uniformComputableInTime_plainBST`: `plainBSTProgram` computes
  `(plainBST I.weightFn I.numKeys).cost` in at most `17 (n + 1)³` instructions for every
  `OptimalBSTInstance` at fitting widths.
* `Cslib.Algorithms.WordRAM.OptimalBST.executes_knuthBST`, `computesInTime_knuthBST`,
  `uniformComputableInTime_knuthBST`: under `QuadrangleIneq` and `MonotoneOnIntervals`,
  `knuthBSTProgram` computes `(knuthBST I.weightFn I.numKeys).cost` in at most `58 (n + 1)²`
  instructions at fitting widths.
* `Cslib.Algorithms.WordRAM.OptimalBST.OptimalBSTInstance.isKnuthValid_knuthWeight`: instances built
  from `knuthWeight p q` satisfy `IsKnuthValid`.

## References

* [D. E. Knuth, *Optimum binary search trees*][Knuth1971]
* [F. F. Yao, *Efficient dynamic programming using quadrangle inequalities*][Yao1980b]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*, Section 15.5][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.OptimalBST

open Cslib.Algorithms.Lean.OptimalBST
open Cslib.WordRAM
open Finset

/-! ## Encoded optimal-BST instances -/

/-- An encoded optimal-BST instance on keys `1, …, numKeys` with interval weights
`weights i j` (`0 ≤ i, j ≤ numKeys`). -/
structure OptimalBSTInstance where
  /-- Number of keys `n`. -/
  numKeys : ℕ
  /-- Interval weight matrix `w(i, j)` for `0 ≤ i, j ≤ numKeys`. -/
  weights : Fin (numKeys + 1) → Fin (numKeys + 1) → ℕ

namespace OptimalBSTInstance

/-- Clamped extension of `I.weights` to `ℕ → ℕ → ℕ`, preserving `QuadrangleIneq` and
`MonotoneOnIntervals`. -/
@[expose] def weightFn (I : OptimalBSTInstance) (i j : ℕ) : ℕ :=
  I.weights ⟨min i I.numKeys, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    ⟨min j I.numKeys, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem weightFn_eq_weights (I : OptimalBSTInstance) {i j : ℕ} (hi : i ≤ I.numKeys)
    (hj : j ≤ I.numKeys) :
    I.weightFn i j = I.weights ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩ := by
  simp only [weightFn, Nat.min_eq_left hi, Nat.min_eq_left hj]

/-- Row-major `(numKeys + 1)²`-word table of `I.weights`. -/
@[expose] def weightTable (I : OptimalBSTInstance) : List ℕ :=
  (List.finRange (I.numKeys + 1)).flatMap fun i => List.ofFn (I.weights i)

/-- Flat Word-RAM input `[numKeys] ++ weightTable`. -/
@[expose] def encode (I : OptimalBSTInstance) : List ℕ :=
  [I.numKeys] ++ I.weightTable

@[simp]
theorem length_weightTable (I : OptimalBSTInstance) :
    I.weightTable.length = (I.numKeys + 1) * (I.numKeys + 1) := by
  rw [weightTable, List.flatMap_ofFn_prod, List.length_ofFn]

@[simp]
theorem length_encode (I : OptimalBSTInstance) :
    I.encode.length = 1 + (I.numKeys + 1) * (I.numKeys + 1) := by
  simp only [encode, List.singleton_append, List.length_cons, length_weightTable]
  omega

/-- Largest interval weight in `I.weightTable`. -/
@[expose] def maxWeight (I : OptimalBSTInstance) : ℕ :=
  I.weightTable.foldr max 0

/-- Address upper bound covering input words, loop counters, and both `(numKeys + 1)²`-word
working tables (`cost` and `root`). -/
@[expose] def addrBound (I : OptimalBSTInstance) : ℕ :=
  I.encode.length + I.numKeys + 2 * ((I.numKeys + 1) * (I.numKeys + 1)) + 4

/-- Value upper bound `(numKeys + 1) * maxWeight`, dominating every input weight and intermediate
DP cost sum on intervals inside `[0, numKeys]`. -/
@[expose] def valueBound (I : OptimalBSTInstance) : ℕ :=
  (I.numKeys + 1) * I.maxWeight

/-- Word-width condition for `plainBSTProgram` and `knuthBSTProgram`. -/
abbrev FitsWidth (I : OptimalBSTInstance) (w : ℕ) : Prop :=
  Fits w I.addrBound ∧ Fits w I.valueBound

private theorem weights_mem_weightTable (I : OptimalBSTInstance) (i j : Fin (I.numKeys + 1)) :
    I.weights i j ∈ I.weightTable := by
  rw [weightTable, List.mem_flatMap]
  exact ⟨i, List.mem_finRange i, List.mem_ofFn.2 ⟨j, rfl⟩⟩

theorem weights_le_maxWeight (I : OptimalBSTInstance) (i j : Fin (I.numKeys + 1)) :
    I.weights i j ≤ I.maxWeight :=
  List.le_max_of_le' 0 (weights_mem_weightTable I i j) le_rfl

theorem weightFn_le_maxWeight (I : OptimalBSTInstance) (i j : ℕ) :
    I.weightFn i j ≤ I.maxWeight :=
  I.weights_le_maxWeight _ _

/-- `FitsWidth` already bounds the length and every word of `I.encode`. -/
theorem FitsWidth.inputFits {I : OptimalBSTInstance} {w : ℕ} (hw : I.FitsWidth w) :
    InputFits w I.encode := by
  obtain ⟨hwAddr, hwVal⟩ := hw
  dsimp only [addrBound] at hwAddr
  dsimp only [valueBound] at hwVal
  have hlen := I.length_encode
  refine ⟨hwAddr.of_le (by omega), fun v hv => ?_⟩
  simp only [encode, List.singleton_append, List.mem_cons] at hv
  rcases hv with rfl | hwt
  · exact hwAddr.of_le (by omega)
  · have hle : v ≤ I.maxWeight := List.le_max_of_le' 0 hwt le_rfl
    exact hwVal.of_le (by nlinarith)

/-- Every `OptimalBSTInstance` admits a fitting word width. -/
theorem inputAdmissible : InputAdmissible (fun _ => encode) FitsWidth := by
  intro I
  let B := max I.addrBound I.valueBound
  obtain ⟨w, hw0, _⟩ := InputFits.exists_width I.encode B
  have hB : Fits w B := (fits_self B).mono hw0
  have hw : I.FitsWidth w :=
    ⟨hB.of_le (Nat.le_max_left _ _), hB.of_le (Nat.le_max_right _ _)⟩
  exact ⟨w, hw, hw.inputFits⟩

/-- `I.weightFn` satisfies the quadrangle inequality and interval monotonicity required by Knuth's
quadratic speedup. -/
abbrev IsKnuthValid (I : OptimalBSTInstance) : Prop :=
  QuadrangleIneq I.weightFn ∧ MonotoneOnIntervals I.weightFn

/-- Restrict any interval weight `w : ℕ → ℕ → ℕ` to keys `1, …, n`. -/
@[expose] def ofWeight (n : ℕ) (w : ℕ → ℕ → ℕ) : OptimalBSTInstance where
  numKeys := n
  weights i j := w i.val j.val

@[simp]
theorem ofWeight_numKeys (n : ℕ) (w : ℕ → ℕ → ℕ) : (ofWeight n w).numKeys = n := rfl

theorem ofWeight_weightFn_eq (n : ℕ) (w : ℕ → ℕ → ℕ) (i j : ℕ) :
    (ofWeight n w).weightFn i j = w (min i n) (min j n) := rfl

theorem optCost_ofWeight_eq (n : ℕ) (w : ℕ → ℕ → ℕ) :
    optCost (ofWeight n w).weightFn 0 n = optCost w 0 n :=
  optCost_congr fun a b _ hab hb => by
    simp only [ofWeight_weightFn_eq, Nat.min_eq_left (hab.le.trans hb), Nat.min_eq_left hb]

theorem plainBST_cost_ofWeight (n : ℕ) (w : ℕ → ℕ → ℕ) :
    (plainBST (ofWeight n w).weightFn n).cost = (plainBST w n).cost := by
  rw [plainBST_eq, plainBST_eq, optCost_ofWeight_eq]

theorem isKnuthValid_ofWeight {w : ℕ → ℕ → ℕ} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : (ofWeight n w).IsKnuthValid :=
  ⟨fun _ _ _ _ h₁ h₂ h₃ =>
      hqi (min_le_min_right n h₁) (min_le_min_right n h₂) (min_le_min_right n h₃),
    fun _ _ _ _ h₁ h₂ h₃ =>
      hmono (min_le_min_right n h₁) (min_le_min_right n h₂) (min_le_min_right n h₃)⟩

theorem knuthBST_cost_ofWeight {w : ℕ → ℕ → ℕ} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) :
    (knuthBST (ofWeight n w).weightFn n).cost = (knuthBST w n).cost := by
  have hv := isKnuthValid_ofWeight hqi hmono n
  rw [knuthBST_eq hv.1 hv.2, knuthBST_eq hqi hmono, optCost_ofWeight_eq]

theorem isKnuthValid_knuthWeight (n : ℕ) (p q : ℕ → ℕ) :
    (ofWeight n (knuthWeight p q)).IsKnuthValid :=
  isKnuthValid_ofWeight (quadrangleIneq_knuthWeight p q)
    (monotoneOnIntervals_knuthWeight (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)) n

theorem inputAdmissible_knuthValid :
    InputAdmissible (fun _ (I : {I : OptimalBSTInstance // I.IsKnuthValid}) => I.1.encode)
      (fun I w => I.1.FitsWidth w) :=
  fun ⟨I, _⟩ => inputAdmissible I

end OptimalBSTInstance

/-! ## Variable-cost counting loop helper -/

private theorem loop_count_sum_aux {B : Basis} {r w N : ℕ} {index limit : Fin r}
    {body : Code B r} (P : ℕ → Data r → Prop) (cost : ℕ → ℕ)
    (hlimit : ∀ y, P (y.regs index) y → y.regs limit = N)
    (hbody : ∀ y, P (y.regs index) y → y.regs index < N →
      ∃ z, ExecWithin w body y z (cost (y.regs index)) ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1) :
    ∀ m k (x : Data r), k + m = N → x.regs index = k → P k x →
      ∃ y, ExecWithin w (.loop (.lt index limit) body) x y
        ((∑ t ∈ range m, (cost (k + t) + 2)) + 2) ∧ P N y ∧ y.regs index = N
  | 0, k, x, hkm, hxk, hPx => by
    subst hkm
    have hstop : ¬Cond.Holds (.lt index limit) x := by
      simp [Cond.holds_lt, hxk, hlimit x (hxk.symm ▸ hPx)]
    simpa [sum_range_zero] using ⟨x, ExecWithin.loop_exit hstop, hPx, hxk⟩
  | m + 1, k, x, hkm, hxk, hPx => by
    have hkN : k < N := by omega
    have hgo : Cond.Holds (.lt index limit) x := by
      simp [Cond.holds_lt, hxk, hlimit x (hxk.symm ▸ hPx), hkN]
    obtain ⟨z, hz, hPz, hzk⟩ := hbody x (hxk.symm ▸ hPx) (hxk.symm ▸ hkN)
    rw [hxk] at hz hPz hzk
    obtain ⟨y, hy, hPy, hyN⟩ :=
      loop_count_sum_aux P cost hlimit hbody m (k + 1) z (by omega) hzk hPz
    refine ⟨y, (ExecWithin.loop_iter hgo hz hy).mono ?_, hPy, hyN⟩
    rw [sum_range_succ']
    have hsum : ∑ t ∈ range m, (cost (k + (t + 1)) + 2) =
        ∑ t ∈ range m, (cost (k + 1 + t) + 2) :=
      sum_congr rfl fun t _ => by congr 1; congr 1; omega
    have hk0 : cost (k + 0) = cost k := congrArg cost (Nat.add_zero k)
    omega

private theorem loop_count_sum {B : Basis} {r w N : ℕ} {index limit : Fin r}
    {body : Code B r} (P : ℕ → Data r → Prop) (cost : ℕ → ℕ)
    (hlimit : ∀ y, P (y.regs index) y → y.regs limit = N)
    (hbody : ∀ y, P (y.regs index) y → y.regs index < N →
      ∃ z, ExecWithin w body y z (cost (y.regs index)) ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1)
    {x : Data r} (hx0 : x.regs index = 0) (hx : P 0 x) :
    ∃ y, ExecWithin w (.loop (.lt index limit) body) x y
      ((∑ i ∈ range N, (cost i + 2)) + 2) ∧ P N y ∧ y.regs index = N := by
  simpa using loop_count_sum_aux P cost hlimit hbody N 0 x (Nat.zero_add N) hx0 hx

/-! ## Registers and shared Word-RAM DP engine -/

private abbrev regN : Fin 22 := 0
private abbrev regStride : Fin 22 := 1
private abbrev regWBase : Fin 22 := 2
private abbrev regCostBase : Fin 22 := 3
private abbrev regRootBase : Fin 22 := 4
private abbrev regOne : Fin 22 := 5
private abbrev regZero : Fin 22 := 6
private abbrev regD : Fin 22 := 7
private abbrev regLen : Fin 22 := 8
private abbrev regILim : Fin 22 := 9
private abbrev regI : Fin 22 := 10
private abbrev regJ : Fin 22 := 11
private abbrev regLo : Fin 22 := 12
private abbrev regHi : Fin 22 := 13
private abbrev regK : Fin 22 := 14
private abbrev regKLim : Fin 22 := 15
private abbrev regBestCost : Fin 22 := 16
private abbrev regBestRoot : Fin 22 := 17
private abbrev regCand : Fin 22 := 18
private abbrev regTmp0 : Fin 22 := 19
private abbrev regTmp1 : Fin 22 := 20
private abbrev regOut : Fin 22 := 21

private abbrev stride (I : OptimalBSTInstance) : ℕ := I.numKeys + 1
private abbrev costBase (I : OptimalBSTInstance) : ℕ := I.encode.length + 1
private abbrev rootBase (I : OptimalBSTInstance) : ℕ := costBase I + stride I * stride I
private abbrev costAddr (I : OptimalBSTInstance) (a b : ℕ) : ℕ := costBase I + a * stride I + b
private abbrev rootAddr (I : OptimalBSTInstance) (a b : ℕ) : ℕ := rootBase I + a * stride I + b

private structure FixedRegs (I : OptimalBSTInstance) (st : Data 22) : Prop where
  n : st.regs regN = I.numKeys
  str : st.regs regStride = stride I
  wb : st.regs regWBase = 2
  cb : st.regs regCostBase = costBase I
  rb : st.regs regRootBase = rootBase I
  one : st.regs regOne = 1
  zero : st.regs regZero = 0

private theorem fixedRegs_of_regs_eq {I : OptimalBSTInstance} {s₁ s₂ : Data 22}
    (h : FixedRegs I s₁) (hr : ∀ idx : Fin 22, idx.val < 7 → s₂.regs idx = s₁.regs idx) :
    FixedRegs I s₂ :=
  ⟨(hr _ (by decide)).trans h.n, (hr _ (by decide)).trans h.str,
   (hr _ (by decide)).trans h.wb, (hr _ (by decide)).trans h.cb,
   (hr _ (by decide)).trans h.rb, (hr _ (by decide)).trans h.one,
   (hr _ (by decide)).trans h.zero⟩

private def bstSetup : Code .standard 22 :=
  ram[
    regZero ← #0;
    regOne ← #1;
    regWBase ← #2;
    regTmp0 ← #1;
    regN ← *regTmp0;
    regStride ← regN + regOne;
    regCostBase ← *regZero;
    regCostBase ← regCostBase + regOne;
    regTmp0 ← regStride * regStride;
    regRootBase ← regCostBase + regTmp0;
    regD ← #0 ]

private def plainWindowCode : Code .standard 22 :=
  ram[
    regLo ← regI + regOne;
    regHi ← regJ ]

private def knuthWindowPos : Code .standard 22 :=
  ram[
    regTmp0 ← regI * regStride;
    regTmp1 ← regJ - regOne;
    regTmp0 ← regTmp0 + regTmp1;
    regTmp0 ← regRootBase + regTmp0;
    regLo ← *regTmp0;
    regTmp0 ← regI + regOne;
    regTmp0 ← regTmp0 * regStride;
    regTmp0 ← regTmp0 + regJ;
    regTmp0 ← regRootBase + regTmp0;
    regHi ← *regTmp0 ]

private def knuthWindowCode : Code .standard 22 :=
  .branch (.lt regZero regD)
    knuthWindowPos
    (ram[
      regLo ← regJ;
      regHi ← regJ ])

private def evalCandLeft : Code .standard 22 :=
  ram[
    regTmp0 ← regI * regStride;
    regTmp1 ← regK - regOne;
    regTmp0 ← regTmp0 + regTmp1;
    regTmp0 ← regCostBase + regTmp0;
    regTmp0 ← *regTmp0 ]

private def evalCandRight : Code .standard 22 :=
  ram[
    regTmp1 ← regK * regStride;
    regTmp1 ← regTmp1 + regJ;
    regTmp1 ← regCostBase + regTmp1;
    regTmp1 ← *regTmp1;
    regCand ← regTmp0 + regTmp1 ]

private def evalCandCode : Code .standard 22 :=
  .seq evalCandLeft evalCandRight

private def scanInitCode : Code .standard 22 :=
  .seq (ram[ regK ← regLo ])
    (.seq evalCandCode
      (ram[
        regBestCost ← regCand;
        regBestRoot ← regLo;
        regK ← regLo + regOne;
        regKLim ← regHi + regOne ]))

private def scanUpdateCode : Code .standard 22 :=
  .branch (.lt regBestCost regCand)
    (ram[ regBestCost ← regBestCost ])
    (ram[
      regBestCost ← regCand;
      regBestRoot ← regK ])

private def scanStepCode : Code .standard 22 :=
  .seq evalCandCode (.seq scanUpdateCode (ram[ regK ← regK + regOne ]))

private def cellAddWeight : Code .standard 22 :=
  ram[
    regTmp0 ← regI * regStride;
    regTmp0 ← regTmp0 + regJ;
    regTmp1 ← regWBase + regTmp0;
    regTmp1 ← *regTmp1;
    regBestCost ← regTmp1 + regBestCost ]

private def cellStoreBoth : Code .standard 22 :=
  ram[
    regTmp1 ← regCostBase + regTmp0;
    *regTmp1 ← regBestCost;
    regTmp1 ← regRootBase + regTmp0;
    *regTmp1 ← regBestRoot;
    regI ← regI + regOne ]

private def cellWriteCode : Code .standard 22 :=
  .seq cellAddWeight cellStoreBoth

private def cellBody (winCode : Code .standard 22) : Code .standard 22 :=
  .seq (ram[ regJ ← regI + regLen ])
    (.seq winCode
      (.seq scanInitCode
        (.seq (.loop (.lt regK regKLim) scanStepCode)
          cellWriteCode)))

private def diagPreCode : Code .standard 22 :=
  ram[
    regLen ← regD + regOne;
    regILim ← regStride - regLen;
    regI ← #0 ]

private def diagBody (winCode : Code .standard 22) : Code .standard 22 :=
  .seq diagPreCode
    (.seq (.loop (.lt regI regILim) (cellBody winCode))
      (ram[ regD ← regD + regOne ]))

private def bstFinalRead : Code .standard 22 :=
  ram[
    regTmp0 ← regCostBase + regN;
    regOut ← *regTmp0 ]

private def bstCode (winCode : Code .standard 22) : Code .standard 22 :=
  .seq bstSetup
    (.seq (.loop (.lt regD regN) (diagBody winCode))
      bstFinalRead)

/-- Fixed standard-basis Word-RAM program for the `O(n³)` optimal-BST dynamic program. -/
def plainBSTProgram : Program .standard 22 :=
  (bstCode plainWindowCode).program regOut

/-- Fixed standard-basis Word-RAM program for Knuth's `O(n²)` window optimal-BST algorithm. -/
def knuthBSTProgram : Program .standard 22 :=
  (bstCode knuthWindowCode).program regOut

/-! ## Memory representation and framing lemmas -/

private theorem init_mem_above (input : List ℕ) {addr : ℕ} (h : input.length + 1 ≤ addr) :
    (Data.init input : Data 22).mem addr = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, addr = k + 1 := ⟨addr - 1, by omega⟩
  rw [Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private theorem bst_read_weight (I : OptimalBSTInstance) {i j : ℕ} (hi : i ≤ I.numKeys)
    (hj : j ≤ I.numKeys) :
    (Data.init I.encode : Data 22).mem (2 + (i * stride I + j)) = I.weightFn i j := by
  have hlt : i * stride I + j < I.weightTable.length := by
    rw [I.length_weightTable]; dsimp only [stride]; nlinarith
  have h := Data.init_realizes_append (r := 22) [I.numKeys] I.weightTable []
    ⟨i * stride I + j, hlt⟩
  rw [List.append_nil] at h
  change (Data.init I.encode : Data 22).mem (2 + (i * stride I + j)) =
    I.weightTable[i * stride I + j] at h
  have hgd := List.getD_flatMap_ofFn I.weights 0
    ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩
  change I.weightTable.getD (i * stride I + j) 0 = _ at hgd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at hgd
  rw [h, hgd, I.weightFn_eq_weights hi hj]

private theorem optCost_le_mul_maxWeight (I : OptimalBSTInstance) (i j : ℕ) :
    optCost I.weightFn i j ≤ (j - i) * I.maxWeight := by
  simpa only [Nat.nsmul_eq_mul] using
    optCost_le_nsmul (w := I.weightFn) (M := I.maxWeight) (i := i) (j := j)
      fun a b _ _ _ => I.weightFn_le_maxWeight a b

private def memTable (I : OptimalBSTInstance) (mem : ℕ → ℕ) : Table ℕ :=
  fun a b =>
    if a ≤ I.numKeys ∧ b ≤ I.numKeys then
      ⟨mem (costAddr I a b), mem (rootAddr I a b)⟩
    else ⟨0, 0⟩

private theorem memTable_in_bounds (I : OptimalBSTInstance) (mem : ℕ → ℕ) {a b : ℕ}
    (ha : a ≤ I.numKeys) (hb : b ≤ I.numKeys) :
    memTable I mem a b = ⟨mem (costAddr I a b), mem (rootAddr I a b)⟩ := by
  simp [memTable, ha, hb]

private theorem offset_lt_sq (I : OptimalBSTInstance) {a b : ℕ} (ha : a ≤ I.numKeys)
    (hb : b ≤ I.numKeys) :
    a * stride I + b < stride I * stride I := by
  dsimp only [stride]; nlinarith

private theorem offset_inj (I : OptimalBSTInstance) {a b a' b' : ℕ}
    (hb : b ≤ I.numKeys) (hb' : b' ≤ I.numKeys)
    (heq : a * stride I + b = a' * stride I + b') : a = a' ∧ b = b' := by
  dsimp only [stride] at heq
  by_cases ha : a = a'
  · subst ha; exact ⟨rfl, by omega⟩
  · exfalso
    rcases Nat.lt_or_gt_of_ne ha with hlt | hgt <;> nlinarith

private def DiagBoundaryMem (I : OptimalBSTInstance) (d : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ addr < costBase I, mem addr = (Data.init I.encode : Data 22).mem addr) ∧
    Agrees I.weightFn I.numKeys d (memTable I mem)

private def MidDiagMem (I : OptimalBSTInstance) (d i : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ addr < costBase I, mem addr = (Data.init I.encode : Data 22).mem addr) ∧
    Agrees I.weightFn I.numKeys d (memTable I mem) ∧
    ∀ i' < i, memTable I mem i' (i' + d + 1) =
      ⟨optCost I.weightFn i' (i' + d + 1), optRoot I.weightFn i' (i' + d + 1)⟩

private theorem diagBoundaryMem_init (I : OptimalBSTInstance) :
    DiagBoundaryMem I 0 (Data.init I.encode : Data 22).mem := by
  refine ⟨fun _ _ => rfl, fun a b _ hab => ?_⟩
  have hba : b ≤ a := by omega
  rw [optCost_of_le I.weightFn hba, optRoot_of_le I.weightFn hba]
  unfold memTable
  split_ifs with h
  · have hc : (Data.init I.encode : Data 22).mem (costAddr I a b) = 0 :=
      init_mem_above I.encode (by dsimp only [costAddr, costBase]; omega)
    have hr : (Data.init I.encode : Data 22).mem (rootAddr I a b) = 0 :=
      init_mem_above I.encode (by dsimp only [rootAddr, rootBase, costBase]; omega)
    rw [hc, hr]
  · rfl

private theorem midDiagMem_zero (I : OptimalBSTInstance) {d : ℕ} {mem : ℕ → ℕ}
    (hd : DiagBoundaryMem I d mem) : MidDiagMem I d 0 mem :=
  ⟨hd.1, hd.2, fun _ h => absurd h (Nat.not_lt_zero _)⟩

private theorem midDiagMem_finish (I : OptimalBSTInstance) {d : ℕ} {mem : ℕ → ℕ}
    (hm : MidDiagMem I d (I.numKeys - d) mem) :
    DiagBoundaryMem I (d + 1) mem := by
  refine ⟨hm.1, fun a b hb hab => ?_⟩
  by_cases hle : b - a ≤ d
  · exact hm.2.1 a b hb hle
  · obtain rfl : b = a + d + 1 := by omega
    exact hm.2.2 a (by omega)

private theorem memTable_write_cell (I : OptimalBSTInstance) (mem : ℕ → ℕ)
    {i j : ℕ} (hi : i ≤ I.numKeys) (hj : j ≤ I.numKeys) (c r : ℕ) :
    let mem' := Function.update (Function.update mem (costAddr I i j) c) (rootAddr I i j) r
    memTable I mem' i j = ⟨c, r⟩ ∧
      ∀ a b, (a ≠ i ∨ b ≠ j) → memTable I mem' a b = memTable I mem a b := by
  intro mem'
  have hoff_ij := offset_lt_sq I hi hj
  have hcr_ne : costAddr I i j ≠ rootAddr I i j := by
    dsimp only [costAddr, rootAddr, rootBase]; omega
  refine ⟨?_, fun a b hne => ?_⟩
  · rw [memTable_in_bounds I mem' hi hj]
    dsimp only [mem']
    rw [Function.update_of_ne hcr_ne, Function.update_self, Function.update_self]
  · unfold memTable
    split_ifs with hab
    · have hoff_ab := offset_lt_sq I hab.1 hab.2
      have hoff_ne : a * stride I + b ≠ i * stride I + j := fun heq => by
        obtain ⟨rfl, rfl⟩ := offset_inj I hab.2 hj heq
        rcases hne with h | h <;> exact h rfl
      have hc1 : costAddr I a b ≠ rootAddr I i j := by
        dsimp only [costAddr, rootAddr, rootBase]; omega
      have hc2 : costAddr I a b ≠ costAddr I i j := by
        dsimp only [costAddr]; omega
      have hr1 : rootAddr I a b ≠ rootAddr I i j := by
        dsimp only [rootAddr]; omega
      have hr2 : rootAddr I a b ≠ costAddr I i j := by
        dsimp only [costAddr, rootAddr, rootBase]; omega
      dsimp only [mem']
      rw [Function.update_of_ne hc1, Function.update_of_ne hc2,
        Function.update_of_ne hr1, Function.update_of_ne hr2]
    · rfl

private theorem midDiagMem_step (I : OptimalBSTInstance) {d i : ℕ}
    (hi : i < I.numKeys - d) {mem : ℕ → ℕ} (hm : MidDiagMem I d i mem) :
    MidDiagMem I d (i + 1)
      (Function.update
        (Function.update mem (costAddr I i (i + d + 1)) (optCost I.weightFn i (i + d + 1)))
        (rootAddr I i (i + d + 1)) (optRoot I.weightFn i (i + d + 1))) := by
  have hi_le : i ≤ I.numKeys := by omega
  have hj_le : i + d + 1 ≤ I.numKeys := by omega
  obtain ⟨hself, hother⟩ := memTable_write_cell I mem hi_le hj_le
    (optCost I.weightFn i (i + d + 1)) (optRoot I.weightFn i (i + d + 1))
  refine ⟨fun addr hlt => ?_, fun a b hb hab => ?_, fun i' hi' => ?_⟩
  · rw [Function.update_of_ne (by dsimp only [rootAddr, rootBase]; omega),
      Function.update_of_ne (by dsimp only [costAddr]; omega)]
    exact hm.1 addr hlt
  · rw [hother a b (by omega)]
    exact hm.2.1 a b hb hab
  · rcases (show i' < i ∨ i' = i by omega) with hlt | rfl
    · rw [hother i' (i' + d + 1) (Or.inl (by omega))]
      exact hm.2.2 i' hlt
    · exact hself

/-! ## Execution of setup, candidate evaluation, inner scan, and cell body -/

private theorem exec_bstSetup {w : ℕ} (I : OptimalBSTInstance) (hwAddr : Fits w I.addrBound) :
    ∃ x₀, ExecWithin w bstSetup (.init I.encode) x₀ 11 ∧
      FixedRegs I x₀ ∧ x₀.regs regD = 0 ∧ x₀.mem = (Data.init I.encode : Data 22).mem := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  have hlen := I.length_encode
  have hm0 : (Data.init I.encode : Data 22).mem 0 = I.encode.length := rfl
  have hm1 : (Data.init I.encode : Data 22).mem 1 = I.numKeys := by simp [OptimalBSTInstance.encode]
  unfold bstSetup
  wram_exec *
  refine ⟨?_, by wram_simp *, rfl⟩
  constructor <;> wram_simp *

private theorem set5_regs_lt18 (s : Data 22) {r1 r2 r3 r4 r5 : Fin 22} {v1 v2 v3 v4 v5 : ℕ}
    (h1 : 18 ≤ r1.val) (h2 : 18 ≤ r2.val) (h3 : 18 ≤ r3.val) (h4 : 18 ≤ r4.val)
    (h5 : 18 ≤ r5.val) {idx : Fin 22} (hidx : idx.val < 18) :
    (((((s.set r1 v1).set r2 v2).set r3 v3).set r4 v4).set r5 v5).regs idx = s.regs idx := by
  rw [Data.set_regs_of_ne (by omega), Data.set_regs_of_ne (by omega),
    Data.set_regs_of_ne (by omega), Data.set_regs_of_ne (by omega),
    Data.set_regs_of_ne (by omega)]

private theorem exec_evalCandCode {w : ℕ} (I : OptimalBSTInstance)
    (hwAddr : Fits w I.addrBound) (hwVal : Fits w I.valueBound)
    {d i j k : ℕ} (hd : d < I.numKeys) (hj_eq : j = i + d + 1) (hj : j ≤ I.numKeys)
    (hik : i < k) (hkj : k ≤ j)
    (st : Data 22) (hfix : FixedRegs I st)
    (hi_r : st.regs regI = i) (hj_r : st.regs regJ = j) (hk_r : st.regs regK = k)
    (hT : Agrees I.weightFn I.numKeys d (memTable I st.mem)) :
    ∃ st', ExecWithin w evalCandCode st st' 10 ∧
      st'.mem = st.mem ∧
      (∀ idx : Fin 22, idx.val < 18 → st'.regs idx = st.regs idx) ∧
      st'.regs regCand = (memTable I st.mem).candidate i j k := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  dsimp only [OptimalBSTInstance.valueBound] at hwVal
  have hlen := I.length_encode
  have hstr : stride I = I.numKeys + 1 := rfl
  have hcb : costBase I = I.encode.length + 1 := rfl
  have hoff1 : i * (I.numKeys + 1) + (k - 1) < (I.numKeys + 1) * (I.numKeys + 1) :=
    offset_lt_sq I (by omega) (by omega)
  have hoff2 : k * (I.numKeys + 1) + j < (I.numKeys + 1) * (I.numKeys + 1) :=
    offset_lt_sq I (by omega) hj
  have hmul1 : i * (I.numKeys + 1) ≤ (I.numKeys + 1) * (I.numKeys + 1) := by omega
  have hmul2 : k * (I.numKeys + 1) ≤ (I.numKeys + 1) * (I.numKeys + 1) := by omega
  have ht1_orig := hT i (k - 1) (by omega) (by omega)
  have ht1 := ht1_orig
  rw [memTable_in_bounds I st.mem (by omega) (by omega)] at ht1
  have hm_left : st.mem (costBase I + (i * stride I + (k - 1))) = optCost I.weightFn i (k - 1) := by
    simpa only [costAddr, Nat.add_assoc] using congrArg Entry.cost ht1
  have ht2_orig := hT k j hj (by omega)
  have ht2 := ht2_orig
  rw [memTable_in_bounds I st.mem (by omega) hj] at ht2
  have hm_right : st.mem (costBase I + (k * stride I + j)) = optCost I.weightFn k j := by
    simpa only [costAddr, Nat.add_assoc] using congrArg Entry.cost ht2
  have hc1 := optCost_le_mul_maxWeight I i (k - 1)
  have hc2 := optCost_le_mul_maxWeight I k j
  have hsum_le : optCost I.weightFn i (k - 1) + optCost I.weightFn k j ≤
      (I.numKeys + 1) * I.maxWeight := by
    have hsub : (k - 1 - i) + (j - k) ≤ I.numKeys + 1 := by omega
    nlinarith
  have hfit_cand : Fits w (optCost I.weightFn i (k - 1) + optCost I.weightFn k j) :=
    hwVal.of_le hsum_le
  have hleft : ∃ s1, ExecWithin w evalCandLeft st s1 5 ∧
      s1.mem = st.mem ∧
      (∀ idx : Fin 22, idx.val < 18 → s1.regs idx = st.regs idx) ∧
      s1.regs regTmp0 = optCost I.weightFn i (k - 1) := by
    unfold evalCandLeft
    wram_exec * [hm_left]
    · exact ⟨rfl, fun _ hidx =>
        set5_regs_lt18 _ (by decide) (by decide) (by decide) (by decide) (by decide) hidx,
        by wram_simp * [hm_left]⟩
    all_goals exact hwAddr.of_le (by dsimp only [stride, costBase, rootBase]; omega)
  obtain ⟨s1, he1, hm1, hr1, ht0_s1⟩ := hleft
  have hfix1 : FixedRegs I s1 := fixedRegs_of_regs_eq hfix fun _ h => hr1 _ (by omega)
  have hk_s1 : s1.regs regK = k := (hr1 _ (by decide)).trans hk_r
  have hj_s1 : s1.regs regJ = j := (hr1 _ (by decide)).trans hj_r
  have hm_right1 : s1.mem (costBase I + (k * stride I + j)) = optCost I.weightFn k j := by
    rw [hm1]; exact hm_right
  have hright : ∃ s2, ExecWithin w evalCandRight s1 s2 5 ∧
      s2.mem = s1.mem ∧
      (∀ idx : Fin 22, idx.val < 18 → s2.regs idx = s1.regs idx) ∧
      s2.regs regCand = optCost I.weightFn i (k - 1) + optCost I.weightFn k j := by
    unfold evalCandRight
    wram_exec * [hm_right1, hfit_cand]
    · exact ⟨rfl, fun _ hidx =>
        set5_regs_lt18 _ (by decide) (by decide) (by decide) (by decide) (by decide) hidx,
        by wram_simp * [hm_right1]⟩
    all_goals exact hwAddr.of_le (by dsimp only [stride, costBase, rootBase]; omega)
  obtain ⟨s2, he2, hm2, hr2, hcand2⟩ := hright
  unfold evalCandCode
  refine ⟨s2, (he1.seq he2).mono (by omega), hm2.trans hm1,
    fun idx hidx => (hr2 idx hidx).trans (hr1 idx hidx), ?_⟩
  rw [hcand2, Table.candidate, ht1_orig, ht2_orig]

private theorem exec_scanInitCode {w : ℕ} (I : OptimalBSTInstance)
    (hwAddr : Fits w I.addrBound) (hwVal : Fits w I.valueBound)
    {d i j lo hi : ℕ} (hd : d < I.numKeys) (hj_eq : j = i + d + 1) (hj : j ≤ I.numKeys)
    (hlo : i < lo) (hlohi : lo ≤ hi) (hhi : hi ≤ j)
    (st : Data 22) (hfix : FixedRegs I st)
    (hd_r : st.regs regD = d) (hlen_r : st.regs regLen = d + 1)
    (hilim_r : st.regs regILim = I.numKeys - d)
    (hi_r : st.regs regI = i) (hj_r : st.regs regJ = j)
    (hlo_r : st.regs regLo = lo) (hhi_r : st.regs regHi = hi)
    (hT : Agrees I.weightFn I.numKeys d (memTable I st.mem)) :
    ∃ st', ExecWithin w scanInitCode st st' 15 ∧
      st'.mem = st.mem ∧ FixedRegs I st' ∧
      st'.regs regD = d ∧ st'.regs regLen = d + 1 ∧ st'.regs regILim = I.numKeys - d ∧
      st'.regs regI = i ∧ st'.regs regJ = j ∧
      st'.regs regLo = lo ∧ st'.regs regHi = hi ∧
      st'.regs regK = lo + 1 ∧ st'.regs regKLim = hi + 1 ∧
      (⟨st'.regs regBestCost, st'.regs regBestRoot⟩ : Entry ℕ) =
        ⟨(memTable I st.mem).candidate i j lo, lo⟩ := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  have hlen := I.length_encode
  let st0 := st.set regK lo
  have he0 : ExecWithin w (ram[ regK ← regLo ] : Code .standard 22) st st0 1 := by
    dsimp only [st0]; rw [← hlo_r]; exact Exec.copy.within
  have hr0 : ∀ idx : Fin 22, idx ≠ regK → st0.regs idx = st.regs idx :=
    fun idx hne => Data.set_regs_of_ne hne _
  have hfix0 : FixedRegs I st0 :=
    fixedRegs_of_regs_eq hfix fun _ h => hr0 _ (Fin.ne_of_val_ne (by dsimp only [regK]; omega))
  obtain ⟨st1, he1, hm1, hr1, hcand1⟩ :=
    exec_evalCandCode I hwAddr hwVal hd hj_eq hj hlo (hlohi.trans hhi) st0 hfix0
      ((hr0 _ (by decide)).trans hi_r) ((hr0 _ (by decide)).trans hj_r)
      (Data.set_regs_self st regK lo) hT
  have hcand1' : st1.regs regCand = (memTable I st.mem).candidate i j lo := hcand1
  have hr01 : ∀ idx : Fin 22, idx.val < 14 → st1.regs idx = st.regs idx := fun _ h =>
    (hr1 _ (by omega)).trans
      (hr0 _ (Fin.ne_of_val_ne (by dsimp only [regK]; omega)))
  have hfix1 : FixedRegs I st1 := fixedRegs_of_regs_eq hfix fun _ h => hr01 _ (by omega)
  have hd1 : st1.regs regD = d := (hr01 _ (by decide)).trans hd_r
  have hlen1 : st1.regs regLen = d + 1 := (hr01 _ (by decide)).trans hlen_r
  have hilim1 : st1.regs regILim = I.numKeys - d := (hr01 _ (by decide)).trans hilim_r
  have hi1 : st1.regs regI = i := (hr01 _ (by decide)).trans hi_r
  have hj1 : st1.regs regJ = j := (hr01 _ (by decide)).trans hj_r
  have hlo1 : st1.regs regLo = lo := (hr01 _ (by decide)).trans hlo_r
  have hhi1 : st1.regs regHi = hi := (hr01 _ (by decide)).trans hhi_r
  have hetail : ∃ st2, ExecWithin w (ram[
        regBestCost ← regCand;
        regBestRoot ← regLo;
        regK ← regLo + regOne;
        regKLim ← regHi + regOne ]) st1 st2 4 ∧
      st2.mem = st1.mem ∧ FixedRegs I st2 ∧
      st2.regs regD = d ∧ st2.regs regLen = d + 1 ∧ st2.regs regILim = I.numKeys - d ∧
      st2.regs regI = i ∧ st2.regs regJ = j ∧
      st2.regs regLo = lo ∧ st2.regs regHi = hi ∧
      st2.regs regK = lo + 1 ∧ st2.regs regKLim = hi + 1 ∧
      (⟨st2.regs regBestCost, st2.regs regBestRoot⟩ : Entry ℕ) =
        ⟨(memTable I st.mem).candidate i j lo, lo⟩ := by
    wram_exec *
    refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
      by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *,
      by wram_simp *, ?_⟩
    ext <;> wram_simp *
  obtain ⟨st2, he2, hm2, hrest⟩ := hetail
  unfold scanInitCode
  exact ⟨st2, (he0.seq (he1.seq he2)).mono (by omega), hm2.trans hm1, hrest⟩

private theorem exec_scanUpdateCode {w : ℕ} (c : ℕ → ℕ) (e : Entry ℕ) (k : ℕ) (st : Data 22)
    (hbc : st.regs regBestCost = e.cost) (hbr : st.regs regBestRoot = e.root)
    (hcand : st.regs regCand = c k) (hk : st.regs regK = k) :
    ∃ st', ExecWithin w scanUpdateCode st st' 4 ∧
      st'.mem = st.mem ∧
      (∀ idx : Fin 22, idx ≠ regBestCost → idx ≠ regBestRoot → st'.regs idx = st.regs idx) ∧
      (⟨st'.regs regBestCost, st'.regs regBestRoot⟩ : Entry ℕ) = bestStep c e k := by
  unfold scanUpdateCode
  wram_exec *
  · refine ⟨rfl, fun idx h1 _ => Data.set_regs_of_ne h1 _, ?_⟩
    wram_simp *
    rw [bestStep, ite_eq_right (by omega)]
  · refine ⟨rfl, fun idx h1 h2 => ?_, ?_⟩
    · rw [Data.set_regs_of_ne h2, Data.set_regs_of_ne h1]
    · ext <;> wram_simp * <;> rw [bestStep, ite_eq_left (by omega)]

private theorem exec_scanLoop {w : ℕ} (I : OptimalBSTInstance)
    (hwAddr : Fits w I.addrBound) (hwVal : Fits w I.valueBound)
    {d i j lo hi : ℕ} (hd : d < I.numKeys) (hj_eq : j = i + d + 1) (hj : j ≤ I.numKeys)
    (hlo : i < lo) (hlohi : lo ≤ hi) (hhi : hi ≤ j)
    (st₀ : Data 22) (hfix₀ : FixedRegs I st₀)
    (hd₀ : st₀.regs regD = d) (hlen₀ : st₀.regs regLen = d + 1)
    (hilim₀ : st₀.regs regILim = I.numKeys - d)
    (hi₀ : st₀.regs regI = i) (hj₀ : st₀.regs regJ = j)
    (hlo₀ : st₀.regs regLo = lo) (hhi₀ : st₀.regs regHi = hi)
    (hk₀ : st₀.regs regK = lo + 1) (hklim₀ : st₀.regs regKLim = hi + 1)
    (hbest₀ : (⟨st₀.regs regBestCost, st₀.regs regBestRoot⟩ : Entry ℕ) =
      ⟨(memTable I st₀.mem).candidate i j lo, lo⟩)
    (hT : Agrees I.weightFn I.numKeys d (memTable I st₀.mem)) :
    ∃ stf, ExecWithin w (.loop (.lt regK regKLim) scanStepCode) st₀ stf
        (17 * (hi - lo) + 2) ∧
      stf.mem = st₀.mem ∧ FixedRegs I stf ∧
      stf.regs regD = d ∧ stf.regs regLen = d + 1 ∧ stf.regs regILim = I.numKeys - d ∧
      stf.regs regI = i ∧ stf.regs regJ = j ∧
      (⟨stf.regs regBestCost, stf.regs regBestRoot⟩ : Entry ℕ) =
        scan ((memTable I st₀.mem).candidate i j) lo hi := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  have hlen := I.length_encode
  let c := (memTable I st₀.mem).candidate i j
  let P (k : ℕ) (st : Data 22) : Prop :=
    lo + 1 ≤ k ∧ st.mem = st₀.mem ∧ FixedRegs I st ∧
      st.regs regD = d ∧ st.regs regLen = d + 1 ∧ st.regs regILim = I.numKeys - d ∧
      st.regs regI = i ∧ st.regs regJ = j ∧ st.regs regKLim = hi + 1 ∧
      (⟨st.regs regBestCost, st.regs regBestRoot⟩ : Entry ℕ) =
        (List.range' (lo + 1) (k - (lo + 1))).foldl (bestStep c) ⟨c lo, lo⟩
  have hbody : ∀ st, P (st.regs regK) st → st.regs regK < hi + 1 →
      ∃ st', ExecWithin w scanStepCode st st' 15 ∧
        P (st.regs regK + 1) st' ∧ st'.regs regK = st.regs regK + 1 := by
    intro st ⟨hk_ge, hmem, hfix, hd_r, hlen_r, hilim_r, hi_r, hj_r, hklim_r, hbest⟩ hk_lt
    set k := st.regs regK with hk_def
    have hk_reg : st.regs regK = k := hk_def.symm
    let curBest := (List.range' (lo + 1) (k - (lo + 1))).foldl (bestStep c) ⟨c lo, lo⟩
    have hbc : st.regs regBestCost = curBest.cost := congrArg Entry.cost hbest
    have hbr : st.regs regBestRoot = curBest.root := congrArg Entry.root hbest
    obtain ⟨st1, he1, hm1, hr1, hcand1⟩ :=
      exec_evalCandCode I hwAddr hwVal hd hj_eq hj (by omega) (by omega) st hfix
        hi_r hj_r hk_reg (hmem ▸ hT)
    rw [hmem] at hcand1
    obtain ⟨st2, he2, hm2, hr2, hbest2⟩ :=
      exec_scanUpdateCode c curBest k st1
        ((hr1 _ (by decide)).trans hbc) ((hr1 _ (by decide)).trans hbr)
        hcand1 ((hr1 _ (by decide)).trans hk_reg)
    have hr12 : ∀ idx : Fin 22, idx.val < 16 → st2.regs idx = st.regs idx := fun _ h =>
      (hr2 _ (Fin.ne_of_val_ne (by dsimp only [regBestCost]; omega))
        (Fin.ne_of_val_ne (by dsimp only [regBestRoot]; omega))).trans
        (hr1 _ (by omega))
    have hfix2 : FixedRegs I st2 := fixedRegs_of_regs_eq hfix fun _ h => hr12 _ (by omega)
    have hk2 : st2.regs regK = k := (hr12 _ (by decide)).trans hk_reg
    have hd2 : st2.regs regD = d := (hr12 _ (by decide)).trans hd_r
    have hlen2 : st2.regs regLen = d + 1 := (hr12 _ (by decide)).trans hlen_r
    have hilim2 : st2.regs regILim = I.numKeys - d := (hr12 _ (by decide)).trans hilim_r
    have hi2 : st2.regs regI = i := (hr12 _ (by decide)).trans hi_r
    have hj2 : st2.regs regJ = j := (hr12 _ (by decide)).trans hj_r
    have hklim2 : st2.regs regKLim = hi + 1 := (hr12 _ (by decide)).trans hklim_r
    have hbc2 : st2.regs regBestCost = (bestStep c curBest k).cost := congrArg Entry.cost hbest2
    have hbr2 : st2.regs regBestRoot = (bestStep c curBest k).root := congrArg Entry.root hbest2
    have hfold_step : bestStep c curBest k =
        (List.range' (lo + 1) (k + 1 - (lo + 1))).foldl (bestStep c) ⟨c lo, lo⟩ := by
      have hm_eq : k + 1 - (lo + 1) = (k - (lo + 1)) + 1 := by omega
      have hidx : lo + 1 + 1 * (k - (lo + 1)) = k := by omega
      rw [hm_eq, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, hidx]
    have hinc : ∃ st3, ExecWithin w (ram[ regK ← regK + regOne ]) st2 st3 1 ∧
        st3.mem = st2.mem ∧ FixedRegs I st3 ∧
        st3.regs regD = d ∧ st3.regs regLen = d + 1 ∧ st3.regs regILim = I.numKeys - d ∧
        st3.regs regI = i ∧ st3.regs regJ = j ∧ st3.regs regKLim = hi + 1 ∧
        st3.regs regK = k + 1 ∧
        (⟨st3.regs regBestCost, st3.regs regBestRoot⟩ : Entry ℕ) =
          (List.range' (lo + 1) (k + 1 - (lo + 1))).foldl (bestStep c) ⟨c lo, lo⟩ := by
      wram_exec *
      refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
        by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *, ?_⟩
      rw [← hfold_step]
      ext <;> wram_simp *
    obtain ⟨st3, he3, hm3, hfix3, hd3, hlen3, hilim3, hi3, hj3, hklim3, hk3, hbest3⟩ := hinc
    unfold scanStepCode
    exact ⟨st3, (he1.seq (he2.seq he3)).mono (by omega),
      ⟨by omega, hm3.trans (hm2.trans (hm1.trans hmem)), hfix3, hd3, hlen3, hilim3, hi3, hj3,
       hklim3, hbest3⟩,
      hk3⟩
  have hP0 : P (st₀.regs regK) st₀ := by
    dsimp only [P]
    rw [hk₀, Nat.sub_self, List.range'_zero, List.foldl_nil]
    exact ⟨le_rfl, rfl, hfix₀, hd₀, hlen₀, hilim₀, hi₀, hj₀, hklim₀, hbest₀⟩
  obtain ⟨stf, hexec, ⟨_, hmemf, hfixf, hdf, hlenf, hilimf, hif, hjf, _, hbestf⟩, _⟩ :=
    ExecWithin.loop_count P (fun _ hp => hp.2.2.2.2.2.2.2.2.1) hbody
      (by rw [hk₀]; omega) hP0
  rw [hk₀, show (hi + 1 - (lo + 1)) * (15 + 2) + 2 = 17 * (hi - lo) + 2 by omega] at hexec
  rw [show hi + 1 - (lo + 1) = hi - lo by omega] at hbestf
  exact ⟨stf, hexec, hmemf, hfixf, hdf, hlenf, hilimf, hif, hjf, hbestf⟩

private theorem exec_cellWriteCode {w : ℕ} (I : OptimalBSTInstance)
    (hwAddr : Fits w I.addrBound) (hwVal : Fits w I.valueBound)
    {d i j : ℕ} (hi_lt : i < I.numKeys - d) (hj_eq : j = i + d + 1)
    (st : Data 22) (hfix : FixedRegs I st)
    (hd_r : st.regs regD = d) (hlen_r : st.regs regLen = d + 1)
    (hilim_r : st.regs regILim = I.numKeys - d)
    (hi_r : st.regs regI = i) (hj_r : st.regs regJ = j)
    (hbest_opt :
      I.weightFn i j + st.regs regBestCost = optCost I.weightFn i j ∧
        st.regs regBestRoot = optRoot I.weightFn i j)
    (hm : MidDiagMem I d i st.mem) :
    ∃ st', ExecWithin w cellWriteCode st st' 10 ∧
      FixedRegs I st' ∧
      st'.regs regD = d ∧ st'.regs regLen = d + 1 ∧ st'.regs regILim = I.numKeys - d ∧
      st'.regs regI = i + 1 ∧
      MidDiagMem I d (i + 1) st'.mem := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  dsimp only [OptimalBSTInstance.valueBound] at hwVal
  have hlen := I.length_encode
  have hstr : stride I = I.numKeys + 1 := rfl
  have hcb : costBase I = I.encode.length + 1 := rfl
  have hrb : rootBase I = costBase I + stride I * stride I := rfl
  have hi_le : i ≤ I.numKeys := by omega
  have hj_le : j ≤ I.numKeys := by omega
  have hoff : i * (I.numKeys + 1) + j < (I.numKeys + 1) * (I.numKeys + 1) :=
    offset_lt_sq I hi_le hj_le
  have hmul : i * (I.numKeys + 1) ≤ (I.numKeys + 1) * (I.numKeys + 1) := by omega
  have hread_w : st.mem (2 + (i * stride I + j)) = I.weightFn i j := by
    have hlt_cb : 2 + (i * (I.numKeys + 1) + j) < I.encode.length + 1 := by omega
    rw [hm.1 _ hlt_cb]
    exact bst_read_weight I hi_le hj_le
  have hopt_le : optCost I.weightFn i j ≤ (I.numKeys + 1) * I.maxWeight := by
    have hc := optCost_le_mul_maxWeight I i j
    have hsub : j - i ≤ I.numKeys + 1 := by omega
    nlinarith
  have hfit_sum : Fits w (I.weightFn i j + st.regs regBestCost) := by
    rw [hbest_opt.1]; exact hwVal.of_le hopt_le
  obtain ⟨hbc_opt, hbr_opt⟩ := hbest_opt
  have hpart1 : ∃ s1, ExecWithin w cellAddWeight st s1 5 ∧
      s1.mem = st.mem ∧ FixedRegs I s1 ∧
      s1.regs regD = d ∧ s1.regs regLen = d + 1 ∧ s1.regs regILim = I.numKeys - d ∧
      s1.regs regI = i ∧ s1.regs regTmp0 = i * stride I + j ∧
      s1.regs regBestCost = optCost I.weightFn i j ∧
      s1.regs regBestRoot = optRoot I.weightFn i j := by
    unfold cellAddWeight
    wram_exec * [hread_w, hfit_sum]
    · refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
        by wram_simp *, by wram_simp *, ?_, by wram_simp *⟩
      wram_simp * [hread_w]; exact hbc_opt
    all_goals exact hwAddr.of_le (by dsimp only [stride, costBase, rootBase]; omega)
  obtain ⟨s1, he1, hm1, hfix1, hd1, hlen1, hilim1, hi1, htmp0_1, hbc1, hbr1⟩ := hpart1
  have hpart2 : ∃ s2, ExecWithin w cellStoreBoth s1 s2 5 ∧
      FixedRegs I s2 ∧
      s2.regs regD = d ∧ s2.regs regLen = d + 1 ∧ s2.regs regILim = I.numKeys - d ∧
      s2.regs regI = i + 1 ∧
      s2.mem = Function.update
        (Function.update s1.mem (costAddr I i j) (optCost I.weightFn i j))
        (rootAddr I i j) (optRoot I.weightFn i j) := by
    unfold cellStoreBoth
    wram_exec *
    · refine ⟨by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *, by wram_simp *, ?_⟩
      rw [Data.set_mem, Data.write_mem, Data.set_mem, Data.write_mem, Data.set_mem]
      dsimp only [costAddr, rootAddr]
      simp only [Nat.add_assoc]
    all_goals exact hwAddr.of_le (by dsimp only [stride, costBase, rootBase]; omega)
  obtain ⟨s2, he2, hfix2, hd2, hlen2, hilim2, hi2, hm2⟩ := hpart2
  unfold cellWriteCode
  refine ⟨s2, (he1.seq he2).mono (by omega), hfix2, hd2, hlen2, hilim2, hi2, ?_⟩
  rw [hm2, hm1, hj_eq]
  exact midDiagMem_step I hi_lt hm

/-! ## Parameterized execution of `bstCode` -/

private theorem exec_bstCode {w : ℕ} (I : OptimalBSTInstance) (hw : I.FitsWidth w)
    (W : Window ℕ) (winCode : Code .standard 22) (Tw diagWinSumBound : ℕ)
    (hW : W.Valid I.weightFn I.numKeys)
    (hW_congr : ∀ d (T₁ T₂ : Table ℕ) i,
      Agrees I.weightFn I.numKeys d T₁ → Agrees I.weightFn I.numKeys d T₂ →
        i + d + 1 ≤ I.numKeys →
        W.lo T₁ i (i + d + 1) = W.lo T₂ i (i + d + 1) ∧
          W.hi T₁ i (i + d + 1) = W.hi T₂ i (i + d + 1))
    (hsum : ∀ d (T : Table ℕ), d < I.numKeys → Agrees I.weightFn I.numKeys d T →
      ∑ i ∈ range (I.numKeys - d),
        (W.hi T i (i + d + 1) - W.lo T i (i + d + 1) + 1) ≤ diagWinSumBound)
    (hwin : ∀ d i, d < I.numKeys → i < I.numKeys - d → ∀ (st : Data 22),
      FixedRegs I st →
      st.regs regD = d → st.regs regLen = d + 1 → st.regs regILim = I.numKeys - d →
      st.regs regI = i → st.regs regJ = i + d + 1 →
      Agrees I.weightFn I.numKeys d (memTable I st.mem) →
      ∃ st', ExecWithin w winCode st st' Tw ∧
        st'.mem = st.mem ∧ FixedRegs I st' ∧
        st'.regs regD = d ∧ st'.regs regLen = d + 1 ∧ st'.regs regILim = I.numKeys - d ∧
        st'.regs regI = i ∧ st'.regs regJ = i + d + 1 ∧
        st'.regs regLo = W.lo (memTable I st.mem) i (i + d + 1) ∧
        st'.regs regHi = W.hi (memTable I st.mem) i (i + d + 1)) :
    ∃ xf, ExecWithin w (bstCode winCode) (.init I.encode) xf
        (I.numKeys * (17 * diagWinSumBound + (Tw + 13) * I.numKeys + 8) + 15) ∧
      xf.regs regOut = optCost I.weightFn 0 I.numKeys := by
  obtain ⟨hwAddr, hwVal⟩ := hw
  obtain ⟨x₀, hsetup, hfix₀, hd₀, hmem₀⟩ := exec_bstSetup I hwAddr
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  have hlen := I.length_encode
  have hstr_def : stride I = I.numKeys + 1 := rfl
  let Pdiag (d : ℕ) (st : Data 22) : Prop :=
    FixedRegs I st ∧ DiagBoundaryMem I d st.mem
  have hdiagBody : ∀ st, Pdiag (st.regs regD) st → st.regs regD < I.numKeys →
      ∃ st', ExecWithin w (diagBody winCode) st st'
          (17 * diagWinSumBound + (Tw + 13) * I.numKeys + 6) ∧
        Pdiag (st.regs regD + 1) st' ∧ st'.regs regD = st.regs regD + 1 := by
    intro st ⟨hfix, hdb⟩ hd_lt
    set d := st.regs regD with hd_def
    have hd_reg : st.regs regD = d := hd_def.symm
    let T₀ := memTable I st.mem
    have hT₀ : Agrees I.weightFn I.numKeys d T₀ := hdb.2
    have hpre : ∃ st1, ExecWithin w diagPreCode st st1 3 ∧
        st1.mem = st.mem ∧ FixedRegs I st1 ∧
        st1.regs regD = d ∧ st1.regs regLen = d + 1 ∧
        st1.regs regILim = I.numKeys - d ∧ st1.regs regI = 0 := by
      unfold diagPreCode
      wram_exec *
      refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, ?_, by wram_simp *⟩
      wram_simp *; omega
    obtain ⟨st1, hpre_ex, hm1, hfix1, hd1, hlen1, hilim1, hi1⟩ := hpre
    let cellCost (i : ℕ) : ℕ :=
      17 * (W.hi T₀ i (i + d + 1) - W.lo T₀ i (i + d + 1) + 1) + Tw + 11
    let Pcell (i : ℕ) (q : Data 22) : Prop :=
      FixedRegs I q ∧ q.regs regD = d ∧ q.regs regLen = d + 1 ∧
        q.regs regILim = I.numKeys - d ∧ MidDiagMem I d i q.mem
    have hcellBody : ∀ q, Pcell (q.regs regI) q → q.regs regI < I.numKeys - d →
        ∃ q', ExecWithin w (cellBody winCode) q q' (cellCost (q.regs regI)) ∧
          Pcell (q.regs regI + 1) q' ∧ q'.regs regI = q.regs regI + 1 := by
      intro q ⟨hq_fix, hq_d, hq_len, hq_ilim, hq_mem⟩ hi_lt
      set i := q.regs regI with hi_def
      have hi_reg : q.regs regI = i := hi_def.symm
      let j := i + d + 1
      have hj_le : j ≤ I.numKeys := by omega
      have hsetJ : ∃ q1, ExecWithin w (ram[ regJ ← regI + regLen ]) q q1 1 ∧
          q1.mem = q.mem ∧ FixedRegs I q1 ∧
          q1.regs regD = d ∧ q1.regs regLen = d + 1 ∧ q1.regs regILim = I.numKeys - d ∧
          q1.regs regI = i ∧ q1.regs regJ = j := by
        wram_exec *
        exact ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
          by wram_simp *, by wram_simp *; omega⟩
      obtain ⟨q1, heJ, hmJ, hfixJ, hdJ, hlenJ, hilimJ, hiJ, hjJ⟩ := hsetJ
      have hTq1 : Agrees I.weightFn I.numKeys d (memTable I q1.mem) := hmJ ▸ hq_mem.2.1
      obtain ⟨q2, heW, hmW, hfixW, hdW, hlenW, hilimW, hiW, hjW, hloW, hhiW⟩ :=
        hwin d i hd_lt hi_lt q1 hfixJ hdJ hlenJ hilimJ hiJ hjJ hTq1
      obtain ⟨hlo_eq, hhi_eq⟩ := hW_congr d (memTable I q1.mem) T₀ i hTq1 hT₀ hj_le
      rw [hlo_eq] at hloW
      rw [hhi_eq] at hhiW
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hW d T₀ i hT₀ hj_le
      have hTq2 : Agrees I.weightFn I.numKeys d (memTable I q2.mem) := hmW ▸ hTq1
      obtain ⟨q3, heInit, hmInit, hfix3, hd3, hlen3, hilim3, hi3, hj3, hlo3, hhi3, hk3, hklim3,
          hbest3⟩ :=
        exec_scanInitCode I hwAddr hwVal hd_lt rfl hj_le h₁ (h₂.trans h₃) h₄
          q2 hfixW hdW hlenW hilimW hiW hjW hloW hhiW hTq2
      rw [← hmInit] at hbest3
      have hTq3 : Agrees I.weightFn I.numKeys d (memTable I q3.mem) := hmInit ▸ hTq2
      obtain ⟨q4, heLoop, hmLoop, hfix4, hd4, hlen4, hilim4, hi4, hj4, hbest4⟩ :=
        exec_scanLoop I hwAddr hwVal hd_lt rfl hj_le h₁ (h₂.trans h₃) h₄
          q3 hfix3 hd3 hlen3 hilim3 hi3 hj3 hlo3 hhi3 hk3 hklim3 hbest3 hTq3
      obtain ⟨hlo_q3, hhi_q3⟩ := hW_congr d T₀ (memTable I q3.mem) i hT₀ hTq3 hj_le
      have hcell_eq := cell_eq_opt hTq3 hj_le
        (hlo_q3 ▸ h₁) (hlo_q3 ▸ h₂) (hhi_q3 ▸ h₃) (hhi_q3 ▸ h₄)
      unfold cell at hcell_eq
      rw [← hlo_q3, ← hhi_q3, ← hbest4] at hcell_eq
      have hbest_opt :
          I.weightFn i j + q4.regs regBestCost = optCost I.weightFn i j ∧
            q4.regs regBestRoot = optRoot I.weightFn i j :=
        ⟨congrArg Entry.cost hcell_eq, congrArg Entry.root hcell_eq⟩
      have hm4_mid : MidDiagMem I d i q4.mem := by
        rw [hmLoop, hmInit, hmW, hmJ]; exact hq_mem
      obtain ⟨q5, heWr, hfix5, hd5, hlen5, hilim5, hi5, hm5⟩ :=
        exec_cellWriteCode I hwAddr hwVal hi_lt rfl q4 hfix4 hd4 hlen4 hilim4 hi4 hj4
          hbest_opt hm4_mid
      unfold cellBody
      have hcost_le :
          1 + (Tw + (15 + (17 * (W.hi T₀ i j - W.lo T₀ i j) + 2 + 10))) ≤ cellCost i := by
        dsimp only [cellCost, j]
        have hlohi : W.lo T₀ i (i + d + 1) ≤ W.hi T₀ i (i + d + 1) := h₂.trans h₃
        omega
      exact ⟨q5, (heJ.seq (heW.seq (heInit.seq (heLoop.seq heWr)))).mono hcost_le,
        ⟨hfix5, hd5, hlen5, hilim5, hm5⟩, hi5⟩
    have hPcell0 : Pcell 0 st1 := ⟨hfix1, hd1, hlen1, hilim1, hm1 ▸ midDiagMem_zero I hdb⟩
    obtain ⟨st2, hmidLoop, ⟨hfix2, hd2, _, _, hm2⟩, _⟩ :=
      loop_count_sum Pcell cellCost (fun _ hp => hp.2.2.2.1) hcellBody hi1 hPcell0
    have hincD : ∃ st3, ExecWithin w (ram[ regD ← regD + regOne ]) st2 st3 1 ∧
        st3.mem = st2.mem ∧ FixedRegs I st3 ∧ st3.regs regD = d + 1 := by
      wram_exec *
      exact ⟨rfl, by regs_frame, by wram_simp *⟩
    obtain ⟨st3, heIncD, hm3, hfix3, hd3⟩ := hincD
    have hsum_bound :
        (∑ i ∈ range (I.numKeys - d), (cellCost i + 2)) + 2 ≤
          17 * diagWinSumBound + (Tw + 13) * I.numKeys + 2 := by
      have hsplit : ∑ i ∈ range (I.numKeys - d), (cellCost i + 2) =
          17 * (∑ i ∈ range (I.numKeys - d),
            (W.hi T₀ i (i + d + 1) - W.lo T₀ i (i + d + 1) + 1)) +
          (I.numKeys - d) * (Tw + 13) := by
        dsimp only [cellCost]
        have hcongr : ∑ i ∈ range (I.numKeys - d),
            (17 * (W.hi T₀ i (i + d + 1) - W.lo T₀ i (i + d + 1) + 1) + Tw + 11 + 2) =
            ∑ i ∈ range (I.numKeys - d),
              (17 * (W.hi T₀ i (i + d + 1) - W.lo T₀ i (i + d + 1) + 1) + (Tw + 13)) :=
          sum_congr rfl fun _ _ => by omega
        rw [hcongr, sum_add_distrib, ← mul_sum, sum_const, card_range, Nat.nsmul_eq_mul]
      have hw_le := hsum d T₀ hd_lt hT₀
      have hnd_le : I.numKeys - d ≤ I.numKeys := Nat.sub_le _ _
      rw [hsplit]
      nlinarith
    unfold diagBody
    exact ⟨st3, (hpre_ex.seq (hmidLoop.seq heIncD)).mono (by omega),
      ⟨hfix3, hm3 ▸ midDiagMem_finish I hm2⟩, hd3⟩
  have hPdiag0 : Pdiag (x₀.regs regD) x₀ := by
    dsimp only [Pdiag]
    rw [hd₀, hmem₀]
    exact ⟨hfix₀, diagBoundaryMem_init I⟩
  obtain ⟨x₁, houterLoop, ⟨hfix₁, hdb₁⟩, _⟩ :=
    ExecWithin.loop_count Pdiag (fun _ hp => hp.1.n) hdiagBody
      (by rw [hd₀]; exact Nat.zero_le _) hPdiag0
  rw [hd₀, Nat.sub_zero] at houterLoop
  have hcb_def : costBase I = I.encode.length + 1 := rfl
  have hfin_cell := hdb₁.2 0 I.numKeys le_rfl (by omega)
  rw [memTable_in_bounds I x₁.mem (Nat.zero_le _) le_rfl] at hfin_cell
  have hmem_out : x₁.mem (costBase I + I.numKeys) = optCost I.weightFn 0 I.numKeys := by
    simpa only [costAddr, Nat.zero_mul, Nat.add_zero] using congrArg Entry.cost hfin_cell
  have hfinal : ∃ xf, ExecWithin w bstFinalRead x₁ xf 2 ∧
      xf.regs regOut = optCost I.weightFn 0 I.numKeys := by
    unfold bstFinalRead
    wram_exec * [hmem_out]
    wram_simp * [hmem_out]
  obtain ⟨xf, hfin_ex, hres⟩ := hfinal
  unfold bstCode
  exact ⟨xf, (hsetup.seq (houterLoop.seq hfin_ex)).mono (by nlinarith), hres⟩

/-! ## Cubic algorithm (`plainBSTProgram`) and Knuth's quadratic algorithm (`knuthBSTProgram`) -/

private theorem exec_plainWindowCode {w : ℕ} (I : OptimalBSTInstance)
    (hwAddr : Fits w I.addrBound)
    (d i : ℕ) (hd : d < I.numKeys) (hi : i < I.numKeys - d) (st : Data 22)
    (hfix : FixedRegs I st) (hd_r : st.regs regD = d) (hlen_r : st.regs regLen = d + 1)
    (hilim_r : st.regs regILim = I.numKeys - d)
    (hi_r : st.regs regI = i) (hj_r : st.regs regJ = i + d + 1)
    (_hT : Agrees I.weightFn I.numKeys d (memTable I st.mem)) :
    ∃ st', ExecWithin w plainWindowCode st st' 2 ∧
      st'.mem = st.mem ∧ FixedRegs I st' ∧
      st'.regs regD = d ∧ st'.regs regLen = d + 1 ∧ st'.regs regILim = I.numKeys - d ∧
      st'.regs regI = i ∧ st'.regs regJ = i + d + 1 ∧
      st'.regs regLo = (Window.plain : Window ℕ).lo (memTable I st.mem) i (i + d + 1) ∧
      st'.regs regHi = (Window.plain : Window ℕ).hi (memTable I st.mem) i (i + d + 1) := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  have hlen := I.length_encode
  unfold plainWindowCode
  wram_exec *
  exact ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
    by wram_simp *, by wram_simp *, by wram_simp *; rfl, by wram_simp *; rfl⟩

private theorem exec_plainBSTCode {w : ℕ} (I : OptimalBSTInstance) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w (bstCode plainWindowCode) (.init I.encode) xf
        (17 * I.numKeys ^ 3 + 15 * I.numKeys ^ 2 + 8 * I.numKeys + 15) ∧
      xf.regs regOut = (plainBST I.weightFn I.numKeys).cost := by
  obtain ⟨xf, hexec, hres⟩ :=
    exec_bstCode I hw Window.plain plainWindowCode 2 (I.numKeys * I.numKeys)
      (Window.valid_plain I.weightFn I.numKeys)
      (fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩)
      (fun d T hd _ => by
        calc ∑ i ∈ range (I.numKeys - d),
              ((Window.plain : Window ℕ).hi T i (i + d + 1) -
                (Window.plain : Window ℕ).lo T i (i + d + 1) + 1)
            = ∑ _i ∈ range (I.numKeys - d), (d + 1) :=
              sum_congr rfl fun i _ => by simp only [Window.plain]; omega
          _ = (I.numKeys - d) * (d + 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]
          _ ≤ I.numKeys * I.numKeys := Nat.mul_le_mul (Nat.sub_le _ _) (by omega))
      (exec_plainWindowCode I hw.1)
  rw [plainBST_eq]
  exact ⟨xf, hexec.mono (le_of_eq (by ring)), hres⟩

/-- **Word-RAM cubic running time of `plainBST`.** For every `I : OptimalBSTInstance` (with no
quadrangle or monotonicity hypothesis), `plainBSTProgram` computes
`(plainBST I.weightFn I.numKeys).cost` in at most `17 (n + 1)³` instructions at every fitting
width `w`. -/
theorem computesInTime_plainBST :
    plainBSTProgram.ComputesInTime (fun _ => OptimalBSTInstance.encode)
      (fun I _ => 17 * (I.numKeys + 1) ^ 3)
      OptimalBSTInstance.FitsWidth
      (fun I => (plainBST I.weightFn I.numKeys).cost) :=
  ((bstCode plainWindowCode).computesInTime_program regOut
    (time := fun I _ =>
      17 * I.numKeys ^ 3 + 15 * I.numKeys ^ 2 + 8 * I.numKeys + 15)
    (fun I _ hw _ => exec_plainBSTCode I hw)).mono
    (fun _ _ => by nlinarith) (fun _ _ h => h)

/-- Uniform `O(n³)` Word-RAM computability of `plainBST` cost, bundling width admissibility. -/
theorem uniformComputableInTime_plainBST :
    UniformComputableInTime .standard (fun I => (plainBST I.weightFn I.numKeys).cost)
      (fun _ => OptimalBSTInstance.encode)
      (fun I _ => 17 * (I.numKeys + 1) ^ 3) OptimalBSTInstance.FitsWidth :=
  ⟨22, plainBSTProgram, computesInTime_plainBST, OptimalBSTInstance.inputAdmissible⟩

private theorem exec_knuthWindowCode {w : ℕ} (I : OptimalBSTInstance)
    (hwAddr : Fits w I.addrBound)
    (d i : ℕ) (hd : d < I.numKeys) (hi : i < I.numKeys - d) (st : Data 22)
    (hfix : FixedRegs I st) (hd_r : st.regs regD = d) (hlen_r : st.regs regLen = d + 1)
    (hilim_r : st.regs regILim = I.numKeys - d)
    (hi_r : st.regs regI = i) (hj_r : st.regs regJ = i + d + 1)
    (_hT : Agrees I.weightFn I.numKeys d (memTable I st.mem)) :
    ∃ st', ExecWithin w knuthWindowCode st st' 11 ∧
      st'.mem = st.mem ∧ FixedRegs I st' ∧
      st'.regs regD = d ∧ st'.regs regLen = d + 1 ∧ st'.regs regILim = I.numKeys - d ∧
      st'.regs regI = i ∧ st'.regs regJ = i + d + 1 ∧
      st'.regs regLo = (Window.knuth : Window ℕ).lo (memTable I st.mem) i (i + d + 1) ∧
      st'.regs regHi = (Window.knuth : Window ℕ).hi (memTable I st.mem) i (i + d + 1) := by
  dsimp only [OptimalBSTInstance.addrBound] at hwAddr
  have hlen := I.length_encode
  have hstr : stride I = I.numKeys + 1 := rfl
  have hrb : rootBase I = I.encode.length + 1 + stride I * stride I := rfl
  unfold knuthWindowCode
  by_cases hd0 : 0 < d
  · have hoff1 : i * (I.numKeys + 1) + (i + d + 1 - 1) < (I.numKeys + 1) * (I.numKeys + 1) :=
      offset_lt_sq I (by omega) (by omega)
    have hoff2 : (i + 1) * (I.numKeys + 1) + (i + d + 1) < (I.numKeys + 1) * (I.numKeys + 1) :=
      offset_lt_sq I (by omega) (by omega)
    have hmul1 : i * (I.numKeys + 1) ≤ (I.numKeys + 1) * (I.numKeys + 1) := by omega
    have hmul2 : (i + 1) * (I.numKeys + 1) ≤ (I.numKeys + 1) * (I.numKeys + 1) := by omega
    have hmt1 := memTable_in_bounds I st.mem (a := i) (b := i + d + 1 - 1) (by omega) (by omega)
    have hmt2 := memTable_in_bounds I st.mem (a := i + 1) (b := i + d + 1) (by omega) (by omega)
    unfold knuthWindowPos
    wram_exec * [hd0]
    · refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
        by wram_simp *, by wram_simp *, ?_, ?_⟩
      · wram_simp *
        simp only [Window.knuth, show i + 1 < i + d + 1 by omega, ↓reduceIte, hmt1]
        dsimp only [rootAddr]
        congr 1; omega
      · wram_simp *
        simp only [Window.knuth, show i + 1 < i + d + 1 by omega, ↓reduceIte, hmt2]
        dsimp only [rootAddr]
        congr 1; omega
    all_goals exact hwAddr.of_le (by dsimp only [stride, costBase, rootBase]; omega)
  · have hd_zero : d = 0 := by omega
    wram_exec * [hd0]
    refine ⟨rfl, by regs_frame, by wram_simp *, by wram_simp *, by wram_simp *,
      by wram_simp *, by wram_simp *, ?_, ?_⟩
    · wram_simp *; simp [Window.knuth, hd_zero]
    · wram_simp *; simp [Window.knuth, hd_zero]

private theorem exec_knuthBSTCode {w : ℕ} (I : OptimalBSTInstance)
    (hqi : QuadrangleIneq I.weightFn) (hmono : MonotoneOnIntervals I.weightFn)
    (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w (bstCode knuthWindowCode) (.init I.encode) xf
        (58 * I.numKeys ^ 2 + 8 * I.numKeys + 15) ∧
      xf.regs regOut = (knuthBST I.weightFn I.numKeys).cost := by
  obtain ⟨xf, hexec, hres⟩ :=
    exec_bstCode I hw Window.knuth knuthWindowCode 11 (2 * I.numKeys)
      (Window.valid_knuth hqi hmono I.numKeys)
      (fun d T₁ T₂ i hT₁ hT₂ hj => by
        simp only [Window.knuth]
        split_ifs with hlt
        · rw [hT₁ i (i + d + 1 - 1) (by omega) (by omega),
            hT₂ i (i + d + 1 - 1) (by omega) (by omega),
            hT₁ (i + 1) (i + d + 1) hj (by omega),
            hT₂ (i + 1) (i + d + 1) hj (by omega)]
          exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩)
      (fun d T _ hT => by
        have htel := sum_knuth_window_le hqi hmono hT
        have hsub : I.numKeys + 1 - (d + 1) = I.numKeys - d := by omega
        rw [hsub] at htel
        simpa only [Nat.add_assoc] using htel)
      (exec_knuthWindowCode I hw.1)
  rw [knuthBST_eq hqi hmono]
  exact ⟨xf, hexec.mono (le_of_eq (by ring)), hres⟩

/-- `Program.ComputesInTime` theorem for `knuthBSTProgram` over instances satisfying
`OptimalBSTInstance.IsKnuthValid`. -/
theorem computesInTime_knuthBST :
    knuthBSTProgram.ComputesInTime
      (fun _ (I : {I : OptimalBSTInstance // I.IsKnuthValid}) => I.1.encode)
      (fun I _ => 58 * (I.1.numKeys + 1) ^ 2)
      (fun I w => I.1.FitsWidth w)
      (fun I => (knuthBST I.1.weightFn I.1.numKeys).cost) :=
  ((bstCode knuthWindowCode).computesInTime_program regOut
    (time := fun (I : {I : OptimalBSTInstance // I.IsKnuthValid}) _ =>
      58 * I.1.numKeys ^ 2 + 8 * I.1.numKeys + 15)
    (fun ⟨I, hqi, hmono⟩ _ hw _ => exec_knuthBSTCode I hqi hmono hw)).mono
    (fun ⟨_, _⟩ _ => by nlinarith) (fun _ _ h => h)

/-- **Word-RAM quadratic running time of Knuth's optimal-BST algorithm.** Whenever `I.weightFn`
satisfies `QuadrangleIneq` and `MonotoneOnIntervals`, `knuthBSTProgram` halts within
`58 (n + 1)²` instructions returning `(knuthBST I.weightFn I.numKeys).cost` at every fitting
width `w`. -/
theorem executes_knuthBST {I : OptimalBSTInstance} {w : ℕ}
    (hqi : QuadrangleIneq I.weightFn) (hmono : MonotoneOnIntervals I.weightFn)
    (hw : I.FitsWidth w) :
    ∃ n, Executes w knuthBSTProgram (.init I.encode) (knuthBST I.weightFn I.numKeys).cost n ∧
      n ≤ 58 * (I.numKeys + 1) ^ 2 :=
  computesInTime_knuthBST ⟨I, hqi, hmono⟩ w hw hw.inputFits

/-- Uniform `O(n²)` Word-RAM computability of Knuth's optimal-BST algorithm over instances
satisfying `OptimalBSTInstance.IsKnuthValid`. -/
theorem uniformComputableInTime_knuthBST :
    UniformComputableInTime .standard
      (fun I : {I : OptimalBSTInstance // I.IsKnuthValid} =>
        (knuthBST I.1.weightFn I.1.numKeys).cost)
      (fun _ I => I.1.encode)
      (fun I _ => 58 * (I.1.numKeys + 1) ^ 2)
      (fun I w => I.1.FitsWidth w) :=
  ⟨22, knuthBSTProgram, computesInTime_knuthBST, OptimalBSTInstance.inputAdmissible_knuthValid⟩

end Cslib.Algorithms.WordRAM.OptimalBST
