/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TSP.HeldKarp
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Nat.Bitwise.Carry
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM Bellman–Held–Karp dynamic programming for TSP

Checked standard-basis Word-RAM implementation and `O(n² · 2ⁿ)` running-time bound for the
Bellman–Held–Karp optimal traveling-salesman tour cost [Bellman1962] [HeldKarp1962]
(`Cslib.Algorithms.Lean.TSP.heldKarp`).

An instance `I : Instance` specifies `n` non-origin cities (`n + 1` total cities `Fin (n + 1)`) and
a pairwise distance function `I.dist : Fin (n + 1) → Fin (n + 1) → ℕ`, encoded in input memory as
`I.n` followed by the `(n + 1)²` row-major distance entries (`Instance.encode`). Without using the
multiplier instruction (`Basis.standard`), the fixed program `program` maintains row and bitmask
strides additively, fills the `2ⁿ × (n + 1)` subset-by-target table in increasing bitmask order,
and halts with `heldKarp I.dist` in at most `80 (n² · 2ⁿ + 1)` instructions at every fitting word
width `w` (`Instance.FitsWidth`). Every address calculation, bitmask test, memory read/write,
comparison, addition, loop branch/jump, and `halt` is charged.

## Main definitions

* `Cslib.Algorithms.WordRAM.HeldKarp.Instance`: `(n + 1) × (n + 1)` natural distance matrix, its
  flat word encoding `Instance.encode`, address bound `Instance.spaceBound`, maximum entry
  `Instance.maxEntry`, and width condition `Instance.FitsWidth`.
* `Cslib.Algorithms.WordRAM.HeldKarp.program`: uniform `Program .standard 18` computing optimal
  tour cost.

## Main results

* `Cslib.Algorithms.WordRAM.HeldKarp.Instance.FitsWidth.inputFits`,
  `Instance.inputAdmissible`: word-width fit implies `InputFits` and every instance admits a
  fitting width.
* `Cslib.Algorithms.WordRAM.HeldKarp.executes_program`, `computesInTime_program`,
  `uniformComputableInTime_heldKarp`: `program` computes `heldKarp I.dist` within
  `80 (n² · 2ⁿ + 1)` standard-basis instructions.
* `Cslib.Algorithms.WordRAM.HeldKarp.uniformComputableInO_heldKarp`: uniform `O(n² · 2ⁿ)`
  Word-RAM running time in `I.n`.

## References

* [R. Bellman, *Dynamic programming treatment of the travelling salesman problem*][Bellman1962]
* [M. Held and R. M. Karp, *A dynamic programming approach to sequencing
  problems*][HeldKarp1962]
-/

public section

namespace Cslib.Algorithms.WordRAM.HeldKarp

open Cslib.Algorithms.Lean.TSP
open Cslib.WordRAM

/-! ## Problem instances and word-width admissibility -/

/-- An `(n + 1)`-city traveling-salesman distance matrix over `ℕ`. -/
structure Instance where
  /-- Number of non-origin cities (`n + 1` total cities `Fin (n + 1)`). -/
  n : ℕ
  /-- Pairwise distances between cities in `Fin (n + 1)`. -/
  dist : Fin (n + 1) → Fin (n + 1) → ℕ

namespace Instance

/-- Flat input word encoding `[n, d(0,0), …, d(0,n), …, d(n,0), …, d(n,n)]`. -/
@[expose] def encode (I : Instance) : List ℕ :=
  I.n :: (List.finRange (I.n + 1)).flatMap fun i =>
    (List.finRange (I.n + 1)).map fun j => I.dist i j

/-- Address bound covering the input header, `(n + 1)²` distance entries, and the `2ⁿ × (n + 1)`
dynamic-programming table. -/
@[expose] def spaceBound (I : Instance) : ℕ :=
  3 + (I.n + 1) * (I.n + 1) + 2 ^ I.n * (I.n + 1)

/-- Largest single-edge distance in `I.dist`. -/
@[expose] def maxEntry (I : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin (I.n + 1) × Fin (I.n + 1) => I.dist p.1 p.2

/-- Word width `w` fits all table addresses/strides and all `(n + 1)`-step tour costs. -/
@[expose] def FitsWidth (I : Instance) (w : ℕ) : Prop :=
  Fits w I.spaceBound ∧ Fits w ((I.n + 1) * I.maxEntry)

theorem dist_le_maxEntry (I : Instance) (i j : Fin (I.n + 1)) :
    I.dist i j ≤ I.maxEntry :=
  Finset.le_sup (f := fun p : Fin (I.n + 1) × Fin (I.n + 1) => I.dist p.1 p.2)
    (Finset.mem_univ (i, j))

theorem encode_length (I : Instance) :
    I.encode.length = 1 + (I.n + 1) * (I.n + 1) := by
  simp [encode, List.length_flatMap, List.map_const', List.sum_replicate, Nat.add_comm]

private theorem init_mem_dist {r : ℕ} (I : Instance) (i j : Fin (I.n + 1)) :
    (Data.init I.encode : Data r).mem (2 + i.val * (I.n + 1) + j.val) = I.dist i j := by
  rw [show 2 + i.val * (I.n + 1) + j.val = (i.val * (I.n + 1) + j.val + 1) + 1 by omega,
    Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_flatMap_mul_add _ _ (I.n + 1) (by simp) (by simp [i.isLt]) j.isLt,
    List.getElem?_map, List.getElem?_eq_getElem (by simp [j.isLt])]
  simp

private theorem init_mem_n {r : ℕ} (I : Instance) :
    (Data.init I.encode : Data r).mem 1 = I.n := by
  rw [Data.init_mem_succ, encode, List.getD_cons_zero]

theorem FitsWidth.inputFits {I : Instance} {w : ℕ} (h : I.FitsWidth w) :
    InputFits w I.encode := by
  have hpow : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  refine ⟨h.1.of_le (by rw [I.encode_length, spaceBound]; nlinarith), fun v hv => ?_⟩
  rw [encode, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact h.1.of_le (by rw [spaceBound]; nlinarith)
  · obtain ⟨i, -, hj⟩ := List.mem_flatMap.mp hv
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hj
    exact h.2.of_le ((I.dist_le_maxEntry i j).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))

theorem inputAdmissible : InputAdmissible (fun _ => Instance.encode) Instance.FitsWidth := by
  intro I
  let w := I.spaceBound + (I.n + 1) * I.maxEntry
  have hw : I.FitsWidth w :=
    ⟨Nat.lt_of_le_of_lt (Nat.le_add_right _ _) Nat.lt_two_pow_self,
     Nat.lt_of_le_of_lt (Nat.le_add_left _ _) Nat.lt_two_pow_self⟩
  exact ⟨w, hw, hw.inputFits⟩

end Instance

/-! ## Subset bitmasks and walk-cost bounds -/

/-- The subset of `Fin n` encoded by the low `n` bits of `mask`. -/
private def maskSet (n mask : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => mask.testBit i.val

private theorem mem_maskSet {n mask : ℕ} {i : Fin n} :
    i ∈ maskSet n mask ↔ mask.testBit i.val = true := by
  simp [maskSet]

private theorem maskSet_zero (n : ℕ) : maskSet n 0 = ∅ := by
  ext i
  simp [maskSet]

private theorem maskSet_two_pow_sub_one (n : ℕ) : maskSet n (2 ^ n - 1) = Finset.univ := by
  ext i
  simp [maskSet, Nat.testBit_two_pow_sub_one]

private theorem exists_bit_of_pos_lt {n mask : ℕ} (hpos : 0 < mask) (hlt : mask < 2 ^ n) :
    ∃ i : Fin n, mask.testBit i.val = true := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hpos.ne'
  refine ⟨⟨i, ?_⟩, hi⟩
  by_contra h
  simp [Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right two_pos (not_lt.1 h)))] at hi

private theorem maskSet_sub_two_pow {n mask : ℕ} {i : Fin n} (h : mask.testBit i.val = true) :
    maskSet n (mask - 2 ^ i.val) = (maskSet n mask).erase i := by
  ext j
  simp [mem_maskSet, Nat.testBit_sub_two_pow h, Fin.val_ne_iff, and_comm]

private theorem walkCost_le_mul_maxEntry (I : Instance) (a : Fin (I.n + 1))
    (L : List (Fin (I.n + 1))) (b : Fin (I.n + 1)) :
    walkCost I.dist a L b ≤ (L.length + 1) * I.maxEntry := by
  induction L generalizing a with
  | nil =>
    simpa [walkCost] using I.dist_le_maxEntry a b
  | cons x L ih =>
    simp only [walkCost, List.length_cons]
    nlinarith [I.dist_le_maxEntry a x, ih x]

private theorem isLeast_walkCosts_le (I : Instance) {S : Finset (Fin I.n)} {t : Fin (I.n + 1)}
    {v : ℕ} (hv : IsLeast (walkCosts I.dist S t) v) :
    v ≤ (S.card + 1) * I.maxEntry := by
  obtain ⟨⟨L, hnd, rfl, rfl⟩, -⟩ := hv
  simpa [List.toFinset_card_of_nodup hnd] using walkCost_le_mul_maxEntry I 0 (L.map Fin.succ) t

/-! ## Structured Word-RAM program -/

private abbrev rZero : Fin 18 := 0
private abbrev rOne : Fin 18 := 1
private abbrev rn : Fin 18 := 2
private abbrev rN : Fin 18 := 3
private abbrev rDistBase : Fin 18 := 4
private abbrev rDpBase : Fin 18 := 5
private abbrev rPowN : Fin 18 := 6
private abbrev rMask : Fin 18 := 7
private abbrev rMaskBase : Fin 18 := 8
private abbrev rT : Fin 18 := 9
private abbrev rI : Fin 18 := 10
private abbrev rBit : Fin 18 := 11
private abbrev rBitStride : Fin 18 := 12
private abbrev rRowDist : Fin 18 := 13
private abbrev rHasBest : Fin 18 := 14
private abbrev rBest : Fin 18 := 15
private abbrev rTmp0 : Fin 18 := 16
private abbrev rTmp1 : Fin 18 := 17

private def nop : Code .standard 18 :=
  ram[ rZero ← rZero ]

private theorem exec_nop {w : ℕ} (s : Data 18) : ExecWithin w nop s s 1 := by
  have he : Exec w nop s (s.set rZero (s.regs rZero)) 1 := Exec.copy
  convert he.within
  ext i <;> simp [Data.set]

private def dpBaseStep : Code .standard 18 :=
  ram[ rDpBase ← rDpBase + rN; rT ← rT + rOne ]

private def powNStep : Code .standard 18 :=
  ram[ rPowN ← rPowN + rPowN; rI ← rI + rOne ]

private def baseMaskStep : Code .standard 18 :=
  ram[
    rTmp0 ← rDistBase + rT;
    rTmp1 ← *rTmp0;
    rTmp0 ← rDpBase + rT;
    *rTmp0 ← rTmp1;
    rT ← rT + rOne ]

private def relaxLoad : Code .standard 18 :=
  ram[
    rTmp0 ← rMaskBase - rBitStride;
    rTmp0 ← rTmp0 + rI;
    rTmp0 ← rTmp0 + rOne;
    rTmp0 ← *rTmp0;
    rTmp1 ← rRowDist + rT;
    rTmp1 ← *rTmp1;
    rTmp0 ← rTmp0 + rTmp1 ]

private def relaxUpd : Code .standard 18 :=
  .branch (.eq rHasBest rZero)
    (ram[ rBest ← rTmp0; rHasBest ← #1 ])
    (.branch (.lt rTmp0 rBest)
      (ram[ rBest ← rTmp0 ])
      nop)

private def relaxThen : Code .standard 18 :=
  .seq relaxLoad relaxUpd

private def innerBitPre : Code .standard 18 :=
  ram[ rTmp0 ← rMask &&& rBit ]

private def innerBitPost : Code .standard 18 :=
  ram[
    rBit ← rBit + rBit;
    rBitStride ← rBitStride + rBitStride;
    rRowDist ← rRowDist + rN;
    rI ← rI + rOne ]

private def innerBitStep : Code .standard 18 :=
  .seq innerBitPre (.seq (.branch (.lt rZero rTmp0) relaxThen nop) innerBitPost)

private def targetInit : Code .standard 18 :=
  ram[
    rHasBest ← #0;
    rBest ← #0;
    rI ← #0;
    rBit ← #1;
    rBitStride ← rN;
    rRowDist ← rDistBase + rN ]

private def targetStore : Code .standard 18 :=
  ram[
    rTmp0 ← rMaskBase + rT;
    *rTmp0 ← rBest;
    rT ← rT + rOne ]

private def targetStep : Code .standard 18 :=
  .seq targetInit (.seq (.loop (.lt rI rn) innerBitStep) targetStore)

private def maskZeroT : Code .standard 18 :=
  ram[ rT ← #0 ]

private def maskInc : Code .standard 18 :=
  ram[ rMask ← rMask + rOne; rMaskBase ← rMaskBase + rN ]

private def maskStep : Code .standard 18 :=
  .seq maskZeroT (.seq (.loop (.lt rT rN) targetStep) maskInc)

private def setupInit : Code .standard 18 :=
  ram[
    rZero ← #0;
    rOne ← #1;
    rn ← *rOne;
    rN ← rn + rOne;
    rDistBase ← #2;
    rDpBase ← #2;
    rT ← #0 ]

private def setupPowInit : Code .standard 18 :=
  ram[ rPowN ← #1; rI ← #0 ]

private def setupMaskInit : Code .standard 18 :=
  ram[ rMask ← #1; rMaskBase ← rDpBase + rN ]

private def setupCode : Code .standard 18 :=
  .seq setupInit
    (.seq (.loop (.lt rT rN) dpBaseStep)
      (.seq setupPowInit
        (.seq (.loop (.lt rI rn) powNStep)
          (.seq maskZeroT
            (.seq (.loop (.lt rT rN) baseMaskStep) setupMaskInit)))))

private def finalReadCode : Code .standard 18 :=
  ram[ rTmp0 ← rMaskBase - rN; rBest ← *rTmp0 ]

private def heldKarpCode : Code .standard 18 :=
  .seq setupCode (.seq (.loop (.lt rMask rPowN) maskStep) finalReadCode)

/-- Uniform standard-basis Word-RAM program computing `heldKarp I.dist`. -/
def program : Program .standard 18 :=
  heldKarpCode.program rBest

/-! ## Symbolic execution and loop invariants -/

private structure FixedRegs (I : Instance) (s : Data 18) : Prop where
  zero : s.regs rZero = 0
  one : s.regs rOne = 1
  n_eq : s.regs rn = I.n
  N_eq : s.regs rN = I.n + 1
  distB : s.regs rDistBase = 2
  dpB : s.regs rDpBase = 2 + (I.n + 1) * (I.n + 1)
  powN : s.regs rPowN = 2 ^ I.n

private def DistIntact (I : Instance) (mem : ℕ → ℕ) : Prop :=
  ∀ i j : Fin (I.n + 1), mem (2 + i.val * (I.n + 1) + j.val) = I.dist i j

private def TableInv (I : Instance) (maskBound : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ m < maskBound, ∀ t : Fin (I.n + 1),
    IsLeast (walkCosts I.dist (maskSet I.n m) t)
      (mem (2 + (I.n + 1) * (I.n + 1) + m * (I.n + 1) + t.val))

private theorem exec_setupInit {w : ℕ} (I : Instance) (hwS : Fits w I.spaceBound) :
    ∃ s1, ExecWithin w setupInit (.init I.encode) s1 7 ∧
      s1.mem = (Data.init I.encode : Data 18).mem ∧
      s1.regs rZero = 0 ∧ s1.regs rOne = 1 ∧ s1.regs rn = I.n ∧
      s1.regs rN = I.n + 1 ∧ s1.regs rDistBase = 2 ∧ s1.regs rDpBase = 2 ∧ s1.regs rT = 0 := by
  have hn_mem := I.init_mem_n (r := 18)
  have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
  have hfitN : Fits w (I.n + 1) := hwS.of_le (by rw [Instance.spaceBound]; omega)
  have hfit2 : Fits w 2 := hwS.of_le (by rw [Instance.spaceBound]; omega)
  dsimp [setupInit]
  wram_exec [hn_mem]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wram_simp [hn_mem]

private theorem exec_baseMaskStep {w : ℕ} (I : Instance) (hwS : Fits w I.spaceBound)
    (mem0 : ℕ → ℕ)
    (hmem0 : ∀ a < 2 + (I.n + 1) * (I.n + 1), mem0 a = (Data.init I.encode : Data 18).mem a)
    (y : Data 18) (hyfix : FixedRegs I y)
    (hylow : ∀ a < 2 + (I.n + 1) * (I.n + 1), y.mem a = mem0 a)
    (hywr : ∀ j < y.regs rT, ∀ (hj : j < I.n + 1),
      y.mem (2 + (I.n + 1) * (I.n + 1) + j) = I.dist 0 ⟨j, hj⟩)
    (hlt : y.regs rT < I.n + 1) :
    ∃ y', ExecWithin w baseMaskStep y y' 5 ∧
      FixedRegs I y' ∧
      (∀ a < 2 + (I.n + 1) * (I.n + 1), y'.mem a = mem0 a) ∧
      (∀ j < y.regs rT + 1, ∀ (hj : j < I.n + 1),
        y'.mem (2 + (I.n + 1) * (I.n + 1) + j) = I.dist 0 ⟨j, hj⟩) ∧
      y'.regs rT = y.regs rT + 1 := by
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  have hyo := hyfix.one; have hydb := hyfix.distB; have hydp := hyfix.dpB
  have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hmul : I.n + 1 ≤ 2 ^ I.n * (I.n + 1) := Nat.le_mul_of_pos_left _ hpow1
  have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
  have hfit_src : Fits w (2 + y.regs rT) := hwS.of_le (by rw [Instance.spaceBound]; omega)
  have hfit_dst : Fits w (2 + (I.n + 1) * (I.n + 1) + y.regs rT) :=
    hwS.of_le (by rw [Instance.spaceBound]; omega)
  have hfit_t : Fits w (y.regs rT + 1) := hwS.of_le (by rw [Instance.spaceBound]; omega)
  have hsrc_mem : y.mem (2 + y.regs rT) = I.dist 0 ⟨y.regs rT, hlt⟩ := by
    rw [hylow _ (by nlinarith only [hlt]), hmem0 _ (by nlinarith only [hlt])]
    simpa using I.init_mem_dist (r := 18) 0 ⟨y.regs rT, hlt⟩
  dsimp [baseMaskStep]
  wram_exec [hydb, hydp, hyo, hsrc_mem]
  refine ⟨by struct_frame hyfix, ?_, ?_, by wram_simp [hyo]⟩
  · intro a ha
    wram_simp [hydp]
    exact hylow a ha
  · intro j hj hjlt
    by_cases hjeq : j = y.regs rT
    · subst hjeq; wram_simp [hydb, hydp, hsrc_mem]
    · wram_simp [hydb, hydp, hsrc_mem]
      exact hywr j (by omega) hjlt

private theorem exec_setup {w : ℕ} (I : Instance) (hw : I.FitsWidth w) :
    ∃ s, ExecWithin w setupCode (.init I.encode) s (15 * I.n + 30) ∧
      FixedRegs I s ∧
      DistIntact I s.mem ∧
      TableInv I 1 s.mem ∧
      s.regs rMask = 1 ∧
      s.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + (I.n + 1) := by
  obtain ⟨hwS, _⟩ := hw
  have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  obtain ⟨s1, he1, hm1, hz1, ho1, hn1, hN1, hdb1, hdp1, ht1⟩ := exec_setupInit I hwS
  let P1 (k : ℕ) (s : Data 18) : Prop :=
    s.mem = s1.mem ∧ s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rn = I.n ∧
      s.regs rN = I.n + 1 ∧ s.regs rDistBase = 2 ∧ s.regs rDpBase = 2 + k * (I.n + 1)
  have hloop1 := ExecWithin.loop_count (w := w) (N := I.n + 1) (T := 2)
    (index := rT) (limit := rN) (body := dpBaseStep) P1
    (fun y hy => hy.2.2.2.2.1)
    (fun y ⟨hym, hyz, hyo, hyn, hyN, hydb, hydp⟩ hlt => by
      have hfit_dp : Fits w ((2 + y.regs rT * (I.n + 1)) + (I.n + 1)) :=
        hwS.of_le (by rw [Instance.spaceBound]; nlinarith only [hlt, hpow1])
      have hfit_t : Fits w (y.regs rT + 1) :=
        hwS.of_le (by rw [Instance.spaceBound]; nlinarith only [hlt, hpow1])
      dsimp [dpBaseStep]
      wram_exec [hyN, hydp, hyo]
      refine ⟨⟨hym, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> wram_simp [hyz, hyo, hyn, hyN, hydb, hydp]
      ring)
    (by rw [ht1]; omega)
    (by rw [ht1]; exact ⟨rfl, hz1, ho1, hn1, hN1, hdb1, by simp [hdp1]⟩)
  rw [ht1, Nat.sub_zero] at hloop1
  obtain ⟨s2, he2, ⟨hm2, hz2, ho2, hn2, hN2, hdb2, hdp2⟩, -⟩ := hloop1
  obtain ⟨s3, he3, hm3, hz3, ho3, hn3, hN3, hdb3, hdp3, hpow3, hi3⟩ :
      ∃ s3, ExecWithin w setupPowInit s2 s3 2 ∧
        s3.mem = s1.mem ∧ s3.regs rZero = 0 ∧ s3.regs rOne = 1 ∧ s3.regs rn = I.n ∧
        s3.regs rN = I.n + 1 ∧ s3.regs rDistBase = 2 ∧
        s3.regs rDpBase = 2 + (I.n + 1) * (I.n + 1) ∧ s3.regs rPowN = 1 ∧ s3.regs rI = 0 := by
    have hfit1 : Fits w 1 := hwS.of_le (by rw [Instance.spaceBound]; omega)
    dsimp [setupPowInit]
    wram_exec
    refine ⟨hm2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp [hz2, ho2, hn2, hN2, hdb2, hdp2]
  let P2 (k : ℕ) (s : Data 18) : Prop :=
    s.mem = s1.mem ∧ s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rn = I.n ∧
      s.regs rN = I.n + 1 ∧ s.regs rDistBase = 2 ∧
      s.regs rDpBase = 2 + (I.n + 1) * (I.n + 1) ∧ s.regs rPowN = 2 ^ k
  have hloop2 := ExecWithin.loop_count (w := w) (N := I.n) (T := 2)
    (index := rI) (limit := rn) (body := powNStep) P2
    (fun y hy => hy.2.2.2.1)
    (fun y ⟨hym, hyz, hyo, hyn, hyN, hydb, hydp, hypow⟩ hlt => by
      have hp_le : 2 ^ (y.regs rI + 1) ≤ 2 ^ I.n := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow_mul : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have hfit_pow : Fits w (2 ^ y.regs rI + 2 ^ y.regs rI) :=
        hwS.of_le (by
          rw [Instance.spaceBound, ← two_mul, mul_comm, ← pow_succ]
          omega)
      have hfit_i : Fits w (y.regs rI + 1) :=
        hwS.of_le (by rw [Instance.spaceBound]; nlinarith only [hlt, hpow1])
      dsimp [powNStep]
      wram_exec [hypow, hyo]
      refine ⟨⟨hym, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        wram_simp [hyz, hyo, hyn, hyN, hydb, hydp, hypow]
      ring)
    (by rw [hi3]; omega)
    (by rw [hi3]; exact ⟨hm3, hz3, ho3, hn3, hN3, hdb3, hdp3, by simp [hpow3]⟩)
  rw [hi3, Nat.sub_zero] at hloop2
  obtain ⟨s4, he4, ⟨hm4, hz4, ho4, hn4, hN4, hdb4, hdp4, hpow4⟩, -⟩ := hloop2
  obtain ⟨s5, he5, hm5, hfix5, ht5⟩ : ∃ s5, ExecWithin w maskZeroT s4 s5 1 ∧
      s5.mem = s1.mem ∧ FixedRegs I s5 ∧ s5.regs rT = 0 := by
    dsimp [maskZeroT]
    wram_exec [hz4]
    refine ⟨hm4, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      wram_simp [hz4, ho4, hn4, hN4, hdb4, hdp4, hpow4]
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  let P3 (k : ℕ) (s : Data 18) : Prop :=
    FixedRegs I s ∧
      (∀ a < dp0, s.mem a = s1.mem a) ∧
      ∀ j < k, ∀ (hj : j < I.n + 1), s.mem (dp0 + j) = I.dist 0 ⟨j, hj⟩
  have hloop3 := ExecWithin.loop_count (w := w) (N := I.n + 1) (T := 5)
    (index := rT) (limit := rN) (body := baseMaskStep) P3
    (fun y hy => hy.1.N_eq)
    (fun y ⟨hyfix, hylow, hywr⟩ hlt => by
      obtain ⟨y', he, h1, h2, h3, h4⟩ :=
        exec_baseMaskStep I hwS s1.mem (fun _ _ => by rw [hm1]) y hyfix hylow hywr hlt
      exact ⟨y', he, ⟨h1, h2, h3⟩, h4⟩)
    (by rw [ht5]; omega)
    (by rw [ht5]; exact ⟨hfix5, fun a _ => by rw [hm5], fun j hj => absurd hj (by omega)⟩)
  rw [ht5, Nat.sub_zero] at hloop3
  obtain ⟨s6, he6, ⟨hfix6, hlow6, hwr6⟩, -⟩ := hloop3
  obtain ⟨s7, he7, hm7, hfix7, hmask7, hmb7⟩ : ∃ s7, ExecWithin w setupMaskInit s6 s7 2 ∧
      s7.mem = s6.mem ∧ FixedRegs I s7 ∧ s7.regs rMask = 1 ∧
      s7.regs rMaskBase = dp0 + (I.n + 1) := by
    have hfit1 : Fits w 1 := hwS.of_le (by rw [Instance.spaceBound]; omega)
    have hfit_mb : Fits w (dp0 + (I.n + 1)) :=
      hwS.of_le (by rw [Instance.spaceBound]; dsimp [dp0]; nlinarith only [hpow1])
    dsimp [dp0, setupMaskInit]
    wram_exec [hfix6.dpB, hfix6.N_eq]
    exact ⟨rfl, by struct_frame hfix6, by wram_simp, by wram_simp [hfix6.dpB, hfix6.N_eq]⟩
  refine ⟨s7,
    (he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (he6.seq he7)))))).mono (by omega),
    hfix7, ?_, ?_, hmask7, hmb7⟩
  · intro i j
    rw [hm7, hlow6 _ (by dsimp [dp0]; nlinarith only [i.isLt, j.isLt]), hm1]
    exact I.init_mem_dist i j
  · intro m hm t
    obtain rfl : m = 0 := by omega
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [hm7, hwr6 t.val t.isLt t.isLt, maskSet_zero]
    exact isLeast_walkCosts_empty I.dist t

private def PrefixSet (I : Instance) (mask k : ℕ) : Finset (Fin I.n) :=
  Finset.univ.filter fun i => i.val < k ∧ mask.testBit i.val = true

private theorem prefixSet_zero (I : Instance) (mask : ℕ) : PrefixSet I mask 0 = ∅ := by
  simp [PrefixSet]

private theorem prefixSet_full (I : Instance) (mask : ℕ) :
    PrefixSet I mask I.n = maskSet I.n mask := by
  ext i
  simp [PrefixSet, maskSet]

private theorem fit_table_cell {w : ℕ} {I : Instance} (hwS : Fits w I.spaceBound)
    {mask t : ℕ} (hm : mask < 2 ^ I.n) (ht : t < I.n + 1) :
    Fits w (2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) + t) := by
  have h1 : mask + 1 ≤ 2 ^ I.n := hm
  exact hwS.of_le (by rw [Instance.spaceBound]; nlinarith)

private theorem prefixSet_succ (I : Instance) (mask : ℕ) {k : ℕ} (hk : k < I.n) :
    PrefixSet I mask (k + 1) =
      if mask.testBit k then insert ⟨k, hk⟩ (PrefixSet I mask k) else PrefixSet I mask k := by
  ext j
  by_cases hj : j = ⟨k, hk⟩
  · subst hj
    split_ifs <;> simp_all [PrefixSet]
  · have hjk : j.val ≠ k := fun h => hj (Fin.ext h)
    have : j.val ≤ k ↔ j.val < k := by omega
    split_ifs <;> simp [PrefixSet, this, hj]

/-- The cost of a walk to `t` whose last stop before `t` is `j.succ`, read from the table row of
`mask` without bit `j`. -/
private def cand (I : Instance) (mask : ℕ) (t : Fin (I.n + 1)) (mem : ℕ → ℕ) (j : Fin I.n) : ℕ :=
  mem (2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)) + I.dist j.succ t

/-- `hasBest` and `best` after scanning `S`: whether a candidate has been seen, and the least
candidate `f j` over `j ∈ S`. -/
private structure BestInv {α : Type} (S : Finset α) (f : α → ℕ) (hasBest best : ℕ) : Prop where
  hasBest_eq : hasBest = if S.Nonempty then 1 else 0
  le : ∀ j ∈ S, best ≤ f j
  eq : S.Nonempty → ∃ j ∈ S, best = f j

/-- The first candidate seen becomes the best one. -/
private theorem BestInv.insert_first {α : Type} [DecidableEq α] {S : Finset α} {f : α → ℕ}
    {hb b : ℕ} (h : BestInv S f hb b) (h0 : hb = 0) (j : α) :
    BestInv (insert j S) f 1 (f j) := by
  have hS : ¬S.Nonempty := fun hS => by simpa [hS, h0] using h.hasBest_eq
  obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hS
  exact ⟨by simp, by simp, fun _ => ⟨j, by simp, rfl⟩⟩

/-- A later candidate `f j` replaces the best value `b` by a value `b'` that is one of them and at
most both. -/
private theorem BestInv.insert_of_ne {α : Type} [DecidableEq α] {S : Finset α} {f : α → ℕ}
    {hb b b' : ℕ} (h : BestInv S f hb b) (h0 : hb ≠ 0) {j : α} (hj : b' ≤ f j) (hb' : b' ≤ b)
    (hmem : b' = f j ∨ b' = b) : BestInv (insert j S) f hb b' := by
  have hS : S.Nonempty := by by_contra hS; simp [h.hasBest_eq, hS] at h0
  refine ⟨by simp [h.hasBest_eq, hS], fun i hi => ?_, fun _ => ?_⟩
  · rcases Finset.mem_insert.1 hi with rfl | hi
    exacts [hj, hb'.trans (h.le i hi)]
  · rcases hmem with rfl | rfl
    exacts [⟨j, by simp, rfl⟩, (h.eq hS).imp fun i hi => ⟨Finset.mem_insert_of_mem hi.1, hi.2⟩]

/-- The registers of the scan of bit `k` of `mask` for target `t`, other than the bit index. -/
private structure BitRegs (I : Instance) (mask : ℕ) (t : Fin (I.n + 1)) (k : ℕ) (s : Data 18) :
    Prop where
  mask_eq : s.regs rMask = mask
  maskBase_eq : s.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1)
  t_eq : s.regs rT = t.val
  bit_eq : s.regs rBit = 2 ^ k
  bitStride_eq : s.regs rBitStride = 2 ^ k * (I.n + 1)
  rowDist_eq : s.regs rRowDist = 2 + (k + 1) * (I.n + 1)

private theorem exec_innerBitStep {w : ℕ} (I : Instance) (hw : I.FitsWidth w)
    {mask : ℕ} (hmask_lt : mask < 2 ^ I.n) (t : Fin (I.n + 1)) (s : Data 18)
    (hfix : FixedRegs I s) (hdist : DistIntact I s.mem) (htab : TableInv I mask s.mem)
    {k : ℕ} (hk : k < I.n) (hs : BitRegs I mask t k s) (hi : s.regs rI = k)
    (hbest : BestInv (PrefixSet I mask k) (cand I mask t s.mem) (s.regs rHasBest) (s.regs rBest)) :
    ∃ z, ExecWithin w innerBitStep s z 20 ∧ z.mem = s.mem ∧ FixedRegs I z ∧
      BitRegs I mask t (k + 1) z ∧ z.regs rI = k + 1 ∧
      BestInv (PrefixSet I mask (k + 1)) (cand I mask t s.mem) (z.regs rHasBest)
        (z.regs rBest) := by
  obtain ⟨hwS, hwV⟩ := hw
  have hpow_le : 2 ^ (k + 1) ≤ 2 ^ I.n := Nat.pow_le_pow_right (by omega) hk
  have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
  have hpow_mul : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hbs_le : 2 ^ (k + 1) * (I.n + 1) ≤ 2 ^ I.n * (I.n + 1) := Nat.mul_le_mul_right _ hpow_le
  have hrow : (k + 2) * (I.n + 1) ≤ (I.n + 1) * (I.n + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [Instance.spaceBound] at hwS
  have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  have hbs2 : 2 ^ (k + 1) * (I.n + 1) = 2 ^ k * (I.n + 1) + 2 ^ k * (I.n + 1) := by ring
  have hrd2 : (k + 2) * (I.n + 1) = (k + 1) * (I.n + 1) + (I.n + 1) := by ring
  rw [prefixSet_succ I mask hk]
  unfold innerBitStep innerBitPre innerBitPost relaxThen relaxLoad relaxUpd nop
  rcases Bool.eq_false_or_eq_true (mask.testBit k) with hbit | hbit
  · simp only [hbit, ↓reduceIte]
    have hbit_le : 2 ^ k ≤ mask := Nat.ge_two_pow_of_testBit hbit
    have hand : mask &&& 2 ^ k = 2 ^ k := by simp [Nat.and_two_pow, hbit]
    -- The candidate is a table entry for a set of at most `n - 1` cities, plus one edge.
    have hcand_le : cand I mask t s.mem ⟨k, hk⟩ ≤ (I.n + 1) * I.maxEntry := by
      have hcard : (maskSet I.n (mask - 2 ^ k)).card + 1 ≤ I.n := by
        simpa only [maskSet_sub_two_pow (i := ⟨k, hk⟩) hbit, Fintype.card_fin,
          Nat.add_one_le_iff] using
          (Finset.card_lt_iff_ne_univ ((maskSet I.n mask).erase ⟨k, hk⟩)).2 fun h =>
            Finset.notMem_erase (⟨k, hk⟩ : Fin I.n) _ (h ▸ Finset.mem_univ _)
      have h1 := (isLeast_walkCosts_le I (htab (mask - 2 ^ k)
        (by have := Nat.two_pow_pos k; omega) (Fin.succ ⟨k, hk⟩))).trans
          (Nat.mul_le_mul_right _ hcard)
      have h2 := I.dist_le_maxEntry (Fin.succ ⟨k, hk⟩) t
      simp only [cand, Fin.val_succ] at h1 ⊢
      nlinarith only [h1, h2]
    have hsub : 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) - 2 ^ k * (I.n + 1) =
        2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ k) * (I.n + 1) := by
      have := Nat.mul_le_mul_right (I.n + 1) hbit_le
      rw [Nat.sub_mul]
      omega
    have hcell := fit_table_cell (t := k + 1) (by simp only [Instance.spaceBound]; exact hwS)
      (lt_of_le_of_lt (Nat.sub_le mask (2 ^ k)) hmask_lt) (by omega)
    have hval : s.mem (2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) - 2 ^ k * (I.n + 1) + k + 1) +
        s.mem (2 + (k + 1) * (I.n + 1) + t) = cand I mask t s.mem ⟨k, hk⟩ := by
      rw [hsub, Nat.add_assoc _ k 1]
      exact congrArg₂ (· + ·) rfl (hdist (Fin.succ ⟨k, hk⟩) t)
    have hfit_cand : Fits w (cand I mask t s.mem ⟨k, hk⟩) := hwV.of_le hcand_le
    wram_exec [hs.mask_eq, hs.bit_eq, hand, Nat.two_pow_pos k, hs.maskBase_eq, hs.bitStride_eq,
      hi, hfix.zero, hfix.one, hfix.N_eq, hs.rowDist_eq, hs.t_eq, hval]
    all_goals
      refine ⟨by wram_simp, by struct_frame hfix, by struct_frame hs <;> wram_simp <;> ring,
        by wram_simp, ?_⟩
      wram_simp
    · exact hbest.insert_first hc _
    · exact hbest.insert_of_ne (by assumption) le_rfl hc.le (.inl rfl)
    · exact hbest.insert_of_ne (by assumption) (not_lt.1 hc) le_rfl (.inr rfl)
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
    have hand : mask &&& 2 ^ k = 0 := by simp [Nat.and_two_pow, hbit]
    wram_exec [hs.mask_eq, hs.bit_eq, hand, hi, hfix.zero, hfix.one, hfix.N_eq, hs.bitStride_eq,
      hs.rowDist_eq]
    exact ⟨by wram_simp, by struct_frame hfix, by struct_frame hs <;> wram_simp <;> ring,
      by wram_simp, by wram_simp; exact hbest⟩

private theorem exec_targetStep {w : ℕ} (I : Instance) (hw : I.FitsWidth w)
    {mask : ℕ} (hm_pos : 0 < mask) (hlt : mask < 2 ^ I.n)
    (st : Data 18) (hst_fix : FixedRegs I st) (hst_dist : DistIntact I st.mem)
    (hst_tab : TableInv I mask st.mem)
    (hst_m : st.regs rMask = mask)
    (hst_mb : st.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1))
    {tIdx : ℕ} (ht_eq : st.regs rT = tIdx) (ht_lt : tIdx < I.n + 1)
    (hst_cur : ∀ j < tIdx, ∀ (hj : j < I.n + 1),
      IsLeast (walkCosts I.dist (maskSet I.n mask) ⟨j, hj⟩)
        (st.mem (2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) + j))) :
    ∃ u2, ExecWithin w targetStep st u2 (22 * I.n + 11) ∧
      FixedRegs I u2 ∧ DistIntact I u2.mem ∧ TableInv I mask u2.mem ∧
      u2.regs rMask = mask ∧
      u2.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) ∧
      (∀ j < tIdx + 1, ∀ (hj : j < I.n + 1),
        IsLeast (walkCosts I.dist (maskSet I.n mask) ⟨j, hj⟩)
          (u2.mem (2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) + j))) ∧
      u2.regs rT = tIdx + 1 := by
  obtain ⟨hwS, hwV⟩ := hw
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  let tFin : Fin (I.n + 1) := ⟨tIdx, ht_lt⟩
  have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
  have hfit1 : Fits w 1 := hwS.of_le (by rw [Instance.spaceBound]; omega)
  have hfit_rd0 : Fits w (2 + (I.n + 1)) := hwS.of_le (by rw [Instance.spaceBound]; omega)
  obtain ⟨u0, he_u0, hmu0, hfix_u0, hs_u0, hi_u0, hhb_u0⟩ :
      ∃ u0, ExecWithin w targetInit st u0 6 ∧ u0.mem = st.mem ∧ FixedRegs I u0 ∧
        BitRegs I mask tFin 0 u0 ∧ u0.regs rI = 0 ∧ u0.regs rHasBest = 0 := by
    dsimp [targetInit]
    wram_exec [hst_fix.N_eq, hst_fix.distB]
    refine ⟨rfl, by struct_frame hst_fix, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      wram_simp [hst_fix.N_eq, hst_fix.distB, hst_m, hst_mb, ht_eq] <;> first | rfl | simp
  let PBit (k : ℕ) (u : Data 18) : Prop :=
    u.mem = st.mem ∧ FixedRegs I u ∧ BitRegs I mask tFin k u ∧
      BestInv (PrefixSet I mask k) (cand I mask tFin st.mem) (u.regs rHasBest) (u.regs rBest)
  have hloop_i := ExecWithin.loop_count (w := w) (N := I.n) (T := 20)
    (index := rI) (limit := rn) (body := innerBitStep) PBit
    (fun u hu => hu.2.1.n_eq)
    (fun u ⟨hmu, hfix_u, hs_u, hinv_u⟩ hk_lt => by
      rw [← hmu] at hinv_u
      obtain ⟨u', he_u', hmu', hfix_u', hs_u', hi_u', hinv_u'⟩ := exec_innerBitStep I ⟨hwS, hwV⟩
        hlt tFin u hfix_u (hmu ▸ hst_dist) (hmu ▸ hst_tab) hk_lt hs_u rfl hinv_u
      exact ⟨u', he_u', ⟨hmu'.trans hmu, hfix_u', hs_u', hmu ▸ hinv_u'⟩, hi_u'⟩)
    (by rw [hi_u0]; omega)
    (by rw [hi_u0]; exact ⟨hmu0, hfix_u0, hs_u0, by simp [prefixSet_zero, hhb_u0], by
      simp [prefixSet_zero], by simp [prefixSet_zero]⟩)
  rw [hi_u0, Nat.sub_zero] at hloop_i
  obtain ⟨u1, he_u1, ⟨hmu1, hfix_u1, hs_u1, hinv_u1⟩, -⟩ := hloop_i
  rw [prefixSet_full] at hinv_u1
  obtain ⟨i₀, hi₀⟩ := exists_bit_of_pos_lt hm_pos hlt
  have hbest_least : IsLeast (walkCosts I.dist (maskSet I.n mask) tFin) (u1.regs rBest) := by
    refine isLeast_walkCosts_of_forall
      (f := fun j => st.mem (dp0 + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)))
      (fun j hj => ?_) hinv_u1.le (hinv_u1.eq ⟨i₀, mem_maskSet.2 hi₀⟩)
    have hj_bit := mem_maskSet.1 hj
    have hge := Nat.ge_two_pow_of_testBit hj_bit
    have hpos := Nat.two_pow_pos j.val
    rw [← maskSet_sub_two_pow hj_bit]
    exact hst_tab (mask - 2 ^ j.val) (by omega) j.succ
  obtain ⟨u2, he_u2, hmu2, hfix_u2, hm_u2, hmb_u2, ht_u2⟩ :
      ∃ u2, ExecWithin w targetStore u1 u2 3 ∧
        u2.mem = Function.update st.mem (dp0 + mask * (I.n + 1) + tIdx) (u1.regs rBest) ∧
        FixedRegs I u2 ∧ u2.regs rMask = mask ∧
        u2.regs rMaskBase = dp0 + mask * (I.n + 1) ∧ u2.regs rT = tIdx + 1 := by
    have hfit_addr : Fits w (dp0 + mask * (I.n + 1) + tIdx) := fit_table_cell hwS hlt ht_lt
    have hfit_t1 : Fits w (tIdx + 1) := hwS.of_le (by rw [Instance.spaceBound]; omega)
    have ht_u1 : u1.regs rT = tIdx := hs_u1.t_eq
    dsimp only [dp0, targetStore]
    wram_exec [hs_u1.maskBase_eq, ht_u1, hfix_u1.one]
    exact ⟨by wram_simp [hmu1, hs_u1.maskBase_eq, ht_u1],
      by struct_frame hfix_u1,
      by wram_simp [hs_u1.mask_eq],
      by wram_simp [hs_u1.maskBase_eq],
      by wram_simp [ht_u1, hfix_u1.one]⟩
  refine ⟨u2, (he_u0.seq (he_u1.seq he_u2)).mono (by omega),
    hfix_u2, ?_, ?_, hm_u2, hmb_u2, ?_, ht_u2⟩
  · intro i j
    rw [hmu2, Function.update_of_ne (by dsimp [dp0]; nlinarith only [i.isLt, j.isLt])]
    exact hst_dist i j
  · intro m hm t'
    rw [hmu2, Function.update_of_ne (by dsimp [dp0]; nlinarith only [hm, t'.isLt])]
    exact hst_tab m hm t'
  · intro j hj hjlt
    by_cases hjeq : j = tIdx
    · subst hjeq
      simpa [hmu2, dp0] using hbest_least
    · rw [hmu2, Function.update_of_ne (by omega)]
      exact hst_cur j (by omega) hjlt

private theorem exec_maskStep {w : ℕ} (I : Instance) (hw : I.FitsWidth w)
    {mask : ℕ} (hm_pos : 0 < mask) (hlt : mask < 2 ^ I.n)
    (y : Data 18) (hyfix : FixedRegs I y) (hydist : DistIntact I y.mem)
    (hytab : TableInv I mask y.mem)
    (hym : y.regs rMask = mask)
    (hymb : y.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1)) :
    ∃ y3, ExecWithin w maskStep y y3 ((I.n + 1) * (22 * I.n + 13) + 5) ∧
      1 ≤ mask + 1 ∧ FixedRegs I y3 ∧ DistIntact I y3.mem ∧
      TableInv I (mask + 1) y3.mem ∧
      y3.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + (mask + 1) * (I.n + 1) ∧
      y3.regs rMask = mask + 1 := by
  obtain ⟨hwS, hwV⟩ := hw
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  obtain ⟨y1, he_y1, hmy1, hfix_y1, hm_y1, hmb_y1, ht_y1⟩ :
      ∃ y1, ExecWithin w maskZeroT y y1 1 ∧ y1.mem = y.mem ∧ FixedRegs I y1 ∧
        y1.regs rMask = mask ∧ y1.regs rMaskBase = dp0 + mask * (I.n + 1) ∧ y1.regs rT = 0 := by
    dsimp [dp0, maskZeroT]
    wram_exec [hyfix.zero]
    exact ⟨rfl, by struct_frame hyfix, by wram_simp [hym], by wram_simp [hymb], by wram_simp⟩
  let PTarget (tIdx : ℕ) (st : Data 18) : Prop :=
    FixedRegs I st ∧ DistIntact I st.mem ∧ TableInv I mask st.mem ∧
      st.regs rMask = mask ∧ st.regs rMaskBase = dp0 + mask * (I.n + 1) ∧
      ∀ j < tIdx, ∀ (hj : j < I.n + 1),
        IsLeast (walkCosts I.dist (maskSet I.n mask) ⟨j, hj⟩)
          (st.mem (dp0 + mask * (I.n + 1) + j))
  have hloop_t := ExecWithin.loop_count (w := w) (N := I.n + 1) (T := 22 * I.n + 11)
    (index := rT) (limit := rN) (body := targetStep) PTarget
    (fun st hst => hst.1.N_eq)
    (fun st ⟨hst_fix, hst_dist, hst_tab, hst_m, hst_mb, hst_cur⟩ ht_lt => by
      obtain ⟨u2, he, hfix, hdist, htab, hm, hmb, hcur, ht⟩ :=
        exec_targetStep I ⟨hwS, hwV⟩ hm_pos hlt st hst_fix hst_dist hst_tab hst_m hst_mb
          rfl ht_lt hst_cur
      exact ⟨u2, he, ⟨hfix, hdist, htab, hm, hmb, hcur⟩, ht⟩)
    (by rw [ht_y1]; omega)
    (by
      rw [ht_y1]
      exact ⟨hfix_y1, hmy1 ▸ hydist, hmy1 ▸ hytab, hm_y1, hmb_y1,
        fun j hj => absurd hj (by omega)⟩)
  rw [ht_y1, Nat.sub_zero] at hloop_t
  obtain ⟨y2, he_y2, ⟨hfix_y2, hdist_y2, htab_y2, hm_y2, hmb_y2, hcur_y2⟩, -⟩ := hloop_t
  obtain ⟨y3, he_y3, hmy3, hfix_y3, hm_y3, hmb_y3⟩ : ∃ y3, ExecWithin w maskInc y2 y3 2 ∧
      y3.mem = y2.mem ∧ FixedRegs I y3 ∧ y3.regs rMask = mask + 1 ∧
      y3.regs rMaskBase = dp0 + (mask + 1) * (I.n + 1) := by
    have ho2 := hfix_y2.one
    have hN2 := hfix_y2.N_eq
    have hfit_m1 : Fits w (mask + 1) :=
      hwS.of_le (by rw [Instance.spaceBound]; nlinarith)
    have hfit_mb1 : Fits w ((dp0 + mask * (I.n + 1)) + (I.n + 1)) :=
      hwS.of_le (by rw [Instance.spaceBound]; dsimp [dp0]; nlinarith)
    dsimp [maskInc]
    wram_exec [hm_y2, ho2, hmb_y2, hN2]
    exact ⟨rfl, by struct_frame hfix_y2, by wram_simp [hm_y2, ho2],
      by wram_simp [hmb_y2, hN2]; ring⟩
  refine ⟨y3, (he_y1.seq (he_y2.seq he_y3)).mono (by nlinarith),
    by omega, hfix_y3, hmy3 ▸ hdist_y2, ?_, hmb_y3, hm_y3⟩
  intro m hm t'
  rw [hmy3]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hm) with hlt_m | rfl
  · exact htab_y2 m hlt_m t'
  · exact hcur_y2 t'.val t'.isLt t'.isLt

private theorem exec_heldKarpCode {w : ℕ} (I : Instance) (hw : I.FitsWidth w) :
    ∃ z, ExecWithin w heldKarpCode (.init I.encode) z (80 * (I.n ^ 2 * 2 ^ I.n + 1) - 1) ∧
      z.regs rBest = heldKarp I.dist := by
  obtain ⟨hwS, hwV⟩ := hw
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  obtain ⟨s0, he_setup, hfix0, hdist0, htab0, hmask0, hmb0⟩ := exec_setup I ⟨hwS, hwV⟩
  let PMask (m : ℕ) (s : Data 18) : Prop :=
    1 ≤ m ∧ FixedRegs I s ∧ DistIntact I s.mem ∧ TableInv I m s.mem ∧
      s.regs rMaskBase = dp0 + m * (I.n + 1)
  have hloop_mask := ExecWithin.loop_count (w := w) (N := 2 ^ I.n)
    (T := (I.n + 1) * (22 * I.n + 13) + 5)
    (index := rMask) (limit := rPowN) (body := maskStep) PMask
    (fun y hy => hy.2.1.powN)
    (fun y ⟨hym_ge, hyfix, hydist, hytab, hymb⟩ hlt => by
      obtain ⟨y3, he_y3, hm1, hfix3, hdist3, htab3, hmb3, hm3⟩ :=
        exec_maskStep I ⟨hwS, hwV⟩ (by omega) hlt y hyfix hydist hytab rfl hymb
      exact ⟨y3, he_y3, ⟨hm1, hfix3, hdist3, htab3, hmb3⟩, hm3⟩)
    (by rw [hmask0]; exact Nat.one_le_two_pow)
    (by rw [hmask0]; exact ⟨le_rfl, hfix0, hdist0, htab0, by simpa using hmb0⟩)
  rw [hmask0] at hloop_mask
  obtain ⟨sf, he_mask, ⟨-, hfixf, -, htabf, hmbf⟩, -⟩ := hloop_mask
  have hsub_final : dp0 + 2 ^ I.n * (I.n + 1) - (I.n + 1) =
      dp0 + (2 ^ I.n - 1) * (I.n + 1) := by
    rw [Nat.sub_mul, one_mul, Nat.add_sub_assoc (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)]
  have hfinal_least := htabf (2 ^ I.n - 1) (Nat.sub_lt Nat.one_le_two_pow Nat.one_pos) 0
  simp only [maskSet_two_pow_sub_one, Fin.val_zero, Nat.add_zero] at hfinal_least
  have hans_eq : sf.mem (dp0 + (2 ^ I.n - 1) * (I.n + 1)) = heldKarp I.dist :=
    hfinal_least.unique (isLeast_heldKarp I.dist)
  have hfit_final : Fits w (dp0 + (2 ^ I.n - 1) * (I.n + 1)) :=
    fit_table_cell hwS (Nat.sub_lt Nat.one_le_two_pow Nat.one_pos) (Nat.succ_pos _)
  obtain ⟨z, he_fin, hz_best⟩ :
      ∃ z, ExecWithin w finalReadCode sf z 2 ∧ z.regs rBest = heldKarp I.dist := by
    dsimp [finalReadCode]
    wram_exec [hmbf, hfixf.N_eq, hsub_final, hans_eq]
    wram_simp [hmbf, hfixf.N_eq, hsub_final, hans_eq]
  refine ⟨z, (he_setup.seq (he_mask.seq he_fin)).mono ?_, hz_best⟩
  rcases Nat.eq_zero_or_pos I.n with hn0 | hn_pos
  · simp [hn0]
  · have h1 := Nat.mul_le_mul_left (2 ^ I.n - 1)
      (show (I.n + 1) * (22 * I.n + 13) + 5 + 2 ≤ 77 * I.n ^ 2 by nlinarith only [hn_pos])
    have h2 : (2 ^ I.n - 1) * (77 * I.n ^ 2) + 77 * I.n ^ 2 = 77 * (I.n ^ 2 * 2 ^ I.n) := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel Nat.one_le_two_pow]
      ring
    have h3 : 15 * I.n + 34 ≤ 77 * I.n ^ 2 := by nlinarith only [hn_pos]
    exact Nat.le_sub_one_of_lt (by omega)

/-! ## Public running-time theorems -/

/-- `program` computes `heldKarp I.dist` in at most `80 (n² · 2ⁿ + 1)` standard-basis instructions
at every fitting word width. -/
theorem computesInTime_program :
    program.ComputesInTime (fun _ => Instance.encode)
      (fun I _ => 80 * (I.n ^ 2 * 2 ^ I.n + 1))
      Instance.FitsWidth (fun I => heldKarp I.dist) := by
  exact (heldKarpCode.computesInTime_program rBest
    (encode := fun _ => Instance.encode)
    (time := fun I _ => 80 * (I.n ^ 2 * 2 ^ I.n + 1) - 1)
    fun I w hw _ => exec_heldKarpCode I hw).mono
    (fun _ _ => by omega) (fun _ _ h => h)

/-- **Word-RAM Bellman–Held–Karp execution bound** [Bellman1962] [HeldKarp1962]. At every fitting
word width `w`, `program` halts on `State.init I.encode` with `heldKarp I.dist` within
`80 (n² · 2ⁿ + 1)` standard-basis instructions. -/
theorem executes_program {I : Instance} {w : ℕ} (hw : I.FitsWidth w) :
    ∃ m ≤ 80 * (I.n ^ 2 * 2 ^ I.n + 1),
      Executes w program (.init I.encode) (heldKarp I.dist) m :=
  (computesInTime_program I w hw hw.inputFits).imp fun _ ⟨hexec, hm⟩ => ⟨hm, hexec⟩

/-- Uniform standard-basis Word-RAM computability of Bellman–Held–Karp optimal tour cost in
`80 (n² · 2ⁿ + 1)` instructions. -/
theorem uniformComputableInTime_heldKarp :
    UniformComputableInTime .standard (fun I : Instance => heldKarp I.dist)
      (fun _ => Instance.encode)
      (fun I _ => 80 * (I.n ^ 2 * 2 ^ I.n + 1))
      Instance.FitsWidth :=
  ⟨18, program, computesInTime_program, Instance.inputAdmissible⟩

/-- Uniform `O(n² · 2ⁿ)` standard-basis Word-RAM running time for Bellman–Held–Karp optimal tour
cost in the number `I.n` of non-origin cities. -/
theorem uniformComputableInO_heldKarp :
    UniformComputableInO .standard (fun I : Instance => heldKarp I.dist)
      (fun _ => Instance.encode) Instance.n
      (fun n _ => n ^ 2 * 2 ^ n) Instance.FitsWidth := by
  refine ⟨fun I _ => 80 * (I.n ^ 2 * 2 ^ I.n + 1), uniformComputableInTime_heldKarp,
    160, 1, by omega, fun I _ hn _ => ?_⟩
  nlinarith [Nat.one_le_two_pow (n := I.n)]

end Cslib.Algorithms.WordRAM.HeldKarp
