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
import CslibFrontier.Foundations.Data.List.RowMajor
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

private theorem length_flatMap_dist (I : Instance) :
    ((List.finRange (I.n + 1)).flatMap fun i =>
      (List.finRange (I.n + 1)).map fun j => I.dist i j).length = (I.n + 1) * (I.n + 1) := by
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

theorem encode_length (I : Instance) :
    I.encode.length = 1 + (I.n + 1) * (I.n + 1) := by
  rw [encode, List.length_cons, length_flatMap_dist]
  omega

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
  refine ⟨h.1.of_le ?_, fun v hv => ?_⟩
  · rw [I.encode_length, spaceBound]
    have := Nat.one_le_two_pow (n := I.n)
    nlinarith
  · rw [encode, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h.1.of_le (by
        rw [spaceBound]
        have := Nat.one_le_two_pow (n := I.n)
        nlinarith)
    · rw [List.mem_flatMap] at hv
      obtain ⟨i, -, hj⟩ := hv
      rw [List.mem_map] at hj
      obtain ⟨j, -, rfl⟩ := hj
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
  by_contra hall
  push Not at hall
  have hzero : mask = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.zero_testBit]
    by_cases hk : k < n
    · have := hall ⟨k, hk⟩
      cases h : mask.testBit k <;> simp_all
    · exact Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  omega

private theorem and_two_pow_pos_iff (mask i : ℕ) :
    0 < mask &&& 2 ^ i ↔ mask.testBit i = true := by
  constructor
  · intro h
    by_contra hfalse
    have hf : mask.testBit i = false := by cases hm : mask.testBit i <;> simp_all
    have hz : mask &&& 2 ^ i = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
      by_cases hki : i = k
      · subst hki; simp [hf]
      · simp [hki]
    omega
  · intro h
    refine Nat.pos_of_ne_zero fun hz => ?_
    have := congrArg (fun x => x.testBit i) hz
    simp [Nat.testBit_and, h] at this

private theorem two_pow_le_of_testBit {mask i : ℕ} (h : mask.testBit i = true) :
    2 ^ i ≤ mask := by
  by_contra hlt
  push Not at hlt
  have := Nat.testBit_lt_two_pow hlt
  simp [h] at this

private theorem sub_two_pow_testBit {mask i : ℕ} (h : mask.testBit i = true) (k : ℕ) :
    (mask - 2 ^ i).testBit k = (if k = i then false else mask.testBit k) := by
  have hdiv_odd : (mask / 2 ^ i) % 2 = 1 := by
    have h0 := Nat.testBit_zero (mask / 2 ^ i)
    rw [← Nat.testBit_add mask 0 i, Nat.zero_add, h] at h0
    simpa [Nat.mod_two_not_eq_zero] using h0.symm
  let lo := mask % 2 ^ i
  let q := mask / 2 ^ i
  let r := q / 2
  have hlo : lo < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  have hq : q = 1 + 2 * r := by dsimp [q, r]; omega
  have hmask : mask = lo + 2 ^ i * (1 + 2 * r) := by
    have hdm : 2 ^ i * q + lo = mask := Nat.div_add_mod mask (2 ^ i)
    rw [← hdm, hq]
    ring
  have hsub : mask - 2 ^ i = lo + 2 ^ i * (2 * r) := by
    rw [hmask, Nat.mul_add, Nat.mul_one]
    omega
  rcases lt_trichotomy k i with hlt | heq | hgt
  · rw [ite_eq_right hlt.ne]
    have hm1 : (mask - 2 ^ i) % 2 ^ i = lo := by
      rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    have hm2 : mask % 2 ^ i = lo := rfl
    have hb1 := Nat.testBit_mod_two_pow (mask - 2 ^ i) i k
    have hb2 := Nat.testBit_mod_two_pow mask i k
    simp only [hlt, decide_true, Bool.true_and] at hb1 hb2
    rw [← hb1, hm1, ← hm2, hb2]
  · subst heq
    simp only [↓reduceIte]
    have hdiv_sub : (mask - 2 ^ k) / 2 ^ k = 2 * r := by
      have heq' : mask - 2 ^ k = lo + (2 * r) * 2 ^ k := by rw [hsub]; ring
      rw [heq', Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlo, zero_add]
    have ht0 := Nat.testBit_add (mask - 2 ^ k) 0 k
    rw [Nat.zero_add, hdiv_sub] at ht0
    rw [ht0]
    simp
  · rw [ite_eq_right hgt.ne']
    obtain ⟨d, rfl⟩ : ∃ d, k = (i + 1) + d := ⟨k - (i + 1), by omega⟩
    have hd1 : (mask - 2 ^ i) / (2 ^ i * 2) = r := by
      have heq' : mask - 2 ^ i = lo + r * (2 ^ i * 2) := by rw [hsub]; ring
      have hlo2 : lo < 2 ^ i * 2 := by omega
      rw [heq', Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlo2, zero_add]
    have hd2 : mask / (2 ^ i * 2) = r := by
      have heq' : mask = (lo + 2 ^ i) + r * (2 ^ i * 2) := by rw [hmask]; ring
      have hlo2 : lo + 2 ^ i < 2 ^ i * 2 := by omega
      rw [heq', Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlo2, zero_add]
    rw [show (i + 1) + d = d + (i + 1) by omega, Nat.testBit_add, Nat.testBit_add,
      pow_succ, hd1, hd2]

private theorem maskSet_sub_two_pow {n mask : ℕ} {i : Fin n} (h : mask.testBit i.val = true) :
    maskSet n (mask - 2 ^ i.val) = (maskSet n mask).erase i := by
  ext j
  simp only [mem_maskSet, Finset.mem_erase, sub_two_pow_testBit h]
  by_cases hji : j = i
  · subst hji; simp
  · have hval : j.val ≠ i.val := fun hv => hji (Fin.ext hv)
    simp [hji, hval]

private theorem walkCost_le_mul_maxEntry (I : Instance) (a : Fin (I.n + 1))
    (L : List (Fin (I.n + 1))) (b : Fin (I.n + 1)) :
    walkCost I.dist a L b ≤ (L.length + 1) * I.maxEntry := by
  induction L generalizing a with
  | nil =>
    simpa [walkCost] using I.dist_le_maxEntry a b
  | cons x L ih =>
    simp only [walkCost, List.length_cons]
    have hx := I.dist_le_maxEntry a x
    have hL := ih x
    nlinarith

private theorem isLeast_walkCosts_le (I : Instance) {S : Finset (Fin I.n)} {t : Fin (I.n + 1)}
    {v : ℕ} (hv : IsLeast (walkCosts I.dist S t) v) :
    v ≤ (S.card + 1) * I.maxEntry := by
  obtain ⟨⟨L, hnd, hL, rfl⟩, -⟩ := hv
  have hcard : S.card = L.length := by
    rw [← hL, List.toFinset_card_of_nodup hnd]
  rw [hcard, ← List.length_map (f := Fin.succ)]
  exact walkCost_le_mul_maxEntry I 0 (L.map Fin.succ) t

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
  have hyz := hyfix.zero; have hyo := hyfix.one; have hyn := hyfix.n_eq
  have hyN := hyfix.N_eq; have hydb := hyfix.distB; have hydp := hyfix.dpB
  have hypow := hyfix.powN
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
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · wram_simp [hyz]
  · wram_simp [hyo]
  · wram_simp [hyn]
  · wram_simp [hyN]
  · wram_simp [hydb]
  · wram_simp [hydp]
  · wram_simp [hypow]
  · intro a ha
    wram_simp [hydp]
    exact hylow a ha
  · intro j hj hjlt
    by_cases hjeq : j = y.regs rT
    · subst hjeq; wram_simp [hydb, hydp, hsrc_mem]
    · wram_simp [hydb, hydp, hsrc_mem]
      exact hywr j (by omega) hjlt
  · wram_simp [hyo]

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
      refine ⟨⟨hym, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · wram_simp [hyz]
      · wram_simp [hyo]
      · wram_simp [hyn]
      · wram_simp [hyN]
      · wram_simp [hydb]
      · wram_simp [hydp, hyN]; ring
      · wram_simp [hyo])
    (by rw [ht1]; omega)
    (by rw [ht1]; exact ⟨rfl, hz1, ho1, hn1, hN1, hdb1, by simp [hdp1]⟩)
  rw [ht1, Nat.sub_zero] at hloop1
  obtain ⟨s2, he2, ⟨hm2, hz2, ho2, hn2, hN2, hdb2, hdp2⟩, -⟩ := hloop1
  have h3 : ∃ s3, ExecWithin w setupPowInit s2 s3 2 ∧
      s3.mem = s1.mem ∧ s3.regs rZero = 0 ∧ s3.regs rOne = 1 ∧ s3.regs rn = I.n ∧
      s3.regs rN = I.n + 1 ∧ s3.regs rDistBase = 2 ∧
      s3.regs rDpBase = 2 + (I.n + 1) * (I.n + 1) ∧ s3.regs rPowN = 1 ∧ s3.regs rI = 0 := by
    have hfit1 : Fits w 1 := hwS.of_le (by rw [Instance.spaceBound]; omega)
    dsimp [setupPowInit]
    wram_exec
    refine ⟨hm2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp [hz2, ho2, hn2, hN2, hdb2, hdp2]
  obtain ⟨s3, he3, hm3, hz3, ho3, hn3, hN3, hdb3, hdp3, hpow3, hi3⟩ := h3
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
      refine ⟨⟨hym, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · wram_simp [hyz]
      · wram_simp [hyo]
      · wram_simp [hyn]
      · wram_simp [hyN]
      · wram_simp [hydb]
      · wram_simp [hydp]
      · wram_simp [hypow]; ring
      · wram_simp [hyo])
    (by rw [hi3]; omega)
    (by rw [hi3]; exact ⟨hm3, hz3, ho3, hn3, hN3, hdb3, hdp3, by simp [hpow3]⟩)
  rw [hi3, Nat.sub_zero] at hloop2
  obtain ⟨s4, he4, ⟨hm4, hz4, ho4, hn4, hN4, hdb4, hdp4, hpow4⟩, -⟩ := hloop2
  have h5 : ∃ s5, ExecWithin w maskZeroT s4 s5 1 ∧
      s5.mem = s1.mem ∧ FixedRegs I s5 ∧ s5.regs rT = 0 := by
    dsimp [maskZeroT]
    wram_exec [hz4]
    refine ⟨hm4, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      wram_simp [hz4, ho4, hn4, hN4, hdb4, hdp4, hpow4]
  obtain ⟨s5, he5, hm5, hfix5, ht5⟩ := h5
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
  have h7 : ∃ s7, ExecWithin w setupMaskInit s6 s7 2 ∧
      s7.mem = s6.mem ∧ FixedRegs I s7 ∧ s7.regs rMask = 1 ∧
      s7.regs rMaskBase = dp0 + (I.n + 1) := by
    have hz6 := hfix6.zero; have ho6 := hfix6.one; have hn6 := hfix6.n_eq
    have hN6 := hfix6.N_eq; have hdb6 := hfix6.distB; have hdp6 := hfix6.dpB
    have hpow6 := hfix6.powN
    have hfit1 : Fits w 1 := hwS.of_le (by rw [Instance.spaceBound]; omega)
    have hfit_mb : Fits w (dp0 + (I.n + 1)) :=
      hwS.of_le (by rw [Instance.spaceBound]; dsimp [dp0]; nlinarith only [hpow1])
    dsimp [dp0, setupMaskInit]
    wram_exec [hdp6, hN6]
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      wram_simp [hz6, ho6, hn6, hN6, hdb6, hdp6, hpow6]
  obtain ⟨s7, he7, hm7, hfix7, hmask7, hmb7⟩ := h7
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
  ext i
  simp [PrefixSet]

private theorem prefixSet_full (I : Instance) (mask : ℕ) :
    PrefixSet I mask I.n = maskSet I.n mask := by
  ext i
  simp [PrefixSet, maskSet]

private theorem exec_innerBitPost {w : ℕ} (I : Instance) (hwS : Fits w I.spaceBound)
    (mask k : ℕ) (hk : k < I.n) (t : Fin (I.n + 1))
    (s : Data 18) (hfix : FixedRegs I s)
    (hmask_reg : s.regs rMask = mask)
    (hmb_reg : s.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1))
    (ht_reg : s.regs rT = t.val) (hi_reg : s.regs rI = k)
    (hbit_reg : s.regs rBit = 2 ^ k) (hbs_reg : s.regs rBitStride = 2 ^ k * (I.n + 1))
    (hrd_reg : s.regs rRowDist = 2 + (k + 1) * (I.n + 1)) :
    ∃ z, ExecWithin w innerBitPost s z 4 ∧
      z.mem = s.mem ∧
      FixedRegs I z ∧
      z.regs rMask = mask ∧
      z.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) ∧
      z.regs rT = t.val ∧
      z.regs rI = k + 1 ∧
      z.regs rBit = 2 ^ (k + 1) ∧
      z.regs rBitStride = 2 ^ (k + 1) * (I.n + 1) ∧
      z.regs rRowDist = 2 + (k + 2) * (I.n + 1) ∧
      z.regs rHasBest = s.regs rHasBest ∧
      z.regs rBest = s.regs rBest := by
  have hz := hfix.zero; have ho := hfix.one; have hn := hfix.n_eq
  have hN := hfix.N_eq; have hdb := hfix.distB; have hdp := hfix.dpB; have hpow := hfix.powN
  have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hpow_le : 2 ^ (k + 1) ≤ 2 ^ I.n := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow_mul : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hfit_k1 : Fits w (k + 1) :=
    hwS.of_le (by rw [Instance.spaceBound]; nlinarith only [hk, hpow1])
  have hfit_bit2 : Fits w (2 ^ k + 2 ^ k) :=
    hwS.of_le (by rw [Instance.spaceBound, ← two_mul, mul_comm, ← pow_succ]; omega)
  have hfit_bs2 : Fits w (2 ^ k * (I.n + 1) + 2 ^ k * (I.n + 1)) :=
    hwS.of_le (by
      have : 2 ^ k * (I.n + 1) + 2 ^ k * (I.n + 1) = 2 ^ (k + 1) * (I.n + 1) := by ring
      rw [this, Instance.spaceBound]; nlinarith only [hpow_le])
  have hfit_rd : Fits w (2 + (k + 1) * (I.n + 1) + (I.n + 1)) :=
    hwS.of_le (by rw [Instance.spaceBound]; nlinarith only [hk, hpow1])
  dsimp [innerBitPost]
  wram_exec [hi_reg, ho, hbit_reg, hbs_reg, hrd_reg, hN]
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · wram_simp [hz]
  · wram_simp [ho]
  · wram_simp [hn]
  · wram_simp [hN]
  · wram_simp [hdb]
  · wram_simp [hdp]
  · wram_simp [hpow]
  · wram_simp [hmask_reg]
  · wram_simp [hmb_reg]
  · wram_simp [ht_reg]
  · wram_simp [hi_reg, ho]
  · wram_simp [hbit_reg]; ring
  · wram_simp [hbs_reg]; ring
  · wram_simp [hrd_reg, hN]; ring
  · wram_simp
  · wram_simp

private theorem exec_relaxLoad {w : ℕ} (I : Instance) (hw : I.FitsWidth w)
    {mask k : ℕ} (hk : k < I.n) (hbit_le : 2 ^ k ≤ mask) (hlt_mask : mask < 2 ^ I.n)
    (t : Fin (I.n + 1)) (s1 : Data 18)
    (hmb_reg : s1.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1))
    (hbs_reg : s1.regs rBitStride = 2 ^ k * (I.n + 1))
    (hi_reg : s1.regs rI = k) (ho : s1.regs rOne = 1)
    (hrd_reg : s1.regs rRowDist = 2 + (k + 1) * (I.n + 1))
    (ht_reg : s1.regs rT = t.val)
    (hdist_val : s1.mem (2 + (k + 1) * (I.n + 1) + t.val) = I.dist ⟨k + 1, by omega⟩ t)
    (hle_cand : s1.mem (2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ k) * (I.n + 1) + (k + 1)) +
      I.dist ⟨k + 1, by omega⟩ t ≤ (I.n + 1) * I.maxEntry) :
    ∃ s2, ExecWithin w relaxLoad s1 s2 7 ∧
      s2.mem = s1.mem ∧
      (∀ r : Fin 18, r ≠ rTmp0 → r ≠ rTmp1 → s2.regs r = s1.regs r) ∧
      s2.regs rTmp0 = s1.mem (2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ k) * (I.n + 1) + (k + 1)) +
        I.dist ⟨k + 1, by omega⟩ t := by
  obtain ⟨hwS, hwV⟩ := hw
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hm_sub : mask - 2 ^ k + 1 ≤ 2 ^ I.n := by
    have := Nat.two_pow_pos k
    omega
  have hm_mul : (mask - 2 ^ k) * (I.n + 1) + (I.n + 1) ≤ 2 ^ I.n * (I.n + 1) := by
    calc (mask - 2 ^ k) * (I.n + 1) + (I.n + 1)
        = (mask - 2 ^ k + 1) * (I.n + 1) := by ring
      _ ≤ 2 ^ I.n * (I.n + 1) := Nat.mul_le_mul_right _ hm_sub
  have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
  have hrow_le : (k + 1) * (I.n + 1) + t.val ≤ (I.n + 1) * (I.n + 1) := by
    have h1 : (k + 1) * (I.n + 1) + t.val ≤ (k + 1) * (I.n + 1) + (I.n + 1) := by omega
    calc (k + 1) * (I.n + 1) + t.val
        ≤ (k + 2) * (I.n + 1) := by linarith only [h1]
      _ ≤ (I.n + 1) * (I.n + 1) := Nat.mul_le_mul_right _ (by omega)
  have hfit_prev1 : Fits w ((dp0 + (mask - 2 ^ k) * (I.n + 1)) + k) :=
    hwS.of_le (by rw [Instance.spaceBound]; dsimp [dp0]; omega)
  have hfit_prev2 : Fits w ((dp0 + (mask - 2 ^ k) * (I.n + 1) + k) + 1) :=
    hwS.of_le (by rw [Instance.spaceBound]; dsimp [dp0]; omega)
  have hfit_dist : Fits w (2 + (k + 1) * (I.n + 1) + t.val) :=
    hwS.of_le (by rw [Instance.spaceBound]; omega)
  have hfit_cand : Fits w _ := hwV.of_le hle_cand
  have hmb_le : 2 ^ k * (I.n + 1) ≤ 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) := by
    have := Nat.mul_le_mul_right (I.n + 1) hbit_le
    omega
  have hsub_addr : 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) - 2 ^ k * (I.n + 1) =
      2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ k) * (I.n + 1) := by
    have : 2 ^ k * (I.n + 1) ≤ mask * (I.n + 1) := Nat.mul_le_mul_right _ hbit_le
    rw [Nat.sub_mul]
    omega
  dsimp [relaxLoad]
  wram_exec [hmb_reg, hbs_reg, hi_reg, ho, hrd_reg, ht_reg]
  · refine ⟨rfl, fun r hr0 hr1 => ?_, ?_⟩
    · simp [Data.set, hr0, hr1]
    · wram_simp [hmb_reg, hbs_reg, hi_reg, ho, hrd_reg, ht_reg]
      rw [hsub_addr, Nat.add_assoc _ k 1, hdist_val]
  · rw [hsub_addr, Nat.add_assoc _ k 1, hdist_val]
    exact hfit_cand

private theorem exec_innerBitStep {w : ℕ} (I : Instance) (hw : I.FitsWidth w)
    {mask : ℕ} (_hmask_pos : 0 < mask) (hmask_lt : mask < 2 ^ I.n) (t : Fin (I.n + 1))
    (s : Data 18) (hfix : FixedRegs I s) (hdist : DistIntact I s.mem)
    (htab : TableInv I mask s.mem)
    (hmask_reg : s.regs rMask = mask)
    (hmb_reg : s.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1))
    (ht_reg : s.regs rT = t.val)
    {k : ℕ} (hk : k < I.n)
    (hi_reg : s.regs rI = k)
    (hbit_reg : s.regs rBit = 2 ^ k)
    (hbs_reg : s.regs rBitStride = 2 ^ k * (I.n + 1))
    (hrd_reg : s.regs rRowDist = 2 + (k + 1) * (I.n + 1))
    (hbest_inv :
      let cand (j : Fin I.n) :=
        s.mem (2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)) +
          I.dist j.succ t
      if (PrefixSet I mask k).Nonempty then
        s.regs rHasBest = 1 ∧
          (∀ j ∈ PrefixSet I mask k, s.regs rBest ≤ cand j) ∧
          ∃ j ∈ PrefixSet I mask k, s.regs rBest = cand j
      else
        s.regs rHasBest = 0) :
    ∃ z, ExecWithin w innerBitStep s z 20 ∧
      z.mem = s.mem ∧
      FixedRegs I z ∧
      z.regs rMask = mask ∧
      z.regs rMaskBase = 2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) ∧
      z.regs rT = t.val ∧
      z.regs rI = k + 1 ∧
      z.regs rBit = 2 ^ (k + 1) ∧
      z.regs rBitStride = 2 ^ (k + 1) * (I.n + 1) ∧
      z.regs rRowDist = 2 + (k + 2) * (I.n + 1) ∧
      (let cand (j : Fin I.n) :=
        z.mem (2 + (I.n + 1) * (I.n + 1) + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)) +
          I.dist j.succ t
      if (PrefixSet I mask (k + 1)).Nonempty then
        z.regs rHasBest = 1 ∧
          (∀ j ∈ PrefixSet I mask (k + 1), z.regs rBest ≤ cand j) ∧
          ∃ j ∈ PrefixSet I mask (k + 1), z.regs rBest = cand j
      else
        z.regs rHasBest = 0) := by
  obtain ⟨hwS, hwV⟩ := hw
  have hz := hfix.zero; have ho := hfix.one; have hn := hfix.n_eq
  have hN := hfix.N_eq; have hdb := hfix.distB; have hdp := hfix.dpB; have hpow := hfix.powN
  let dp0 := 2 + (I.n + 1) * (I.n + 1)
  let cand (j : Fin I.n) :=
    s.mem (dp0 + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)) + I.dist j.succ t
  have hfit_and : Fits w (mask &&& 2 ^ k) := by
    refine hwS.of_le ((Nat.and_le_left ..).trans ?_)
    have hpow_mul : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    rw [Instance.spaceBound]
    omega
  have hand_step : ∃ s1, ExecWithin w innerBitPre s s1 1 ∧
      s1 = s.set rTmp0 (mask &&& 2 ^ k) := by
    dsimp [innerBitPre]
    wram_exec [hmask_reg, hbit_reg]
    rfl
  obtain ⟨s1, he_and, hs1⟩ := hand_step
  have hs3_step : ∃ s3, ExecWithin w (.branch (.lt rZero rTmp0) relaxThen nop) s1 s3 14 ∧
      s3.mem = s.mem ∧
      FixedRegs I s3 ∧
      s3.regs rMask = mask ∧
      s3.regs rMaskBase = dp0 + mask * (I.n + 1) ∧
      s3.regs rT = t.val ∧
      s3.regs rI = k ∧
      s3.regs rBit = 2 ^ k ∧
      s3.regs rBitStride = 2 ^ k * (I.n + 1) ∧
      s3.regs rRowDist = 2 + (k + 1) * (I.n + 1) ∧
      (if (PrefixSet I mask (k + 1)).Nonempty then
        s3.regs rHasBest = 1 ∧
          (∀ j ∈ PrefixSet I mask (k + 1), s3.regs rBest ≤ cand j) ∧
          ∃ j ∈ PrefixSet I mask (k + 1), s3.regs rBest = cand j
      else
        s3.regs rHasBest = 0) := by
    by_cases hbit : mask.testBit k = true
    · have hand_pos : 0 < mask &&& 2 ^ k := (and_two_pow_pos_iff mask k).2 hbit
      have hbit_le : 2 ^ k ≤ mask := two_pow_le_of_testBit hbit
      have hprev_lt : mask - 2 ^ k < mask := by
        have := Nat.two_pow_pos k
        omega
      let ik : Fin I.n := ⟨k, hk⟩
      have hprev_least := htab (mask - 2 ^ k) hprev_lt ik.succ
      have hprev_val_le :
          s.mem (dp0 + (mask - 2 ^ k) * (I.n + 1) + (k + 1)) ≤ I.n * I.maxEntry := by
        have hcard_le : (maskSet I.n (mask - 2 ^ k)).card + 1 ≤ I.n := by
          rw [maskSet_sub_two_pow (i := ik) hbit, Finset.card_erase_of_mem (mem_maskSet.2 hbit)]
          have hle_univ : (maskSet I.n mask).card ≤ Fintype.card (Fin I.n) := Finset.card_le_univ _
          have hpos_card : 1 ≤ (maskSet I.n mask).card :=
            Finset.card_pos.2 ⟨ik, mem_maskSet.2 hbit⟩
          rw [Fintype.card_fin] at hle_univ
          omega
        exact (isLeast_walkCosts_le I hprev_least).trans (Nat.mul_le_mul_right _ hcard_le)
      have hcand_le : cand ik ≤ (I.n + 1) * I.maxEntry := by
        dsimp [cand, ik]
        have hd_le := I.dist_le_maxEntry ⟨k + 1, by omega⟩ t
        nlinarith only [hprev_val_le, hd_le]
      have hload : ∃ s2, ExecWithin w relaxLoad s1 s2 7 ∧
          s2.mem = s.mem ∧
          (∀ r : Fin 18, r ≠ rTmp0 → r ≠ rTmp1 → s2.regs r = s.regs r) ∧
          s2.regs rTmp0 = cand ik := by
        have hm1 : s1.mem = s.mem := by simp [hs1]
        have hmb1 : s1.regs rMaskBase = dp0 + mask * (I.n + 1) := by
          rw [hs1, Data.set_regs_of_ne (by decide), hmb_reg]
        have hbs1 : s1.regs rBitStride = 2 ^ k * (I.n + 1) := by
          rw [hs1, Data.set_regs_of_ne (by decide), hbs_reg]
        have hi1 : s1.regs rI = k := by
          rw [hs1, Data.set_regs_of_ne (by decide), hi_reg]
        have ho1 : s1.regs rOne = 1 := by
          rw [hs1, Data.set_regs_of_ne (by decide), ho]
        have hrd1 : s1.regs rRowDist = 2 + (k + 1) * (I.n + 1) := by
          rw [hs1, Data.set_regs_of_ne (by decide), hrd_reg]
        have ht1 : s1.regs rT = t.val := by
          rw [hs1, Data.set_regs_of_ne (by decide), ht_reg]
        have hdist1 : s1.mem (2 + (k + 1) * (I.n + 1) + t.val) = I.dist ik.succ t := by
          rw [hm1]; exact hdist ik.succ t
        have hcand1 : s1.mem (dp0 + (mask - 2 ^ k) * (I.n + 1) + (k + 1)) +
            I.dist ik.succ t ≤ (I.n + 1) * I.maxEntry := by
          rw [hm1]; exact hcand_le
        obtain ⟨s2, he2, hm2, hr2, htmp2⟩ := exec_relaxLoad I ⟨hwS, hwV⟩ hk hbit_le hmask_lt t s1
          hmb1 hbs1 hi1 ho1 hrd1 ht1 hdist1 hcand1
        refine ⟨s2, he2, hm2.trans hm1, fun r hr0 hr1 => ?_, ?_⟩
        · rw [hr2 r hr0 hr1, hs1]
          simp [Data.set, hr0]
        · rw [htmp2, hm1]; rfl
      obtain ⟨s2, he_load, hm2, hr2, hcand2⟩ := hload
      have hupd : ∃ s3, ExecWithin w relaxUpd s2 s3 6 ∧
          s3.mem = s.mem ∧
          (∀ r : Fin 18, r ≠ rBest → r ≠ rHasBest → r ≠ rTmp0 → r ≠ rTmp1 →
            s3.regs r = s.regs r) ∧
          s3.regs rHasBest = 1 ∧
          (∀ j ∈ PrefixSet I mask (k + 1), s3.regs rBest ≤ cand j) ∧
          ∃ j ∈ PrefixSet I mask (k + 1), s3.regs rBest = cand j := by
        have hz2 : s2.regs rZero = 0 := (hr2 rZero (by decide) (by decide)).trans hz
        have hhb2 : s2.regs rHasBest = s.regs rHasBest := hr2 rHasBest (by decide) (by decide)
        have hrb2 : s2.regs rBest = s.regs rBest := hr2 rBest (by decide) (by decide)
        have hpow1 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
        have hfit1 : Fits w 1 := hwS.of_le (by rw [Instance.spaceBound]; omega)
        have hik_mem : ik ∈ PrefixSet I mask (k + 1) := by
          simp [PrefixSet, ik, hbit]
        have hmem_split : ∀ j ∈ PrefixSet I mask (k + 1), j ∈ PrefixSet I mask k ∨ j = ik := by
          intro j hj
          simp only [PrefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj.1) with hlt' | heq'
          · exact Or.inl ⟨hlt', hj.2⟩
          · exact Or.inr (Fin.ext heq')
        by_cases hne : (PrefixSet I mask k).Nonempty
        · simp only [hne, ↓reduceIte] at hbest_inv
          obtain ⟨hhb_one, hle_prev, j₀, hj₀_mem, hj₀_eq⟩ := hbest_inv
          have hcond_f : ¬Cond.Holds (.eq rHasBest rZero) s2 := by
            simp [Cond.Holds, hhb2, hhb_one, hz2]
          have hj₀_mem' : j₀ ∈ PrefixSet I mask (k + 1) := by
            simp only [PrefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj₀_mem ⊢
            exact ⟨by omega, hj₀_mem.2⟩
          by_cases hlt_c : cand ik < s.regs rBest
          · have hcond_lt : Cond.Holds (.lt rTmp0 rBest) s2 := by
              simp [Cond.Holds, hcand2, hrb2, hlt_c]
            let setB : Code .standard 18 := ram[ rBest ← rTmp0 ]
            have hstep_b : ∃ s3, ExecWithin w setB s2 s3 1 ∧ s3 = s2.set rBest (cand ik) := by
              dsimp [setB]
              wram_exec [hcand2]
              rfl
            obtain ⟨s3, he_b, rfl⟩ := hstep_b
            refine ⟨s2.set rBest (cand ik),
              (ExecWithin.branch_neg hcond_f (ExecWithin.branch_pos hcond_lt he_b)).mono (by omega),
              hm2, fun r hrb hrh hr0 hr1 => by simp [Data.set, hrb, hr2 r hr0 hr1],
              by rw [Data.set_regs_of_ne (by decide), hhb2, hhb_one],
              fun j hj => ?_, ⟨ik, hik_mem, by simp⟩⟩
            simp only [Data.set_regs_self]
            rcases hmem_split j hj with hj_old | rfl
            · exact hlt_c.le.trans (hle_prev j hj_old)
            · exact le_rfl
          · have hcond_nlt : ¬Cond.Holds (.lt rTmp0 rBest) s2 := by
              simp [Cond.Holds, hcand2, hrb2, hlt_c]
            refine ⟨s2,
              (ExecWithin.branch_neg hcond_f
                (ExecWithin.branch_neg hcond_nlt (exec_nop s2))).mono (by omega),
              hm2, fun r _ _ hr0 hr1 => hr2 r hr0 hr1,
              hhb2.trans hhb_one,
              fun j hj => ?_, ⟨j₀, hj₀_mem', hrb2.trans hj₀_eq⟩⟩
            rw [hrb2]
            rcases hmem_split j hj with hj_old | rfl
            · exact hle_prev j hj_old
            · omega
        · simp only [hne, ↓reduceIte] at hbest_inv
          have hcond_t : Cond.Holds (.eq rHasBest rZero) s2 := by
            simp [Cond.Holds, hhb2, hbest_inv, hz2]
          let initB : Code .standard 18 := ram[ rBest ← rTmp0; rHasBest ← #1 ]
          have hstep_t : ∃ s3, ExecWithin w initB s2 s3 2 ∧
              s3 = (s2.set rBest (cand ik)).set rHasBest 1 := by
            dsimp [initB]
            wram_exec [hcand2]
            rfl
          obtain ⟨s3, he_t, rfl⟩ := hstep_t
          refine ⟨_, (ExecWithin.branch_pos hcond_t he_t).mono (by omega),
            hm2, fun r hrb hrh hr0 hr1 => by simp [Data.set, hrb, hrh, hr2 r hr0 hr1],
            by simp,
            fun j hj => ?_,
            ⟨ik, hik_mem, by rw [Data.set_regs_of_ne (by decide), Data.set_regs_self]⟩⟩
          rcases hmem_split j hj with hj_old | rfl
          · exact absurd ⟨j, hj_old⟩ hne
          · rw [Data.set_regs_of_ne (by decide), Data.set_regs_self]
      obtain ⟨s3, he_upd, hm3, hr3, hhb3, hle3, hex3⟩ := hupd
      have hcond_outer : Cond.Holds (.lt rZero rTmp0) s1 := by
        have hz1 : s1.regs rZero = 0 := by rw [hs1, Data.set_regs_of_ne (by decide), hz]
        have htmp1 : s1.regs rTmp0 = mask &&& 2 ^ k := by simp [hs1]
        simp [Cond.Holds, hz1, htmp1, hand_pos]
      have hne_next : (PrefixSet I mask (k + 1)).Nonempty :=
        ⟨ik, by simp [PrefixSet, ik, hbit]⟩
      refine ⟨s3, (ExecWithin.branch_pos hcond_outer (he_load.seq he_upd)).mono (by omega),
        hm3,
        ⟨(hr3 rZero (by decide) (by decide) (by decide) (by decide)).trans hz,
         (hr3 rOne (by decide) (by decide) (by decide) (by decide)).trans ho,
         (hr3 rn (by decide) (by decide) (by decide) (by decide)).trans hn,
         (hr3 rN (by decide) (by decide) (by decide) (by decide)).trans hN,
         (hr3 rDistBase (by decide) (by decide) (by decide) (by decide)).trans hdb,
         (hr3 rDpBase (by decide) (by decide) (by decide) (by decide)).trans hdp,
         (hr3 rPowN (by decide) (by decide) (by decide) (by decide)).trans hpow⟩,
        (hr3 rMask (by decide) (by decide) (by decide) (by decide)).trans hmask_reg,
        (hr3 rMaskBase (by decide) (by decide) (by decide) (by decide)).trans hmb_reg,
        (hr3 rT (by decide) (by decide) (by decide) (by decide)).trans ht_reg,
        (hr3 rI (by decide) (by decide) (by decide) (by decide)).trans hi_reg,
        (hr3 rBit (by decide) (by decide) (by decide) (by decide)).trans hbit_reg,
        (hr3 rBitStride (by decide) (by decide) (by decide) (by decide)).trans hbs_reg,
        (hr3 rRowDist (by decide) (by decide) (by decide) (by decide)).trans hrd_reg, ?_⟩
      simpa only [hne_next, ↓reduceIte] using ⟨hhb3, hle3, hex3⟩
    · have hbit_f : mask.testBit k = false := by cases hm : mask.testBit k <;> simp_all
      have hand_zero : mask &&& 2 ^ k = 0 := by
        by_contra hnz
        exact hbit ((and_two_pow_pos_iff mask k).1 (Nat.pos_of_ne_zero hnz))
      have hcond_outer : ¬Cond.Holds (.lt rZero rTmp0) s1 := by
        rw [hs1, Cond.Holds, Data.set_regs_of_ne (by decide), hz, Data.set_regs_self, hand_zero]
        simp
      have hpref_eq : PrefixSet I mask (k + 1) = PrefixSet I mask k := by
        ext j
        simp only [PrefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hjlt, hjbit⟩
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hjlt) with hlt' | heq'
          · exact ⟨hlt', hjbit⟩
          · rw [heq', hbit_f] at hjbit; simp at hjbit
        · rintro ⟨hjlt, hjbit⟩
          exact ⟨by omega, hjbit⟩
      subst hs1
      have hfix1 : FixedRegs I (s.set rTmp0 (mask &&& 2 ^ k)) :=
        { zero := by rw [Data.set_regs_of_ne (by decide), hz]
          one := by rw [Data.set_regs_of_ne (by decide), ho]
          n_eq := by rw [Data.set_regs_of_ne (by decide), hn]
          N_eq := by rw [Data.set_regs_of_ne (by decide), hN]
          distB := by rw [Data.set_regs_of_ne (by decide), hdb]
          dpB := by rw [Data.set_regs_of_ne (by decide), hdp]
          powN := by rw [Data.set_regs_of_ne (by decide), hpow] }
      refine ⟨s.set rTmp0 (mask &&& 2 ^ k),
        (ExecWithin.branch_neg hcond_outer (exec_nop _)).mono (by omega),
        rfl, hfix1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Data.set_regs_of_ne (by decide), hmask_reg]
      · rw [Data.set_regs_of_ne (by decide), hmb_reg]
      · rw [Data.set_regs_of_ne (by decide), ht_reg]
      · rw [Data.set_regs_of_ne (by decide), hi_reg]
      · rw [Data.set_regs_of_ne (by decide), hbit_reg]
      · rw [Data.set_regs_of_ne (by decide), hbs_reg]
      · rw [Data.set_regs_of_ne (by decide), hrd_reg]
      · simpa only [hpref_eq, Data.set_regs_of_ne (by decide : rHasBest ≠ rTmp0),
          Data.set_regs_of_ne (by decide : rBest ≠ rTmp0)] using hbest_inv
  obtain ⟨s3, he_ite, hm3, hfix3, hms3, hmbs3, hts3, his3, hbits3, hbss3, hrds3, hbest3⟩ :=
    hs3_step
  obtain ⟨z, he_post, hmz, hfixz, hmz_r, hmbz_r, htz_r, hiz_r, hbitz_r, hbsz_r, hrdz_r,
    hhbz, hrbz⟩ := exec_innerBitPost I hwS mask k hk t s3 hfix3 hms3 hmbs3 hts3 his3 hbits3
      hbss3 hrds3
  refine ⟨z, (he_and.seq (he_ite.seq he_post)).mono (by omega),
    hmz.trans hm3, hfixz, hmz_r, hmbz_r, htz_r, hiz_r, hbitz_r, hbsz_r, hrdz_r, ?_⟩
  simpa only [hmz, hm3, hhbz, hrbz] using hbest3

private theorem fit_table_cell {w : ℕ} {I : Instance} (hwS : Fits w I.spaceBound)
    {mask t : ℕ} (hm : mask < 2 ^ I.n) (ht : t < I.n + 1) :
    Fits w (2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) + t) := by
  refine hwS.of_le ?_
  rw [Instance.spaceBound]
  have h1 : mask + 1 ≤ 2 ^ I.n := hm
  nlinarith

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
  have hz := hst_fix.zero; have ho := hst_fix.one; have hn := hst_fix.n_eq
  have hN := hst_fix.N_eq; have hdb := hst_fix.distB; have hdp := hst_fix.dpB
  have hpow := hst_fix.powN
  have hfit1 : Fits w 1 := by
    refine hwS.of_le ?_
    rw [Instance.spaceBound]
    have := Nat.one_le_two_pow (n := I.n)
    omega
  have hfit_rd0 : Fits w (2 + (I.n + 1)) := by
    refine hwS.of_le ?_
    have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
    have := Nat.one_le_two_pow (n := I.n)
    rw [Instance.spaceBound]
    omega
  have hinit_i : ∃ u0, ExecWithin w targetInit st u0 6 ∧
      u0.mem = st.mem ∧ FixedRegs I u0 ∧ u0.regs rMask = mask ∧
      u0.regs rMaskBase = dp0 + mask * (I.n + 1) ∧ u0.regs rT = tIdx ∧
      u0.regs rI = 0 ∧ u0.regs rBit = 1 ∧ u0.regs rBitStride = I.n + 1 ∧
      u0.regs rRowDist = 2 + (I.n + 1) ∧ u0.regs rHasBest = 0 := by
    dsimp [dp0, targetInit]
    wram_exec [hz, ho, hN, hdb]
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp [hz, ho, hn, hN, hdb, hdp, hpow, hst_m, hst_mb, ht_eq]
  obtain ⟨u0, he_u0, hmu0, hfix_u0, hm_u0, hmb_u0, ht_u0, hi_u0, hbit_u0, hbs_u0,
    hrd_u0, hhb_u0⟩ := hinit_i
  let PBit (k : ℕ) (u : Data 18) : Prop :=
    u.mem = st.mem ∧ FixedRegs I u ∧ u.regs rMask = mask ∧
      u.regs rMaskBase = dp0 + mask * (I.n + 1) ∧ u.regs rT = tFin.val ∧
      u.regs rBit = 2 ^ k ∧ u.regs rBitStride = 2 ^ k * (I.n + 1) ∧
      u.regs rRowDist = 2 + (k + 1) * (I.n + 1) ∧
      (let cand (j : Fin I.n) :=
        u.mem (dp0 + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)) + I.dist j.succ tFin
      if (PrefixSet I mask k).Nonempty then
        u.regs rHasBest = 1 ∧
          (∀ j ∈ PrefixSet I mask k, u.regs rBest ≤ cand j) ∧
          ∃ j ∈ PrefixSet I mask k, u.regs rBest = cand j
      else
        u.regs rHasBest = 0)
  have hloop_i := ExecWithin.loop_count (w := w) (N := I.n) (T := 20)
    (index := rI) (limit := rn) (body := innerBitStep) PBit
    (fun u hu => hu.2.1.n_eq)
    (fun u ⟨hmu, hfix_u, hm_u, hmb_u, ht_u, hbit_u, hbs_u, hrd_u, hinv_u⟩ hk_lt => by
      obtain ⟨u', he_u', hmu', hfix_u', hm_u', hmb_u', ht_u', hi_u', hbit_u', hbs_u',
        hrd_u', hinv_u'⟩ := exec_innerBitStep I ⟨hwS, hwV⟩ hm_pos hlt tFin u hfix_u
        (hmu ▸ hst_dist) (hmu ▸ hst_tab) hm_u hmb_u ht_u hk_lt rfl hbit_u hbs_u hrd_u
        hinv_u
      exact ⟨u', he_u', ⟨hmu'.trans hmu, hfix_u', hm_u', hmb_u', ht_u', hbit_u', hbs_u',
        hrd_u', hinv_u'⟩, hi_u'⟩)
    (by rw [hi_u0]; omega)
    (by
      rw [hi_u0]
      refine ⟨hmu0, hfix_u0, hm_u0, hmb_u0, ht_u0, by simp [hbit_u0], by simp [hbs_u0],
        by simp [hrd_u0], ?_⟩
      simp [prefixSet_zero, hhb_u0])
  rw [hi_u0, Nat.sub_zero] at hloop_i
  obtain ⟨u1, he_u1, ⟨hmu1, hfix_u1, hm_u1, hmb_u1, ht_u1, -, -, -, hinv_u1⟩, -⟩ :=
    hloop_i
  rw [prefixSet_full] at hinv_u1
  obtain ⟨i₀, hi₀⟩ := exists_bit_of_pos_lt hm_pos hlt
  have hne_mask : (maskSet I.n mask).Nonempty := ⟨i₀, mem_maskSet.2 hi₀⟩
  simp only [hne_mask, ↓reduceIte] at hinv_u1
  obtain ⟨-, hle_best, hex_best⟩ := hinv_u1
  have hbest_least : IsLeast (walkCosts I.dist (maskSet I.n mask) tFin) (u1.regs rBest) := by
    refine isLeast_walkCosts_of_forall
      (f := fun j => st.mem (dp0 + (mask - 2 ^ j.val) * (I.n + 1) + (j.val + 1)))
      (fun j hj => ?_) (fun j hj => ?_) ?_
    · have hj_bit := mem_maskSet.1 hj
      rw [← maskSet_sub_two_pow hj_bit]
      have hlt_sub : mask - 2 ^ j.val < mask := by
        have := two_pow_le_of_testBit hj_bit
        have := Nat.two_pow_pos j.val
        omega
      exact hst_tab (mask - 2 ^ j.val) hlt_sub j.succ
    · simpa [hmu1] using hle_best j hj
    · obtain ⟨j, hj, heq⟩ := hex_best
      exact ⟨j, hj, by simpa [hmu1] using heq⟩
  have hstore : ∃ u2, ExecWithin w targetStore u1 u2 3 ∧
      u2.mem = Function.update st.mem (dp0 + mask * (I.n + 1) + tIdx)
        (u1.regs rBest) ∧
      FixedRegs I u2 ∧ u2.regs rMask = mask ∧
      u2.regs rMaskBase = dp0 + mask * (I.n + 1) ∧
      u2.regs rT = tIdx + 1 := by
    have hz1 := hfix_u1.zero; have ho1 := hfix_u1.one; have hn1 := hfix_u1.n_eq
    have hN1 := hfix_u1.N_eq; have hdb1 := hfix_u1.distB; have hdp1 := hfix_u1.dpB
    have hpow1 := hfix_u1.powN
    have hfit_addr : Fits w (dp0 + mask * (I.n + 1) + tIdx) :=
      fit_table_cell hwS hlt ht_lt
    have hfit_t1 : Fits w (tIdx + 1) := by
      refine hwS.of_le ?_
      have h1 : tIdx + 1 ≤ (I.n + 1) * (I.n + 1) := by
        have hsq : I.n + 1 ≤ (I.n + 1) * (I.n + 1) := Nat.le_mul_self _
        omega
      rw [Instance.spaceBound]
      omega
    have ht_u1' : u1.regs rT = tIdx := ht_u1
    dsimp [targetStore]
    wram_exec [hmb_u1, ht_u1', ho1]
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · wram_simp [hmb_u1, ht_u1']; rw [hmu1]
    · wram_simp [hz1]
    · wram_simp [ho1]
    · wram_simp [hn1]
    · wram_simp [hN1]
    · wram_simp [hdb1]
    · wram_simp [hdp1]
    · wram_simp [hpow1]
    · wram_simp [hm_u1]
    · wram_simp [hmb_u1]
    · wram_simp [ht_u1', ho1]
  obtain ⟨u2, he_u2, hmu2, hfix_u2, hm_u2, hmb_u2, ht_u2⟩ := hstore
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
      have hbest_eq : u2.mem (2 + (I.n + 1) * (I.n + 1) + mask * (I.n + 1) + j) =
          u1.regs rBest := by
        rw [hmu2]
        simp [dp0]
      rw [hbest_eq]
      exact hbest_least
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
  have h1 : ∃ y1, ExecWithin w maskZeroT y y1 1 ∧
      y1.mem = y.mem ∧ FixedRegs I y1 ∧ y1.regs rMask = mask ∧
      y1.regs rMaskBase = dp0 + mask * (I.n + 1) ∧ y1.regs rT = 0 := by
    have hz := hyfix.zero; have ho := hyfix.one; have hn := hyfix.n_eq
    have hN := hyfix.N_eq; have hdb := hyfix.distB; have hdp := hyfix.dpB
    have hpow := hyfix.powN
    dsimp [dp0, maskZeroT]
    wram_exec [hz]
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      wram_simp [hz, ho, hn, hN, hdb, hdp, hpow, hym, hymb]
  obtain ⟨y1, he_y1, hmy1, hfix_y1, hm_y1, hmb_y1, ht_y1⟩ := h1
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
  have hinc : ∃ y3, ExecWithin w maskInc y2 y3 2 ∧
      y3.mem = y2.mem ∧ FixedRegs I y3 ∧ y3.regs rMask = mask + 1 ∧
      y3.regs rMaskBase = dp0 + (mask + 1) * (I.n + 1) := by
    have hz2 := hfix_y2.zero; have ho2 := hfix_y2.one; have hn2 := hfix_y2.n_eq
    have hN2 := hfix_y2.N_eq; have hdb2 := hfix_y2.distB; have hdp2 := hfix_y2.dpB
    have hpow2 := hfix_y2.powN
    have hfit_m1 : Fits w (mask + 1) :=
      hwS.of_le (by rw [Instance.spaceBound]; nlinarith)
    have hfit_mb1 : Fits w ((dp0 + mask * (I.n + 1)) + (I.n + 1)) :=
      hwS.of_le (by rw [Instance.spaceBound]; dsimp [dp0]; nlinarith)
    dsimp [maskInc]
    wram_exec [hm_y2, ho2, hmb_y2, hN2]
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · wram_simp [hz2]
    · wram_simp [ho2]
    · wram_simp [hn2]
    · wram_simp [hN2]
    · wram_simp [hdb2]
    · wram_simp [hdp2]
    · wram_simp [hpow2]
    · wram_simp [hm_y2, ho2]
    · wram_simp [hmb_y2, hN2]; ring
  obtain ⟨y3, he_y3, hmy3, hfix_y3, hm_y3, hmb_y3⟩ := hinc
  have h13 : (I.n + 1) * (22 * I.n + 11 + 2) + 2 + 1 + 2 ≤ (I.n + 1) * (22 * I.n + 13) + 5 := by
    nlinarith
  refine ⟨y3, (he_y1.seq (he_y2.seq he_y3)).mono (by omega),
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
  have hpow_pos : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hmb_ge : I.n + 1 ≤ dp0 + 2 ^ I.n * (I.n + 1) :=
    (Nat.le_mul_of_pos_left _ hpow_pos).trans (Nat.le_add_left _ _)
  have hsub_final : dp0 + 2 ^ I.n * (I.n + 1) - (I.n + 1) =
      dp0 + (2 ^ I.n - 1) * (I.n + 1) := by
    have h1 : 1 * (I.n + 1) ≤ 2 ^ I.n * (I.n + 1) := Nat.mul_le_mul_right _ hpow_pos
    rw [Nat.add_sub_assoc (by simpa using h1)]
    congr 1
    rw [Nat.sub_mul, one_mul]
  have hfinal_least := htabf (2 ^ I.n - 1) (by omega) 0
  simp only [maskSet_two_pow_sub_one, Fin.val_zero, Nat.add_zero] at hfinal_least
  have hans_eq : sf.mem (dp0 + (2 ^ I.n - 1) * (I.n + 1)) = heldKarp I.dist :=
    hfinal_least.unique (isLeast_heldKarp I.dist)
  have hfit_final : Fits w (dp0 + (2 ^ I.n - 1) * (I.n + 1)) := by
    have hlt_pow : 2 ^ I.n - 1 < 2 ^ I.n := Nat.sub_lt hpow_pos Nat.one_pos
    simpa [dp0] using fit_table_cell hwS hlt_pow (Nat.succ_pos _)
  have hfin : ∃ z, ExecWithin w finalReadCode sf z 2 ∧ z.regs rBest = heldKarp I.dist := by
    have hNf := hfixf.N_eq
    dsimp [finalReadCode]
    wram_exec [hmbf, hNf, hsub_final, hans_eq]
    wram_simp [hmbf, hNf, hsub_final, hans_eq]
  obtain ⟨z, he_fin, hz_best⟩ := hfin
  refine ⟨z, (he_setup.seq (he_mask.seq he_fin)).mono ?_, hz_best⟩
  rcases Nat.eq_zero_or_pos I.n with hn0 | hn_pos
  · simp [hn0]
  · obtain ⟨k, hk⟩ : ∃ k, I.n = k + 1 := ⟨I.n - 1, by omega⟩
    have hp : 2 ≤ 2 ^ I.n := by rw [hk, pow_succ]; have := Nat.one_le_two_pow (n := k); omega
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ I.n = m + 2 := ⟨2 ^ I.n - 2, by omega⟩
    rw [hm, hk]
    have hpoly :
        (15 * (k + 1) + 30 +
          ((m + 2 - 1) * ((k + 1 + 1) * (22 * (k + 1) + 13) + 5 + 2) + 2 + 2)) +
          (58 * m * k ^ 2 + 81 * m * k + 3 * m + 138 * k ^ 2 + 226 * k + 114) =
        80 * ((k + 1) ^ 2 * (m + 2) + 1) := by
      rw [show m + 2 - 1 = m + 1 by omega]
      ring
    have hrem : 1 ≤ 58 * m * k ^ 2 + 81 * m * k + 3 * m + 138 * k ^ 2 + 226 * k + 114 := by omega
    exact Nat.le_sub_one_of_lt (by omega)

/-! ## Public running-time theorems -/

/-- `program` computes `heldKarp I.dist` in at most `80 (n² · 2ⁿ + 1)` standard-basis instructions
at every fitting word width. -/
theorem computesInTime_program :
    program.ComputesInTime (fun _ => Instance.encode)
      (fun I _ => 80 * (I.n ^ 2 * 2 ^ I.n + 1))
      Instance.FitsWidth (fun I => heldKarp I.dist) := by
  refine (heldKarpCode.computesInTime_program rBest
    (encode := fun _ => Instance.encode)
    (time := fun I _ => 80 * (I.n ^ 2 * 2 ^ I.n + 1) - 1)
    fun I w hw _ => exec_heldKarpCode I hw).mono
    (fun I _ => ?_) (fun _ _ h => h)
  have h1 : 1 ≤ I.n ^ 2 * 2 ^ I.n + 1 := Nat.succ_pos _
  omega

/-- **Word-RAM Bellman–Held–Karp execution bound** [Bellman1962] [HeldKarp1962]. At every fitting
word width `w`, `program` halts on `State.init I.encode` with `heldKarp I.dist` within
`80 (n² · 2ⁿ + 1)` standard-basis instructions. -/
theorem executes_program {I : Instance} {w : ℕ} (hw : I.FitsWidth w) :
    ∃ m ≤ 80 * (I.n ^ 2 * 2 ^ I.n + 1),
      Executes w program (.init I.encode) (heldKarp I.dist) m := by
  obtain ⟨m, hexec, hm⟩ := computesInTime_program I w hw hw.inputFits
  exact ⟨m, hm, hexec⟩

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
  have h1 : 1 ≤ I.n ^ 2 * 2 ^ I.n := by
    have := Nat.one_le_two_pow (n := I.n)
    nlinarith
  nlinarith

end Cslib.Algorithms.WordRAM.HeldKarp
