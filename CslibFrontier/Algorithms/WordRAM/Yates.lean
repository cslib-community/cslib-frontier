/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Yates
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
import CslibFrontier.Computability.GenericRAM.Signed.Fits
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Yates's fast zeta and Möbius transforms on the word RAM

Checked standard-basis word-RAM (`Cslib.WordRAM.Basis.standard`) implementations of Yates's
algorithm (`CslibFrontier.Algorithms.Lean.Yates`) running in `O((n + 1) · 2 ^ n)` instructions:

* **Unsigned `ℕ` fast zeta transform (`zetaNatProgram`)**: transforms an encoded table
  `I : NatInstance` (`I.n :: I.entries.toList`) in place to `(Yates.zeta I.entries).toList` in at
  most `32 * ((I.n + 1) * 2 ^ I.n)` instructions at every width `w` with `I.FitsWidth w`.
* **Signed `ℤ` fast zeta and Möbius transforms (`zetaIntProgram`, `mobiusIntProgram`)**:
  transforms an encoded integer table `I : IntInstance`
  (`I.n :: I.entries.toList.map Signed.encode`) in place via `Signed.add` and `Signed.subtract` to
  `(Yates.zeta I.entries).toList.map Signed.encode` and
  `(Yates.mobius I.entries).toList.map Signed.encode`, each in at most
  `48 * ((I.n + 1) * 2 ^ I.n)` instructions at every width `w` with `I.FitsWidth w`.

All three programs share a single parameterized in-place block-and-offset butterfly loop
(`butterfly`) that avoids bitwise instructions by iterating over aligned blocks of size
`2 ^ (i + 1)` and offsets `0 ≤ j < 2 ^ i`. Memory is updated directly in the input buffer
starting at address `2`, with the output length written to address `1` and `halt` returning `1`.

## Word-size conditions

* For `NatInstance`, every intermediate and final zeta entry is a sum of distinct entries of
  `I.entries`, hence at most `I.totalSum = ∑ k, I.entries[k]`. The envelope
  `I.wordBound = 4 * (2 ^ I.n + I.totalSum + 16)` covers all table entries, addresses, and
  loop counters.
* For `IntInstance`, every intermediate and final zeta or Möbius entry is a `(±1)`-weighted sum
  of distinct entries of `I.entries`, hence has magnitude at most
  `I.sumAbs = ∑ k, I.entries[k].natAbs`.
  The envelope `I.wordBound = 8 * (2 ^ I.n + I.sumAbs + 16)` provides the two extra unsigned bits
  required by `Signed.exec_add` and `Signed.exec_subtract`.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009], Section 2.2
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014], Lemma 4.2
-/

public section

namespace Cslib.Algorithms.WordRAM.Yates

open Cslib.Algorithms.Lean.Yates
open Cslib.BitString
open Cslib.WordRAM
open Finset

/-! ## Problem instances -/

/-- A table of `2 ^ n` natural numbers for the unsigned fast zeta transform. -/
structure NatInstance where
  /-- Number of coordinates `n`. -/
  n : ℕ
  /-- Table entries indexed by `k < 2 ^ n` (`maskSet n k`). -/
  entries : Vector ℕ (2 ^ n)

namespace NatInstance

/-- Flat Word-RAM input `[n] ++ entries.toList`. -/
@[expose] def encode (I : NatInstance) : List ℕ :=
  I.n :: I.entries.toList

/-- Sum of all table entries, bounding every intermediate and final zeta entry. -/
@[expose] def totalSum (I : NatInstance) : ℕ :=
  ∑ k : Fin (2 ^ I.n), I.entries[k.1]

/-- Word-size envelope covering indices, addresses, and all intermediate zeta sums. -/
@[expose] def wordBound (I : NatInstance) : ℕ :=
  4 * (2 ^ I.n + I.totalSum + 16)

/-- Width admissibility predicate for `NatInstance`. -/
@[expose] def FitsWidth (I : NatInstance) (w : ℕ) : Prop :=
  Fits w I.wordBound

@[simp] theorem length_encode (I : NatInstance) : I.encode.length = 2 ^ I.n + 1 := by
  simp [encode]

theorem entry_le_totalSum (I : NatInstance) (k : Fin (2 ^ I.n)) :
    I.entries[k.1] ≤ I.totalSum :=
  Finset.single_le_sum (f := fun j : Fin (2 ^ I.n) => I.entries[j.1])
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem fits_of_le (I : NatInstance) {w x : ℕ} (hfit : I.FitsWidth w) (hx : x ≤ I.wordBound) :
    Fits w x :=
  hfit.of_le hx

theorem inputFits (I : NatInstance) {w : ℕ} (hfit : I.FitsWidth w) : InputFits w I.encode := by
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  refine ⟨I.fits_of_le hfit (by simp only [length_encode]; unfold wordBound; omega), ?_⟩
  intro x hx
  simp only [encode, List.mem_cons, Vector.mem_toList_iff] at hx
  rcases hx with rfl | hx
  · exact I.fits_of_le hfit (by
      have hn : I.n < 2 ^ I.n := Nat.lt_two_pow_self
      unfold wordBound; omega)
  · obtain ⟨k, hk, rfl⟩ := Vector.mem_iff_getElem.mp hx
    have hle := I.entry_le_totalSum ⟨k, hk⟩
    dsimp only at hle
    exact I.fits_of_le hfit (by unfold wordBound; omega)

end NatInstance

/-- A table of `2 ^ n` signed integers for the signed fast zeta and Möbius transforms. -/
structure IntInstance where
  /-- Number of coordinates `n`. -/
  n : ℕ
  /-- Integer table entries indexed by `k < 2 ^ n` (`maskSet n k`). -/
  entries : Vector ℤ (2 ^ n)

namespace IntInstance

/-- Flat Word-RAM input `[n] ++ entries.toList.map Signed.encode`. -/
@[expose] def encode (I : IntInstance) : List ℕ :=
  I.n :: I.entries.toList.map Signed.encode

/-- Sum of absolute values of all entries, bounding every intermediate zeta or Möbius entry. -/
@[expose] def sumAbs (I : IntInstance) : ℕ :=
  ∑ k : Fin (2 ^ I.n), I.entries[k.1].natAbs

/-- Word-size envelope covering encoded signed words, indices, addresses, and the two extra bits
needed by `Signed.exec_add` and `Signed.exec_subtract`. -/
@[expose] def wordBound (I : IntInstance) : ℕ :=
  8 * (2 ^ I.n + I.sumAbs + 16)

/-- Width admissibility predicate for `IntInstance`. -/
@[expose] def FitsWidth (I : IntInstance) (w : ℕ) : Prop :=
  Fits w I.wordBound

@[simp] theorem length_encode (I : IntInstance) : I.encode.length = 2 ^ I.n + 1 := by
  simp [encode]

theorem natAbs_le_sumAbs (I : IntInstance) (k : Fin (2 ^ I.n)) :
    I.entries[k.1].natAbs ≤ I.sumAbs :=
  Finset.single_le_sum (f := fun j : Fin (2 ^ I.n) => I.entries[j.1].natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem eight_le_width (I : IntInstance) {w : ℕ} (hfit : I.FitsWidth w) : 8 ≤ w := by
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have h129 : 129 ≤ 2 ^ w := by
    have hbound : I.wordBound < 2 ^ w := hfit
    unfold wordBound at hbound
    omega
  by_contra hlt
  have hw : w ≤ 7 := by omega
  have h2w : 2 ^ w ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hw
  norm_num at h2w
  omega

theorem signedFits_sumAbs (I : IntInstance) {w : ℕ} (hfit : I.FitsWidth w) :
    GenericRAM.Signed.Fits (w - 2) (I.sumAbs : ℤ) := by
  have hw8 : 8 ≤ w := I.eight_le_width hfit
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have hbound : I.wordBound < 2 ^ w := hfit
  have hpow : 2 ^ w = 8 * 2 ^ (w - 3) := by
    rw [show w = 3 + (w - 3) by omega, pow_add]
    norm_num
  rw [hpow] at hbound
  have hlt : I.sumAbs < 2 ^ (w - 3) := by
    unfold wordBound at hbound
    omega
  have hw3 : w - 2 - 1 = w - 3 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · have hpos : (0 : ℤ) ≤ 2 ^ (w - 2 - 1) := by positivity
    omega
  · rw [hw3]
    exact_mod_cast hlt

theorem fits_signedEncode (I : IntInstance) {w : ℕ}
    (hfit : Fits w (8 * (2 ^ I.n + I.sumAbs + 16))) {z : ℤ}
    (hz : z.natAbs ≤ I.sumAbs) : Fits w (Signed.encode z) := by
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  have h : Signed.encode z ≤ 2 * I.sumAbs + 1 := by
    unfold Signed.encode
    split_ifs <;> omega
  exact hfit.of_le (by omega)

theorem inputFits (I : IntInstance) {w : ℕ} (hfit : I.FitsWidth w) : InputFits w I.encode := by
  have hpow2 : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
  refine ⟨hfit.of_le (by simp only [length_encode]; unfold wordBound; omega), ?_⟩
  intro x hx
  simp only [encode, List.mem_cons, List.mem_map, Vector.mem_toList_iff] at hx
  rcases hx with rfl | ⟨z, hz, rfl⟩
  · have hn : I.n < 2 ^ I.n := Nat.lt_two_pow_self
    exact hfit.of_le (by unfold wordBound; omega)
  · obtain ⟨k, hk, rfl⟩ := Vector.mem_iff_getElem.mp hz
    exact I.fits_signedEncode hfit (I.natAbs_le_sumAbs ⟨k, hk⟩)

end IntInstance

/-! ## Shared butterfly engine -/

private abbrev nReg : Fin 20 := ⟨9, by decide⟩
private abbrev arrSize : Fin 20 := ⟨10, by decide⟩
private abbrev outReg : Fin 20 := ⟨11, by decide⟩
private abbrev twoReg : Fin 20 := ⟨12, by decide⟩
private abbrev iReg : Fin 20 := ⟨13, by decide⟩
private abbrev stepReg : Fin 20 := ⟨14, by decide⟩
private abbrev twoStepReg : Fin 20 := ⟨15, by decide⟩
private abbrev baseReg : Fin 20 := ⟨16, by decide⟩
private abbrev jReg : Fin 20 := ⟨17, by decide⟩
private abbrev idxLow : Fin 20 := ⟨18, by decide⟩
private abbrev idxHigh : Fin 20 := ⟨19, by decide⟩

private def setupCode : Code .standard 20 := ram[
  outReg ← #1;
  twoReg ← #2;
  nReg ← *outReg;
  arrSize ← #1;
  iReg ← #0;
  while iReg < nReg do [
    arrSize ← arrSize + arrSize;
    iReg ← iReg + outReg
  ];
  *outReg ← arrSize;
  iReg ← #0;
  stepReg ← #1
]

private def innerBody (cellOp : Code .standard 20) : Code .standard 20 := ram[
  idxLow ← twoReg + baseReg;
  idxLow ← idxLow + jReg;
  idxHigh ← idxLow + stepReg;
  Signed.left ← *idxHigh;
  Signed.right ← *idxLow;
  ⟪cellOp⟫;
  *idxHigh ← Signed.result;
  jReg ← jReg + outReg
]

private def butterflyLoop (cellOp : Code .standard 20) : Code .standard 20 := ram[
  while iReg < nReg do [
    twoStepReg ← stepReg + stepReg;
    baseReg ← #0;
    while baseReg < arrSize do [
      jReg ← #0;
      while jReg < stepReg do [
        ⟪innerBody cellOp⟫
      ];
      baseReg ← baseReg + twoStepReg
    ];
    stepReg ← twoStepReg;
    iReg ← iReg + outReg
  ]
]

private def butterfly (cellOp : Code .standard 20) : Code .standard 20 := ram[
  ⟪setupCode⟫;
  ⟪butterflyLoop cellOp⟫
]

private def natAddOp : Code .standard 20 := ram[
  Signed.result ← Signed.left + Signed.right
]

/-- Standard-basis Word-RAM program computing the unsigned fast zeta transform on `NatInstance`,
halting with output address `1`. -/
def zetaNatProgram : Program .standard 20 := (butterfly natAddOp).program outReg

/-- Standard-basis Word-RAM program computing the signed fast zeta transform on `IntInstance`,
halting with output address `1`. -/
def zetaIntProgram : Program .standard 20 :=
  (butterfly (Signed.add (r := 11))).program outReg

/-- Standard-basis Word-RAM program computing the signed fast Möbius transform on `IntInstance`,
halting with output address `1`. -/
def mobiusIntProgram : Program .standard 20 :=
  (butterfly (Signed.subtract (r := 11))).program outReg

/-! ## Setup and butterfly execution -/

private theorem exec_setupCode {w n B : ℕ} (t0 : Fin (2 ^ n) → ℕ)
    (hfit : Fits w (2 ^ n + B + 16))
    (hx_len : (Data.init (n :: List.ofFn t0) : Data 20).mem 1 = n) :
    ∃ y, ExecWithin w setupCode (Data.init (n :: List.ofFn t0)) y (4 * n + 10) ∧
      y.regs outReg = 1 ∧ y.regs twoReg = 2 ∧ y.regs nReg = n ∧ y.regs arrSize = 2 ^ n ∧
      y.regs iReg = 0 ∧ y.regs stepReg = 1 ∧
      y.mem 1 = 2 ^ n ∧ ∀ k : Fin (2 ^ n), y.mem (2 + k.1) = t0 k := by
  have hpow2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hn_fit : Fits w n := hfit.of_le (by have := Nat.lt_two_pow_self (n := n); omega)
  have h1_fit : Fits w 1 := hfit.of_le (by omega)
  have h2_fit : Fits w 2 := hfit.of_le (by omega)
  have h0_fit : Fits w 0 := hfit.of_le (by omega)
  unfold setupCode
  refine (WP.seq ?_).exists_execWithin
  wram_exec [hx_len]
  refine WP.name fun x1 hx1 => ?_
  have hloop : ∃ x2, ExecWithin w (Code.loop (.lt iReg nReg) ram[
      arrSize ← arrSize + arrSize; iReg ← iReg + outReg ]) x1 x2 (n * (2 + 2) + 2) ∧
      x2.regs iReg = n ∧ x2.regs arrSize = 2 ^ n ∧ x2.regs nReg = n ∧
      x2.regs outReg = 1 ∧ x2.regs twoReg = 2 ∧ x2.mem = x1.mem := by
    let P (i : ℕ) (d : Data 20) : Prop :=
      i ≤ n ∧ d.regs arrSize = 2 ^ i ∧ d.regs nReg = n ∧ d.regs outReg = 1 ∧
        d.regs twoReg = 2 ∧ d.mem = x1.mem
    have hx1P : P (x1.regs iReg) x1 := by
      subst hx1
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
      · wram_simp; exact Nat.zero_le n
      · wram_simp; simp
      all_goals wram_simp
    have hxi : x1.regs iReg ≤ n := by subst hx1; wram_simp; exact Nat.zero_le n
    obtain ⟨x2, hx2, hx2P, hx2i⟩ := ExecWithin.loop_count (w := w) (T := 2)
      (body := ram[ arrSize ← arrSize + arrSize; iReg ← iReg + outReg ]) P (fun _ h => h.2.2.1)
      (fun d hP hlt => by
        obtain ⟨hi_le, ha, hn, h1, h2, hm⟩ := hP
        have hi_lt : d.regs iReg < n := hlt
        have ha2 : 2 ^ d.regs iReg + 2 ^ d.regs iReg ≤ 2 ^ n := by
          rw [← two_mul, ← pow_succ']
          exact Nat.pow_le_pow_right (by norm_num) hi_lt
        have hf_a : Fits w (d.regs arrSize + d.regs arrSize) := by
          rw [ha]
          exact hfit.of_le (by omega)
        have hf_i : Fits w (d.regs iReg + d.regs outReg) := by
          rw [h1]
          have hlt2n : n < 2 ^ n := Nat.lt_two_pow_self
          exact hfit.of_le (by omega)
        refine ⟨(d.set arrSize (d.regs arrSize + d.regs arrSize)).set iReg
            (d.regs iReg + d.regs outReg), ?_, ⟨hi_lt, ?_, ?_, ?_, ?_, hm⟩, ?_⟩
        · wram_exec
        · wram_simp [ha, ← two_mul, ← pow_succ']
        · wram_simp [hn]
        · wram_simp [h1]
        · wram_simp [h2]
        · wram_simp [h1])
      hxi hx1P
    rw [show (n - x1.regs iReg) * (2 + 2) + 2 = n * (2 + 2) + 2 by
      rw [show x1.regs iReg = 0 by subst hx1; wram_simp, Nat.sub_zero]] at hx2
    exact ⟨x2, hx2, hx2i, hx2P.2.1, hx2P.2.2.1, hx2P.2.2.2.1, hx2P.2.2.2.2.1, hx2P.2.2.2.2.2⟩
  obtain ⟨x2, hx2, hx2i, hx2a, hx2n, hx21, hx22, hx2m⟩ := hloop
  refine WP.of_execWithin hx2 ?_
  have h2pow_fit : Fits w (2 ^ n) := hfit.of_le (by omega)
  wram_exec [hx21, hx22, hx2a, hx2n]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · wram_simp [hx21]
  · wram_simp [hx22]
  · wram_simp [hx2n]
  · wram_simp [hx2a]
  · wram_simp
  · wram_simp
  · simp only [Data.write, Data.set, Function.update_self]
  · intro k
    have hne : 2 + k.1 ≠ 1 := by omega
    simp only [Data.write, Data.set]
    rw [Function.update_of_ne hne, hx2m]
    subst hx1
    simp only [Data.set]
    rw [show (2 : ℕ) + k.1 = (k.1 + 1) + 1 by omega, Data.init_mem_succ,
      List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [k.isLt]

private theorem testBit_add_of_div {i step : ℕ} (hstep : step = 2 ^ i) :
    ∀ q j, j < step →
      (q * (2 * step) + j).testBit i = false ∧
      (q * (2 * step) + step + j).testBit i = true := by
  intro q j hj
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  subst hstep
  have h1 : (q * (2 * 2 ^ i) + j) / 2 ^ i = 2 * q := by
    rw [show q * (2 * 2 ^ i) + j = 2 * q * 2 ^ i + j by ring,
      Nat.add_div_of_dvd_right (dvd_mul_left _ _), Nat.mul_div_cancel _ hpos,
      Nat.div_eq_of_lt hj, add_zero]
  have h2 : (q * (2 * 2 ^ i) + 2 ^ i + j) / 2 ^ i = 2 * q + 1 := by
    rw [show q * (2 * 2 ^ i) + 2 ^ i + j = (2 * q + 1) * 2 ^ i + j by ring,
      Nat.add_div_of_dvd_right (dvd_mul_left _ _), Nat.mul_div_cancel _ hpos,
      Nat.div_eq_of_lt hj, add_zero]
  simp [h1, h2]

private theorem xor_two_pow_of_block {i q j : ℕ} (hj : j < 2 ^ i) :
    (q * (2 * 2 ^ i) + 2 ^ i + j) ^^^ 2 ^ i = q * (2 * 2 ^ i) + j := by
  refine Nat.eq_of_testBit_eq fun r => ?_
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy r i with hri | rfl | hir
  · have hpow : 2 ^ i = 2 ^ (r + 1) * 2 ^ (i - 1 - r) := by
      rw [← pow_add, show r + 1 + (i - 1 - r) = i by omega]
    have hdvd : 2 ^ (r + 1) ∣ 2 ^ i := ⟨2 ^ (i - 1 - r), hpow⟩
    have hposr : 0 < 2 ^ r := Nat.two_pow_pos r
    have hpow2 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ']
    have ha : (q * (2 * 2 ^ i) + 2 ^ i + j) / 2 ^ r % 2 = j / 2 ^ r % 2 := by
      have hm : (q * (2 * 2 ^ i) + 2 ^ i) = (q * 2 + 1) * (2 * 2 ^ (i - 1 - r)) * 2 ^ r := by
        rw [show (q * (2 * 2 ^ i) + 2 ^ i) = (q * 2 + 1) * 2 ^ i by ring, hpow, hpow2]; ring
      rw [show q * (2 * 2 ^ i) + 2 ^ i + j = j + (q * 2 + 1) * 2 ^ (i - 1 - r) * 2 * 2 ^ r by
          rw [hm]; ring,
        Nat.add_mul_div_right _ _ hposr, Nat.add_mul_mod_self_right]
    have hb : (q * (2 * 2 ^ i) + j) / 2 ^ r % 2 = j / 2 ^ r % 2 := by
      have hm : q * (2 * 2 ^ i) = q * (2 * 2 ^ (i - 1 - r)) * 2 * 2 ^ r := by
        rw [hpow, hpow2]; ring
      rw [show q * (2 * 2 ^ i) + j = j + q * (2 * 2 ^ (i - 1 - r)) * 2 * 2 ^ r by rw [hm]; ring,
        Nat.add_mul_div_right _ _ hposr, Nat.add_mul_mod_self_right]
    simp [Nat.testBit_eq_decide_div_mod_eq, ha, hb, Nat.ne_of_gt hri]
  · have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
    have h1 : (q * (2 * 2 ^ r) + 2 ^ r + j) / 2 ^ r = 2 * q + 1 := by
      rw [show q * (2 * 2 ^ r) + 2 ^ r + j = j + (2 * q + 1) * 2 ^ r by ring,
        Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
    have h2 : (q * (2 * 2 ^ r) + j) / 2 ^ r = 2 * q := by
      rw [show q * (2 * 2 ^ r) + j = j + (2 * q) * 2 ^ r by ring,
        Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
    simp [Nat.testBit_eq_decide_div_mod_eq, h1, h2]
  · have hpos1 : 0 < 2 ^ (i + 1) := Nat.two_pow_pos (i + 1)
    have hpowr : 2 ^ r = 2 ^ (i + 1) * 2 ^ (r - i - 1) := by
      rw [← pow_add, show i + 1 + (r - i - 1) = r by omega]
    have hdiv1 : (2 ^ i + j) / 2 ^ (i + 1) = 0 :=
      Nat.div_eq_of_lt (by rw [pow_succ']; omega)
    have hdiv2 : j / 2 ^ (i + 1) = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hj (by rw [pow_succ']; omega))
    have ha : (q * (2 * 2 ^ i) + 2 ^ i + j) / 2 ^ r = q / 2 ^ (r - i - 1) := by
      rw [hpowr, ← Nat.div_div_eq_div_mul,
        show q * (2 * 2 ^ i) + 2 ^ i + j = (2 ^ i + j) + q * 2 ^ (i + 1) by
          rw [pow_succ']; ring,
        Nat.add_mul_div_right _ _ hpos1, hdiv1, zero_add]
    have hb : (q * (2 * 2 ^ i) + j) / 2 ^ r = q / 2 ^ (r - i - 1) := by
      rw [hpowr, ← Nat.div_div_eq_div_mul,
        show q * (2 * 2 ^ i) + j = j + q * 2 ^ (i + 1) by rw [pow_succ']; ring,
        Nat.add_mul_div_right _ _ hpos1, hdiv2, zero_add]
    simp [Nat.testBit_eq_decide_div_mod_eq, ha, hb, Nat.ne_of_lt hir]

private theorem lt_next_block_iff {i q m : ℕ} (hm_bit : m.testBit i = true) :
    m < (q + 1) * (2 * 2 ^ i) ↔ m < (q + 1) * (2 * 2 ^ i) + 2 ^ i := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  · intro h
    by_contra hge
    set b := (q + 1) * (2 * 2 ^ i)
    change m < b + 2 ^ i at h
    change ¬ m < b at hge
    set j := m - b
    have hj : j < 2 ^ i := by omega
    have hm_eq : m = b + j := by omega
    have hfalse := (testBit_add_of_div rfl (q + 1) j hj).1
    rw [← hm_eq, hm_bit] at hfalse
    cases hfalse

private theorem exec_pass {w n i B T_op : ℕ} {cellOp : Code .standard 20}
    (opWord : ℕ → ℕ → ℕ)
    (prev next : Fin (2 ^ n) → ℕ)
    (Pmem : (Fin (2 ^ n) → ℕ) → Prop)
    (hi : i < n)
    (hnext_def : ∀ k : Fin (2 ^ n),
      next k = if k.1.testBit i then
        opWord (prev k) (prev ⟨k.1 ^^^ 2 ^ i, Nat.xor_lt_two_pow k.isLt
          (Nat.pow_lt_pow_right (by norm_num) hi)⟩)
      else prev k)
    (hOp : ∀ (x : Data 20) (t : Fin (2 ^ n) → ℕ) (a b : Fin (2 ^ n)),
      Pmem t → x.regs Signed.left = t a → x.regs Signed.right = t b →
      ∃ y, ExecWithin w cellOp x y T_op ∧
        y.regs Signed.result = opWord (t a) (t b) ∧ y.mem = x.mem ∧
        ∀ r : Fin 20, 9 ≤ r.1 → y.regs r = x.regs r)
    (_hP_prev : Pmem prev)
    (hP_mix : ∀ kcut : ℕ, Pmem fun k =>
      if k.1.testBit i ∧ k.1 < kcut then next k else prev k)
    (hfit : Fits w (2 ^ n + B + 16))
    (hfit_val : ∀ t, Pmem t → ∀ k, Fits w (t k))
    (x : Data 20)
    (hx1 : x.regs outReg = 1) (hx2 : x.regs twoReg = 2)
    (hxn : x.regs nReg = n) (hxa : x.regs arrSize = 2 ^ n)
    (hxi : x.regs iReg = i) (hxs : x.regs stepReg = 2 ^ i)
    (hmem_arr : ∀ k : Fin (2 ^ n), x.mem (2 + k.1) = prev k)
    (hmem1 : x.mem 1 = 2 ^ n) :
    ∃ y, ExecWithin w (ram[
      twoStepReg ← stepReg + stepReg;
      baseReg ← #0;
      while baseReg < arrSize do [
        jReg ← #0;
        while jReg < stepReg do [
          ⟪innerBody cellOp⟫
        ];
        baseReg ← baseReg + twoStepReg
      ];
      stepReg ← twoStepReg;
      iReg ← iReg + outReg ]) x y ((2 ^ (n - 1 - i) * (2 ^ i * (9 + T_op) + 6) + 2) + 4) ∧
      y.regs outReg = 1 ∧ y.regs twoReg = 2 ∧ y.regs nReg = n ∧ y.regs arrSize = 2 ^ n ∧
      y.regs iReg = i + 1 ∧ y.regs stepReg = 2 ^ (i + 1) ∧
      y.mem 1 = 2 ^ n ∧ (∀ k : Fin (2 ^ n), y.mem (2 + k.1) = next k) := by
  have htwoStep_eq : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by rw [← two_mul, ← pow_succ']
  have htwoStep_le : 2 ^ (i + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hi
  have htwoStep_fit : Fits w (2 ^ (i + 1)) := hfit.of_le (by omega)
  have hn_split : 2 ^ n = 2 ^ (n - 1 - i) * (2 ^ (i + 1)) := by
    rw [← pow_add, show n - 1 - i + (i + 1) = n by omega]
  have h0_fit : Fits w 0 := hfit.of_le (by omega)
  refine (WP.seq ?_).exists_execWithin
  wram_exec [hxs, htwoStep_eq]
  refine WP.name fun x1 hx1' => ?_
  -- Middle loop invariant indexed by `q ≤ 2 ^ (n - 1 - i)`
  let InvMid (q : ℕ) (d : Data 20) : Prop :=
    q ≤ 2 ^ (n - 1 - i) ∧
    d.regs baseReg = q * 2 ^ (i + 1) ∧
    d.regs stepReg = 2 ^ i ∧ d.regs twoStepReg = 2 ^ (i + 1) ∧
    d.regs arrSize = 2 ^ n ∧ d.regs nReg = n ∧ d.regs outReg = 1 ∧ d.regs twoReg = 2 ∧
    d.regs iReg = i ∧ d.mem 1 = 2 ^ n ∧
    ∀ k : Fin (2 ^ n), d.mem (2 + k.1) =
      if k.1.testBit i ∧ k.1 < q * 2 ^ (i + 1) then next k else prev k
  have hMid0 : InvMid 0 x1 := by
    subst hx1'
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_⟩
    · wram_simp; simp
    · wram_simp [hxs]
    · wram_simp [htwoStep_eq]
    · wram_simp [hxa]
    · wram_simp [hxn]
    · wram_simp [hx1]
    · wram_simp [hx2]
    · wram_simp [hxi]
    · wram_simp [hmem1]
    · wram_simp; simp [hmem_arr k]
  obtain ⟨x2, hx2', hMid_end, hstop⟩ := ExecWithin.loop_invariant
    (w := w)
    (cond := .lt baseReg arrSize)
    (body := ram[
      jReg ← #0;
      while jReg < stepReg do [
        ⟪innerBody cellOp⟫
      ];
      baseReg ← baseReg + twoStepReg ])
    (fun d => ∃ q, InvMid q d)
    (fun d => (2 ^ n - d.regs baseReg) / 2 ^ (i + 1))
    (T := 2 ^ i * (9 + T_op) + 4)
    (by
      intro d ⟨q, hq_le, hb, hs, hts, ha, hn, h1, h2, hi', hm1, hmem⟩ hcond
      have hlt_a : d.regs baseReg < 2 ^ n := by simpa only [Cond.holds_lt, ha] using hcond
      have hq_lt : q < 2 ^ (n - 1 - i) := by
        rw [hb, hn_split] at hlt_a
        exact Nat.lt_of_mul_lt_mul_right hlt_a
      -- Inner loop invariant indexed by `j ≤ 2 ^ i`
      let InvIn (j : ℕ) (d1 : Data 20) : Prop :=
        j ≤ 2 ^ i ∧
        d1.regs baseReg = q * 2 ^ (i + 1) ∧
        d1.regs stepReg = 2 ^ i ∧ d1.regs twoStepReg = 2 ^ (i + 1) ∧
        d1.regs arrSize = 2 ^ n ∧ d1.regs nReg = n ∧ d1.regs outReg = 1 ∧ d1.regs twoReg = 2 ∧
        d1.regs iReg = i ∧ d1.mem 1 = 2 ^ n ∧
        ∀ k : Fin (2 ^ n), d1.mem (2 + k.1) =
          if k.1.testBit i ∧ k.1 < q * 2 ^ (i + 1) + 2 ^ i + j then next k else prev k
      refine (WP.seq ?_).exists_execWithin
      wram_exec
      refine WP.name fun d0 hd0 => ?_
      have hd0_inv : InvIn (d0.regs jReg) d0 := by
        subst hd0
        refine ⟨by wram_simp; exact Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_⟩
        · wram_simp [hb]
        · wram_simp [hs]
        · wram_simp [hts]
        · wram_simp [ha]
        · wram_simp [hn]
        · wram_simp [h1]
        · wram_simp [h2]
        · wram_simp [hi']
        · wram_simp [hm1]
        · simp only [Data.set]
          rw [hmem k]
          by_cases hbit : k.1.testBit i = true
          · simp only [hbit, true_and]
            have hiff : k.1 < q * 2 ^ (i + 1) ↔ k.1 < q * 2 ^ (i + 1) + 2 ^ i := by
              by_cases hq0 : q = 0
              · subst hq0
                rw [zero_mul, zero_add]
                constructor
                · intro hk0; omega
                · intro hk2
                  have hfalse := (testBit_add_of_div rfl 0 k.1 hk2).1
                  rw [zero_mul, zero_add, hbit] at hfalse
                  cases hfalse
              · obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
                simpa only [pow_succ', Nat.mul_comm (2 ^ i) 2] using
                  lt_next_block_iff (q := q') hbit
            by_cases h1' : k.1 < q * 2 ^ (i + 1)
            · simp [h1', hiff.mp h1']
            · simp [h1', mt hiff.mpr h1']
          · simp [hbit]
      have hd0j_le : d0.regs jReg ≤ 2 ^ i := by subst hd0; wram_simp; exact Nat.zero_le _
      obtain ⟨d2, hd2, hd2_inv, hd2j⟩ := ExecWithin.loop_count (w := w) (T := 7 + T_op)
        (body := innerBody cellOp) InvIn (fun _ h => h.2.2.1)
        (fun s hs_inv hj_lt => by
          obtain ⟨hj_le, sb, ss, sts, sa, sn, s1, s2, si', sm1, smem⟩ := hs_inv
          let j := s.regs jReg
          have hj : j < 2 ^ i := hj_lt
          have hlow_lt : q * 2 ^ (i + 1) + j < 2 ^ n := by
            have : q * 2 ^ (i + 1) + 2 ^ (i + 1) ≤ 2 ^ n := by
              rw [show q * 2 ^ (i + 1) + 2 ^ (i + 1) = (q + 1) * 2 ^ (i + 1) by ring, hn_split]
              exact Nat.mul_le_mul_right _ hq_lt
            omega
          have hhigh_lt : q * 2 ^ (i + 1) + 2 ^ i + j < 2 ^ n := by
            have : q * 2 ^ (i + 1) + 2 ^ (i + 1) ≤ 2 ^ n := by
              rw [show q * 2 ^ (i + 1) + 2 ^ (i + 1) = (q + 1) * 2 ^ (i + 1) by ring, hn_split]
              exact Nat.mul_le_mul_right _ hq_lt
            omega
          let kHigh : Fin (2 ^ n) := ⟨q * 2 ^ (i + 1) + 2 ^ i + j, hhigh_lt⟩
          let kLow : Fin (2 ^ n) := ⟨q * 2 ^ (i + 1) + j, hlow_lt⟩
          have haddr_low_fit : Fits w (2 + kLow.1) := hfit.of_le (by omega)
          have haddr_high_fit : Fits w (2 + kHigh.1) := hfit.of_le (by omega)
          have hlow_fit : Fits w (2 + (q * 2 ^ (i + 1))) := hfit.of_le (by omega)
          let cur : Fin (2 ^ n) → ℕ := fun k =>
            if k.1.testBit i ∧ k.1 < q * 2 ^ (i + 1) + 2 ^ i + j then next k else prev k
          have hcur_P : Pmem cur := hP_mix _
          have hcur_high : cur kHigh = prev kHigh := by
            simp [cur, kHigh]
          have hkLow_bit : kLow.1.testBit i = false := by
            simpa [kLow, pow_succ', two_mul] using (testBit_add_of_div rfl q j hj).1
          have hkHigh_bit : kHigh.1.testBit i = true := by
            simpa [kHigh, pow_succ', two_mul] using (testBit_add_of_div rfl q j hj).2
          have hcur_low : cur kLow = prev kLow := by
            simp [cur, hkLow_bit]
          have hs_high : s.mem (2 + q * 2 ^ (i + 1) + j + 2 ^ i) = cur kHigh := by
            rw [show 2 + q * 2 ^ (i + 1) + j + 2 ^ i = 2 + kHigh.1 by simp [kHigh]; omega]
            exact smem kHigh
          have hs_low : s.mem (2 + q * 2 ^ (i + 1) + j) = cur kLow := by
            rw [show 2 + q * 2 ^ (i + 1) + j = 2 + kLow.1 by simp [kLow]; omega]
            exact smem kLow
          have hcur_fit_high : Fits w (cur kHigh) := hfit_val cur hcur_P kHigh
          have hcur_fit_low : Fits w (cur kLow) := hfit_val cur hcur_P kLow
          unfold innerBody
          refine (WP.seq ?_).exists_execWithin
          wram_exec [s2, sb, ss, hs_high, hs_low]
          refine WP.name fun s1' hs1' => ?_
          have hOp_res := hOp s1' cur kHigh kLow hcur_P
            (by rw [hs1']; wram_simp; exact hs_high) (by rw [hs1']; wram_simp; exact hs_low)
          obtain ⟨s2', hs2'_ex, hs2'_res, hs2'_mem, hs2'_frame⟩ := hOp_res
          have hkLow_xor : kHigh.1 ^^^ 2 ^ i = kLow.1 := by
            simpa [kHigh, kLow, pow_succ', two_mul] using xor_two_pow_of_block hj
          have hop_eq : opWord (cur kHigh) (cur kLow) = next kHigh := by
            rw [hcur_high, hcur_low, hnext_def kHigh, ite_eq_left hkHigh_bit]
            congr 2
            ext
            exact hkLow_xor.symm
          have hs2'_res_fit : Fits w (s2'.regs Signed.result) := by
            rw [hs2'_res, hop_eq]
            have hp := hP_mix (2 ^ n)
            have hnext_eq : next = fun k =>
                if k.1.testBit i ∧ k.1 < 2 ^ n then next k else prev k := by
              funext k
              by_cases hnot : k.1.testBit i = true <;> simp [hnot, hnext_def k]
            rw [hnext_eq]
            exact hfit_val _ hp kHigh
          have hs2'_j_fit : Fits w (s2'.regs jReg + 1) := by
            rw [hs2'_frame jReg (by decide), show s1'.regs jReg = j by rw [hs1']; wram_simp; rfl]
            exact hfit.of_le (by omega)
          have hs2'_idxHigh : s2'.regs idxHigh = 2 + kHigh.1 := by
            rw [hs2'_frame idxHigh (by decide), hs1']
            wram_simp [s2, sb, ss, kHigh, j, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hs2'_out : s2'.regs outReg = 1 := by
            rw [hs2'_frame outReg (by decide), hs1']
            wram_simp [s1]
          have hs2'_j : s2'.regs jReg = j := by
            rw [hs2'_frame jReg (by decide), hs1']
            wram_simp; rfl
          refine WP.of_execWithin hs2'_ex ?_
          wram_exec [hs2'_idxHigh, hs2'_res, hs2'_out, hs2'_j]
          refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_⟩, ?_⟩
          · wram_simp [hs2'_frame baseReg (by decide), hs1', sb]
          · wram_simp [hs2'_frame stepReg (by decide), hs1', ss]
          · wram_simp [hs2'_frame twoStepReg (by decide), hs1', sts]
          · wram_simp [hs2'_frame arrSize (by decide), hs1', sa]
          · wram_simp [hs2'_frame nReg (by decide), hs1', sn]
          · wram_simp [hs2'_out]
          · wram_simp [hs2'_frame twoReg (by decide), hs1', s2]
          · wram_simp [hs2'_frame iReg (by decide), hs1', si']
          · wram_simp [hs2'_mem, hs1']
            exact sm1
          · have hm_eq : s2'.mem = s.mem := by rw [hs2'_mem, hs1']; wram_simp
            simp only [Data.write, Data.set, hm_eq]
            by_cases hk : k = kHigh
            · subst hk
              rw [Function.update_self, hop_eq, ite_eq_left ⟨hkHigh_bit, by simp [kHigh, j]⟩]
            · have hne : k.1 ≠ q * 2 ^ (i + 1) + 2 ^ i + s.regs jReg := by
                intro heq; apply hk; ext; simp [kHigh, j, heq]
              rw [Function.update_of_ne (by omega), smem k]
              by_cases h1k : k.1.testBit i = true <;>
                by_cases h2k : k.1 < q * 2 ^ (i + 1) + 2 ^ i + s.regs jReg
              · simp [h1k, h2k, show k.1 < q * 2 ^ (i + 1) + 2 ^ i + (s.regs jReg + 1) by omega]
              · simp [h1k, h2k, show ¬ k.1 < q * 2 ^ (i + 1) + 2 ^ i + (s.regs jReg + 1) by omega]
              · simp [h1k]
              · simp [h1k]
          · wram_simp [hs2'_j, hs2'_out]; rfl)
        hd0j_le hd0_inv
      have hd2_b_fit : Fits w (d2.regs baseReg + d2.regs twoStepReg) := by
        rw [hd2_inv.2.1, hd2_inv.2.2.2.1]
        have : (q + 1) * 2 ^ (i + 1) ≤ 2 ^ n := by
          rw [hn_split]; exact Nat.mul_le_mul_right _ hq_lt
        exact hfit.of_le (by linarith)
      rw [show (2 ^ i - d0.regs jReg) * (7 + T_op + 2) + 2 =
        2 ^ i * (9 + T_op) + 2 by
        rw [show d0.regs jReg = 0 by subst hd0; wram_simp, Nat.sub_zero]; ring] at hd2
      refine WP.of_execWithin hd2 ?_
      wram_exec [hd2_inv.2.1, hd2_inv.2.2.2.1]
      refine ⟨⟨q + 1, hq_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_⟩, ?_⟩
      · rw [add_mul, one_mul]; wram_simp [hd2_inv.2.1, hd2_inv.2.2.2.1]
      all_goals wram_simp [hd2_inv.2.2.1, hd2_inv.2.2.2.1, hd2_inv.2.2.2.2.1,
        hd2_inv.2.2.2.2.2.1, hd2_inv.2.2.2.2.2.2.1, hd2_inv.2.2.2.2.2.2.2.1,
        hd2_inv.2.2.2.2.2.2.2.2.1, hd2_inv.2.2.2.2.2.2.2.2.2.1]
      · rw [hd2_inv.2.2.2.2.2.2.2.2.2.2 k, add_mul, one_mul, Nat.add_assoc, htwoStep_eq]
      · rw [hb]
        have hpos : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
        have hdiff1 : 2 ^ n - (q * 2 ^ (i + 1) + 2 ^ (i + 1)) =
            (2 ^ (n - 1 - i) - (q + 1)) * 2 ^ (i + 1) := by
          rw [hn_split, show q * 2 ^ (i + 1) + 2 ^ (i + 1) = (q + 1) * 2 ^ (i + 1) by ring,
            ← Nat.sub_mul]
        have hdiff2 : 2 ^ n - q * 2 ^ (i + 1) = (2 ^ (n - 1 - i) - q) * 2 ^ (i + 1) := by
          rw [hn_split, ← Nat.sub_mul]
        rw [hdiff1, hdiff2, Nat.mul_div_cancel _ hpos, Nat.mul_div_cancel _ hpos]
        omega)
    ⟨0, hMid0⟩
  obtain ⟨q_end, hq_end_le, hq_end_b, hq_end_s, hq_end_ts, hq_end_a, hq_end_n, hq_end_1, hq_end_2,
    hq_end_i, hq_end_m1, hq_end_mem⟩ := hMid_end
  have hq_end_eq : q_end = 2 ^ (n - 1 - i) := by
    have hnot : ¬ x2.regs baseReg < x2.regs arrSize := by
      simpa only [Cond.holds_lt] using hstop
    rw [hq_end_b, hq_end_a, hn_split] at hnot
    have : 2 ^ (n - 1 - i) ≤ q_end := Nat.le_of_mul_le_mul_right (Nat.le_of_not_lt hnot)
      (Nat.two_pow_pos _)
    omega
  refine WP.of_execWithin (hx2'.mono (T₂ := 2 ^ (n - 1 - i) * (2 ^ i * (9 + T_op) + 6) + 2) ?_) ?_
  · have hq0_measure : (2 ^ n - x1.regs baseReg) / 2 ^ (i + 1) = 2 ^ (n - 1 - i) := by
      have hx1b : x1.regs baseReg = 0 := by subst hx1'; wram_simp
      rw [hx1b, Nat.sub_zero, hn_split, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    rw [hq0_measure]
  have hi_fit : Fits w (i + 1) := hfit.of_le (by have := Nat.lt_two_pow_self (n := n); omega)
  wram_exec [hq_end_ts, hq_end_i, hq_end_1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · wram_simp [hq_end_1]
  · wram_simp [hq_end_2]
  · wram_simp [hq_end_n]
  · wram_simp [hq_end_a]
  · wram_simp [hq_end_i]
  · wram_simp [hq_end_ts]
  · wram_simp [hq_end_m1]
  · intro k
    wram_simp
    rw [hq_end_mem k, hq_end_eq, ← hn_split, if_congr (and_iff_left k.isLt) rfl rfl]
    by_cases hbit : k.1.testBit i = true
    · simp [hbit]
    · simp [hbit, hnext_def k]

private theorem exec_butterfly {w n B T_op : ℕ} {cellOp : Code .standard 20}
    (opWord : ℕ → ℕ → ℕ)
    (stepTable : Fin n → (Fin (2 ^ n) → ℕ) → Fin (2 ^ n) → ℕ)
    (Pmem : (Fin (2 ^ n) → ℕ) → Prop)
    (t0 : Fin (2 ^ n) → ℕ)
    (hstep_def : ∀ (i : Fin n) (t : Fin (2 ^ n) → ℕ) (k : Fin (2 ^ n)),
      stepTable i t k = if k.1.testBit i.1 then
        opWord (t k) (t ⟨k.1 ^^^ 2 ^ i.1, Nat.xor_lt_two_pow k.isLt
          (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩)
      else t k)
    (hOp : ∀ (x : Data 20) (t : Fin (2 ^ n) → ℕ) (a b : Fin (2 ^ n)),
      Pmem t → x.regs Signed.left = t a → x.regs Signed.right = t b →
      ∃ y, ExecWithin w cellOp x y T_op ∧
        y.regs Signed.result = opWord (t a) (t b) ∧ y.mem = x.mem ∧
        ∀ r : Fin 20, 9 ≤ r.1 → y.regs r = x.regs r)
    (hP_step : ∀ (l : List (Fin n)) (kcut : ℕ) (i : Fin n),
      l.Nodup → i ∉ l →
      let prev := l.foldl (fun t j => stepTable j t) t0
      Pmem prev ∧ Pmem fun k =>
        if k.1.testBit i.1 ∧ k.1 < kcut then stepTable i prev k else prev k)
    (hfit : Fits w (2 ^ n + B + 16))
    (hfit_val : ∀ t, Pmem t → ∀ k, Fits w (t k)) :
    ∃ y, ExecWithin w (butterfly cellOp) (Data.init (n :: List.ofFn t0)) y
      ((4 * n + 10) + (n * (((14 + (T_op + 1) / 2) * 2 ^ n) + 6) + 2)) ∧
      outputList y.mem (y.regs outReg) =
        List.ofFn ((List.finRange n).foldl (fun t j => stepTable j t) t0) ∧
      Fits w (y.regs outReg + (List.ofFn ((List.finRange n).foldl
        (fun t j => stepTable j t) t0)).length) := by
  have hx_len : (Data.init (n :: List.ofFn t0) : Data 20).mem 1 = n := by
    change (Data.init (n :: List.ofFn t0) : Data 20).mem (0 + 1) = n
    rw [Data.init_mem_succ]
    rfl
  obtain ⟨x1, hx1, h1, h2, hn, ha, hi0, hs1, hm1, hm_arr⟩ := exec_setupCode t0 hfit hx_len
  let InvOut (i : ℕ) (d : Data 20) : Prop :=
    i ≤ n ∧
    d.regs outReg = 1 ∧ d.regs twoReg = 2 ∧ d.regs nReg = n ∧ d.regs arrSize = 2 ^ n ∧
    d.regs stepReg = 2 ^ i ∧ d.mem 1 = 2 ^ n ∧
    ∀ k : Fin (2 ^ n), d.mem (2 + k.1) =
      (((List.finRange n).take i).foldl (fun t j => stepTable j t) t0) k
  have hInv0 : InvOut (x1.regs iReg) x1 := by
    rw [hi0]
    refine ⟨Nat.zero_le _, h1, h2, hn, ha, by simpa using hs1, hm1, fun k => ?_⟩
    simpa using hm_arr k
  obtain ⟨x2, hx2, hInv_end, hxi_end⟩ := ExecWithin.loop_count InvOut (fun _ h => h.2.2.2.1)
    (fun d hd hlt => by
      obtain ⟨hi_le, d1, d2, dn, da, ds, dm1, dmem⟩ := hd
      let i : Fin n := ⟨d.regs iReg, hlt⟩
      let l : List (Fin n) := (List.finRange n).take i.1
      have hl_nodup : l.Nodup := List.Nodup.sublist (List.take_sublist _ _) (List.nodup_finRange n)
      have hi_notin : i ∉ l := by
        intro him
        obtain ⟨m, hm, hmeq⟩ := by
          simpa only [l, List.mem_iff_getElem, List.length_take, List.length_finRange] using him
        rw [List.getElem_take, List.getElem_finRange] at hmeq
        have hltm : m < i.1 := by omega
        have hval : m = i.1 := Fin.ext_iff.mp hmeq
        omega
      let prev := l.foldl (fun t j => stepTable j t) t0
      let next := stepTable i prev
      obtain ⟨y, hy, y1, y2, yn, ya, yi, ys, ym1, ymem⟩ := exec_pass opWord prev next Pmem
        hlt (fun k => hstep_def i prev k) hOp
        (hP_step l 0 i hl_nodup hi_notin).1
        (fun kcut => (hP_step l kcut i hl_nodup hi_notin).2)
        hfit hfit_val d d1 d2 dn da rfl ds dmem dm1
      have hbody_le : 2 ^ (n - 1 - d.regs iReg) * (2 ^ d.regs iReg * (9 + T_op) + 6) + 2 + 4 ≤
          (14 + (T_op + 1) / 2) * 2 ^ n + 4 := by
        have hp1 : 2 * (2 ^ (n - 1 - d.regs iReg) * 2 ^ d.regs iReg) = 2 ^ n := by
          rw [← pow_add, show n - 1 - d.regs iReg + d.regs iReg = n - 1 by omega,
            ← pow_succ', show n - 1 + 1 = n by omega]
        have hp2 : 2 ^ (n - 1 - d.regs iReg) ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have hp3 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
        have hp4 : 2 ^ (n - 1 - d.regs iReg) * 2 ^ d.regs iReg * (9 + T_op) ≤
            (5 + (T_op + 1) / 2) * 2 ^ n := by
          have h9 : 9 + T_op ≤ 2 * (5 + (T_op + 1) / 2) := by omega
          calc
            2 ^ (n - 1 - d.regs iReg) * 2 ^ d.regs iReg * (9 + T_op)
                ≤ 2 ^ (n - 1 - d.regs iReg) * 2 ^ d.regs iReg * (2 * (5 + (T_op + 1) / 2)) :=
                    Nat.mul_le_mul_left _ h9
            _ = (5 + (T_op + 1) / 2) * (2 * (2 ^ (n - 1 - d.regs iReg) * 2 ^ d.regs iReg)) := by
                  ring
            _ = (5 + (T_op + 1) / 2) * 2 ^ n := by rw [hp1]
        calc
          2 ^ (n - 1 - d.regs iReg) * (2 ^ d.regs iReg * (9 + T_op) + 6) + 2 + 4
              = 2 ^ (n - 1 - d.regs iReg) * 2 ^ d.regs iReg * (9 + T_op) +
                  6 * 2 ^ (n - 1 - d.regs iReg) + 6 := by ring
          _ ≤ (5 + (T_op + 1) / 2) * 2 ^ n + 6 * 2 ^ n + 2 * 2 ^ n + 4 := by omega
          _ ≤ (14 + (T_op + 1) / 2) * 2 ^ n + 4 := by
              have : 13 ≤ 14 := by decide
              nlinarith
      refine ⟨y, hy.mono hbody_le, ⟨hlt, y1, y2, yn, ya, ys, ym1, fun k => ?_⟩, yi⟩
      rw [ymem k]
      have htake : (List.finRange n).take (d.regs iReg + 1) = l ++ [i] := by
        rw [List.take_succ_eq_append_getElem (by simp [hlt]), List.getElem_finRange]
        rfl
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil])
    (by rw [hi0]; exact Nat.zero_le _) hInv0
  rw [hi0, Nat.sub_zero] at hx2
  refine ⟨x2, hx1.seq hx2, ?_, ?_⟩
  · refine outputList_eq_iff.2 ⟨?_, fun k => ?_⟩
    · simp [hInv_end.2.1, hInv_end.2.2.2.2.2.2.1]
    · change x2.mem (x2.regs outReg + 1 + k.1) =
        (List.ofFn ((List.finRange n).foldl (fun t j => stepTable j t) t0))[k.1]
      rw [hInv_end.2.1, show 1 + 1 + k.1 = 2 + k.1 by omega, List.getElem_ofFn]
      have hmemk := hInv_end.2.2.2.2.2.2.2 ⟨k.1, by simpa using k.isLt⟩
      have htake : (List.finRange n).take n = List.finRange n := by simp
      simpa [htake] using hmemk
  · rw [hInv_end.2.1, List.length_ofFn]
    exact hfit.of_le (by omega)

/-! ## Public correctness and running-time theorems -/

private theorem foldl_yatesPass_eq_of_fn {M R : Type*} [AddCommMonoid M] [Monoid R]
    [DistribMulAction R M] {n : ℕ} (c : R) (f₀ : Finset (Fin n) → M) :
    ∀ (l : List (Fin n)) (k : Fin (2 ^ n)),
      (l.foldl (fun t (i : Fin n) => fun m : Fin (2 ^ n) =>
        if m.1.testBit i.1 then t m + c • t ⟨m.1 ^^^ 2 ^ i.1, Nat.xor_lt_two_pow m.isLt
          (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩ else t m)
        (fun m => f₀ (maskSet n m.1))) k =
      yatesTransform c l f₀ (maskSet n k.1)
  | [], k => rfl
  | i :: l, k => by
    simp only [List.foldl_cons, yatesTransform_cons]
    have hstep : (fun m : Fin (2 ^ n) =>
        if m.1.testBit i.1 then
          f₀ (maskSet n m.1) + c • f₀ (maskSet n (m.1 ^^^ 2 ^ i.1))
        else f₀ (maskSet n m.1)) =
        fun m : Fin (2 ^ n) => yatesPass c i f₀ (maskSet n m.1) := by
      funext m
      simp only [yatesPass, mem_maskSet]
      split_ifs with hm
      · rw [maskSet_xor_two_pow hm]
      · rfl
    rw [hstep]
    exact foldl_yatesPass_eq_of_fn c (yatesPass c i f₀) l k

private theorem nat_yatesTransform_le (I : NatInstance) {l : List (Fin I.n)} (hl : l.Nodup)
    (k : Fin (2 ^ I.n)) :
    yatesTransform (1 : ℕ) l (fun S => I.entries[(maskIndex S).1]) (maskSet I.n k.1) ≤
      I.totalSum := by
  rw [yatesTransform_apply (1 : ℕ) hl]
  simp only [one_pow, one_smul]
  let φ : Finset (Fin I.n) → Fin (2 ^ I.n) := fun U => maskIndex (maskSet I.n k.1 \ U)
  have hinj : Set.InjOn φ ↑(maskSet I.n k.1 ∩ l.toFinset).powerset := by
    intro U₁ hU₁ U₂ hU₂ hEq
    have hU₁S : U₁ ⊆ maskSet I.n k.1 := (Finset.mem_powerset.mp hU₁).trans Finset.inter_subset_left
    have hU₂S : U₂ ⊆ maskSet I.n k.1 := (Finset.mem_powerset.mp hU₂).trans Finset.inter_subset_left
    have hset : maskSet I.n k.1 \ U₁ = maskSet I.n k.1 \ U₂ := by
      have := congrArg (fun x => maskSet I.n x.1) hEq
      simpa [φ, maskSet_maskIndex] using this
    calc
      U₁ = maskSet I.n k.1 \ (maskSet I.n k.1 \ U₁) := (Finset.sdiff_sdiff_eq_self hU₁S).symm
      _ = maskSet I.n k.1 \ (maskSet I.n k.1 \ U₂) := by rw [hset]
      _ = U₂ := Finset.sdiff_sdiff_eq_self hU₂S
  calc
    ∑ U ∈ (maskSet I.n k.1 ∩ l.toFinset).powerset, I.entries[(maskIndex (maskSet I.n k.1 \ U)).1]
        = ∑ U ∈ (maskSet I.n k.1 ∩ l.toFinset).powerset, I.entries[(φ U).1] := rfl
    _ ≤ ∑ m : Fin (2 ^ I.n), I.entries[m.1] := by
        rw [← Finset.sum_image (f := fun m : Fin (2 ^ I.n) => I.entries[m.1])
          (fun _ h₁ _ h₂ => hinj h₁ h₂)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
    _ = I.totalSum := rfl

private theorem int_yatesTransform_natAbs_le (I : IntInstance) (c : ℤ) (hc : c.natAbs = 1)
    {l : List (Fin I.n)} (hl : l.Nodup) (k : Fin (2 ^ I.n)) :
    (yatesTransform c l (fun S => I.entries[(maskIndex S).1]) (maskSet I.n k.1)).natAbs ≤
      I.sumAbs := by
  rw [yatesTransform_apply c hl]
  let φ : Finset (Fin I.n) → Fin (2 ^ I.n) := fun U => maskIndex (maskSet I.n k.1 \ U)
  have hinj : Set.InjOn φ ↑(maskSet I.n k.1 ∩ l.toFinset).powerset := by
    intro U₁ hU₁ U₂ hU₂ hEq
    have hU₁S : U₁ ⊆ maskSet I.n k.1 := (Finset.mem_powerset.mp hU₁).trans Finset.inter_subset_left
    have hU₂S : U₂ ⊆ maskSet I.n k.1 := (Finset.mem_powerset.mp hU₂).trans Finset.inter_subset_left
    have hset : maskSet I.n k.1 \ U₁ = maskSet I.n k.1 \ U₂ := by
      have := congrArg (fun x => maskSet I.n x.1) hEq
      simpa [φ, maskSet_maskIndex] using this
    calc
      U₁ = maskSet I.n k.1 \ (maskSet I.n k.1 \ U₁) := (Finset.sdiff_sdiff_eq_self hU₁S).symm
      _ = maskSet I.n k.1 \ (maskSet I.n k.1 \ U₂) := by rw [hset]
      _ = U₂ := Finset.sdiff_sdiff_eq_self hU₂S
  have htri : (∑ U ∈ (maskSet I.n k.1 ∩ l.toFinset).powerset,
        c ^ #U • I.entries[(φ U).1]).natAbs ≤
      ∑ U ∈ (maskSet I.n k.1 ∩ l.toFinset).powerset, I.entries[(φ U).1].natAbs := by
    refine (Int.natAbs_sum_le _ _).trans (Finset.sum_le_sum fun U _ => ?_)
    rw [smul_eq_mul, Int.natAbs_mul, Int.natAbs_pow, hc, one_pow, one_mul]
  calc
    (∑ U ∈ (maskSet I.n k.1 ∩ l.toFinset).powerset, c ^ #U • I.entries[(φ U).1]).natAbs
        ≤ ∑ U ∈ (maskSet I.n k.1 ∩ l.toFinset).powerset, I.entries[(φ U).1].natAbs := htri
    _ ≤ ∑ m : Fin (2 ^ I.n), I.entries[m.1].natAbs := by
        rw [← Finset.sum_image (f := fun m : Fin (2 ^ I.n) => I.entries[m.1].natAbs)
          (fun _ h₁ _ h₂ => hinj h₁ h₂)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
    _ = I.sumAbs := rfl

private theorem foldl_nat_eq_zeta (I : NatInstance) :
    List.ofFn ((List.finRange I.n).foldl
      (fun t (i : Fin I.n) => fun m : Fin (2 ^ I.n) =>
        if m.1.testBit i.1 then t m + t ⟨m.1 ^^^ 2 ^ i.1, Nat.xor_lt_two_pow m.isLt
          (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩ else t m)
      (fun m : Fin (2 ^ I.n) => I.entries[m.1])) =
      (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList := by
  refine List.ext_getElem (by simp) fun k hk _ => ?_
  have hk' : k < 2 ^ I.n := by simpa using hk
  rw [List.getElem_ofFn, Vector.getElem_toList]
  have heq := foldl_yatesPass_eq_of_fn (1 : ℕ) (fun S => I.entries[(maskIndex S).1])
    (List.finRange I.n) ⟨k, hk'⟩
  simp only [one_smul] at heq
  have hbase : (fun m : Fin (2 ^ I.n) => I.entries[(maskIndex (maskSet I.n m.1)).1]) =
      fun m : Fin (2 ^ I.n) => I.entries[m.1] := by
    funext m; simp
  rw [hbase] at heq
  rw [heq, yatesTransform_one_apply (List.nodup_finRange I.n) _ (by simp),
    ← getElem_zeta I.entries (fun S => I.entries[(maskIndex S).1])
      (getElem_eq_maskIndex_maskSet I.entries) k hk']

private theorem yatesTime_le (n T_op : ℕ) :
    ((4 * n + 10) + (n * (((14 + (T_op + 1) / 2) * 2 ^ n) + 6) + 2)) + 1 ≤
      (24 + (T_op + 1) / 2 + 15) * ((n + 1) * 2 ^ n) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hn : n ≤ n * 2 ^ n := Nat.le_mul_of_pos_right n h1
  set c := (T_op + 1) / 2
  calc
    ((4 * n + 10) + (n * (((14 + c) * 2 ^ n) + 6) + 2)) + 1
        = (14 + c) * (n * 2 ^ n) + 10 * n + 13 := by ring
    _ ≤ (14 + c) * (n * 2 ^ n) + 10 * (n * 2 ^ n) + 13 * 2 ^ n := by omega
    _ ≤ (24 + c + 15) * ((n + 1) * 2 ^ n) := by nlinarith

/-- **Unsigned fast zeta transform on the word RAM (`O((n + 1) · 2 ^ n)`).** At every width
`w` with `I.FitsWidth w`, `zetaNatProgram` halts within `40 * ((I.n + 1) * 2 ^ I.n)` instructions
and outputs `(Yates.zeta I.entries).toList`. -/
theorem executesList_zetaNatProgram (I : NatInstance) {w : ℕ} (hfit : I.FitsWidth w) :
    ∃ steps ≤ 40 * ((I.n + 1) * 2 ^ I.n),
      ExecutesList w zetaNatProgram (State.init I.encode)
        (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList steps := by
  let t0 : Fin (2 ^ I.n) → ℕ := fun m => I.entries[m.1]
  let Pmem : (Fin (2 ^ I.n) → ℕ) → Prop := fun t => ∀ k, t k ≤ I.totalSum
  let stepTable (i : Fin I.n) (t : Fin (2 ^ I.n) → ℕ) (k : Fin (2 ^ I.n)) : ℕ :=
    if k.1.testBit i.1 then t k + t ⟨k.1 ^^^ 2 ^ i.1, Nat.xor_lt_two_pow k.isLt
      (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩ else t k
  have hInit : Data.init I.encode = (Data.init (I.n :: List.ofFn t0) : Data 20) := by
    congr 2
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [NatInstance.encode, List.getElem_cons]
    split_ifs with hi0
    · rfl
    · simp only [List.getElem_ofFn, t0, Vector.getElem_toList]
  have hfit_sub : Fits w (2 ^ I.n + I.totalSum + 16) :=
    hfit.of_le (by unfold NatInstance.wordBound; omega)
  have hOp : ∀ (x : Data 20) (t : Fin (2 ^ I.n) → ℕ) (a b : Fin (2 ^ I.n)),
      Pmem t → x.regs Signed.left = t a → x.regs Signed.right = t b →
      ∃ y, ExecWithin w natAddOp x y 1 ∧
        y.regs Signed.result = t a + t b ∧ y.mem = x.mem ∧
        ∀ r : Fin 20, 9 ≤ r.1 → y.regs r = x.regs r := by
    intro x t a b hP hla hrb
    have h2n : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
    have hsum_fit : Fits w (x.regs Signed.left + x.regs Signed.right) := by
      rw [hla, hrb]
      exact hfit.of_le (calc
        t a + t b ≤ I.totalSum + I.totalSum := Nat.add_le_add (hP a) (hP b)
        _ ≤ I.wordBound := by unfold NatInstance.wordBound; omega)
    refine ⟨x.set Signed.result (x.regs Signed.left + x.regs Signed.right), ?_, ?_, rfl,
      fun r hr => ?_⟩
    · unfold natAddOp; wram_exec
    · wram_simp [hla, hrb]
    · wram_simp [show r ≠ Signed.result by intro h; subst h; simp at hr]
  have hP_step : ∀ (l : List (Fin I.n)) (kcut : ℕ) (i : Fin I.n),
      l.Nodup → i ∉ l →
      let prev := l.foldl (fun t j => stepTable j t) t0
      Pmem prev ∧ Pmem fun k =>
        if k.1.testBit i.1 ∧ k.1 < kcut then stepTable i prev k else prev k := by
    intro l kcut i hl hi
    have hfold_eq : ∀ (l' : List (Fin I.n)), l'.Nodup → ∀ k,
        (l'.foldl (fun t j => stepTable j t) t0) k ≤ I.totalSum := by
      intro l' hl' k
      have heq := foldl_yatesPass_eq_of_fn (1 : ℕ) (fun S => I.entries[(maskIndex S).1]) l' k
      simp only [one_smul] at heq
      have hbase : (fun m : Fin (2 ^ I.n) => I.entries[(maskIndex (maskSet I.n m.1)).1]) = t0 := by
        funext m; simp [t0]
      rw [hbase] at heq
      change (l'.foldl (fun t j => stepTable j t) t0) k = _ at heq
      rw [heq]
      exact nat_yatesTransform_le I hl' k
    have hprev : Pmem (l.foldl (fun t j => stepTable j t) t0) := hfold_eq l hl
    have hnext : Pmem (stepTable i (l.foldl (fun t j => stepTable j t) t0)) := by
      have hconcat : stepTable i (l.foldl (fun t j => stepTable j t) t0) =
          (l ++ [i]).foldl (fun t j => stepTable j t) t0 := by
        simp [List.foldl_append]
      rw [hconcat]
      have hnodup' : (l ++ [i]).Nodup :=
        List.nodup_append.mpr ⟨hl, List.nodup_singleton i, fun a ha b hb heq => by
          simp only [List.mem_singleton] at hb
          subst hb
          subst heq
          exact hi ha⟩
      exact hfold_eq (l ++ [i]) hnodup'
    refine ⟨hprev, fun k => ?_⟩
    dsimp only
    split_ifs
    · exact hnext k
    · exact hprev k
  obtain ⟨y, hy_ex, hy_out, hy_fit⟩ := exec_butterfly (· + ·) stepTable Pmem t0
    (fun i t k => rfl) hOp hP_step hfit_sub (fun t hP k => hfit.of_le (by
      have := hP k; have := Nat.one_le_two_pow (n := I.n)
      unfold NatInstance.wordBound; omega))
  obtain ⟨steps, hsteps, hex⟩ := hy_ex
  have htime : steps + 1 ≤ 40 * ((I.n + 1) * 2 ^ I.n) := by
    have h1 := yatesTime_le I.n 1
    omega
  rw [← hInit] at hex
  rw [foldl_nat_eq_zeta I] at hy_out hy_fit
  refine ⟨steps + 1, htime, ?_⟩
  have hexL := hex.executesList outReg (by rwa [hy_out])
  rwa [hy_out] at hexL

/-- Fixed-program `Program.ComputesListInTime` certificate for `zetaNatProgram`. -/
theorem computesListInTime_zetaNatProgram :
    zetaNatProgram.ComputesListInTime (fun _ I => I.encode)
      (fun I _ => 40 * ((I.n + 1) * 2 ^ I.n)) NatInstance.FitsWidth
      (fun I => (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList) := by
  intro I w hfit _
  obtain ⟨steps, hle, hex⟩ := executesList_zetaNatProgram I hfit
  exact ⟨steps, hex, hle⟩

private theorem foldl_int_yatesPass_eq {n : ℕ} (c : ℤ) (F₀ : Finset (Fin n) → ℤ) :
    ∀ (l : List (Fin n)) (k : Fin (2 ^ n)),
      (l.foldl (fun t (i : Fin n) => fun m : Fin (2 ^ n) =>
        if m.1.testBit i.1 then
          Signed.encode (Signed.decode (t m) + c * Signed.decode (t ⟨m.1 ^^^ 2 ^ i.1,
            Nat.xor_lt_two_pow m.isLt (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩))
        else t m)
        (fun m => Signed.encode (F₀ (maskSet n m.1)))) k =
      Signed.encode (yatesTransform c l F₀ (maskSet n k.1))
  | [], k => rfl
  | i :: l, k => by
    simp only [List.foldl_cons, yatesTransform_cons]
    have hstep : (fun m : Fin (2 ^ n) =>
        if m.1.testBit i.1 then
          Signed.encode (Signed.decode (Signed.encode (F₀ (maskSet n m.1))) +
            c * Signed.decode (Signed.encode (F₀ (maskSet n (m.1 ^^^ 2 ^ i.1)))))
        else Signed.encode (F₀ (maskSet n m.1))) =
        fun m : Fin (2 ^ n) => Signed.encode (yatesPass c i F₀ (maskSet n m.1)) := by
      funext m
      simp only [yatesPass, mem_maskSet, Signed.decode_encode, smul_eq_mul]
      split_ifs with hm
      · rw [maskSet_xor_two_pow hm]
      · rfl
    rw [hstep]
    exact foldl_int_yatesPass_eq c (yatesPass c i F₀) l k

private theorem foldl_int_eq_transform (I : IntInstance) (c : ℤ) (hc : c = 1 ∨ c = -1) :
    List.ofFn ((List.finRange I.n).foldl
      (fun t (i : Fin I.n) => fun m : Fin (2 ^ I.n) =>
        if m.1.testBit i.1 then
          Signed.encode (Signed.decode (t m) + c * Signed.decode (t ⟨m.1 ^^^ 2 ^ i.1,
            Nat.xor_lt_two_pow m.isLt (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩))
        else t m)
      (fun m : Fin (2 ^ I.n) => Signed.encode I.entries[m.1])) =
      (if c = 1 then Cslib.Algorithms.Lean.Yates.zeta I.entries
       else Cslib.Algorithms.Lean.Yates.mobius I.entries).toList.map Signed.encode := by
  have h0 : (fun m : Fin (2 ^ I.n) => Signed.encode I.entries[m.1]) =
      fun m => Signed.encode (I.entries[(maskIndex (maskSet I.n m.1)).1]) := by
    funext m; simp
  rcases hc with rfl | rfl
  · simp only [↓reduceIte]
    refine List.ext_getElem (by simp) fun k hk _ => ?_
    have hk' : k < 2 ^ I.n := by simpa using hk
    rw [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
    have hlift := foldl_int_yatesPass_eq (1 : ℤ) (fun S => I.entries[(maskIndex S).1])
      (List.finRange I.n) ⟨k, hk'⟩
    rw [← h0] at hlift
    rw [hlift]
    congr 1
    rw [yatesTransform_apply_of_subset (1 : ℤ) (List.nodup_finRange I.n) _ (by simp)]
    simp only [one_pow, one_smul]
    rw [getElem_zeta I.entries (fun S => I.entries[(maskIndex S).1])
      (getElem_eq_maskIndex_maskSet I.entries) k hk', subsetZeta]
  · simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte]
    refine List.ext_getElem (by simp) fun k hk _ => ?_
    have hk' : k < 2 ^ I.n := by simpa using hk
    rw [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
    have hlift := foldl_int_yatesPass_eq (-1 : ℤ) (fun S => I.entries[(maskIndex S).1])
      (List.finRange I.n) ⟨k, hk'⟩
    rw [← h0] at hlift
    rw [hlift]
    congr 1
    rw [yatesTransform_neg_one_apply (List.nodup_finRange I.n) _ (by simp),
      ← getElem_mobius I.entries (fun S => I.entries[(maskIndex S).1])
        (getElem_eq_maskIndex_maskSet I.entries) k hk']

private theorem executesList_signedTransform (isMobius : Bool) (I : IntInstance) {w : ℕ}
    (hfit : I.FitsWidth w) :
    ∃ steps ≤ 48 * ((I.n + 1) * 2 ^ I.n),
      ExecutesList w
        ((butterfly (if isMobius then Signed.subtract (r := 11) else Signed.add (r := 11))).program
          outReg)
        (State.init I.encode)
        ((if isMobius then Cslib.Algorithms.Lean.Yates.mobius I.entries
          else Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map Signed.encode)
        steps := by
  let c : ℤ := if isMobius then -1 else 1
  have hc_abs : c.natAbs = 1 := by cases isMobius <;> simp [c]
  let t0 : Fin (2 ^ I.n) → ℕ := fun m => Signed.encode I.entries[m.1]
  let Pmem : (Fin (2 ^ I.n) → ℕ) → Prop :=
    fun t => ∀ k, ∃ z : ℤ, z.natAbs ≤ I.sumAbs ∧ t k = Signed.encode z
  let opWord : ℕ → ℕ → ℕ := fun wa wb => Signed.encode (Signed.decode wa + c * Signed.decode wb)
  let stepTable (i : Fin I.n) (t : Fin (2 ^ I.n) → ℕ) (k : Fin (2 ^ I.n)) : ℕ :=
    if k.1.testBit i.1 then
      opWord (t k) (t ⟨k.1 ^^^ 2 ^ i.1, Nat.xor_lt_two_pow k.isLt
        (Nat.pow_lt_pow_right (by norm_num) i.isLt)⟩)
    else t k
  have hInit : I.encode = I.n :: List.ofFn t0 := by
    refine congrArg (I.n :: ·) (List.ext_getElem (by simp) fun i hi _ => ?_)
    have hi' : i < 2 ^ I.n := by simpa using hi
    simp only [List.getElem_map, List.getElem_ofFn, t0, Vector.getElem_toList]
  have hSfit : GenericRAM.Signed.Fits (w - 2) (I.sumAbs : ℤ) := I.signedFits_sumAbs hfit
  have hw8 : 8 ≤ w := I.eight_le_width hfit
  have hw_eq : (w - 2) + 2 = w := by omega
  have hfit_sub : Fits w (2 ^ I.n + I.sumAbs + 16) :=
    hfit.of_le (by unfold IntInstance.wordBound; omega)
  have hOp : ∀ (x : Data 20) (t : Fin (2 ^ I.n) → ℕ) (a b : Fin (2 ^ I.n)),
      Pmem t → x.regs Signed.left = t a → x.regs Signed.right = t b →
      ∃ y, ExecWithin w (if isMobius then Signed.subtract (r := 11) else Signed.add (r := 11)) x y
          17 ∧
        y.regs Signed.result = opWord (t a) (t b) ∧ y.mem = x.mem ∧
        ∀ r : Fin 20, 9 ≤ r.1 → y.regs r = x.regs r := by
    intro x t a b hP hla hrb
    obtain ⟨za, hza_abs, hza_eq⟩ := hP a
    obtain ⟨zb, hzb_abs, hzb_eq⟩ := hP b
    have ha_fit : GenericRAM.Signed.Fits (w - 2) za := hSfit.of_natAbs_le hza_abs
    have hb_fit : GenericRAM.Signed.Fits (w - 2) zb := hSfit.of_natAbs_le hzb_abs
    cases isMobius
    · obtain ⟨y, hy_ex, hy_res, hy_mem, hy_reg⟩ := Signed.exec_add ha_fit hb_fit x
        (by rw [hla, hza_eq]) (by rw [hrb, hzb_eq])
      rw [hw_eq] at hy_ex
      refine ⟨y, hy_ex.mono (by omega), ?_, hy_mem, fun r hr => hy_reg r (Or.inr hr)⟩
      simpa [opWord, c, hza_eq, hzb_eq, GenericRAM.Signed.Arithmetic.eval] using hy_res
    · obtain ⟨y, hy_ex, hy_res, hy_mem, hy_reg⟩ := Signed.exec_subtract ha_fit hb_fit x
        (by rw [hla, hza_eq]) (by rw [hrb, hzb_eq])
      rw [hw_eq] at hy_ex
      refine ⟨y, hy_ex, ?_, hy_mem, fun r hr => hy_reg r (Or.inr hr)⟩
      simpa [opWord, c, hza_eq, hzb_eq, GenericRAM.Signed.Arithmetic.eval, sub_eq_add_neg] using
        hy_res
  have hP_step : ∀ (l : List (Fin I.n)) (kcut : ℕ) (i : Fin I.n),
      l.Nodup → i ∉ l →
      let prev := l.foldl (fun t j => stepTable j t) t0
      Pmem prev ∧ Pmem fun k =>
        if k.1.testBit i.1 ∧ k.1 < kcut then stepTable i prev k else prev k := by
    intro l kcut i hl hi
    have hfold_eq : ∀ (l' : List (Fin I.n)) (k : Fin (2 ^ I.n)),
        (l'.foldl (fun t j => stepTable j t) t0) k =
          Signed.encode (yatesTransform c l' (fun S => I.entries[(maskIndex S).1])
            (maskSet I.n k.1)) := by
      intro l' k
      have h0 : t0 = fun m => Signed.encode (I.entries[(maskIndex (maskSet I.n m.1)).1]) := by
        funext m; simp [t0]
      have hlift := foldl_int_yatesPass_eq c (fun S => I.entries[(maskIndex S).1]) l' k
      rw [← h0] at hlift
      exact hlift
    have hprev : Pmem (l.foldl (fun t j => stepTable j t) t0) := fun k =>
      ⟨_, int_yatesTransform_natAbs_le I c hc_abs hl k, hfold_eq l k⟩
    have hnext : Pmem (stepTable i (l.foldl (fun t j => stepTable j t) t0)) := fun k => by
      have hconcat : stepTable i (l.foldl (fun t j => stepTable j t) t0) =
          (l ++ [i]).foldl (fun t j => stepTable j t) t0 := by
        simp [List.foldl_append]
      rw [hconcat]
      have hnodup' : (l ++ [i]).Nodup :=
        List.nodup_append.mpr ⟨hl, List.nodup_singleton i, fun a ha b hb heq => by
          simp only [List.mem_singleton] at hb
          subst hb
          subst heq
          exact hi ha⟩
      exact ⟨_, int_yatesTransform_natAbs_le I c hc_abs hnodup' k,
        hfold_eq (l ++ [i]) k⟩
    refine ⟨hprev, fun k => ?_⟩
    dsimp only
    split_ifs
    · exact hnext k
    · exact hprev k
  obtain ⟨y, hy_ex, hy_out, hy_fit⟩ := exec_butterfly opWord stepTable Pmem t0
    (fun i t k => rfl) hOp hP_step hfit_sub (fun t hP k => by
      obtain ⟨z, hz_abs, hz_eq⟩ := hP k
      rw [hz_eq]
      exact I.fits_signedEncode hfit hz_abs)
  obtain ⟨steps, hsteps, hex⟩ := hy_ex
  have htime : steps + 1 ≤ 48 * ((I.n + 1) * 2 ^ I.n) := by
    have h1 := yatesTime_le I.n 17
    omega
  have hlist : List.ofFn ((List.finRange I.n).foldl (fun t j => stepTable j t) t0) =
      (if isMobius then Cslib.Algorithms.Lean.Yates.mobius I.entries
       else Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map Signed.encode := by
    cases isMobius
    · have h1 := foldl_int_eq_transform I 1 (Or.inl rfl)
      simp only [↓reduceIte] at h1
      simpa only [Bool.false_eq_true, ↓reduceIte, c, stepTable, opWord, one_mul, t0] using h1
    · have h1 := foldl_int_eq_transform I (-1) (Or.inr rfl)
      simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte] at h1
      simpa only [↓reduceIte, c, stepTable, opWord, neg_one_mul, t0] using h1
  rw [← hInit] at hex
  rw [hlist] at hy_out hy_fit
  refine ⟨steps + 1, htime, ?_⟩
  have hexL := hex.executesList outReg (by rwa [hy_out])
  rwa [hy_out] at hexL

/-- **Signed fast zeta transform on the word RAM (`O((n + 1) · 2 ^ n)`).** At every width `w`
with `I.FitsWidth w`, `zetaIntProgram` halts within `48 * ((I.n + 1) * 2 ^ I.n)` instructions and
outputs `(Yates.zeta I.entries).toList.map Signed.encode`. -/
theorem executesList_zetaIntProgram (I : IntInstance) {w : ℕ} (hfit : I.FitsWidth w) :
    ∃ steps ≤ 48 * ((I.n + 1) * 2 ^ I.n),
      ExecutesList w zetaIntProgram (State.init I.encode)
        ((Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map Signed.encode) steps := by
  simpa [zetaIntProgram] using executesList_signedTransform false I hfit

/-- Fixed-program `Program.ComputesListInTime` certificate for `zetaIntProgram`. -/
theorem computesListInTime_zetaIntProgram :
    zetaIntProgram.ComputesListInTime (fun _ I => I.encode)
      (fun I _ => 48 * ((I.n + 1) * 2 ^ I.n)) IntInstance.FitsWidth
      (fun I => (Cslib.Algorithms.Lean.Yates.zeta I.entries).toList.map Signed.encode) := by
  intro I w hfit _
  obtain ⟨steps, hle, hex⟩ := executesList_zetaIntProgram I hfit
  exact ⟨steps, hex, hle⟩

/-- **Signed fast Möbius transform on the word RAM (`O((n + 1) · 2 ^ n)`).** At every width `w`
with `I.FitsWidth w`, `mobiusIntProgram` halts within `48 * ((I.n + 1) * 2 ^ I.n)` instructions and
outputs `(Yates.mobius I.entries).toList.map Signed.encode`. -/
theorem executesList_mobiusIntProgram (I : IntInstance) {w : ℕ} (hfit : I.FitsWidth w) :
    ∃ steps ≤ 48 * ((I.n + 1) * 2 ^ I.n),
      ExecutesList w mobiusIntProgram (State.init I.encode)
        ((Cslib.Algorithms.Lean.Yates.mobius I.entries).toList.map Signed.encode) steps := by
  simpa [mobiusIntProgram] using executesList_signedTransform true I hfit

/-- Fixed-program `Program.ComputesListInTime` certificate for `mobiusIntProgram`. -/
theorem computesListInTime_mobiusIntProgram :
    mobiusIntProgram.ComputesListInTime (fun _ I => I.encode)
      (fun I _ => 48 * ((I.n + 1) * 2 ^ I.n)) IntInstance.FitsWidth
      (fun I => (Cslib.Algorithms.Lean.Yates.mobius I.entries).toList.map Signed.encode) := by
  intro I w hfit _
  obtain ⟨steps, hle, hex⟩ := executesList_mobiusIntProgram I hfit
  exact ⟨steps, hex, hle⟩

private theorem not_readsWidth_butterfly {cellOp : Code .standard 20}
    (h : ¬ cellOp.ReadsWidth) : ¬ (butterfly cellOp).ReadsWidth := by
  simp only [butterfly, setupCode, butterflyLoop, innerBody, Code.ReadsWidth, Op.ReadsWidth,
    Op.bin, not_or]
  repeat (first | exact h | constructor | decide)

private theorem isRandFree_butterfly {cellOp : Code .standard 20}
    (h : cellOp.IsRandFree) : (butterfly cellOp).IsRandFree := by
  simp only [butterfly, setupCode, butterflyLoop, innerBody, Code.IsRandFree]
  tauto

/-- `zetaNatProgram` does not read the word width (`width%`). -/
theorem not_readsWidth_zetaNatProgram : ¬ zetaNatProgram.ReadsWidth := by
  rw [zetaNatProgram]
  exact Code.not_readsWidth_program (not_readsWidth_butterfly (by
    simp only [natAddOp, Code.ReadsWidth, Op.ReadsWidth, Op.bin]
    decide)) _

/-- `zetaNatProgram` is deterministic (`rand`-free). -/
theorem isRandFree_zetaNatProgram : zetaNatProgram.IsRandFree := by
  rw [zetaNatProgram, Code.isRandFree_program]
  exact isRandFree_butterfly (by simp [natAddOp, Code.IsRandFree])

/-- `zetaIntProgram` does not read the word width (`width%`). -/
theorem not_readsWidth_zetaIntProgram : ¬ zetaIntProgram.ReadsWidth := by
  rw [zetaIntProgram]
  exact Code.not_readsWidth_program (not_readsWidth_butterfly (by decide +kernel)) _

/-- `zetaIntProgram` is deterministic (`rand`-free). -/
theorem isRandFree_zetaIntProgram : zetaIntProgram.IsRandFree := by
  rw [zetaIntProgram, Code.isRandFree_program]
  exact isRandFree_butterfly (by decide +kernel)

/-- `mobiusIntProgram` does not read the word width (`width%`). -/
theorem not_readsWidth_mobiusIntProgram : ¬ mobiusIntProgram.ReadsWidth := by
  rw [mobiusIntProgram]
  exact Code.not_readsWidth_program (not_readsWidth_butterfly (by decide +kernel)) _

/-- `mobiusIntProgram` is deterministic (`rand`-free). -/
theorem isRandFree_mobiusIntProgram : mobiusIntProgram.IsRandFree := by
  rw [mobiusIntProgram, Code.isRandFree_program]
  exact isRandFree_butterfly (by decide +kernel)

end Cslib.Algorithms.WordRAM.Yates
