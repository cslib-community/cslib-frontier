/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.MemoryView
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Probability.Product

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Freivalds
public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Randomized.Law
public import Mathlib.Data.ZMod.Basic

/-!
# Freivalds' Matrix-Product Verifier on the Randomized Word RAM

`Cslib.Algorithms.WordRAM.Freivalds.verifyProgram` implements Freivalds' `k`-trial randomized
matrix-product verifier (`[Freivalds1977]`, `[Freivalds1979]`; `[MitzenmacherUpfal2017]`,
Section 1.3; `[MotwaniRaghavan95]`, Section 7.1) on the randomized word RAM (`Cslib.WordRAM.runRand`
over `Basis.standard`).

On input `encode q k A B C`, storing a positive modulus `q`, trial count `k`, dimensions `l`, `m`,
`n`, and the row-major entries `(M i j).val` of `A : Matrix (Fin l) (Fin m) (ZMod q)`,
`B : Matrix (Fin m) (Fin n) (ZMod q)` and `C : Matrix (Fin l) (Fin n) (ZMod q)`:

1. `setupCode` loads the header parameters and locates four disjoint scratch slices immediately
   after the input for a length-`n` `0`/`1` vector `x` and three modular product vectors `y`, `z`,
   `w`;
2. each of `k` independent trials samples `n` uniform bits via `rand one` (`sampleVecCode`),
   evaluates `y = B *ᵥ (bit ∘ x)`, `z = A *ᵥ y` and `w = C *ᵥ (bit ∘ x)` modulo `q` through a
   shared deterministic matrix-vector subroutine (`mulVecCode`), compares `z` with `w`
   (`vecEqCode`), and folds the Boolean result into `allOk`;
3. the compiled program halts with `1` when all `k` trials pass and `0` otherwise.

Whenever `Fits w (wordBound q k l m n)` holds (`w = O(log (q² + k + l m + m n + l n))`, and in
particular `w = O(log (n + k + 2))` for `n × n` matrices over `ZMod 2`), `verifyProgram_spec`
proves:

* **Worst-case instruction bound:** every execution path halts cleanly within
  `verifyTime k l m n = k * (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 6 * n + 38) + 26`
  instructions (`verifySquareTime k n = k * (36 * n ^ 2 + 46 * n + 38) + 26 = O(k n²)` for square
  `n × n` matrices);
* **Randomness budget:** every path executes at most `k * n` `rand` instructions (`rand one`,
  consuming at most `k * n` entropy bits under `RandBitsBounded`);
* **Exact distributional bridge:** the halting acceptance bit `cfgAccepts` has exact law
  `ProbComp.eval (Cslib.Algorithms.Lean.Freivalds.verify bit k A B C)`, immediately transferring
  perfect completeness (`verifyProgram_accept_of_mul_eq`: probability `1` when `A * B = C`) and
  one-sided soundness (`verifyProgram_accept_le_of_mul_ne`: error probability at most `2⁻¹ ^ k`
  when `A * B ≠ C`, over every modulus `q ≥ 1`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Freivalds.encodeMatrix`,
  `Cslib.Algorithms.WordRAM.Freivalds.encode`: row-major matrix and verifier input word layouts.
* `Cslib.Algorithms.WordRAM.Freivalds.wordBound`: sufficient word-width bound ensuring input and
  intermediate-value fit.
* `Cslib.Algorithms.WordRAM.Freivalds.mulVecCode`, `sampleVecCode`, `vecEqCode`, `verifyCode`,
  `verifyProgram`: structured subroutines and compiled randomized word-RAM program.
* `Cslib.Algorithms.WordRAM.Freivalds.verifyTime`, `verifySquareTime`: worst-case instruction
  bounds for rectangular and square instances.
* `Cslib.Algorithms.WordRAM.Freivalds.cfgAccepts`: whether a halting configuration output `1`.

## Main results

* `Cslib.Algorithms.WordRAM.Freivalds.mulVecCode_spec`: deterministic modular matrix-vector
  multiplication contract on `Code .standard`.
* `Cslib.Algorithms.WordRAM.Freivalds.verifyProgram_spec`: worst-case halting, `k * n` `rand`-call
  and entropy-bit bounds, and exact distributional equality with
  `Cslib.Algorithms.Lean.Freivalds.verify bit k A B C`.
* `Cslib.Algorithms.WordRAM.Freivalds.verifyProgram_accept_of_mul_eq`: perfect completeness when
  `A * B = C`.
* `Cslib.Algorithms.WordRAM.Freivalds.verifyProgram_accept_le_of_mul_ne`: acceptance probability at
  most `2⁻¹ ^ k` when `A * B ≠ C`.
* `Cslib.Algorithms.WordRAM.Freivalds.verifyProgram_square_spec`: specialization to square `n × n`
  matrices in `verifySquareTime k n = O(k n²)` instructions.

## References

* [R. Freivalds, *Probabilistic machines can use less running time*][Freivalds1977]
* [R. Freivalds, *Fast probabilistic algorithms*][Freivalds1979]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan95]
-/

public section

namespace Cslib.Algorithms.WordRAM.Freivalds

open scoped Matrix ENNReal
open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Probability
open Cslib.Algorithms.Lean.Freivalds (check check_eq_decide verify eval_verify eval_verify_of_mul_eq
  eval_verify_bool_true_le)

/-! ### Word layout and memory views -/

/-- Row-major word list of a `rows × cols` matrix over `ZMod q`. -/
def encodeMatrix {q rows cols : ℕ} (M : Matrix (Fin rows) (Fin cols) (ZMod q)) : List ℕ :=
  List.ofFn fun idx : Fin (rows * cols) =>
    if h : cols = 0 then 0
    else
      (M ⟨idx.val / cols,
            Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (Nat.mul_comm rows cols))⟩
         ⟨idx.val % cols, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩).val

@[simp]
theorem length_encodeMatrix {q rows cols : ℕ} (M : Matrix (Fin rows) (Fin cols) (ZMod q)) :
    (encodeMatrix M).length = rows * cols := by
  simp [encodeMatrix]

theorem getElem_encodeMatrix {q rows cols : ℕ} (M : Matrix (Fin rows) (Fin cols) (ZMod q))
    (i : Fin rows) (j : Fin cols) :
    have hlt : i.val * cols + j.val < (encodeMatrix M).length := by
      rw [length_encodeMatrix]
      calc i.val * cols + j.val < i.val * cols + cols := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * cols := by ring
        _ ≤ rows * cols := Nat.mul_le_mul_right cols i.isLt
    (encodeMatrix M)[i.val * cols + j.val] = (M i j).val := by
  have hc0 : cols ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)
  have hcpos : 0 < cols := Nat.pos_of_ne_zero hc0
  have hdiv : (i.val * cols + j.val) / cols = i.val := by
    rw [Nat.mul_comm i.val cols, Nat.mul_add_div hcpos, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hmod : (i.val * cols + j.val) % cols = j.val := by
    rw [Nat.mul_comm i.val cols, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  simp only [encodeMatrix, List.getElem_ofFn, hc0, ↓reduceDIte]
  congr 2
  · exact Fin.ext hdiv
  · exact Fin.ext hmod

theorem mem_encodeMatrix_lt {q rows cols : ℕ} [NeZero q]
    (M : Matrix (Fin rows) (Fin cols) (ZMod q)) {v : ℕ} (hv : v ∈ encodeMatrix M) :
    v < q := by
  rw [encodeMatrix, List.mem_ofFn] at hv
  obtain ⟨idx, rfl⟩ := hv
  split_ifs
  · exact NeZero.pos q
  · exact ZMod.val_lt _

/-- Input word list for `k` trials of Freivalds' verifier modulo `q` on rectangular matrices
`A : l × m`, `B : m × n` and `C : l × n`. -/
def encode (q k : ℕ) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ZMod q))
    (B : Matrix (Fin m) (Fin n) (ZMod q)) (C : Matrix (Fin l) (Fin n) (ZMod q)) : List ℕ :=
  q :: k :: l :: m :: n :: (encodeMatrix A ++ encodeMatrix B ++ encodeMatrix C)

@[simp]
theorem length_encode (q k : ℕ) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ZMod q))
    (B : Matrix (Fin m) (Fin n) (ZMod q)) (C : Matrix (Fin l) (Fin n) (ZMod q)) :
    (encode q k A B C).length = 5 + (l * m + m * n + l * n) := by
  simp only [encode, List.length_cons, List.length_append, length_encodeMatrix]
  omega

/-- Sufficient upper bound on every constant, counter, memory address and intermediate product
computed by `verifyProgram`. -/
@[wram_arith]
def wordBound (q k l m n : ℕ) : ℕ :=
  q * q + 2 * q + k + l * m + m * n + l * n + n + m + 2 * l + 6

/-- Fitting `wordBound q k l m n` in `w` bits guarantees `InputFits w (encode q k A B C)`. -/
theorem inputFits_encode {w q k l m n : ℕ} [NeZero q] (A : Matrix (Fin l) (Fin m) (ZMod q))
    (B : Matrix (Fin m) (Fin n) (ZMod q)) (C : Matrix (Fin l) (Fin n) (ZMod q))
    (hw : Fits w (wordBound q k l m n)) :
    InputFits w (encode q k A B C) := by
  refine ⟨hw.of_le (by rw [length_encode]; unfold wordBound; omega), fun v hv => ?_⟩
  simp only [encode, List.mem_cons, List.mem_append] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | ((hA | hB) | hC)
  · exact hw.of_le (by unfold wordBound; omega)
  · exact hw.of_le (by unfold wordBound; omega)
  · exact hw.of_le (by unfold wordBound; omega)
  · exact hw.of_le (by unfold wordBound; omega)
  · exact hw.of_le (by unfold wordBound; omega)
  · exact hw.of_le (by have := mem_encodeMatrix_lt A hA; unfold wordBound; omega)
  · exact hw.of_le (by have := mem_encodeMatrix_lt B hB; unfold wordBound; omega)
  · exact hw.of_le (by have := mem_encodeMatrix_lt C hC; unfold wordBound; omega)

/-- Matrix `M` is stored in row-major order starting at `base`. -/
def MatrixAt {q rows cols : ℕ} (mem : ℕ → ℕ) (base : ℕ)
    (M : Matrix (Fin rows) (Fin cols) (ZMod q)) : Prop :=
  ∀ (i : Fin rows) (j : Fin cols), mem (base + i.val * cols + j.val) = (M i j).val

private theorem matrixAt_of_holdsList {q rows cols : ℕ} {mem : ℕ → ℕ} {base : ℕ}
    {M : Matrix (Fin rows) (Fin cols) (ZMod q)} (h : HoldsList base (encodeMatrix M) mem) :
    MatrixAt mem base M := by
  intro i j
  have hlt : i.val * cols + j.val < (encodeMatrix M).length := by
    rw [length_encodeMatrix]
    calc i.val * cols + j.val < i.val * cols + cols := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * cols := by ring
      _ ≤ rows * cols := Nat.mul_le_mul_right cols i.isLt
  simpa only [Nat.add_assoc, getElem_encodeMatrix M i j] using h.get (i.val * cols + j.val) hlt

private theorem matrixAt_frame {q rows cols : ℕ} {mem mem' : ℕ → ℕ} {base : ℕ}
    {M : Matrix (Fin rows) (Fin cols) (ZMod q)} (h : MatrixAt mem base M)
    (heq : ∀ a, base ≤ a → a < base + rows * cols → mem' a = mem a) :
    MatrixAt mem' base M := by
  intro i j
  have hlt : i.val * cols + j.val < rows * cols := by
    calc i.val * cols + j.val < i.val * cols + cols := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * cols := by ring
      _ ≤ rows * cols := Nat.mul_le_mul_right cols i.isLt
  rw [heq _ (by omega) (by omega)]
  exact h i j

/-- Vector `v : Fin len → ZMod q` is stored at `base` as canonical residues `(v i).val`. -/
def VecAt {q len : ℕ} (mem : ℕ → ℕ) (base : ℕ) (v : Fin len → ZMod q) : Prop :=
  ∀ i : Fin len, mem (base + i.val) = (v i).val

private theorem vecAt_frame {q len : ℕ} {mem mem' : ℕ → ℕ} {base : ℕ} {v : Fin len → ZMod q}
    (h : VecAt mem base v) (heq : ∀ a, base ≤ a → a < base + len → mem' a = mem a) :
    VecAt mem' base v := by
  intro i
  rw [heq _ (by omega) (by omega)]
  exact h i

/-- Read `len` words starting at `base` as a vector over `ZMod q` via natural-number coercion. -/
def readVec (q : ℕ) (mem : ℕ → ℕ) (base len : ℕ) : Fin len → ZMod q :=
  fun i => (mem (base + i.val) : ZMod q)

private theorem readVec_of_vecAt {q len : ℕ} [NeZero q] {mem : ℕ → ℕ} {base : ℕ}
    {v : Fin len → ZMod q} (h : VecAt mem base v) :
    readVec q mem base len = v := by
  funext i
  simp only [readVec, h i, ZMod.natCast_zmod_val]

private theorem readVec_frame {q len : ℕ} {mem mem' : ℕ → ℕ} {base : ℕ}
    (heq : ∀ a, base ≤ a → a < base + len → mem' a = mem a) :
    readVec q mem' base len = readVec q mem base len := by
  funext i
  simp only [readVec]
  rw [heq _ (by omega) (by omega)]

/-- Read `n` words at `base` as a Boolean vector (`true` when the word equals `1`). -/
def bitsAt (mem : ℕ → ℕ) (base n : ℕ) : Fin n → Bool :=
  fun i => decide (mem (base + i.val) = 1)

private theorem bitsAt_update_self {n : ℕ} (mem : ℕ → ℕ) (base : ℕ) (i : Fin n) (v : ℕ) :
    bitsAt (Function.update mem (base + i.val) v) base n =
      Function.update (bitsAt mem base n) i (decide (v = 1)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [bitsAt]
  · have hne : base + j.val ≠ base + i.val := fun h => hj (Fin.ext (by omega))
    simp [bitsAt, Function.update_of_ne hne, Function.update_of_ne hj]

private theorem readVec_eq_bit_comp_bitsAt {q n : ℕ} {mem : ℕ → ℕ} {base : ℕ}
    (hbits : ∀ j < n, mem (base + j) ≤ 1) :
    readVec q mem base n = bit ∘ bitsAt mem base n := by
  funext j
  have hj := hbits j.val j.isLt
  simp only [readVec, bitsAt, Function.comp_apply]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h0 | h1
  · simp [h0, bit_false]
  · simp [h1, bit_true]

/-! ### Registers and structured subroutines

Register allocation for the 28-register Freivalds verifier. Registers `0..13` are read-only
after `setupCode`; `14` is the outer trial counter and `15` accumulates acceptance across trials. -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 28 := 0
/-- Constant `1`. -/
abbrev one : Fin 28 := 1
/-- Modulus `q`. -/
abbrev qReg : Fin 28 := 2
/-- Trial count `k`. -/
abbrev kReg : Fin 28 := 3
/-- Row dimension `l` of `A` and `C`. -/
abbrev lReg : Fin 28 := 4
/-- Shared dimension `m` (columns of `A`, rows of `B`). -/
abbrev mReg : Fin 28 := 5
/-- Column dimension `n` of `B` and `C`. -/
abbrev nReg : Fin 28 := 6
/-- Base address of `A` (`6`). -/
abbrev aBase : Fin 28 := 7
/-- Base address of `B` (`6 + l * m`). -/
abbrev bBase : Fin 28 := 8
/-- Base address of `C` (`6 + l * m + m * n`). -/
abbrev cBase : Fin 28 := 9
/-- Base address of sampled bit vector `x` (`6 + l * m + m * n + l * n`). -/
abbrev xBase : Fin 28 := 10
/-- Base address of intermediate vector `y = B *ᵥ x` (`xBase + n`). -/
abbrev yBase : Fin 28 := 11
/-- Base address of intermediate vector `z = A *ᵥ y` (`yBase + m`). -/
abbrev zBase : Fin 28 := 12
/-- Base address of intermediate vector `w = C *ᵥ x` (`zBase + l`). -/
abbrev wBase : Fin 28 := 13
/-- Current trial index (`0..k`). -/
abbrev trialIdx : Fin 28 := 14
/-- Running conjunction of trial outcomes (`1` if all completed trials passed, `0` otherwise). -/
abbrev allOk : Fin 28 := 15
/-- Subroutine matrix base pointer. -/
abbrev matPtr : Fin 28 := 16
/-- Subroutine input-vector base pointer. -/
abbrev vecPtr : Fin 28 := 17
/-- Subroutine output-vector base pointer. -/
abbrev outPtr : Fin 28 := 18
/-- Subroutine row bound. -/
abbrev rowsReg : Fin 28 := 19
/-- Subroutine column bound. -/
abbrev colsReg : Fin 28 := 20
/-- Row counter in `mulVecCode` and `vecEqCode`. -/
abbrev row : Fin 28 := 21
/-- Current matrix row base address `matPtr + row * cols` in `mulVecCode`. -/
abbrev mCur : Fin 28 := 22
/-- Column counter in `mulVecCode` and `sampleVecCode`. -/
abbrev col : Fin 28 := 23
/-- Running modular accumulator in `mulVecCode` and equality flag in `vecEqCode`. -/
abbrev acc : Fin 28 := 24
/-- Scratch memory address. -/
abbrev addr : Fin 28 := 25
/-- Loaded matrix / left-vector word. -/
abbrev mVal : Fin 28 := 26
/-- Loaded right-vector word / modular product / sampled bit. -/
abbrev vVal : Fin 28 := 27

end Reg

open Reg

/-- Inner dot-product step: add `M[row, col] * (v[col] % q) mod q` into `acc`. -/
def dotBody : Code .standard 28 := ram[
  addr ← mCur + col;
  mVal ← *addr;
  addr ← vecPtr + col;
  vVal ← *addr;
  vVal ← vVal % qReg;
  vVal ← mVal * vVal;
  vVal ← vVal % qReg;
  acc ← acc + vVal;
  acc ← acc % qReg;
  col ← col + one ]

/-- Inner dot-product loop over `col ∈ [0, cols)`. -/
def dotLoop : Code .standard 28 := .loop (.lt col colsReg) dotBody

/-- Outer matrix-vector row body: compute dot product of row `row` and store at `outPtr + row`. -/
def mulVecRowBody : Code .standard 28 := ram[
  acc ← zero;
  col ← zero;
  ⟪dotLoop⟫;
  addr ← outPtr + row;
  *addr ← acc;
  mCur ← mCur + colsReg;
  row ← row + one ]

/-- Outer matrix-vector loop over `row ∈ [0, rows)`. -/
def mulVecLoop : Code .standard 28 := .loop (.lt row rowsReg) mulVecRowBody

/-- Deterministic modular matrix-vector multiplication: stores `M *ᵥ readVec q mem vecPtr cols`
at `[outPtr, outPtr + rows)`. -/
def mulVecCode : Code .standard 28 := ram[
  row ← zero;
  mCur ← matPtr;
  ⟪mulVecLoop⟫ ]

/-- Single coordinate equality step comparing `zBase[row]` with `wBase[row]`. -/
def vecEqBody : Code .standard 28 := ram[
  addr ← zBase + row;
  mVal ← *addr;
  addr ← wBase + row;
  vVal ← *addr;
  if mVal = vVal then [ acc ← acc ] else [ acc ← zero ];
  row ← row + one ]

/-- Equality loop over `row ∈ [0, l)`. -/
def vecEqLoop : Code .standard 28 := .loop (.lt row lReg) vecEqBody

/-- Compare the length-`l` vectors at `zBase` and `wBase`, setting `acc` to `1` if equal and `0`
otherwise. -/
def vecEqCode : Code .standard 28 := ram[
  acc ← one;
  row ← zero;
  ⟪vecEqLoop⟫ ]

/-- Sample one random bit into `xBase[col]` and advance `col`. -/
def sampleBody : Code .standard 28 := ram[
  vVal ← rand one;
  addr ← xBase + col;
  *addr ← vVal;
  col ← col + one ]

/-- Loop sampling `n` independent bits into `[xBase, xBase + n)`. -/
def sampleLoop : Code .standard 28 := .loop (.lt col nReg) sampleBody

/-- Sample a uniform `0`/`1` vector of length `n` into `[xBase, xBase + n)`. -/
def sampleVecCode : Code .standard 28 := ram[
  col ← zero;
  ⟪sampleLoop⟫ ]

/-- Compute `y = B *ᵥ x` at `yBase`. -/
def callMulB : Code .standard 28 := ram[
  matPtr ← bBase; vecPtr ← xBase; outPtr ← yBase; rowsReg ← mReg; colsReg ← nReg;
  ⟪mulVecCode⟫ ]

/-- Compute `z = A *ᵥ y` at `zBase`. -/
def callMulA : Code .standard 28 := ram[
  matPtr ← aBase; vecPtr ← yBase; outPtr ← zBase; rowsReg ← lReg; colsReg ← mReg;
  ⟪mulVecCode⟫ ]

/-- Compute `w = C *ᵥ x` at `wBase`. -/
def callMulC : Code .standard 28 := ram[
  matPtr ← cBase; vecPtr ← xBase; outPtr ← wBase; rowsReg ← lReg; colsReg ← nReg;
  ⟪mulVecCode⟫ ]

/-- Deterministic evaluation of one Freivalds check on the vector stored at `xBase`, folding its
result into `allOk`. -/
def checkCurrentVec : Code .standard 28 := ram[
  ⟪callMulB⟫;
  ⟪callMulA⟫;
  ⟪callMulC⟫;
  ⟪vecEqCode⟫;
  allOk ← allOk &&& acc ]

/-- Body of one verification trial: sample `x`, run `checkCurrentVec`, and increment `trialIdx`. -/
def trialBody : Code .standard 28 := ram[
  ⟪sampleVecCode⟫;
  ⟪checkCurrentVec⟫;
  trialIdx ← trialIdx + one ]

/-- Main `k`-trial verification loop. -/
def trialsLoop : Code .standard 28 := .loop (.lt trialIdx kReg) trialBody

/-- Initialize header constants and slice base pointers from `Data.init (encode q k A B C)`. -/
def setupCode : Code .standard 28 := ram[
  zero ← #0;
  one ← #1;
  qReg ← *one;
  addr ← #2;
  kReg ← *addr;
  addr ← #3;
  lReg ← *addr;
  addr ← #4;
  mReg ← *addr;
  addr ← #5;
  nReg ← *addr;
  aBase ← #6;
  vVal ← lReg * mReg;
  bBase ← aBase + vVal;
  vVal ← mReg * nReg;
  cBase ← bBase + vVal;
  vVal ← lReg * nReg;
  xBase ← cBase + vVal;
  yBase ← xBase + nReg;
  zBase ← yBase + mReg;
  wBase ← zBase + lReg;
  trialIdx ← zero;
  allOk ← one ]

/-- Complete structured Freivalds `k`-trial verifier. -/
def verifyCode : Code .standard 28 := ram[
  ⟪setupCode⟫;
  ⟪trialsLoop⟫ ]

/-- Compiled flat randomized word-RAM program returning `allOk` (`1` accept, `0` reject). -/
def verifyProgram : Program .standard 28 := verifyCode.program allOk

/-- Worst-case instruction bound of `verifyProgram` on dimensions `(k, l, m, n)`. -/
def verifyTime (k l m n : ℕ) : ℕ :=
  k * (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 6 * n + 38) + 26

/-- Worst-case instruction bound of `verifyProgram` on square `n × n` matrices (`O(k n²)`). -/
def verifySquareTime (k n : ℕ) : ℕ :=
  k * (36 * n ^ 2 + 46 * n + 38) + 26

theorem verifyTime_square_eq (k n : ℕ) : verifyTime k n n n = verifySquareTime k n := by
  unfold verifyTime verifySquareTime
  ring

/-- Whether a halting configuration of `verifyProgram` accepted (`1` accept, `0` reject). -/
def cfgAccepts {r : ℕ} : RandCfg r → Bool
  | .halted v _ => decide (v = 1)
  | _ => false

/-! ### Proof of deterministic matrix-vector multiplication (`mulVecCode`) -/

private def partialDot {q cols : ℕ} (u v : Fin cols → ZMod q) : ℕ → ZMod q
  | 0 => 0
  | j + 1 => partialDot u v j + if h : j < cols then u ⟨j, h⟩ * v ⟨j, h⟩ else 0

private theorem partialDot_init {q cols : ℕ} (u v : Fin (cols + 1) → ZMod q) :
    ∀ j ≤ cols, partialDot u v j = partialDot (Fin.init u) (Fin.init v) j
  | 0, _ => rfl
  | j + 1, hj => by
    have hlt1 : j < cols + 1 := by omega
    have hlt2 : j < cols := by omega
    simp only [partialDot, hlt1, hlt2, ↓reduceDIte, partialDot_init u v j (by omega)]
    rfl

private theorem partialDot_self {q : ℕ} :
    ∀ {cols : ℕ} (u v : Fin cols → ZMod q), partialDot u v cols = u ⬝ᵥ v
  | 0, u, v => by simp [partialDot, dotProduct]
  | cols + 1, u, v => by
    have hlt : cols < cols + 1 := Nat.lt_succ_self cols
    simp only [partialDot, hlt, ↓reduceDIte, partialDot_init u v cols le_rfl,
      partialDot_self (Fin.init u) (Fin.init v)]
    symm
    rw [dotProduct, Fin.sum_univ_castSucc]
    rfl

private theorem dotLoop_spec {w q cols mBase vBase : ℕ} [NeZero q]
    (u : Fin cols → ZMod q) (x : Data 28)
    (ho : x.regs one = 1) (hq : x.regs qReg = q)
    (hcols : x.regs colsReg = cols) (hmCur : x.regs mCur = mBase) (hvec : x.regs vecPtr = vBase)
    (hcol0 : x.regs col = 0) (hacc0 : x.regs acc = 0)
    (hu : ∀ j : Fin cols, x.mem (mBase + j.val) = (u j).val)
    (hw_arith : Fits w (q * q + 2 * q))
    (hw_m : Fits w (mBase + cols)) (hw_v : Fits w (vBase + cols)) :
    ∃ y, ExecWithin w dotLoop x y (12 * cols + 2) ∧
      y.mem = x.mem ∧
      y.regs acc = (u ⬝ᵥ readVec q x.mem vBase cols).val ∧
      ∀ i : Fin 28, i.val < 23 → y.regs i = x.regs i := by
  let v := readVec q x.mem vBase cols
  let P (j : ℕ) (y : Data 28) : Prop :=
    y.mem = x.mem ∧
    y.regs acc = (partialDot u v j).val ∧
    ∀ i : Fin 28, i.val < 23 → y.regs i = x.regs i
  have hP0 : P (x.regs col) x := by
    rw [hcol0]
    exact ⟨rfl, by simp [hacc0, partialDot], fun _ _ => rfl⟩
  obtain ⟨y, hy, ⟨hym, hyacc, hyregs⟩, _⟩ :=
    ExecWithin.loop_count (B := .standard) (w := w) (N := cols) (T := 10) P
      (fun y hyP => (hyP.2.2 colsReg (by decide)).trans hcols)
      (fun y ⟨hym, hyacc, hyregs⟩ hj => by
        set j := y.regs col with hj_eq
        symm at hj_eq
        have hqpos : 0 < q := NeZero.pos q
        have h1 : y.regs one = 1 := (hyregs one (by decide)).trans ho
        have hq' : y.regs qReg = q := (hyregs qReg (by decide)).trans hq
        have hmCur' : y.regs mCur = mBase := (hyregs mCur (by decide)).trans hmCur
        have hvec' : y.regs vecPtr = vBase := (hyregs vecPtr (by decide)).trans hvec
        have hmcell : y.mem (mBase + j) = (u ⟨j, hj⟩).val := by
          rw [hym]
          exact hu ⟨j, hj⟩
        have hvcell : y.mem (vBase + j) = x.mem (vBase + j) := by rw [hym]
        have hult : (u ⟨j, hj⟩).val < q := ZMod.val_lt _
        have hvmod_lt : x.mem (vBase + j) % q < q := Nat.mod_lt _ hqpos
        have hprod_lt : (u ⟨j, hj⟩).val * (x.mem (vBase + j) % q) < q * q :=
          Nat.mul_lt_mul'' hult hvmod_lt
        have hacc_lt : (partialDot u v j).val < q := ZMod.val_lt _
        have hpmod_lt : ((u ⟨j, hj⟩).val * (x.mem (vBase + j) % q)) % q < q :=
          Nat.mod_lt _ hqpos
        have hsum_mod_lt :
            (((partialDot u v j).val + ((u ⟨j, hj⟩).val * (x.mem (vBase + j) % q)) % q) % q) < q :=
          Nat.mod_lt _ hqpos
        have : Fits w (mBase + j) := hw_m.of_le (by omega)
        have : Fits w (vBase + j) := hw_v.of_le (by omega)
        have : Fits w (x.mem (vBase + j) % q) := hw_arith.of_le (by omega)
        have : Fits w ((u ⟨j, hj⟩).val * (x.mem (vBase + j) % q)) :=
          hw_arith.of_le (by omega)
        have : Fits w (((u ⟨j, hj⟩).val * (x.mem (vBase + j) % q)) % q) :=
          hw_arith.of_le (by omega)
        have : Fits w ((partialDot u v j).val +
            ((u ⟨j, hj⟩).val * (x.mem (vBase + j) % q)) % q) :=
          hw_arith.of_le (by omega)
        have : Fits w (((partialDot u v j).val +
            ((u ⟨j, hj⟩).val * (x.mem (vBase + j) % q)) % q) % q) :=
          hw_arith.of_le (by omega)
        have : Fits w (j + 1) := hw_m.of_le (by omega)
        refine WP.exists_execWithin (w := w) (c := dotBody) ?_
        unfold dotBody
        wram_exec [hj_eq, h1, hq', hmCur', hvec', hmcell, hvcell, hyacc]
        refine ⟨⟨hym, ?_, fun i hi => ?_⟩, by wram_simp [hj_eq]⟩
        · wram_simp
          simp only [partialDot, hj, ↓reduceDIte]
          have hvval : x.mem (vBase + j) % q = (v ⟨j, hj⟩).val := by
            simp only [v, readVec, ZMod.val_natCast]
          rw [hvval, ← ZMod.val_mul, ← ZMod.val_add]
        · have hne23 : i ≠ col := by rintro rfl; exact absurd hi (by decide)
          have hne24 : i ≠ acc := by rintro rfl; exact absurd hi (by decide)
          have hne25 : i ≠ addr := by rintro rfl; exact absurd hi (by decide)
          have hne26 : i ≠ mVal := by rintro rfl; exact absurd hi (by decide)
          have hne27 : i ≠ vVal := by rintro rfl; exact absurd hi (by decide)
          simp only [Data.set_regs, Function.update_of_ne hne23, Function.update_of_ne hne24,
            Function.update_of_ne hne25, Function.update_of_ne hne26,
            Function.update_of_ne hne27]
          exact hyregs i hi)
      (by rw [hcol0]; exact Nat.zero_le _) hP0
  refine ⟨y, hy.mono (by rw [hcol0]; omega), hym, ?_, hyregs⟩
  rw [hyacc, partialDot_self]

/-- **Deterministic modular matrix-vector multiplication.** When `M : Matrix (Fin rows) (Fin cols)
(ZMod q)` is stored at `matPtr` and `[outPtr, outPtr + rows)` is disjoint from both `M`'s slice
and `[vecPtr, vecPtr + cols)`, `mulVecCode` writes `M *ᵥ readVec q x.mem vecPtr cols` to
`[outPtr, outPtr + rows)` within `rows * (12 * cols + 10) + 4` instructions, preserving memory
outside `[outPtr, outPtr + rows)` and all registers below `21`. -/
theorem mulVecCode_spec {w q rows cols mBase vBase oBase : ℕ} [NeZero q]
    (M : Matrix (Fin rows) (Fin cols) (ZMod q)) (x : Data 28)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hq : x.regs qReg = q)
    (hmPtr : x.regs matPtr = mBase) (hvPtr : x.regs vecPtr = vBase) (hoPtr : x.regs outPtr = oBase)
    (hrows : x.regs rowsReg = rows) (hcols : x.regs colsReg = cols)
    (hM : MatrixAt x.mem mBase M)
    (hdisj_m : mBase + rows * cols ≤ oBase ∨ oBase + rows ≤ mBase)
    (hdisj_v : vBase + cols ≤ oBase ∨ oBase + rows ≤ vBase)
    (hw_arith : Fits w (q * q + 2 * q))
    (hw_m : Fits w (mBase + rows * cols)) (hw_v : Fits w (vBase + cols))
    (hw_o : Fits w (oBase + rows)) :
    ∃ y, ExecWithin w mulVecCode x y (rows * (12 * cols + 10) + 4) ∧
      VecAt y.mem oBase (M *ᵥ readVec q x.mem vBase cols) ∧
      (∀ a, ¬(oBase ≤ a ∧ a < oBase + rows) → y.mem a = x.mem a) ∧
      ∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i := by
  let v := readVec q x.mem vBase cols
  let outVec (r : ℕ) : ℕ :=
    if hr : r < rows then ((M *ᵥ v) ⟨r, hr⟩).val else 0
  let x₀ := (x.set row 0).set mCur mBase
  have hx₀ : ExecWithin (B := .standard) w (ram[row ← zero; mCur ← matPtr]) x x₀ 2 :=
    WP.execWithin (B := .standard) (c := ram[row ← zero; mCur ← matPtr])
      (by wram_exec [hz, hmPtr]; rfl)
  let P (r : ℕ) (y : Data 28) : Prop :=
    y.regs mCur = mBase + r * cols ∧
    (∀ i < r, y.mem (oBase + i) = outVec i) ∧
    (∀ a, ¬(oBase ≤ a ∧ a < oBase + r) → y.mem a = x.mem a) ∧
    ∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i
  have hP0 : P (x₀.regs row) x₀ := by
    have hr0 : x₀.regs row = 0 := by wram_simp [x₀]
    rw [hr0]
    refine ⟨by wram_simp [x₀]; omega, fun _ hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ => rfl, fun i hi => ?_⟩
    have hne21 : i ≠ row := by rintro rfl; exact absurd hi (by decide)
    have hne22 : i ≠ mCur := by rintro rfl; exact absurd hi (by decide)
    simp [x₀, Function.update_of_ne hne21, Function.update_of_ne hne22]
  obtain ⟨y, hy, ⟨_, hpre, hout, hyregs⟩, _⟩ :=
    ExecWithin.loop_count (B := .standard) (w := w) (N := rows) (T := 12 * cols + 8) P
      (fun y hyP => (hyP.2.2.2 rowsReg (by decide)).trans hrows)
      (fun y ⟨hmCur_y, hpre_y, hout_y, hyregs_y⟩ hr => by
        set r := y.regs row
        have hz' : y.regs zero = 0 := (hyregs_y zero (by decide)).trans hz
        have ho' : y.regs one = 1 := (hyregs_y one (by decide)).trans ho
        have hq' : y.regs qReg = q := (hyregs_y qReg (by decide)).trans hq
        have hvPtr' : y.regs vecPtr = vBase := (hyregs_y vecPtr (by decide)).trans hvPtr
        have hoPtr' : y.regs outPtr = oBase := (hyregs_y outPtr (by decide)).trans hoPtr
        have hcols' : y.regs colsReg = cols := (hyregs_y colsReg (by decide)).trans hcols
        have hrow_end : mBase + r * cols + cols ≤ mBase + rows * cols := by
          have : (r + 1) * cols ≤ rows * cols := Nat.mul_le_mul_right cols hr
          calc mBase + r * cols + cols = mBase + (r + 1) * cols := by ring
            _ ≤ mBase + rows * cols := by omega
        have hM_row : ∀ j : Fin cols, y.mem (mBase + r * cols + j.val) = (M ⟨r, hr⟩ j).val := by
          intro j
          have hjlt := j.isLt
          rw [hout_y _ (by rcases hdisj_m with h | h <;> omega)]
          exact hM ⟨r, hr⟩ j
        have hv_eq : readVec q y.mem vBase cols = v :=
          readVec_frame fun a ha1 ha2 => hout_y a (by rcases hdisj_v with h | h <;> omega)
        let y₁ := (y.set acc 0).set col 0
        have hy₁ : ExecWithin (B := .standard) w (ram[acc ← zero; col ← zero]) y y₁ 2 :=
          WP.execWithin (B := .standard) (c := ram[acc ← zero; col ← zero])
            (by wram_exec [hz']; rfl)
        obtain ⟨y₂, hy₂, hym₂, hyacc₂, hyregs₂⟩ :=
          dotLoop_spec (w := w) (mBase := mBase + r * cols) (vBase := vBase) (M ⟨r, hr⟩) y₁
            (by wram_simp [y₁]; exact ho')
            (by wram_simp [y₁]; exact hq')
            (by wram_simp [y₁]; exact hcols')
            (by wram_simp [y₁]; exact hmCur_y)
            (by wram_simp [y₁]; exact hvPtr')
            (by wram_simp [y₁])
            (by wram_simp [y₁])
            (fun j => by simpa [y₁] using hM_row j)
            hw_arith (hw_m.of_le hrow_end) hw_v
        have hy₂_mem : y₂.mem = y.mem := hym₂
        rw [show readVec q y₁.mem vBase cols = v from hv_eq] at hyacc₂
        have hy₂_row : y₂.regs row = r := by
          rw [hyregs₂ row (by decide)]; wram_simp [y₁]; rfl
        have hy₂_mCur : y₂.regs mCur = mBase + r * cols := by
          rw [hyregs₂ mCur (by decide)]; wram_simp [y₁]; exact hmCur_y
        have hy₂_one : y₂.regs one = 1 := by
          rw [hyregs₂ one (by decide)]; wram_simp [y₁]; exact ho'
        have hy₂_oPtr : y₂.regs outPtr = oBase := by
          rw [hyregs₂ outPtr (by decide)]; wram_simp [y₁]; exact hoPtr'
        have hy₂_cols : y₂.regs colsReg = cols := by
          rw [hyregs₂ colsReg (by decide)]; wram_simp [y₁]; exact hcols'
        have : Fits w (oBase + r) := hw_o.of_le (by omega)
        have : Fits w (mBase + r * cols + cols) := hw_m.of_le hrow_end
        have : Fits w (r + 1) := hw_o.of_le (by omega)
        let y₃ := (((y₂.set addr (oBase + r)).write (oBase + r) (y₂.regs acc)).set mCur
          (mBase + r * cols + cols)).set row (r + 1)
        have hy₃ : ExecWithin w
            (ram[addr ← outPtr + row; *addr ← acc; mCur ← mCur + colsReg; row ← row + one])
            y₂ y₃ 4 :=
          WP.execWithin
            (c := ram[addr ← outPtr + row; *addr ← acc; mCur ← mCur + colsReg; row ← row + one])
            (by wram_exec [hy₂_oPtr, hy₂_row, hy₂_mCur, hy₂_cols, hy₂_one]; rfl)
        have hbody_exec : ExecWithin w mulVecRowBody y y₃ (12 * cols + 8) := by
          unfold mulVecRowBody
          rcases hy₁ with ⟨t₁, ht₁, he₁⟩
          rcases hy₂ with ⟨t₂, ht₂, he₂⟩
          rcases hy₃ with ⟨t₃, ht₃, he₃⟩
          cases he₁ with
          | seq ha hb =>
            exact ⟨_, by omega, ha.seq (hb.seq (he₂.seq he₃))⟩
        have hout_val : y₂.regs acc = outVec r := by
          simp only [outVec, hr, ↓reduceDIte, Matrix.mulVec]
          exact hyacc₂
        have hstep_mem := prefix_write_step hpre_y hout_y (z := y₃.mem) (by
          simp only [y₃, Data.set_mem, Data.write_mem, hy₂_mem, hout_val])
        refine ⟨y₃, hbody_exec, ⟨?_, hstep_mem.1, hstep_mem.2, fun i hi => ?_⟩,
          by wram_simp [y₃]⟩
        · wram_simp [y₃]
          ring
        · have hne21 : i ≠ row := by rintro rfl; exact absurd hi (by decide)
          have hne22 : i ≠ mCur := by rintro rfl; exact absurd hi (by decide)
          have hne25 : i ≠ addr := by rintro rfl; exact absurd hi (by decide)
          have hne23 : i ≠ col := by rintro rfl; exact absurd hi (by decide)
          have hne24 : i ≠ acc := by rintro rfl; exact absurd hi (by decide)
          simp only [y₃, Data.set_regs, Data.write_regs, Function.update_of_ne hne21,
            Function.update_of_ne hne22, Function.update_of_ne hne25]
          rw [hyregs₂ i (by omega)]
          simp only [y₁, Data.set_regs, Function.update_of_ne hne23, Function.update_of_ne hne24]
          exact hyregs_y i hi)
      (by have hr0 : x₀.regs row = 0 := by wram_simp [x₀]
          omega) hP0
  have hx₀_row : x₀.regs row = 0 := by wram_simp [x₀]
  have hall : ExecWithin w mulVecCode x y (rows * (12 * cols + 10) + 4) := by
    unfold mulVecCode
    rcases hx₀ with ⟨t₀, ht₀, he₀⟩
    rcases hy with ⟨t₁, ht₁, he₁⟩
    rw [hx₀_row, Nat.sub_zero] at ht₁
    cases he₀ with
    | seq ha hb =>
      exact ⟨_, by ring_nf at ht₁ ⊢; omega, ha.seq (hb.seq he₁)⟩
  refine ⟨y, hall, ?_, hout, hyregs⟩
  intro i
  simpa only [outVec, i.isLt, ↓reduceDIte] using hpre i.val i.isLt

/-! ### Vector comparison (`vecEqCode`) -/

private theorem vecEqCode_spec {w q l zAddr wAddr : ℕ} [NeZero q]
    (zvec wvec : Fin l → ZMod q) (x : Data 28)
    (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hl : x.regs lReg = l) (hzPtr : x.regs zBase = zAddr) (hwPtr : x.regs wBase = wAddr)
    (hzv : VecAt x.mem zAddr zvec) (hwv : VecAt x.mem wAddr wvec)
    (hw_z : Fits w (zAddr + l)) (hw_w : Fits w (wAddr + l)) :
    ∃ y, ExecWithin w vecEqCode x y (10 * l + 4) ∧
      y.mem = x.mem ∧
      y.regs acc = (decide (zvec = wvec)).toNat ∧
      ∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i := by
  let x₀ := (x.set acc 1).set row 0
  have hx₀ : ExecWithin (B := .standard) w (ram[acc ← one; row ← zero]) x x₀ 2 :=
    WP.execWithin (B := .standard) (c := ram[acc ← one; row ← zero])
      (by wram_exec [ho, hz]; rfl)
  let P (j : ℕ) (y : Data 28) : Prop :=
    y.mem = x.mem ∧
    y.regs acc = (decide (∀ i : Fin l, i.val < j → zvec i = wvec i)).toNat ∧
    ∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i
  have hP0 : P (x₀.regs row) x₀ := by
    have hr0 : x₀.regs row = 0 := by wram_simp [x₀]
    rw [hr0]
    refine ⟨rfl, by wram_simp [x₀]; simp, fun i hi => ?_⟩
    have hne21 : i ≠ row := by rintro rfl; exact absurd hi (by decide)
    have hne24 : i ≠ acc := by rintro rfl; exact absurd hi (by decide)
    simp [x₀, Function.update_of_ne hne21, Function.update_of_ne hne24]
  obtain ⟨y, hy, ⟨hym, hyacc, hyregs⟩, _⟩ :=
    ExecWithin.loop_count (B := .standard) (w := w) (N := l) (T := 8) P
      (fun y hyP => (hyP.2.2 lReg (by decide)).trans hl)
      (fun y ⟨hym_y, hyacc_y, hyregs_y⟩ hj => by
        set j := y.regs row with hj_eq
        symm at hj_eq
        have hz' : y.regs zero = 0 := (hyregs_y zero (by decide)).trans hz
        have ho' : y.regs one = 1 := (hyregs_y one (by decide)).trans ho
        have hzPtr' : y.regs zBase = zAddr := (hyregs_y zBase (by decide)).trans hzPtr
        have hwPtr' : y.regs wBase = wAddr := (hyregs_y wBase (by decide)).trans hwPtr
        have hzj : y.mem (zAddr + j) = (zvec ⟨j, hj⟩).val := by
          rw [hym_y]; exact hzv ⟨j, hj⟩
        have hwj : y.mem (wAddr + j) = (wvec ⟨j, hj⟩).val := by
          rw [hym_y]; exact hwv ⟨j, hj⟩
        have : Fits w (zAddr + j) := hw_z.of_le (by omega)
        have : Fits w (wAddr + j) := hw_w.of_le (by omega)
        have : Fits w (j + 1) := hw_z.of_le (by omega)
        by_cases heq : (zvec ⟨j, hj⟩).val = (wvec ⟨j, hj⟩).val
        · have hzweq : zvec ⟨j, hj⟩ = wvec ⟨j, hj⟩ := ZMod.val_injective q heq
          refine WP.exists_execWithin (c := vecEqBody) ?_
          unfold vecEqBody
          wram_exec [hj_eq, hzPtr', hwPtr', hzj, hwj, heq, ho', hyacc_y]
          refine ⟨⟨hym_y, ?_, fun i hi => ?_⟩, by wram_simp [hj_eq]⟩
          · wram_simp
            congr 1
            refine decide_eq_decide.mpr ⟨fun hprev i hi => ?_, fun hnext i hi => hnext i (by omega)⟩
            by_cases hij : i.val = j
            · have : i = ⟨j, hj⟩ := Fin.ext hij
              subst this
              exact hzweq
            · exact hprev i (by omega)
          · have hne21 : i ≠ row := by rintro rfl; exact absurd hi (by decide)
            have hne24 : i ≠ acc := by rintro rfl; exact absurd hi (by decide)
            have hne25 : i ≠ addr := by rintro rfl; exact absurd hi (by decide)
            have hne26 : i ≠ mVal := by rintro rfl; exact absurd hi (by decide)
            have hne27 : i ≠ vVal := by rintro rfl; exact absurd hi (by decide)
            simp only [Data.set_regs, Function.update_of_ne hne21, Function.update_of_ne hne24,
              Function.update_of_ne hne25, Function.update_of_ne hne26,
              Function.update_of_ne hne27]
            exact hyregs_y i hi
        · have hzwne : zvec ⟨j, hj⟩ ≠ wvec ⟨j, hj⟩ := fun h => heq (congrArg ZMod.val h)
          refine WP.exists_execWithin (c := vecEqBody) ?_
          unfold vecEqBody
          wram_exec [hj_eq, hzPtr', hwPtr', hzj, hwj, heq, hz', ho']
          refine ⟨⟨hym_y, ?_, fun i hi => ?_⟩, by wram_simp [hj_eq]⟩
          · wram_simp
            have hnot : ¬∀ i : Fin l, i.val < j + 1 → zvec i = wvec i := fun hall =>
              hzwne (hall ⟨j, hj⟩ (Nat.lt_succ_self j))
            rw [decide_eq_false hnot]
            rfl
          · have hne21 : i ≠ row := by rintro rfl; exact absurd hi (by decide)
            have hne24 : i ≠ acc := by rintro rfl; exact absurd hi (by decide)
            have hne25 : i ≠ addr := by rintro rfl; exact absurd hi (by decide)
            have hne26 : i ≠ mVal := by rintro rfl; exact absurd hi (by decide)
            have hne27 : i ≠ vVal := by rintro rfl; exact absurd hi (by decide)
            simp only [Data.set_regs, Function.update_of_ne hne21, Function.update_of_ne hne24,
              Function.update_of_ne hne25, Function.update_of_ne hne26,
              Function.update_of_ne hne27]
            exact hyregs_y i hi)
      (by have hr0 : x₀.regs row = 0 := by wram_simp [x₀]
          omega) hP0
  have hx₀_row : x₀.regs row = 0 := by wram_simp [x₀]
  have hall : ExecWithin w vecEqCode x y (10 * l + 4) := by
    unfold vecEqCode
    rcases hx₀ with ⟨t₀, ht₀, he₀⟩
    rcases hy with ⟨t₁, ht₁, he₁⟩
    rw [hx₀_row, Nat.sub_zero] at ht₁
    cases he₀ with
    | seq ha hb =>
      exact ⟨_, by ring_nf at ht₁ ⊢; omega, ha.seq (hb.seq he₁)⟩
  refine ⟨y, hall, hym, ?_, hyregs⟩
  rw [hyacc]
  congr 1
  exact decide_eq_decide.mpr ⟨fun h => funext fun i => h i i.isLt, fun h i _ => congrFun h i⟩

/-! ### Persistent frame and one-trial verification -/

/-- Persistent machine invariant established by `setupCode` and preserved across all trials. -/
structure Frame (q k : ℕ) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ZMod q))
    (B : Matrix (Fin m) (Fin n) (ZMod q)) (C : Matrix (Fin l) (Fin n) (ZMod q))
    (x : Data 28) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  qReg_eq : x.regs qReg = q
  kReg_eq : x.regs kReg = k
  lReg_eq : x.regs lReg = l
  mReg_eq : x.regs mReg = m
  nReg_eq : x.regs nReg = n
  aBase_eq : x.regs aBase = 6
  bBase_eq : x.regs bBase = 6 + l * m
  cBase_eq : x.regs cBase = 6 + l * m + m * n
  xBase_eq : x.regs xBase = 6 + l * m + m * n + l * n
  yBase_eq : x.regs yBase = 6 + l * m + m * n + l * n + n
  zBase_eq : x.regs zBase = 6 + l * m + m * n + l * n + n + m
  wBase_eq : x.regs wBase = 6 + l * m + m * n + l * n + n + m + l
  matA : MatrixAt x.mem 6 A
  matB : MatrixAt x.mem (6 + l * m) B
  matC : MatrixAt x.mem (6 + l * m + m * n) C

private theorem Frame.congr {q k l m n : ℕ} {A : Matrix (Fin l) (Fin m) (ZMod q)}
    {B : Matrix (Fin m) (Fin n) (ZMod q)} {C : Matrix (Fin l) (Fin n) (ZMod q)}
    {x y : Data 28} (hx : Frame q k A B C x)
    (hregs : ∀ i : Fin 28, i.val < 14 → y.regs i = x.regs i)
    (hmem : ∀ a, a < 6 + l * m + m * n + l * n → y.mem a = x.mem a) :
    Frame q k A B C y where
  zero_eq := (hregs zero (by decide)).trans hx.zero_eq
  one_eq := (hregs one (by decide)).trans hx.one_eq
  qReg_eq := (hregs qReg (by decide)).trans hx.qReg_eq
  kReg_eq := (hregs kReg (by decide)).trans hx.kReg_eq
  lReg_eq := (hregs lReg (by decide)).trans hx.lReg_eq
  mReg_eq := (hregs mReg (by decide)).trans hx.mReg_eq
  nReg_eq := (hregs nReg (by decide)).trans hx.nReg_eq
  aBase_eq := (hregs aBase (by decide)).trans hx.aBase_eq
  bBase_eq := (hregs bBase (by decide)).trans hx.bBase_eq
  cBase_eq := (hregs cBase (by decide)).trans hx.cBase_eq
  xBase_eq := (hregs xBase (by decide)).trans hx.xBase_eq
  yBase_eq := (hregs yBase (by decide)).trans hx.yBase_eq
  zBase_eq := (hregs zBase (by decide)).trans hx.zBase_eq
  wBase_eq := (hregs wBase (by decide)).trans hx.wBase_eq
  matA := matrixAt_frame hx.matA fun a _ ha => hmem a (by omega)
  matB := matrixAt_frame hx.matB fun a _ ha => hmem a (by omega)
  matC := matrixAt_frame hx.matC fun a _ ha => hmem a (by omega)

private theorem seq5_mulVec {w T : ℕ} {p1 p2 p3 p4 p5 : Code .standard 28} {x x₅ y : Data 28}
    (hpre : ExecWithin w (ram[⟪p1⟫; ⟪p2⟫; ⟪p3⟫; ⟪p4⟫; ⟪p5⟫]) x x₅ 5)
    (hmul : ExecWithin w mulVecCode x₅ y T) :
    ExecWithin w (ram[⟪p1⟫; ⟪p2⟫; ⟪p3⟫; ⟪p4⟫; ⟪p5⟫; ⟪mulVecCode⟫]) x y (5 + T) := by
  rcases hpre with ⟨t₀, ht₀, he₀⟩
  rcases hmul with ⟨t₁, ht₁, he₁⟩
  cases he₀ with
  | seq h1 he₀ =>
    cases he₀ with
    | seq h2 he₀ =>
      cases he₀ with
      | seq h3 he₀ =>
        cases he₀ with
        | seq h4 h5 =>
          exact ⟨_, by omega, h1.seq (h2.seq (h3.seq (h4.seq (h5.seq he₁))))⟩

private theorem checkCurrentVec_spec {w q k l m n : ℕ} [NeZero q]
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (x : Data 28) (curOk : Bool)
    (hx : Frame q k A B C x)
    (hbits : ∀ j < n, x.mem (6 + l * m + m * n + l * n + j) ≤ 1)
    (hok : x.regs allOk = curOk.toNat)
    (hw : Fits w (wordBound q k l m n)) :
    let σ := bitsAt x.mem (6 + l * m + m * n + l * n) n
    ∃ y, ExecWithin w checkCurrentVec x y
        (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 32) ∧
      Frame q k A B C y ∧
      y.regs trialIdx = x.regs trialIdx ∧
      y.regs allOk = (curOk && check A B C (bit ∘ σ)).toNat := by
  intro σ
  set xAddr := 6 + l * m + m * n + l * n
  set yAddr := xAddr + n
  set zAddr := yAddr + m
  set wAddr := zAddr + l
  have hw_arith : Fits w (q * q + 2 * q) := hw.of_le (by unfold wordBound; omega)
  have hxvec : readVec q x.mem xAddr n = bit ∘ σ := readVec_eq_bit_comp_bitsAt hbits
  -- 1. `callMulB`: compute `y = B *ᵥ (bit ∘ σ)` at `yAddr`
  let xB := ((((x.set matPtr (6 + l * m)).set vecPtr xAddr).set outPtr yAddr).set rowsReg m).set
    colsReg n
  have hxB_exec : ExecWithin (B := .standard) w
      (ram[matPtr ← bBase; vecPtr ← xBase; outPtr ← yBase; rowsReg ← mReg; colsReg ← nReg])
      x xB 5 :=
    WP.execWithin (B := .standard)
      (c := ram[matPtr ← bBase; vecPtr ← xBase; outPtr ← yBase; rowsReg ← mReg; colsReg ← nReg])
      (by wram_exec [hx.bBase_eq, hx.xBase_eq, hx.yBase_eq, hx.mReg_eq, hx.nReg_eq]; rfl)
  obtain ⟨y₁, hy₁_mul, hy₁_vec, hy₁_out, hy₁_regs⟩ :=
    mulVecCode_spec (w := w) (mBase := 6 + l * m) (vBase := xAddr) (oBase := yAddr) B xB
      (by wram_simp [xB]; exact hx.zero_eq)
      (by wram_simp [xB]; exact hx.one_eq)
      (by wram_simp [xB]; exact hx.qReg_eq)
      (by wram_simp [xB]) (by wram_simp [xB]) (by wram_simp [xB])
      (by wram_simp [xB]) (by wram_simp [xB])
      hx.matB (Or.inl (by omega)) (Or.inl (by omega)) hw_arith
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
  have hy₁_call : ExecWithin w callMulB x y₁ (5 + (m * (12 * n + 10) + 4)) :=
    seq5_mulVec hxB_exec hy₁_mul
  rw [show readVec q xB.mem xAddr n = bit ∘ σ from hxvec] at hy₁_vec
  have hy₁_regs16 : ∀ i : Fin 28, i.val < 16 → y₁.regs i = x.regs i := fun i hi => by
    rw [hy₁_regs i (by omega)]
    have h16 : i ≠ matPtr := by rintro rfl; exact absurd hi (by decide)
    have h17 : i ≠ vecPtr := by rintro rfl; exact absurd hi (by decide)
    have h18 : i ≠ outPtr := by rintro rfl; exact absurd hi (by decide)
    have h19 : i ≠ rowsReg := by rintro rfl; exact absurd hi (by decide)
    have h20 : i ≠ colsReg := by rintro rfl; exact absurd hi (by decide)
    simp [xB, Function.update_of_ne h16, Function.update_of_ne h17, Function.update_of_ne h18,
      Function.update_of_ne h19, Function.update_of_ne h20]
  have hy₁_frame : Frame q k A B C y₁ :=
    hx.congr (fun i hi => hy₁_regs16 i (by omega)) fun a ha => hy₁_out a (by omega)
  have hy₁_xvec : readVec q y₁.mem xAddr n = bit ∘ σ :=
    (readVec_frame fun a _ ha => hy₁_out a (by omega)).trans hxvec
  -- 2. `callMulA`: compute `z = A *ᵥ (B *ᵥ (bit ∘ σ))` at `zAddr`
  let xA := ((((y₁.set matPtr 6).set vecPtr yAddr).set outPtr zAddr).set rowsReg l).set colsReg m
  have hxA_exec : ExecWithin (B := .standard) w
      (ram[matPtr ← aBase; vecPtr ← yBase; outPtr ← zBase; rowsReg ← lReg; colsReg ← mReg])
      y₁ xA 5 :=
    WP.execWithin (B := .standard)
      (c := ram[matPtr ← aBase; vecPtr ← yBase; outPtr ← zBase; rowsReg ← lReg; colsReg ← mReg])
      (by wram_exec [hy₁_frame.aBase_eq, hy₁_frame.yBase_eq, hy₁_frame.zBase_eq, hy₁_frame.lReg_eq,
        hy₁_frame.mReg_eq]; rfl)
  obtain ⟨y₂, hy₂_mul, hy₂_vec, hy₂_out, hy₂_regs⟩ :=
    mulVecCode_spec (w := w) (mBase := 6) (vBase := yAddr) (oBase := zAddr) A xA
      (by wram_simp [xA]; exact hy₁_frame.zero_eq)
      (by wram_simp [xA]; exact hy₁_frame.one_eq)
      (by wram_simp [xA]; exact hy₁_frame.qReg_eq)
      (by wram_simp [xA]) (by wram_simp [xA]) (by wram_simp [xA])
      (by wram_simp [xA]) (by wram_simp [xA])
      hy₁_frame.matA (Or.inl (by omega)) (Or.inl (by omega)) hw_arith
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
  have hy₂_call : ExecWithin w callMulA y₁ y₂ (5 + (l * (12 * m + 10) + 4)) :=
    seq5_mulVec hxA_exec hy₂_mul
  rw [show readVec q xA.mem yAddr m = B *ᵥ (bit ∘ σ) from readVec_of_vecAt hy₁_vec] at hy₂_vec
  have hy₂_regs16 : ∀ i : Fin 28, i.val < 16 → y₂.regs i = x.regs i := fun i hi => by
    rw [hy₂_regs i (by omega)]
    have h16 : i ≠ matPtr := by rintro rfl; exact absurd hi (by decide)
    have h17 : i ≠ vecPtr := by rintro rfl; exact absurd hi (by decide)
    have h18 : i ≠ outPtr := by rintro rfl; exact absurd hi (by decide)
    have h19 : i ≠ rowsReg := by rintro rfl; exact absurd hi (by decide)
    have h20 : i ≠ colsReg := by rintro rfl; exact absurd hi (by decide)
    simp only [xA, Data.set_regs, Function.update_of_ne h16, Function.update_of_ne h17,
      Function.update_of_ne h18, Function.update_of_ne h19, Function.update_of_ne h20]
    exact hy₁_regs16 i hi
  have hy₂_frame : Frame q k A B C y₂ :=
    hy₁_frame.congr (fun i hi => by rw [hy₂_regs16 i (by omega), hy₁_regs16 i (by omega)])
      fun a ha => hy₂_out a (by omega)
  have hy₂_xvec : readVec q y₂.mem xAddr n = bit ∘ σ :=
    (readVec_frame fun a _ ha => hy₂_out a (by omega)).trans hy₁_xvec
  -- 3. `callMulC`: compute `w = C *ᵥ (bit ∘ σ)` at `wAddr`
  let xC :=
    ((((y₂.set matPtr (6 + l * m + m * n)).set vecPtr xAddr).set outPtr wAddr).set rowsReg l).set
      colsReg n
  have hxC_exec : ExecWithin (B := .standard) w
      (ram[matPtr ← cBase; vecPtr ← xBase; outPtr ← wBase; rowsReg ← lReg; colsReg ← nReg])
      y₂ xC 5 :=
    WP.execWithin (B := .standard)
      (c := ram[matPtr ← cBase; vecPtr ← xBase; outPtr ← wBase; rowsReg ← lReg; colsReg ← nReg])
      (by wram_exec [hy₂_frame.cBase_eq, hy₂_frame.xBase_eq, hy₂_frame.wBase_eq, hy₂_frame.lReg_eq,
        hy₂_frame.nReg_eq]; rfl)
  obtain ⟨y₃, hy₃_mul, hy₃_vec, hy₃_out, hy₃_regs⟩ :=
    mulVecCode_spec (w := w) (mBase := 6 + l * m + m * n) (vBase := xAddr) (oBase := wAddr) C xC
      (by wram_simp [xC]; exact hy₂_frame.zero_eq)
      (by wram_simp [xC]; exact hy₂_frame.one_eq)
      (by wram_simp [xC]; exact hy₂_frame.qReg_eq)
      (by wram_simp [xC]) (by wram_simp [xC]) (by wram_simp [xC])
      (by wram_simp [xC]) (by wram_simp [xC])
      hy₂_frame.matC (Or.inl (by omega)) (Or.inl (by omega)) hw_arith
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
  have hy₃_call : ExecWithin w callMulC y₂ y₃ (5 + (l * (12 * n + 10) + 4)) :=
    seq5_mulVec hxC_exec hy₃_mul
  rw [show readVec q xC.mem xAddr n = bit ∘ σ from hy₂_xvec] at hy₃_vec
  have hy₃_regs16 : ∀ i : Fin 28, i.val < 16 → y₃.regs i = x.regs i := fun i hi => by
    rw [hy₃_regs i (by omega)]
    have h16 : i ≠ matPtr := by rintro rfl; exact absurd hi (by decide)
    have h17 : i ≠ vecPtr := by rintro rfl; exact absurd hi (by decide)
    have h18 : i ≠ outPtr := by rintro rfl; exact absurd hi (by decide)
    have h19 : i ≠ rowsReg := by rintro rfl; exact absurd hi (by decide)
    have h20 : i ≠ colsReg := by rintro rfl; exact absurd hi (by decide)
    simp only [xC, Data.set_regs, Function.update_of_ne h16, Function.update_of_ne h17,
      Function.update_of_ne h18, Function.update_of_ne h19, Function.update_of_ne h20]
    exact hy₂_regs16 i hi
  have hy₃_frame : Frame q k A B C y₃ :=
    hy₂_frame.congr (fun i hi => by rw [hy₃_regs16 i (by omega), hy₂_regs16 i (by omega)])
      fun a ha => hy₃_out a (by omega)
  have hy₃_zvec : VecAt y₃.mem zAddr (A *ᵥ (B *ᵥ (bit ∘ σ))) :=
    vecAt_frame hy₂_vec fun a _ ha => hy₃_out a (by omega)
  -- 4. `vecEqCode` and `allOk ← allOk &&& acc`
  obtain ⟨y₄, hy₄_eq, hy₄_mem, hy₄_acc, hy₄_regs⟩ :=
    vecEqCode_spec (w := w) (A *ᵥ (B *ᵥ (bit ∘ σ))) (C *ᵥ (bit ∘ σ)) y₃
      hy₃_frame.zero_eq hy₃_frame.one_eq hy₃_frame.lReg_eq hy₃_frame.zBase_eq hy₃_frame.wBase_eq
      hy₃_zvec hy₃_vec
      (hw.of_le (by unfold wordBound; omega))
      (hw.of_le (by unfold wordBound; omega))
  have hy₄_regs16 : ∀ i : Fin 28, i.val < 16 → y₄.regs i = x.regs i := fun i hi =>
    (hy₄_regs i (by omega)).trans (hy₃_regs16 i hi)
  have hy₄_ok : y₄.regs allOk = curOk.toNat := (hy₄_regs16 allOk (by decide)).trans hok
  have : Fits w ((curOk && check A B C (bit ∘ σ)).toNat) := by
    cases curOk && check A B C (bit ∘ σ) <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;>
      exact hw.of_le (by unfold wordBound; omega)
  let y₅ := y₄.set allOk ((curOk && check A B C (bit ∘ σ)).toNat)
  have hy₅_and : ExecWithin w (ram[allOk ← allOk &&& acc]) y₄ y₅ 1 := by
    have hand : y₄.regs allOk &&& y₄.regs acc = (curOk && check A B C (bit ∘ σ)).toNat := by
      rw [hy₄_ok, hy₄_acc, Matrix.mulVec_mulVec, ← check_eq_decide]
      cases curOk <;> cases check A B C (bit ∘ σ) <;> rfl
    exact WP.execWithin (c := ram[allOk ← allOk &&& acc]) (by wram_exec [hand]; rfl)
  have htot : ExecWithin w checkCurrentVec x y₅
      (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 32) := by
    unfold checkCurrentVec
    exact (hy₁_call.seq (hy₂_call.seq (hy₃_call.seq (hy₄_eq.seq hy₅_and)))).mono
      (by ring_nf; omega)
  have hy₅_frame : Frame q k A B C y₅ :=
    hy₃_frame.congr
      (fun i hi => by
        have hne : i ≠ allOk := by rintro rfl; exact absurd hi (by decide)
        simp only [y₅, Data.set_regs, Function.update_of_ne hne]
        exact hy₄_regs i (by omega))
      (fun a _ => by simp [y₅, hy₄_mem])
  refine ⟨y₅, htot, hy₅_frame, ?_, by wram_simp [y₅]⟩
  have hne : trialIdx ≠ allOk := by decide
  simp only [y₅, Data.set_regs, Function.update_of_ne hne]
  exact hy₄_regs16 trialIdx (by decide)

/-! ### Randomized vector sampling and multi-trial law -/

private theorem sampleLoop_law {w q k l m n : ℕ}
    {A : Matrix (Fin l) (Fin m) (ZMod q)} {B : Matrix (Fin m) (Fin n) (ZMod q)}
    {C : Matrix (Fin l) (Fin n) (ZMod q)} (hw : Fits w (wordBound q k l m n)) :
    ∀ (d : ℕ) (x : Data 28), Frame q k A B C x → x.regs col + d = n →
      (∀ i < x.regs col, x.mem (6 + l * m + m * n + l * n + i) ≤ 1) →
      ExecRandLaw w sampleLoop x
        (fun y => Frame q k A B C y ∧
          (∀ i < n, y.mem (6 + l * m + m * n + l * n + i) ≤ 1) ∧
          y.regs trialIdx = x.regs trialIdx ∧ y.regs allOk = x.regs allOk)
        (6 * d + 2) d
        (fun y => bitsAt y.mem (6 + l * m + m * n + l * n) n)
        ((PMF.uniformOfFintype (Fin n → Bool)).map fun τ i =>
          if i.val < x.regs col then bitsAt x.mem (6 + l * m + m * n + l * n) n i else τ i)
  | 0, x, hx, hd, hbits => by
    have hc : ¬(Cond.lt col nReg).Holds x := by simp [Cond.holds_lt, hx.nReg_eq]; omega
    have hconst : (fun τ : Fin n → Bool => fun i : Fin n =>
        if i.val < x.regs col then bitsAt x.mem (6 + l * m + m * n + l * n) n i else τ i) =
        Function.const _ (bitsAt x.mem (6 + l * m + m * n + l * n) n) := by
      funext τ i
      simp only [Function.const_apply, show i.val < x.regs col by omega, ↓reduceIte]
    rw [hconst, PMF.map_const]
    exact ExecRandLaw.loop_exit hc ⟨hx, fun i hi => hbits i (by omega), rfl, rfl⟩
  | d + 1, x, hx, hd, hbits => by
    set xAddr := 6 + l * m + m * n + l * n
    obtain ⟨j, hj⟩ : ∃ j, x.regs col = j := ⟨_, rfl⟩
    rw [hj] at hd hbits ⊢
    have hjn : j < n := by omega
    have hc : (Cond.lt col nReg).Holds x := by simp [Cond.holds_lt, hx.nReg_eq, hj]; omega
    have : Fits w (xAddr + j) := hw.of_le (by dsimp only [xAddr]; unfold wordBound; omega)
    have : Fits w (j + 1) := hw.of_le (by unfold wordBound; omega)
    let Y (b : ℕ) : Data 28 :=
      (((x.set vVal b).set addr (xAddr + j)).write (xAddr + j) b).set col (j + 1)
    have hrest : ∀ b : Fin (x.regs one + 1),
        ExecWithin w (ram[addr ← xBase + col; *addr ← vVal; col ← col + one])
          (x.set vVal b.val) (Y b.val) 3 := fun _ =>
      WP.execWithin (c := ram[addr ← xBase + col; *addr ← vVal; col ← col + one])
        (by wram_exec [hx.xBase_eq, hx.one_eq, hj]; rfl)
    have hbody := ExecRandLaw.rand_seq (w := w) (f := fun y => bitsAt y.mem xAddr n)
      (P := fun y => ∃ b ≤ 1, y = Y b) (y := fun b => Y b.val)
      (by rw [hx.one_eq]; exact hw.of_le (by unfold wordBound; omega)) hrest
      (fun b => ⟨b.val, by have := b.isLt; have := hx.one_eq; omega, rfl⟩)
    have hlaw := ExecRandLaw.loop_iter
      (Q := fun y => Frame q k A B C y ∧
        (∀ i < n, y.mem (xAddr + i) ≤ 1) ∧
        y.regs trialIdx = x.regs trialIdx ∧ y.regs allOk = x.regs allOk)
      (κ := fun σ' =>
        (PMF.uniformOfFintype (Fin n → Bool)).map fun τ i =>
          if i.val < j + 1 then σ' i else τ i) hc hbody (fun y ⟨b, hb, hy⟩ => by
      subst hy
      have hYc : (Y b).regs col = j + 1 := by wram_simp [Y]
      have hYframe : Frame q k A B C (Y b) :=
        hx.congr
          (fun i hi => by
            have h23 : i ≠ col := by rintro rfl; exact absurd hi (by decide)
            have h25 : i ≠ addr := by rintro rfl; exact absurd hi (by decide)
            have h27 : i ≠ vVal := by rintro rfl; exact absurd hi (by decide)
            simp [Y, Function.update_of_ne h23, Function.update_of_ne h25,
              Function.update_of_ne h27])
          (fun a ha => by
            have hne : a ≠ xAddr + j := by dsimp only [xAddr]; omega
            simp only [Y, Data.set_mem, Data.write_mem, Function.update_of_ne hne])
      have h := sampleLoop_law hw d (Y b) hYframe (by rw [hYc]; omega)
        (fun i hi => by
          rw [hYc] at hi
          simp only [Y, Data.set_mem, Data.write_mem, Function.update_apply]
          split_ifs
          · exact hb
          · exact hbits i (by omega))
      rw [hYc] at h
      have hYt : (Y b).regs trialIdx = x.regs trialIdx := by wram_simp [Y]
      have hYo : (Y b).regs allOk = x.regs allOk := by wram_simp [Y]
      unfold sampleLoop at h
      exact h.mono (fun z ⟨hzf, hzb, hzt, hzo⟩ =>
        ⟨hzf, hzb, hzt.trans hYt, hzo.trans hYo⟩) le_rfl le_rfl)
    refine (hlaw.congr_law ?_).mono (fun _ h => h) (by omega) (by omega)
    rw [hx.one_eq, PMF.bind_map]
    have hYa (b : ℕ) : bitsAt (Y b).mem xAddr n =
        Function.update (bitsAt x.mem xAddr n) ⟨j, hjn⟩ (decide (b = 1)) := by
      simp only [Y, Data.set_mem, Data.write_mem]
      exact bitsAt_update_self x.mem xAddr ⟨j, hjn⟩ b
    let G : (Fin n → Bool) → (Fin n → Bool) := fun τ i =>
      if i.val < j then bitsAt x.mem xAddr n i else τ i
    have hcomp (b : Bool) : (fun τ : Fin n → Bool => fun i : Fin n =>
        if i.val < j + 1 then Function.update (bitsAt x.mem xAddr n) ⟨j, hjn⟩ b i else τ i) =
        G ∘ fun τ => Function.update τ ⟨j, hjn⟩ b := by
      funext τ i
      simp only [G, Function.comp_apply, Function.update_apply, Fin.ext_iff]
      by_cases h1 : i.val < j
      · simp [h1, show i.val < j + 1 by omega, show i.val ≠ j by omega]
      · by_cases h2 : i.val = j
        · simp [h2]
        · simp [h1, h2, show ¬i.val < j + 1 by omega]
    calc (PMF.uniformOfFintype (Fin (1 + 1))).bind
          ((fun σ' => (PMF.uniformOfFintype (Fin n → Bool)).map fun τ i =>
            if i.val < j + 1 then σ' i else τ i) ∘ fun b => bitsAt (Y b.val).mem xAddr n)
        = (PMF.uniformOfFintype (Fin (1 + 1))).bind (fun b =>
            ((PMF.uniformOfFintype (Fin n → Bool)).map
              fun τ => Function.update τ ⟨j, hjn⟩ (finTwoEquiv b)).map G) := by
          congr 1 with b : 1
          have hb : decide (b.val = 1) = finTwoEquiv b := by fin_cases b <;> rfl
          simp only [Function.comp_apply, hYa, hb, hcomp, PMF.map_comp]
      _ = ((PMF.uniformOfFintype Bool).bind fun b =>
            (PMF.uniformOfFintype (Fin n → Bool)).map
              fun τ => Function.update τ ⟨j, hjn⟩ b).map G := by
          rw [← PMF.uniformOfFintype_map_equiv finTwoEquiv, PMF.bind_map, PMF.map_bind]
          rfl
      _ = _ := by rw [PMF.uniformOfFintype_update]

private theorem sampleVecCode_law {w q k l m n : ℕ}
    {A : Matrix (Fin l) (Fin m) (ZMod q)} {B : Matrix (Fin m) (Fin n) (ZMod q)}
    {C : Matrix (Fin l) (Fin n) (ZMod q)} (hw : Fits w (wordBound q k l m n))
    {x : Data 28} (hx : Frame q k A B C x) :
    ExecRandLaw w sampleVecCode x
      (fun y => Frame q k A B C y ∧
        (∀ i < n, y.mem (6 + l * m + m * n + l * n + i) ≤ 1) ∧
        y.regs trialIdx = x.regs trialIdx ∧ y.regs allOk = x.regs allOk)
      (6 * n + 3) n
      (fun y => bitsAt y.mem (6 + l * m + m * n + l * n) n)
      (PMF.uniformOfFintype (Fin n → Bool)) := by
  have hx0_frame : Frame q k A B C (x.set col 0) :=
    hx.congr (fun i hi => by
      have hne : i ≠ col := by rintro rfl; exact absurd hi (by decide)
      simp [Function.update_of_ne hne]) (fun _ _ => rfl)
  have h := sampleLoop_law hw n (x.set col 0) hx0_frame (by simp) (by simp)
  simp only [Data.set_regs, Function.update_self, Nat.not_lt_zero, ↓reduceIte] at h
  rw [show (fun τ : Fin n → Bool => fun i => τ i) = id from rfl, PMF.map_id] at h
  have hcopy := ExecWithin.copy (B := .standard) (w := w) (d := col) (s := zero) (x := x)
  rw [hx.zero_eq] at hcopy
  have hxt : (x.set col 0).regs trialIdx = x.regs trialIdx := by wram_simp
  have hxo : (x.set col 0).regs allOk = x.regs allOk := by wram_simp
  exact (ExecRandLaw.seq_det hcopy h).mono
    (fun y ⟨hyf, hyb, hyt, hyo⟩ => ⟨hyf, hyb, hyt.trans hxt, hyo.trans hxo⟩)
    (by omega) le_rfl

private theorem trialBody_law {w q k l m n : ℕ} [NeZero q]
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (hw : Fits w (wordBound q k l m n))
    {x : Data 28} (hx : Frame q k A B C x) (curOk : Bool)
    (hok : x.regs allOk = curOk.toNat) (htrial : x.regs trialIdx < k) :
    ExecRandLaw w trialBody x
      (fun y => Frame q k A B C y ∧
        y.regs trialIdx = x.regs trialIdx + 1 ∧
        y.regs allOk = (decide (y.regs allOk = 1)).toNat)
      (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 6 * n + 36) n
      (fun y => decide (y.regs allOk = 1))
      ((PMF.uniformOfFintype (Fin n → Bool)).map fun σ => curOk && check A B C (bit ∘ σ)) := by
  have hsample := sampleVecCode_law hw hx
  have hcomb := ExecRandLaw.seq
    (c₁ := sampleVecCode)
    (c₂ := ram[⟪checkCurrentVec⟫; trialIdx ← trialIdx + one])
    (Q := fun y => Frame q k A B C y ∧
      y.regs trialIdx = x.regs trialIdx + 1 ∧
      y.regs allOk = (decide (y.regs allOk = 1)).toNat)
    (f := fun y => decide (y.regs allOk = 1))
    (κ := fun σ => PMF.pure (curOk && check A B C (bit ∘ σ)))
    (T₂ := 12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 33)
    (R₂ := 0) hsample
    (fun y ⟨hyf, hyb, hyt, hyo⟩ => by
      obtain ⟨z, hz_exec, hzf, hzt, hzo⟩ :=
        checkCurrentVec_spec A B C y curOk hyf hyb (hyo.trans hok) hw
      have hinc_fit : Fits w (z.regs trialIdx + 1) := by
        rw [hzt, hyt]
        exact hw.of_le (by unfold wordBound; omega)
      let z' := z.set trialIdx (z.regs trialIdx + 1)
      have hinc : ExecWithin w (ram[trialIdx ← trialIdx + one]) z z' 1 :=
        WP.execWithin (c := ram[trialIdx ← trialIdx + one]) (by wram_exec [hzf.one_eq]; rfl)
      have hz'_frame : Frame q k A B C z' :=
        hzf.congr (fun i hi => by
          have hne : i ≠ trialIdx := by rintro rfl; exact absurd hi (by decide)
          simp [z', Function.update_of_ne hne]) (fun _ _ => rfl)
      have hz'_ok : z'.regs allOk = (curOk && check A B C
          (bit ∘ bitsAt y.mem (6 + l * m + m * n + l * n) n)).toNat := by
        have hne : allOk ≠ trialIdx := by decide
        simpa [z', Function.update_of_ne hne] using hzo
      have hz'_obs : decide (z'.regs allOk = 1) =
          (curOk && check A B C (bit ∘ bitsAt y.mem (6 + l * m + m * n + l * n) n)) := by
        rw [hz'_ok]
        cases curOk && check A B C (bit ∘ bitsAt y.mem (6 + l * m + m * n + l * n) n) <;> rfl
      have hdet : ExecWithin w (ram[⟪checkCurrentVec⟫; trialIdx ← trialIdx + one]) y z'
          (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 33) :=
        (hz_exec.seq hinc).mono (by omega)
      have hpost : Frame q k A B C z' ∧
          z'.regs trialIdx = x.regs trialIdx + 1 ∧
          z'.regs allOk = (decide (z'.regs allOk = 1)).toNat :=
        ⟨hz'_frame, by simp [z', Data.set_regs, hzt, hyt], by rw [hz'_obs, hz'_ok]⟩
      exact (ExecRandLaw.of_execWithin (f := fun w => decide (w.regs allOk = 1))
        hdet hpost).congr_law (by rw [hz'_obs]))
  change ExecRandLaw w trialBody x _ _ _ _ _ at hcomb
  refine (hcomb.congr_law ?_).mono (fun _ h => h) (by omega) (by omega)
  rw [← PMF.bind_pure_comp]
  rfl

private def remOk {q k l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ZMod q))
    (B : Matrix (Fin m) (Fin n) (ZMod q)) (C : Matrix (Fin l) (Fin n) (ZMod q))
    (j : ℕ) (xs : Fin k → Fin n → Bool) : Bool :=
  decide (∀ t : Fin k, j ≤ t.val → check A B C (bit ∘ xs t) = true)

private theorem trialsLoop_law {w q k l m n : ℕ} [NeZero q]
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (hw : Fits w (wordBound q k l m n)) :
    ∀ (d : ℕ) (x : Data 28) (curOk : Bool),
      Frame q k A B C x → x.regs trialIdx + d = k → x.regs allOk = curOk.toNat →
      ExecRandLaw w trialsLoop x
        (fun y => Frame q k A B C y ∧ y.regs allOk = (decide (y.regs allOk = 1)).toNat)
        (d * (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 6 * n + 38) + 2) (d * n)
        (fun y => decide (y.regs allOk = 1))
        ((PMF.uniformOfFintype (Fin k → Fin n → Bool)).map fun xs =>
          curOk && remOk A B C (x.regs trialIdx) xs)
  | 0, x, curOk, hx, hd, hok => by
    have hc : ¬(Cond.lt trialIdx kReg).Holds x := by simp [Cond.holds_lt, hx.kReg_eq]; omega
    have hconst : (fun xs : Fin k → Fin n → Bool =>
        curOk && remOk A B C (x.regs trialIdx) xs) = Function.const _ curOk := by
      funext xs
      have hvac : (∀ t : Fin k, x.regs trialIdx ≤ t.val → check A B C (bit ∘ xs t) = true) :=
        fun t ht => absurd ht (by have := t.isLt; omega)
      simp only [remOk, Function.const_apply, decide_eq_true hvac, Bool.and_true]
    have hx_obs : decide (x.regs allOk = 1) = curOk := by
      rw [hok]; cases curOk <;> rfl
    rw [hconst, PMF.map_const, ← hx_obs]
    exact (ExecRandLaw.loop_exit hc ⟨hx, by rw [hx_obs, hok]⟩).mono
      (fun _ h => h) (by omega) (by omega)
  | d + 1, x, curOk, hx, hd, hok => by
    obtain ⟨j, hj⟩ : ∃ j, x.regs trialIdx = j := ⟨_, rfl⟩
    rw [hj] at hd ⊢
    have hjk : j < k := by omega
    have hc : (Cond.lt trialIdx kReg).Holds x := by simp [Cond.holds_lt, hx.kReg_eq, hj]; omega
    have hb := trialBody_law A B C hw hx curOk hok (by rw [hj]; exact hjk)
    have hlaw := ExecRandLaw.loop_iter
      (Q := fun y => Frame q k A B C y ∧ y.regs allOk = (decide (y.regs allOk = 1)).toNat)
      (g := fun y => decide (y.regs allOk = 1))
      (f := fun y => decide (y.regs allOk = 1))
      (κ := fun b' => (PMF.uniformOfFintype (Fin k → Fin n → Bool)).map fun xs =>
        b' && remOk A B C (j + 1) xs)
      hc hb (fun y ⟨hyf, hyt, hyo⟩ => by
        rw [hj] at hyt
        have h := trialsLoop_law A B C hw d y (decide (y.regs allOk = 1)) hyf
          (by rw [hyt]; omega) hyo
        rw [hyt] at h
        unfold trialsLoop at h
        exact h)
    change ExecRandLaw w trialsLoop x _ _ _ _ _ at hlaw
    refine (hlaw.congr_law ?_).mono (fun _ h => h) (by ring_nf; omega) (by ring_nf; omega)
    rw [PMF.bind_map]
    let G : (Fin k → Fin n → Bool) → Bool := fun xs => curOk && remOk A B C j xs
    have hstep (σ : Fin n → Bool) :
        (fun xs : Fin k → Fin n → Bool =>
          (curOk && check A B C (bit ∘ σ)) && remOk A B C (j + 1) xs) =
        G ∘ fun xs => Function.update xs ⟨j, hjk⟩ σ := by
      funext xs
      simp only [G, remOk, Function.comp_apply, Bool.and_assoc]
      congr 1
      rw [show check A B C (bit ∘ σ) = decide (check A B C (bit ∘ σ) = true) by
        cases check A B C (bit ∘ σ) <;> rfl, ← Bool.decide_and]
      refine decide_eq_decide.mpr ⟨fun ⟨h0, hrest⟩ t ht => ?_, fun hall => ⟨?_, fun t ht => ?_⟩⟩
      · by_cases htj : t.val = j
        · have : t = ⟨j, hjk⟩ := Fin.ext htj
          subst this
          simpa using h0
        · have hne : t ≠ ⟨j, hjk⟩ := fun h => htj (congrArg Fin.val h)
          simpa only [Function.update_of_ne hne] using hrest t (by omega)
      · simpa using hall ⟨j, hjk⟩ le_rfl
      · have hne : t ≠ ⟨j, hjk⟩ := by rintro rfl; exact Nat.not_succ_le_self j ht
        simpa only [Function.update_of_ne hne] using hall t (by omega)
    calc (PMF.uniformOfFintype (Fin n → Bool)).bind
          (((fun b' => (PMF.uniformOfFintype (Fin k → Fin n → Bool)).map fun xs =>
            b' && remOk A B C (j + 1) xs) ∘
            fun σ => curOk && check A B C (bit ∘ σ)))
        = (PMF.uniformOfFintype (Fin n → Bool)).bind (fun σ =>
            ((PMF.uniformOfFintype (Fin k → Fin n → Bool)).map
              fun xs => Function.update xs ⟨j, hjk⟩ σ).map G) := by
          congr 1 with σ : 1
          simp only [Function.comp_apply, hstep σ, PMF.map_comp]
      _ = ((PMF.uniformOfFintype (Fin n → Bool)).bind fun σ =>
            (PMF.uniformOfFintype (Fin k → Fin n → Bool)).map
              fun xs => Function.update xs ⟨j, hjk⟩ σ).map G := by
          rw [PMF.map_bind]
      _ = _ := by rw [PMF.uniformOfFintype_update]

/-! ### Initial setup and compiled end-to-end theorems -/

private theorem holdsList_init (xs : List ℕ) :
    HoldsList 1 xs (Data.init xs : Data 28).mem := fun i => by
  change (Data.init xs : Data 28).mem (1 + i.val) = xs[i.val]
  rw [Nat.add_comm 1 i.val, Data.init_mem_succ, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem i.isLt, Option.getD_some]

private theorem setupCode_spec {w q k l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (hw : Fits w (wordBound q k l m n)) :
    ∃ y, ExecWithin w setupCode (Data.init (encode q k A B C)) y 23 ∧
      Frame q k A B C y ∧ y.regs trialIdx = 0 ∧ y.regs allOk = 1 := by
  let mem0 := (Data.init (encode q k A B C) : Data 28).mem
  have hm1 : (Data.init (encode q k A B C) : Data 28).mem 1 = q := rfl
  have hm2 : (Data.init (encode q k A B C) : Data 28).mem 2 = k := rfl
  have hm3 : (Data.init (encode q k A B C) : Data 28).mem 3 = l := rfl
  have hm4 : (Data.init (encode q k A B C) : Data 28).mem 4 = m := rfl
  have hm5 : (Data.init (encode q k A B C) : Data 28).mem 5 = n := rfl
  have hin : HoldsList 1 (q :: k :: l :: m :: n :: (encodeMatrix A ++ encodeMatrix B ++
      encodeMatrix C)) mem0 := holdsList_init (encode q k A B C)
  simp only [holdsList_cons_iff, holdsList_append_iff, List.length_append,
    length_encodeMatrix] at hin
  obtain ⟨-, -, -, -, -, ⟨hA, hB⟩, hC⟩ := hin
  have : Fits w 0 := fits_zero w
  have : Fits w 1 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 2 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 3 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 4 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 5 := hw.of_le (by unfold wordBound; omega)
  have : Fits w 6 := hw.of_le (by unfold wordBound; omega)
  have : Fits w (l * m) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (6 + l * m) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (m * n) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (6 + l * m + m * n) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (l * n) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (6 + l * m + m * n + l * n) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (6 + l * m + m * n + l * n + n) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (6 + l * m + m * n + l * n + n + m) := hw.of_le (by unfold wordBound; omega)
  have : Fits w (6 + l * m + m * n + l * n + n + m + l) := hw.of_le (by unfold wordBound; omega)
  refine WP.exists_execWithin (w := w) (c := setupCode) ?_
  unfold setupCode
  wram_exec [hm1, hm2, hm3, hm4, hm5]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
    rfl, rfl⟩
  · simp only [Data.set_mem]
    exact matrixAt_of_holdsList hA
  · simp only [Data.set_mem]
    exact matrixAt_of_holdsList hB
  · simp only [Data.set_mem]
    rw [show 1 + 1 + 1 + 1 + 1 + 1 + (l * m + m * n) = 6 + l * m + m * n by omega] at hC
    exact matrixAt_of_holdsList hC

/-- Structured execution law of `verifyCode` from `Data.init (encode q k A B C)`. -/
theorem verifyCode_law {w q k l m n : ℕ} [NeZero q]
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (hw : Fits w (wordBound q k l m n)) :
    ExecRandLaw w verifyCode (Data.init (encode q k A B C))
      (fun y => Frame q k A B C y ∧ y.regs allOk = (decide (y.regs allOk = 1)).toNat)
      (k * (12 * (l * m + m * n + l * n) + 10 * m + 30 * l + 6 * n + 38) + 25) (k * n)
      (fun y => decide (y.regs allOk = 1))
      (ProbComp.eval (verify bit k A B C)) := by
  obtain ⟨y₀, hy₀, hframe₀, htrial₀, hok₀⟩ := setupCode_spec A B C hw
  have hloop := trialsLoop_law A B C hw k y₀ true hframe₀ (by rw [htrial₀]; omega) hok₀
  refine ((ExecRandLaw.seq_det hy₀ hloop).congr_law ?_).mono (fun _ h => h) (by omega) le_rfl
  rw [htrial₀, eval_verify]
  congr 1 with xs : 1
  simp only [remOk, Nat.zero_le, forall_const, Bool.true_and, check_eq_decide, decide_eq_true_eq]

private def usesRandSrc {B : Basis} {r : ℕ} (s : Fin r) : Code B r → Bool
  | .op _ => true
  | .rand _ src => src == s
  | .seq c₁ c₂ => usesRandSrc s c₁ && usesRandSrc s c₂
  | .branch _ pos neg => usesRandSrc s pos && usesRandSrc s neg
  | .loop _ body => usesRandSrc s body

private theorem queriesSatisfy_one_of_execRand {w : ℕ} {c : Code .standard 28} {x : Data 28}
    {m : ProbComp (Data 28 × ℕ)} (h : ExecRand w c x m)
    (hone : x.regs one = 1) (hp : c.Preserves one) (hu : usesRandSrc one c = true) :
    Cslib.OracleComp.QueriesSatisfy (· = 1) m := by
  induction h with
  | @op _ x' y' _ => exact Cslib.OracleComp.QueriesSatisfy.pure _
  | @rand dst src x' _ =>
    simp only [usesRandSrc, beq_iff_eq] at hu
    subst hu
    have hq : Cslib.OracleComp.QueriesSatisfy (· = 1) (ProbComp.unifFin (x'.regs one)) :=
      Cslib.OracleComp.QueriesSatisfy.query (p := (· = 1)) hone
    simpa only [Cslib.OracleComp.QueriesSatisfy, Nat.add_zero] using
      Cslib.OracleComp.IsCostBounded.bind_on_support hq
        fun _ _ => Cslib.OracleComp.QueriesSatisfy.pure _
  | @seq _ _ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [usesRandSrc, Bool.and_eq_true] at hu
    simpa only [Cslib.OracleComp.QueriesSatisfy, Nat.add_zero] using
      Cslib.OracleComp.IsCostBounded.bind_on_support (ih₁ hone hp.1 hu.1) fun z hz =>
        Cslib.OracleComp.IsCostBounded.bind_on_support
          (ih₂ z hz ((h₁.regs_eq hp.1 hz).trans hone) hp.2 hu.2)
          fun _ _ => Cslib.OracleComp.QueriesSatisfy.pure _
  | branch_pos _ _ ih =>
    simp only [usesRandSrc, Bool.and_eq_true] at hu
    exact (Cslib.OracleComp.isCostBounded_map_iff _ _ 0).mpr (ih hone hp.1 hu.1)
  | branch_neg _ _ ih =>
    simp only [usesRandSrc, Bool.and_eq_true] at hu
    exact (Cslib.OracleComp.isCostBounded_map_iff _ _ 0).mpr (ih hone hp.2 hu.2)
  | loop_exit _ => exact Cslib.OracleComp.QueriesSatisfy.pure _
  | @loop_iter _ _ _ _ _ _ hb _ ihb ihl =>
    simp only [usesRandSrc] at hu
    simpa only [Cslib.OracleComp.QueriesSatisfy, Nat.add_zero] using
      Cslib.OracleComp.IsCostBounded.bind_on_support (ihb hone hp hu) fun z hz =>
        Cslib.OracleComp.IsCostBounded.bind_on_support
          (ihl z hz ((hb.regs_eq hp hz).trans hone) hp hu)
          fun _ _ => Cslib.OracleComp.QueriesSatisfy.pure _

private theorem randBitsBounded_verifyProgram {w q k l m n T : ℕ} [NeZero q]
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (hw : Fits w (wordBound q k l m n))
    (hT : verifyTime k l m n ≤ T) :
    RandBitsBounded w verifyProgram (State.init (encode q k A B C)) T (k * n) := by
  obtain ⟨y₀, ⟨t₀, ht₀, he₀⟩, hframe₀, htrial₀, hok₀⟩ := setupCode_spec A B C hw
  obtain ⟨ml, hml, hql, hsupl, -⟩ :=
    trialsLoop_law A B C hw k y₀ true hframe₀ (by rw [htrial₀]; omega) hok₀
  have hseq : ExecRand w verifyCode (Data.init (encode q k A B C))
      ((fun z => (z.1, t₀ + z.2)) <$> ml) := he₀.seqRand hml
  have hrun := hseq.runRand_program allOk (T := T) fun z hz => by
    obtain ⟨z₀, hz₀, rfl⟩ := Cslib.OracleComp.mem_supportWith_map_iff.mp hz
    have := (hsupl z₀ hz₀).2
    unfold verifyTime at hT
    omega
  have hsat_ml : Cslib.OracleComp.QueriesSatisfy (· = 1) ml :=
    queriesSatisfy_one_of_execRand hml hframe₀.one_eq (by decide) (by decide)
  have hcost_ml : Cslib.OracleComp.IsCostBounded unifBitCost ml (k * n) := by
    have hmul := Cslib.OracleComp.IsQueryBounded.isCostBounded_mul
      (cost := unifBitCost) (c := 1) (p := (· = 1)) hql hsat_ml
      fun u hu => by
        subst hu
        decide
    simpa only [Nat.mul_one] using hmul
  simpa only [RandBitsBounded, verifyProgram, State.init, hrun, Functor.map_map,
    Cslib.OracleComp.isCostBounded_map_iff] using hcost_ml

/-- **End-to-end randomized word-RAM specification of Freivalds' `k`-trial verifier.**
At any word width `w` with `Fits w (wordBound q k l m n)` and fuel `T ≥ verifyTime k l m n`:

1. every execution path halts cleanly within `T` instructions (`RandHaltsWithin`);
2. every path executes at most `k * n` `rand` calls (`RandCallsBounded`) and consumes at most
   `k * n` entropy bits (`RandBitsBounded`);
3. the acceptance observation `cfgAccepts` has exact law
   `ProbComp.eval (Cslib.Algorithms.Lean.Freivalds.verify bit k A B C)`. -/
theorem verifyProgram_spec {w q k l m n T : ℕ} [NeZero q]
    (A : Matrix (Fin l) (Fin m) (ZMod q)) (B : Matrix (Fin m) (Fin n) (ZMod q))
    (C : Matrix (Fin l) (Fin n) (ZMod q)) (hw : Fits w (wordBound q k l m n))
    (hT : verifyTime k l m n ≤ T) :
    RandHaltsWithin w verifyProgram (State.init (encode q k A B C)) T ∧
      RandCallsBounded w verifyProgram (State.init (encode q k A B C)) T (k * n) ∧
      RandBitsBounded w verifyProgram (State.init (encode q k A B C)) T (k * n) ∧
      (evalRand w verifyProgram T (State.init (encode q k A B C))).map cfgAccepts =
        ProbComp.eval (verify bit k A B C) := by
  obtain ⟨hhalt, hcalls, -, hlaw⟩ :=
    (verifyCode_law A B C hw).program allOk (T' := T) (by unfold verifyTime at hT; omega)
      cfgAccepts (fun _ _ => rfl)
  exact ⟨hhalt, hcalls, randBitsBounded_verifyProgram A B C hw hT, hlaw⟩

/-- **Perfect completeness:** when `A * B = C`, `verifyProgram` accepts on every path (probability
`1`). -/
theorem verifyProgram_accept_of_mul_eq {w q k l m n T : ℕ} [NeZero q]
    {A : Matrix (Fin l) (Fin m) (ZMod q)} {B : Matrix (Fin m) (Fin n) (ZMod q)}
    {C : Matrix (Fin l) (Fin n) (ZMod q)} (h : A * B = C)
    (hw : Fits w (wordBound q k l m n)) (hT : verifyTime k l m n ≤ T) :
    (evalRand w verifyProgram T (State.init (encode q k A B C))).map cfgAccepts =
      PMF.pure true := by
  rw [(verifyProgram_spec A B C hw hT).2.2.2, eval_verify_of_mul_eq bit k h]

/-- **One-sided soundness:** when `A * B ≠ C`, `verifyProgram` accepts with probability at most
`2⁻¹ ^ k`. -/
theorem verifyProgram_accept_le_of_mul_ne {w q k l m n T : ℕ} [NeZero q]
    {A : Matrix (Fin l) (Fin m) (ZMod q)} {B : Matrix (Fin m) (Fin n) (ZMod q)}
    {C : Matrix (Fin l) (Fin n) (ZMod q)} (h : A * B ≠ C)
    (hw : Fits w (wordBound q k l m n)) (hT : verifyTime k l m n ≤ T) :
    ((evalRand w verifyProgram T (State.init (encode q k A B C))).map cfgAccepts) true ≤
      2⁻¹ ^ k := by
  rw [(verifyProgram_spec A B C hw hT).2.2.2]
  exact eval_verify_bool_true_le k h

/-- **Square-matrix specialization (`O(k n²)` instructions):** on `n × n` matrices over `ZMod q`,
`verifyProgram` halts within `verifySquareTime k n = k * (36 * n ^ 2 + 46 * n + 38) + 26`
instructions, makes at most `k * n` `rand` calls (`k * n` entropy bits), accepts `A * B = C` with
probability `1`, and accepts `A * B ≠ C` with probability at most `2⁻¹ ^ k`. -/
theorem verifyProgram_square_spec {w q k n T : ℕ} [NeZero q]
    (A B C : Matrix (Fin n) (Fin n) (ZMod q))
    (hw : Fits w (wordBound q k n n n)) (hT : verifySquareTime k n ≤ T) :
    RandHaltsWithin w verifyProgram (State.init (encode q k A B C)) T ∧
      RandCallsBounded w verifyProgram (State.init (encode q k A B C)) T (k * n) ∧
      RandBitsBounded w verifyProgram (State.init (encode q k A B C)) T (k * n) ∧
      (A * B = C →
        (evalRand w verifyProgram T (State.init (encode q k A B C))).map cfgAccepts =
          PMF.pure true) ∧
      (A * B ≠ C →
        ((evalRand w verifyProgram T (State.init (encode q k A B C))).map cfgAccepts) true ≤
          2⁻¹ ^ k) := by
  have hT' : verifyTime k n n n ≤ T := (verifyTime_square_eq k n).trans_le hT
  obtain ⟨hhalt, hcalls, hbits, _⟩ := verifyProgram_spec A B C hw hT'
  exact ⟨hhalt, hcalls, hbits,
    fun heq => verifyProgram_accept_of_mul_eq heq hw hT',
    fun hne => verifyProgram_accept_le_of_mul_ne hne hw hT'⟩

end Cslib.Algorithms.WordRAM.Freivalds
