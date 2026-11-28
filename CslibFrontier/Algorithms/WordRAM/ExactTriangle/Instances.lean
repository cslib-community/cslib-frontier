/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.Catalogue
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.InstancePair
import CslibFrontier.Computability.WordRAM.PreservesMask
import CslibFrontier.Computability.WordRAM.Sequence
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall

/-!
# Native ExactTriangle instance preparation

The input header is `(D,g,n,p)`, followed by the three signed weight matrices. The program first
computes the real class/chunk catalogue. It then visits each actual chunk and piece, reads that
chunk's descriptor, computes the piece boundaries and writes its record and two zero/one matrices.
The records share the already computed query arrays. Every visit uses the existing native
`InstancePair.program` rather than assuming a matrix-preparation routine.

The output records and matrices occupy consecutive variable-size blocks. Register `output` names
the first record, `produced` gives their actual number and `heap` is their final allocation end.
Each block has six record words followed by `2nD` matrix words. This module prepares instances;
it does not choose a prime, evaluate their queried products or decide ExactTriangle.

## Main definitions

* `Instances.program`: fixed sixty-four-register initialized instance-preparation program.
* `Instances.visit`: one computed class/chunk/piece visit, including both native matrix calls.
* `Instances.timeBound`: the catalogue cost plus the full native visit and loop budgets,
  including the final halt.
* `Instances.Output`: actual catalogue, record, matrix and frame readback.

## Main results

* `Instances.exec_at`: complete native execution from the original header and weight arrays.
* `Instances.exec_at_with_prefix`: complete execution together with the post-catalogue/setup
  state shared with one-slot streaming callers.
* `Instances.exec_visit`: single-record chunk/piece construction step.

`PreparationInput` supplies the initialized flat-program interface and derived width bounds;
`PreparationBounds` proves the preparation time bound in the source's parameter regime.
Code-stage definitions and single-visit invariants (`pairInput`, `visit_preserves`,
`budget_covers_loop`) are exposed for interpreter and streaming clients; internal proof helpers are
private.

## References

The matrix geometry follows the pinned
[Theorem 17 matrix construction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean).
The native controller and resource proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Instances

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Outer matrix dimension. -/
abbrev size : Fin 64 := 32
/-- Target padded middle dimension. -/
abbrev dimension : Fin 64 := 33
/-- Residue modulus. -/
abbrev modulus : Fin 64 := 34
/-- Computed maximum vertices per piece. -/
abbrev pieceLength : Fin 64 := 35
/-- Computed number of pieces. -/
abbrev pieces : Fin 64 := 36
/-- Actual number of nonempty query chunks. -/
abbrev chunks : Fin 64 := 37
/-- Computed chunk-descriptor array. -/
abbrev descriptors : Fin 64 := 38
/-- First output record. -/
abbrev output : Fin 64 := 39
/-- Number of completely written instance blocks. -/
abbrev produced : Fin 64 := 40
/-- Actual chunk count times piece count. -/
abbrev total : Fin 64 := 41
/-- Next free output record. -/
abbrev heap : Fin 64 := 42
/-- Words per record and its two matrices. -/
abbrev stride : Fin 64 := 43
/-- Constant one. -/
abbrev one : Fin 64 := 44
/-- Words per chunk descriptor. -/
abbrev three : Fin 64 := 45
/-- Words per instance record. -/
abbrev six : Fin 64 := 46
/-- Words in one matrix. -/
abbrev area : Fin 64 := 47
/-- Original A–C residue matrix. -/
abbrev srcLeft : Fin 64 := 48
/-- Original B–C residue matrix. -/
abbrev srcRight : Fin 64 := 49
/-- Descriptor/header address temporary. -/
abbrev addr : Fin 64 := 50
/-- Current chunk ordinal. -/
abbrev chunkIndex : Fin 64 := 51
/-- Current piece ordinal. -/
abbrev pieceIndex : Fin 64 := 52
/-- Residue loaded from the actual chunk descriptor. -/
abbrev rho : Fin 64 := 53
/-- Query pointer loaded from the actual chunk descriptor. -/
abbrev queries : Fin 64 := 54
/-- Query count loaded from the actual chunk descriptor. -/
abbrev queryCount : Fin 64 := 55
/-- First vertex of the current piece. -/
abbrev first : Fin 64 := 56
/-- Actual length of the current piece. -/
abbrev length : Fin 64 := 57
/-- Original weight-matrix area temporary. -/
abbrev temp : Fin 64 := 58

/-- Existing catalogue computation in the lower thirty-two registers. -/
@[expose]
def catalogue : Code .standard 64 := Catalogue.program.rename (Fin.castLE (by decide))

/-- Save the actual catalogue outputs and compute the allocation stride and residue bases. -/
@[expose]
def setup : Code .standard 64 :=
  let lowSize : Fin 64 := 16
  let lowModulus : Fin 64 := 17
  let lowLength : Fin 64 := 28
  let lowPieces : Fin 64 := 29
  let lowChunks : Fin 64 := 21
  let lowDescriptors : Fin 64 := 18
  let lowOutput : Fin 64 := 22
  ram[ one ← #1; three ← #3; six ← #6;
    size ← lowSize; modulus ← lowModulus; pieceLength ← lowLength; pieces ← lowPieces;
    chunks ← lowChunks; descriptors ← lowDescriptors; output ← lowOutput;
    produced ← #0; heap ← output; total ← chunks * pieces;
    addr ← #1; dimension ← *addr; area ← size * dimension;
    stride ← area + area; stride ← stride + six;
    temp ← size * size; srcLeft ← temp + temp; srcLeft ← srcLeft + temp;
    srcRight ← srcLeft + temp; srcLeft ← srcRight + temp; addr ← #5;
    srcLeft ← srcLeft + addr; srcRight ← srcRight + addr ]

/-- Compute the chunk and piece ordinals, then load the real query reference and piece bounds. -/
@[expose]
def select : Code .standard 64 := ram[
  chunkIndex ← produced / pieces; pieceIndex ← produced % pieces;
  addr ← chunkIndex * three; addr ← addr + descriptors; rho ← *addr;
  addr ← addr + one; queries ← *addr; addr ← addr + one; queryCount ← *addr;
  first ← pieceIndex * pieceLength; length ← size - first;
  if pieceLength < length then [ length ← pieceLength ] else [ length ← length ] ]

/-- Deliver every actual pointer, coordinate and count to the existing instance-pair ABI. -/
@[expose]
def deliver : Code .standard 64 :=
  let pairLeft : Fin 64 := 17
  let pairRight : Fin 64 := 18
  let pairBase : Fin 64 := 19
  let pairSize : Fin 64 := 20
  let pairDimension : Fin 64 := 21
  let pairModulus : Fin 64 := 22
  let pairFirst : Fin 64 := 23
  let pairLength : Fin 64 := 24
  let pairRho : Fin 64 := 25
  let pairQueries : Fin 64 := 26
  let pairCount : Fin 64 := 27
  let pairPiece : Fin 64 := 28
  ram[ pairLeft ← srcLeft; pairRight ← srcRight; pairBase ← heap; pairSize ← size;
    pairDimension ← dimension; pairModulus ← modulus; pairFirst ← first; pairLength ← length;
    pairRho ← rho; pairQueries ← queries; pairCount ← queryCount; pairPiece ← pieceIndex ]

/-- Existing native record and matrix-pair writer. -/
@[expose]
def pair : Code .standard 64 := InstancePair.program.rename (Fin.castLE (by decide))

/-- Advance only after the complete pair has been written. -/
@[expose]
def advance : Code .standard 64 := ram[ heap ← heap + stride; produced ← produced + one ]

/-- One actual instance; every selection, argument-delivery and matrix instruction is native. -/
@[expose]
def visit : Code .standard 64 := .seq select (.seq deliver (.seq pair advance))

/-- Prepare every actual chunk/piece pair after computing the catalogue. -/
@[expose]
def program : Code .standard 64 :=
  .seq catalogue (.seq setup (.loop (.lt produced total) visit))

/-- The catalogue prefix, twenty-six setup instructions, each `40nD+66` visit and its two loop
instructions, the two loop-exit instructions and the final halt are accounted separately. -/
@[expose]
def timeBound (n D p K H : ℕ) : ℕ :=
  Catalogue.cost n D p + K * H * (40 * (n * D) + 68) + 29

/-- Original-header bound for all arithmetic and allocated addresses. The conservative maximum
`p*n²` chunk count and `n` pieces cover every actual catalogue entry. Signed weights have their
separate magnitude fit premise; no layout information is supplied by the caller. -/
@[expose]
def budget (n D g p : ℕ) : ℕ :=
  let N := n * n
  let K := p * N
  let out := 5 + 6 * N + p + 2 * N * p + 3 * K
  Catalogue.budget n D g p + 2 * out + (K * n) * (6 + 2 * (n * D)) +
    20 * N + 3 * p + 4 * n + 2 * (n * D) + K * n + 64

private theorem parameter_bounds {n D g : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n)
    (hg : 1 ≤ g) :
    0 < pieceSize D g ∧ pieceSize D g ≤ n ∧
      0 < numPieces n D g ∧ numPieces n D g ≤ n ∧
      ∀ j < numPieces n D g, j * pieceSize D g ≤ n := by
  have hs : 0 < sOf D := Nat.sqrt_pos.mpr hD
  have hc : sOf D ≤ pieceSize D g * g := Nat.le_ceilDiv_mul (by omega : 0 < g)
  have hB : 0 < pieceSize D g := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.zero_mul] at hc
    omega
  have hBn : pieceSize D g ≤ n :=
    (pieceSize_le_sOf hg).trans ((Nat.sqrt_le_self D).trans hDn)
  have hcover : n ≤ numPieces n D g * pieceSize D g := Nat.le_ceilDiv_mul hB
  have hH : 0 < numPieces n D g := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.zero_mul] at hcover
    omega
  have hHn : numPieces n D g ≤ n :=
    (Nat.ceilDiv_le_iff hB).mpr (Nat.le_mul_of_pos_right n hB)
  refine ⟨hB, hBn, hH, hHn, fun j hj => ?_⟩
  have hover : numPieces n D g * pieceSize D g < n + pieceSize D g := Nat.ceilDiv_mul_lt hB
  have hstep := Nat.mul_le_mul_right (pieceSize D g) (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at hstep
  omega

/-- One bounded instruction graph with no word-size reads. -/
theorem program_fixed : program.size ≤ 640 ∧ ¬program.ReadsWidth :=
  ⟨by decide +kernel, Code.not_readsWidth_of_readsWidthBool rfl⟩

private theorem select_preserves : ∀ i : Fin 64, i.val < 50 → select.Preserves i :=
  Code.preserves_of_preservesAllPred (by decide +kernel)

/-- One instance visit preserves metadata except its heap and logical progress counters. -/
theorem visit_preserves : ∀ i : Fin 64,
    (32 ≤ i.val ∧ i.val < 50 ∧ i ≠ heap ∧ i ≠ produced) → visit.Preserves i :=
  Code.preserves_of_preservesAllPred (by decide +kernel)

private abbrev pairBank : Fin 32 → Fin 64 := Fin.castLE (by decide)

private theorem budget_covers_setup {n D g p K H : ℕ}
    (hK : K ≤ p * (n * n)) (hH : H ≤ n) :
    5 * (n * n) + 2 * (n * D) + K * H +
      (5 + 6 * (n * n) + p + 2 * (n * n) * p + 3 * K) + 8 ≤ budget n D g p := by
  have hT := Nat.mul_le_mul hK hH
  dsimp only [budget]
  omega

/-- The original input budget covers every visit using the actual chunk and piece bounds. -/
theorem budget_covers_loop {n D g p K H B : ℕ}
    (hK : K ≤ p * (n * n)) (hH : H ≤ n) (hHB : H * B ≤ n * n) :
    2 * (5 + 6 * (n * n) + p + 2 * (n * n) * p + 3 * K) +
      K * H * (6 + 2 * (n * D)) + 11 * (n * n) + 2 * p + n + H + H * B + K * H + 26 ≤
        budget n D g p := by
  have hT := Nat.mul_le_mul hK hH
  have hTS := Nat.mul_le_mul_right (6 + 2 * (n * D)) hT
  dsimp only [budget]
  omega

/-- Execute the shared catalogue-to-instance setup, charging all twenty-six instructions. -/
private theorem exec_setup {w : ℕ} (x : Data 64) (n D p B H K desc out : ℕ)
    (hn : x.regs 16 = n) (hp : x.regs 17 = p) (hB : x.regs 28 = B)
    (hH : x.regs 29 = H) (hK : x.regs 21 = K) (hd : x.regs 18 = desc)
    (hout : x.regs 22 = out) (hD : x.mem 1 = D)
    (hfit : Fits w (5 * (n * n) + 2 * (n * D) + K * H + out + 8)) :
    ∃ y, ExecWithin w setup x y 26 ∧ y.mem = x.mem ∧
      y.regs size = n ∧ y.regs dimension = D ∧ y.regs modulus = p ∧
      y.regs pieceLength = B ∧ y.regs pieces = H ∧ y.regs chunks = K ∧
      y.regs descriptors = desc ∧ y.regs output = out ∧ y.regs produced = 0 ∧
      y.regs total = K * H ∧ y.regs heap = out ∧ y.regs stride = 6 + 2 * (n * D) ∧
      y.regs one = 1 ∧ y.regs three = 3 ∧
      y.regs srcLeft = 5 + 5 * (n * n) ∧ y.regs srcRight = 5 + 4 * (n * n) := by
  wram_exec [setup, hn, hp, hB, hH, hK, hd, hout, hD]
  wram_simp
  refine ⟨by omega, by omega, by omega⟩

private theorem pairBank_injective : Function.Injective pairBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 64 => k.val) h)

/-- Specification of the delivered metadata, not a runtime layout input. Scratch registers
are irrelevant: the pair arguments and record words read only registers 17–28. -/
@[expose] def pairInput (x : Data 64) : Data 32 where
  regs i := match i.val with
    | 17 => x.regs srcLeft
    | 18 => x.regs srcRight
    | 19 => x.regs heap
    | 20 => x.regs size
    | 21 => x.regs dimension
    | 22 => x.regs modulus
    | 23 => (x.regs produced % x.regs pieces) * x.regs pieceLength
    | 24 => min (x.regs pieceLength)
        (x.regs size - (x.regs produced % x.regs pieces) * x.regs pieceLength)
    | 25 => x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors)
    | 26 => x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 1)
    | 27 => x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 2)
    | 28 => x.regs produced % x.regs pieces
    | _ => 0
  mem := x.mem

private def atInstance (x : Data 64) (i : ℕ) : Data 64 :=
  x.set produced i |>.set heap (x.regs output + i * x.regs stride)

private def Written (x : Data 64) (L R : ℕ → ℕ) (y : Data 64) (i : ℕ) : Prop :=
  let B := pairInput (atInstance x i)
  let M := x.regs size * x.regs dimension
  (Block.mk (x.regs output + i * x.regs stride) 6).Realizes y.mem (InstancePair.recordWords B) ∧
    (Block.mk (InstancePair.leftArgs B).dst M).Realizes y.mem
      (fun j => WriteMatrices.entry false (InstancePair.leftArgs B) L j) ∧
    (Block.mk (InstancePair.rightArgs B).dst M).Realizes y.mem
      (fun j => WriteMatrices.entry true (InstancePair.rightArgs B) R j)

private theorem pairInput_regs_congr (x y : Data 64)
    (hmeta : ∀ i : Fin 64, 32 ≤ i.val → i.val < 50 → y.regs i = x.regs i)
    (hH : 0 < x.regs pieces) (hi : x.regs produced < x.regs chunks * x.regs pieces)
    (hdir : x.regs descriptors + 3 * x.regs chunks ≤ x.regs output)
    (hmem : ∀ a < x.regs output, y.mem a = x.mem a) :
    (pairInput y).regs = (pairInput x).regs := by
  have hk : x.regs produced / x.regs pieces < x.regs chunks :=
    (Nat.div_lt_iff_lt_mul hH).mpr hi
  have hm0 := hmem (x.regs produced / x.regs pieces * 3 + x.regs descriptors) (by omega)
  have hm1 := hmem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 1) (by omega)
  have hm2 := hmem (x.regs produced / x.regs pieces * 3 + x.regs descriptors + 2) (by omega)
  funext i
  dsimp only [pairInput]
  rw [hmeta srcLeft (by decide) (by decide), hmeta srcRight (by decide) (by decide),
    hmeta heap (by decide) (by decide), hmeta size (by decide) (by decide),
    hmeta dimension (by decide) (by decide), hmeta modulus (by decide) (by decide),
    hmeta produced (by decide) (by decide), hmeta pieces (by decide) (by decide),
    hmeta pieceLength (by decide) (by decide), hmeta descriptors (by decide) (by decide),
    hm0, hm1, hm2]

private theorem exec_select {w : ℕ} (x : Data 64)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hH : 0 < x.regs pieces)
    (hi : x.regs produced < x.regs chunks * x.regs pieces)
    (hfit : Fits w (x.regs descriptors + 3 * x.regs chunks + x.regs size + x.regs pieces +
      x.regs pieces * x.regs pieceLength + 3)) :
    let k := x.regs produced / x.regs pieces
    let j := x.regs produced % x.regs pieces
    ∃ y, ExecWithin w select x y 14 ∧
      y.regs chunkIndex = k ∧ y.regs pieceIndex = j ∧
      y.regs rho = x.mem (k * 3 + x.regs descriptors) ∧
      y.regs queries = x.mem (k * 3 + x.regs descriptors + 1) ∧
      y.regs queryCount = x.mem (k * 3 + x.regs descriptors + 2) ∧
      y.regs first = j * x.regs pieceLength ∧
      y.regs length = min (x.regs pieceLength) (x.regs size - j * x.regs pieceLength) ∧
      y.mem = x.mem := by
  have hk : x.regs produced / x.regs pieces < x.regs chunks :=
    (Nat.div_lt_iff_lt_mul hH).mpr hi
  have hj : x.regs produced % x.regs pieces < x.regs pieces := Nat.mod_lt _ hH
  have hfirst : x.regs produced % x.regs pieces * x.regs pieceLength ≤
      x.regs pieces * x.regs pieceLength := Nat.mul_le_mul_right _ hj.le
  wram_exec [select, ho, ht]
  · wram_simp
    omega
  · wram_simp
    omega

/-- Execute one logical chunk/piece at the current heap pointer. Previous records and dirty
scratch outside its destination span are unrestricted. All native argument delivery and both
matrix calls are included in the charge. -/
theorem exec_visit {w : ℕ} (x : Data 64) (L R : ℕ → ℕ)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hH : 0 < x.regs pieces)
    (hi : x.regs produced < x.regs chunks * x.regs pieces)
    (hstride : x.regs stride = 6 + 2 * (x.regs size * x.regs dimension))
    (hstart : (x.regs produced % x.regs pieces) * x.regs pieceLength ≤ x.regs size)
    (hrho : x.mem (x.regs produced / x.regs pieces * 3 + x.regs descriptors) < x.regs modulus)
    (hL : ∀ i < x.regs size * x.regs size, L i < x.regs modulus)
    (hR : ∀ i < x.regs size * x.regs size, R i < x.regs modulus)
    (hleft : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcLeft + i) = L i)
    (hright : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcRight + i) = R i)
    (hsL : x.regs srcLeft + x.regs size * x.regs size ≤ x.regs heap)
    (hsR : x.regs srcRight + x.regs size * x.regs size ≤ x.regs heap)
    (hfit : Fits w (x.regs heap + x.regs stride + x.regs srcLeft + x.regs srcRight +
      2 * (x.regs size * x.regs size) + 2 * x.regs modulus + x.regs descriptors +
        3 * x.regs chunks + x.regs size + x.regs pieces +
          x.regs pieces * x.regs pieceLength + x.regs produced + 16)) :
    let B := pairInput x
    let M := x.regs size * x.regs dimension
    ∃ y, ExecWithin w visit x y (40 * M + 66) ∧
      y.regs produced = x.regs produced + 1 ∧ y.regs heap = x.regs heap + x.regs stride ∧
      (Block.mk (x.regs heap) 6).Realizes y.mem (InstancePair.recordWords B) ∧
      (Block.mk (InstancePair.leftArgs B).dst M).Realizes y.mem
        (fun i => WriteMatrices.entry false (InstancePair.leftArgs B) L i) ∧
      (Block.mk (InstancePair.rightArgs B).dst M).Realizes y.mem
        (fun i => WriteMatrices.entry true (InstancePair.rightArgs B) R i) ∧
      (∀ a, ¬(x.regs heap ≤ a ∧ a < x.regs heap + x.regs stride) → y.mem a = x.mem a) := by
  let B := pairInput x
  let M := x.regs size * x.regs dimension
  obtain ⟨a, ha, -, haj, harho, haq, hacount, hafirst, halen, hamem⟩ :=
    exec_select x ho ht hH hi (hfit.of_le (by omega))
  have hameta (i : Fin 64) (hi : i.val < 50) : a.regs i = x.regs i :=
    ha.regs_eq (select_preserves i hi)
  refine (?_ : ∃ y, ExecWithin w (.seq deliver (.seq pair advance)) a y (40 * M + 52) ∧ _).imp
    fun y ⟨hy, hres⟩ => ⟨(ha.seq hy).mono (by omega), hres⟩
  wram_exec (disch := first | fits | decide | omega)
    [deliver, pair, hameta, harho, haq, hacount, hafirst, halen, haj]
  wram_call (InstancePair.exec _ L R
    (by wram_simp [InstancePair.rho, InstancePair.modulus]; exact hrho)
    (by wram_simp [InstancePair.first, InstancePair.length, InstancePair.size]
        have := min_le_right (x.regs pieceLength)
          (x.regs size - x.regs produced % x.regs pieces * x.regs pieceLength)
        omega)
    (by wram_simp [InstancePair.size, InstancePair.modulus]; exact hL)
    (by wram_simp [InstancePair.size, InstancePair.modulus]; exact hR)
    (by intro i hi
        wram_simp [InstancePair.srcLeft, InstancePair.size] at hi ⊢
        exact hamem ▸ hleft i hi)
    (by intro i hi
        wram_simp [InstancePair.srcRight, InstancePair.size] at hi ⊢
        exact hamem ▸ hright i hi)
    (by wram_simp [InstancePair.srcLeft, InstancePair.size, InstancePair.base]; exact hsL)
    (by wram_simp [InstancePair.srcRight, InstancePair.size, InstancePair.base]; exact hsR)
    (by wram_simp [InstancePair.base, InstancePair.size, InstancePair.dimension,
          InstancePair.srcLeft, InstancePair.srcRight, InstancePair.modulus]
        exact hfit.of_le (by rw [hstride]; omega)))
    canonical pairBank_injective with v ⟨hrecord, hmatL, hmatR, hframe⟩
  wram_exec (disch := first | fits | decide | omega) [advance, hameta, ho]
  wram_simp [InstancePair.size, InstancePair.dimension]
  wram_simp [pairBank, InstancePair.recordWords, InstancePair.rightArgs, InstancePair.leftArgs,
    InstancePair.base, InstancePair.srcLeft, InstancePair.srcRight, InstancePair.size,
    InstancePair.dimension, InstancePair.modulus, InstancePair.first, InstancePair.length,
    InstancePair.rho, InstancePair.queries, InstancePair.count, InstancePair.piece, B,
    pairInput] at hrecord hmatL hmatR
  refine ⟨hrecord, hmatL, hmatR, fun j hj => ?_⟩
  rw [hframe j (by
    wram_simp [pairBank, InstancePair.base, InstancePair.size, InstancePair.dimension]
    rw [hstride] at hj; omega)]
  exact congrFun hamem j

private theorem exec_loop {w : ℕ} (x : Data 64) (L R : ℕ → ℕ)
    (hzero : x.regs produced = 0) (hheap : x.regs heap = x.regs output)
    (htotal : x.regs total = x.regs chunks * x.regs pieces)
    (ho : x.regs one = 1) (ht : x.regs three = 3) (hH : 0 < x.regs pieces)
    (hstride : x.regs stride = 6 + 2 * (x.regs size * x.regs dimension))
    (hstart : ∀ j < x.regs pieces, j * x.regs pieceLength ≤ x.regs size)
    (hdir : x.regs descriptors + 3 * x.regs chunks ≤ x.regs output)
    (hrho : ∀ k < x.regs chunks, x.mem (k * 3 + x.regs descriptors) < x.regs modulus)
    (hL : ∀ i < x.regs size * x.regs size, L i < x.regs modulus)
    (hR : ∀ i < x.regs size * x.regs size, R i < x.regs modulus)
    (hleft : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcLeft + i) = L i)
    (hright : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcRight + i) = R i)
    (hsL : x.regs srcLeft + x.regs size * x.regs size ≤ x.regs output)
    (hsR : x.regs srcRight + x.regs size * x.regs size ≤ x.regs output)
    (hfit : Fits w (x.regs output + x.regs total * x.regs stride + x.regs srcLeft +
      x.regs srcRight + 2 * (x.regs size * x.regs size) + 2 * x.regs modulus +
        x.regs descriptors + 3 * x.regs chunks + x.regs size + x.regs pieces +
          x.regs pieces * x.regs pieceLength + x.regs total + 16)) :
    ∃ y, ExecWithin w (.loop (.lt produced total) visit) x y
        (x.regs total * (40 * (x.regs size * x.regs dimension) + 68) + 2) ∧
      y.regs produced = x.regs total ∧
      y.regs heap = x.regs output + x.regs total * x.regs stride ∧
      (∀ i < x.regs total, Written x L R y i) ∧
      (∀ a, ¬(x.regs output ≤ a ∧ a < y.regs heap) → y.mem a = x.mem a) := by
  let M := x.regs size * x.regs dimension
  let T := x.regs total
  let I (y : Data 64) : Prop :=
    (∀ i : Fin 64, 32 ≤ i.val → i.val < 50 → i ≠ produced → i ≠ heap →
      y.regs i = x.regs i) ∧
      y.regs produced ≤ T ∧
      y.regs heap = x.regs output + y.regs produced * x.regs stride ∧
      (∀ j < y.regs produced, Written x L R y j) ∧
      (∀ a, ¬(x.regs output ≤ a ∧ a < y.regs heap) → y.mem a = x.mem a)
  have hbody (y : Data 64) (hy : I y) (hc : (Cond.lt produced total).Holds y) :
      ∃ z, ExecWithin w visit y z (40 * M + 66) ∧ I z ∧
        T - z.regs produced < T - y.regs produced := by
    obtain ⟨hyr, hyi, hyheap, hywritten, hyframe⟩ := hy
    have hreg (i : Fin 64)
        (hi : 32 ≤ i.val ∧ i.val < 50 ∧ i ≠ produced ∧ i ≠ heap := by decide) :
        y.regs i = x.regs i := hyr i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hlt : y.regs produced < T := by simpa only [Cond.holds_lt, hreg total] using hc
    have hi : y.regs produced < x.regs chunks * x.regs pieces := by simpa only [T, htotal] using hlt
    have hk : y.regs produced / x.regs pieces < x.regs chunks := (Nat.div_lt_iff_lt_mul hH).mpr hi
    have hstep : y.regs produced * x.regs stride + x.regs stride ≤ T * x.regs stride := by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (x.regs stride) (Nat.succ_le_of_lt hlt)
    have hreadonly (a : ℕ) (ha : a < x.regs output) : y.mem a = x.mem a := hyframe a (by omega)
    obtain ⟨z, hz, hzi, hzh, hzrecord, hzL, hzR, hzframe⟩ := exec_visit y L R
      ((hreg one).trans ho) ((hreg three).trans ht) (by simpa only [hreg pieces] using hH)
      (by simpa only [hreg chunks, hreg pieces] using hi)
      (by simpa only [hreg stride, hreg size, hreg dimension] using hstride)
      (by rw [hreg pieces, hreg pieceLength, hreg size]; exact hstart _ (Nat.mod_lt _ hH))
      (by rw [hreg pieces, hreg descriptors, hreg modulus, hreadonly _ (by omega)]; exact hrho _ hk)
      (by simpa only [hreg size, hreg modulus] using hL)
      (by simpa only [hreg size, hreg modulus] using hR)
      (by intro i hi
          rw [hreg size] at hi; rw [hreg srcLeft, hreadonly _ (by omega)]; exact hleft i hi)
      (by intro i hi
          rw [hreg size] at hi; rw [hreg srcRight, hreadonly _ (by omega)]; exact hright i hi)
      (by rw [hreg srcLeft, hreg size, hyheap]; omega)
      (by rw [hreg srcRight, hreg size, hyheap]; omega)
      (hfit.of_le (by
        rw [hyheap, hreg stride, hreg srcLeft, hreg srcRight, hreg size, hreg modulus,
          hreg descriptors, hreg chunks, hreg pieces, hreg pieceLength]
        dsimp only [T] at hstep hyi; omega))
    rw [hreg size, hreg dimension] at hz
    rw [hreg stride] at hzh hzframe
    let old := atInstance x (y.regs produced)
    have hmeta (i : Fin 64) (hi : 32 ≤ i.val) (hi' : i.val < 50) : y.regs i = old.regs i := by
      rcases eq_or_ne i produced with rfl | hp
      · simp only [old, atInstance, Data.set_regs_of_ne (by decide : produced ≠ heap),
          Data.set_regs_self]
      · rcases eq_or_ne i heap with rfl | hh
        · simpa only [old, atInstance, Data.set_regs_self] using hyheap
        · simpa only [old, atInstance, Data.set_regs, Function.update_of_ne hh,
            Function.update_of_ne hp] using hyr i hi hi' hp hh
    have hinputRegs : (pairInput y).regs = (pairInput old).regs :=
      pairInput_regs_congr old y hmeta (by wram_simp [old, atInstance]; exact hH)
        (by wram_simp [old, atInstance]; exact hi) (by wram_simp [old, atInstance]; exact hdir)
        (by wram_simp [old, atInstance]; exact hreadonly)
    rw [show InstancePair.recordWords (pairInput y) = InstancePair.recordWords (pairInput old) by
      unfold InstancePair.recordWords InstancePair.leftArgs InstancePair.rightArgs; rw [hinputRegs],
      hyheap] at hzrecord
    rw [show InstancePair.leftArgs (pairInput y) = InstancePair.leftArgs (pairInput old) by
      unfold InstancePair.leftArgs; rw [hinputRegs], hreg size, hreg dimension] at hzL
    rw [show InstancePair.rightArgs (pairInput y) = InstancePair.rightArgs (pairInput old) by
      unfold InstancePair.rightArgs InstancePair.leftArgs; rw [hinputRegs], hreg size,
      hreg dimension] at hzR
    refine ⟨z, hz, ⟨fun i hi hi' hp hh =>
        (hz.regs_eq (visit_preserves i ⟨hi, hi', hh, hp⟩)).trans (hyr i hi hi' hp hh),
      by omega, by rw [hzh, hyheap, hzi, Nat.add_mul, Nat.one_mul]; omega, ?_,
      fun a ha => by rw [hzh] at ha; rw [hzframe a (by omega), hyframe a (by omega)]⟩, by omega⟩
    intro j hj; rw [hzi] at hj
    rcases eq_or_ne j (y.regs produced) with rfl | hji
    · exact ⟨hzrecord, hzL, hzR⟩
    · have hjlt : j < y.regs produced := by omega
      obtain ⟨hjrecord, hjL, hjR⟩ := hywritten j hjlt
      have hprev : j * x.regs stride + x.regs stride ≤ y.regs produced * x.regs stride := by
        simpa only [Nat.succ_mul] using
          Nat.mul_le_mul_right (x.regs stride) (Nat.succ_le_of_lt hjlt)
      have hrealize {base len : ℕ} {f : Fin len → ℕ} (h : (Block.mk base len).Realizes y.mem f)
          (hle : base + len ≤ y.regs heap) : (Block.mk base len).Realizes z.mem f :=
        fun a => (hzframe _ (by have : a.val < len := a.isLt; dsimp only; omega)).trans (h a)
      exact ⟨hrealize hjrecord (by rw [hyheap]; omega),
        hrealize hjL (by
          change x.regs output + j * x.regs stride + 6 + M ≤ y.regs heap
          rw [hyheap]; dsimp [M]; omega),
        hrealize hjR (by
          change x.regs output + j * x.regs stride + 6 + M + M ≤ y.regs heap
          rw [hyheap]; dsimp [M]; omega)⟩
  have hx : I x := ⟨fun _ _ _ _ _ => rfl, by omega,
    by rw [hzero, Nat.zero_mul, Nat.add_zero]; exact hheap, fun _ hj => by omega, fun _ _ => rfl⟩
  obtain ⟨y, hy, ⟨hmeta, hcount, hheap', hwritten, hframe⟩, hend⟩ :=
    ExecWithin.loop_invariant I (fun y => T - y.regs produced) hbody hx
  have hyT : y.regs total = T := hmeta total (by decide) (by decide) (by decide) (by decide)
  have hfinal : y.regs produced = T := by simp only [Cond.holds_lt, hyT] at hend; omega
  exact ⟨y, by simpa only [hzero, Nat.sub_zero] using hy, hfinal,
    by simpa only [hfinal] using hheap', by simpa only [hfinal] using hwritten, hframe⟩

private theorem written_readback {n D p B H K desc out i : ℕ}
    (b y : Data 64) (L R : ℕ → ℕ) (hH : 0 < H) (hi : i < K * H)
    (hmeta : b.regs size = n ∧ b.regs dimension = D ∧ b.regs modulus = p ∧
      b.regs pieceLength = B ∧ b.regs pieces = H ∧ b.regs descriptors = desc ∧
      b.regs output = out ∧ b.regs stride = 6 + 2 * (n * D) ∧
      b.regs srcLeft = 5 + 5 * (n * n) ∧ b.regs srcRight = 5 + 4 * (n * n))
    (hdirBound : desc + 3 * K ≤ out)
    (hframe : ∀ q < out, y.mem q = b.mem q) (hwritten : Written b L R y i) :
    let base := out + i * (6 + 2 * (n * D))
    let A : WriteMatrices.Args :=
      ⟨5 + 5 * (n * n), base + 6, n, D, p, i % H * B, min B (n - i % H * B),
        y.mem (desc + 3 * (i / H))⟩
    let A' := { A with src := 5 + 4 * (n * n), dst := base + 6 + n * D }
    (Block.mk base 6).Realizes y.mem
      ![A.rho, i % H, y.mem (desc + 3 * (i / H) + 1),
        y.mem (desc + 3 * (i / H) + 2), base + 6, base + 6 + n * D] ∧
      (Block.mk A.dst (n * D)).Realizes y.mem (fun j => WriteMatrices.entry false A L j) ∧
      (Block.mk A'.dst (n * D)).Realizes y.mem (fun j => WriteMatrices.entry true A' R j) := by
  obtain ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩ := hmeta
  let N := n * n
  let S := 6 + 2 * (n * D)
  let base := out + i * S
  let A : WriteMatrices.Args :=
    ⟨5 + 5 * N, base + 6, n, D, p, i % H * B, min B (n - i % H * B),
      y.mem (desc + 3 * (i / H))⟩
  let A' := { A with src := 5 + 4 * N, dst := base + 6 + n * D }
  have hk : i / H < K := (Nat.div_lt_iff_lt_mul hH).mpr hi
  have hdir (t : ℕ) (ht : t < 3) :
      b.mem (i / H * 3 + desc + t) = y.mem (desc + 3 * (i / H) + t) := by
    rw [show i / H * 3 + desc + t = desc + 3 * (i / H) + t by omega]
    exact (hframe _ (by omega)).symm
  have hd0 : b.mem (i / H * 3 + desc) = y.mem (desc + 3 * (i / H)) := by
    simpa only [Nat.add_zero] using hdir 0 (by decide)
  have hd1 := hdir 1 (by decide)
  have hd2 := hdir 2 (by decide)
  have hargsL : InstancePair.leftArgs (pairInput (atInstance b i)) = A := by
    wram_simp [InstancePair.leftArgs, pairInput, atInstance, A, base, N, S,
      hbn, hbD, hbp, hbH, hbB, hbL, hbo, hbs, hbd, hd0,
      InstancePair.srcLeft, InstancePair.base, InstancePair.size, InstancePair.dimension,
      InstancePair.modulus, InstancePair.first, InstancePair.length, InstancePair.rho]
    rfl
  have hargsR : InstancePair.rightArgs (pairInput (atInstance b i)) = A' := by
    unfold InstancePair.rightArgs
    rw [hargsL]
    wram_simp [pairInput, atInstance, A', A, base, N, S,
      hbn, hbD, hbR, hbo, hbs, InstancePair.srcRight, InstancePair.base,
      InstancePair.size, InstancePair.dimension]
    rfl
  have hwords : InstancePair.recordWords (pairInput (atInstance b i)) =
      ![A.rho, i % H, y.mem (desc + 3 * (i / H) + 1),
        y.mem (desc + 3 * (i / H) + 2), base + 6, base + 6 + n * D] := by
    rw [InstancePair.recordWords, hargsL, hargsR]
    wram_simp [pairInput, atInstance, A, A', base, hbH, hbd, hd0, hd1, hd2,
      InstancePair.rho, InstancePair.piece, InstancePair.queries, InstancePair.count]
    rfl
  obtain ⟨hr, hL, hR⟩ := hwritten
  dsimp only at hr hL hR
  rw [hbo, hbs, hwords] at hr
  rw [hargsL, hbn, hbD] at hL
  rw [hargsR, hbn, hbD] at hR
  exact ⟨hr, hL, hR⟩

/-- Exact computed catalogue, record and raw zero/one matrix readback, with the complete
input/output frame. The matrix predicates reuse the existing writer arguments and entry
semantics. -/
@[expose]
def Output (n D g p : ℕ) (values : ℕ → ℤ) (initial y : Data 64) : Prop :=
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let K := ChunkCatalogue.before C (queryCap n D) p
    let H := numPieces n D g
    let B := pieceSize D g
    let desc := 5 + 6 * N + p + 2 * N * p
    let out := desc + 3 * K
    y.regs size = n ∧ y.regs dimension = D ∧ y.regs modulus = p ∧
    y.regs output = out ∧ y.regs produced = K * H ∧
    y.regs heap = out + (K * H) * (6 + 2 * (n * D)) ∧
    (∀ q < 3 * N, y.mem (5 + 3 * N + q) = R q) ∧
    (∀ rho < p, y.mem (5 + 6 * N + rho) = C rho) ∧
    (∀ rho < p, ∀ q < N, R q = rho →
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q) = q / n ∧
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1) = q % n) ∧
    (∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
      y.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
      y.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
        5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
      y.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
        min (queryCap n D) (C rho - k * queryCap n D)) ∧
    (∀ i < K * H,
      let base := out + i * (6 + 2 * (n * D))
      let residue := y.mem (desc + 3 * (i / H))
      let A : WriteMatrices.Args :=
        ⟨5 + 5 * N, base + 6, n, D, p, i % H * B, min B (n - i % H * B), residue⟩
      let A' := { A with src := 5 + 4 * N, dst := base + 6 + n * D }
      (Block.mk base 6).Realizes y.mem
        ![residue, i % H, y.mem (desc + 3 * (i / H) + 1),
          y.mem (desc + 3 * (i / H) + 2), base + 6, base + 6 + n * D] ∧
        (Block.mk A.dst (n * D)).Realizes y.mem
          (fun j => WriteMatrices.entry false A (fun q => R (2 * N + q)) j) ∧
        (Block.mk A'.dst (n * D)).Realizes y.mem
          (fun j => WriteMatrices.entry true A' (fun q => R (N + q)) j)) ∧
    (∀ a, a < 5 + 3 * N ∨ out + (K * H) * (6 + 2 * (n * D)) ≤ a →
      y.mem a = initial.mem a)

private theorem output_of_loop {n D g p : ℕ} (values : ℕ → ℤ)
    (initial : Data 64) (v : Data 32) (b y : Data 64)
    (hcat : Catalogue.Output n D g p values (initial.comap pairBank) v)
    (hbmem : b.mem = v.mem)
    (hmeta :
      let N := n * n
      let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) N
      let K := ChunkCatalogue.before C (queryCap n D) p
      let H := numPieces n D g
      let B := pieceSize D g
      let desc := 5 + 6 * N + p + 2 * N * p
      let out := desc + 3 * K
      b.regs size = n ∧ b.regs dimension = D ∧ b.regs modulus = p ∧
        b.regs pieceLength = B ∧ b.regs pieces = H ∧ b.regs descriptors = desc ∧
        b.regs output = out ∧ b.regs stride = 6 + 2 * (n * D) ∧
        b.regs srcLeft = 5 + 5 * N ∧ b.regs srcRight = 5 + 4 * N)
    (hY : y.regs size = n ∧ y.regs dimension = D ∧ y.regs modulus = p ∧
      y.regs output = b.regs output)
    (hycount : y.regs produced =
      ChunkCatalogue.before (fun rho => Nat.count
        (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)) (queryCap n D) p * numPieces n D g)
    (hyheap : y.regs heap = b.regs output + y.regs produced * b.regs stride)
    (hH : 0 < numPieces n D g)
    (hywritten : ∀ i < y.regs produced,
      Written b (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat)
        (fun q => (values (n * n + q) % (p : ℤ)).toNat) y i)
    (hyframe : ∀ q, ¬(b.regs output ≤ q ∧ q < y.regs heap) → y.mem q = b.mem q) :
    Output n D g p values initial y := by
  let N := n * n
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let B := pieceSize D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  let S := 6 + 2 * (n * D)
  obtain ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩ := hmeta
  obtain ⟨hyn, hyD, hyp, hyo⟩ := hY
  change b.regs output = out at hbo
  obtain ⟨-, -, -, -, -, -, -, -, hvK, -, hvres, hvcounts, hvpairs, hvdesc, hvframe⟩ := hcat
  change v.regs ChunkCatalogue.written = K at hvK
  change y.regs produced = K * H at hycount
  rw [hbo, hycount, hbs] at hyheap
  rw [hycount] at hywritten
  have hbefore (q : ℕ) (hq : q < out) : y.mem q = v.mem q :=
    (hyframe q (by rw [hbo]; omega)).trans (congrFun hbmem q)
  refine ⟨hyn, hyD, hyp, hyo.trans hbo, hycount, hyheap,
    fun q hq => (hbefore _ (by dsimp only [out, desc, N] at hq ⊢; omega)).trans (hvres q hq),
    fun rho hrho => (hbefore _ (by dsimp only [out, desc]; omega)).trans (hvcounts rho hrho),
    ?_, ?_,
    fun i hi => written_readback (K := K) (desc := desc) (out := out) b y
      (fun q => R (2 * N + q)) (fun q => R (N + q)) hH hi
      ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩ (by dsimp only [out]; omega)
      (fun q hq => hyframe q (by rw [hbo]; omega)) (hywritten i hi),
    ?_⟩
  · intro rho hrho q hq hRq
    have hcount : Nat.count (fun k => R k = rho) q ≤ q := Nat.count_le _
    have hbound := Nat.mul_le_mul_left (2 * N) (Nat.succ_le_of_lt hrho)
    rw [Nat.mul_succ] at hbound
    have hread := hvpairs rho hrho q hq hRq
    have hm (t : ℕ) (ht : t ≤ 1) :=
      hbefore (5 + 6 * N + p + 2 * N * rho + 2 * Nat.count (fun k => R k = rho) q + t)
        (by dsimp only [out, desc, N] at hq hbound ⊢; omega)
    exact ⟨(hm 0 (by omega)).trans hread.1, (hm 1 (by omega)).trans hread.2⟩
  · intro rho hrho k hk
    have hindex := ChunkCatalogue.before_add_lt C (queryCap n D) hrho hk
    have hread := hvdesc rho hrho k hk
    have hm (t : ℕ) (ht : t < 3) :=
      hbefore (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + t)
        (by dsimp only [out, K] at hindex ⊢; omega)
    exact ⟨(hm 0 (by decide)).trans hread.1, (hm 1 (by decide)).trans hread.2.1,
      (hm 2 (by decide)).trans hread.2.2⟩
  · intro q hq
    rw [hyframe q (by
      rw [hbo, hyheap]; dsimp only [out, desc, K, H, C, R, S, N] at hq ⊢; omega), hbmem]
    refine hvframe q (hq.imp id fun h => ?_)
    rw [hvK]; dsimp only [out, desc, K, H, C, R, S, N] at h ⊢; omega

/-- Execute just the real catalogue and setup. The returned state is ready for logical
chunk/piece visits but contains no instance records. Its bound excludes any final halt. -/
private theorem exec_prefix {w : ℕ} (n D g p : ℕ) (values : ℕ → ℤ) (initial : Data 64)
    (hDHeader : initial.mem 1 = D) (hgHeader : initial.mem 2 = g)
    (hnHeader : initial.mem 3 = n) (hpHeader : initial.mem 4 = p)
    (hinput : ∀ q < 3 * (n * n), initial.mem (5 + q) = Signed.encode (values q))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (hbudget : Fits (w + 2) (budget n D g p)) :
    ∃ v : Data 32, Catalogue.Output n D g p values (initial.comap (Fin.castLE (by decide))) v ∧
      ∃ b : Data 64,
        ExecWithin (w + 2) (.seq catalogue setup) initial b (Catalogue.cost n D p + 26) ∧
        b.mem = v.mem ∧
        b.regs size = n ∧ b.regs dimension = D ∧ b.regs modulus = p ∧
        b.regs pieceLength = pieceSize D g ∧ b.regs pieces = numPieces n D g ∧
        b.regs chunks = ChunkCatalogue.before
          (fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n))
          (queryCap n D) p ∧
        b.regs descriptors = 5 + 6 * (n * n) + p + 2 * (n * n) * p ∧
        b.regs output = 5 + 6 * (n * n) + p + 2 * (n * n) * p + 3 * b.regs chunks ∧
        b.regs produced = 0 ∧ b.regs total = b.regs chunks * b.regs pieces ∧
        b.regs heap = b.regs output ∧ b.regs stride = 6 + 2 * (n * D) ∧
        b.regs one = 1 ∧ b.regs three = 3 ∧
        b.regs srcLeft = 5 + 5 * (n * n) ∧ b.regs srcRight = 5 + 4 * (n * n) := by
  let N := n * n
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  let C (rho : ℕ) := Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let B := pieceSize D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  obtain ⟨-, -, -, hHn, _⟩ := parameter_bounds hD hDn hg
  have hK : K ≤ p * N := ChunkCatalogue.before_le (one_le_queryCap hD hDn)
    (fun _ _ => Nat.count_le _) le_rfl
  obtain ⟨v, hv, hcatOriginal⟩ := Catalogue.exec_at n D g p values
    (initial.comap pairBank) hDHeader hgHeader hnHeader hpHeader hinput hD hDn hg hp
    hmod hvalues (hbudget.of_le (by dsimp only [budget]; omega))
  have hcatSave := hcatOriginal
  obtain ⟨hvn, hvp, -, -, hvd, -, hvB, hvH, hvK, hvheap, -, -, -, -, hvframe⟩ := hcatOriginal
  dsimp only at hvK hvheap
  let a := v.extend pairBank initial
  have ha : ExecWithin (w + 2) catalogue initial a (Catalogue.cost n D p) :=
    hv.rename pairBank_injective
  have haLow (i : Fin 32) : a.regs (pairBank i) = v.regs i :=
    pairBank_injective.extend_apply _ _ i
  obtain ⟨b, hb, hbmem, hbn, hbD, hbp, hbB, hbH, hbK, hbd, hbo, hbzero, hbt,
      hbh, hbs, hb1, hb3, hbL, hbR⟩ := exec_setup a n D p B H K desc out
    ((haLow ChunkCatalogue.size).trans hvn) ((haLow ChunkCatalogue.modulus).trans hvp)
    ((haLow Catalogue.pieceLength).trans hvB) ((haLow Catalogue.pieces).trans hvH)
    ((haLow ChunkCatalogue.written).trans hvK) ((haLow ChunkCatalogue.dst).trans hvd)
    (by change a.regs (pairBank ChunkCatalogue.heap) = out; rw [haLow, hvheap, hvK])
    ((hvframe 1 (Or.inl (by omega))).trans hDHeader)
    (hbudget.of_le (budget_covers_setup hK hHn))
  refine ⟨v, hcatSave, b, ha.seq hb, hbmem, hbn, hbD, hbp, hbB, hbH, hbK, hbd,
    ?_, hbzero, ?_, hbh.trans hbo.symm, hbs, hb1, hb3, hbL, hbR⟩
  · rw [hbo, hbK]
  · rw [hbt, hbK, hbH]

/-- Execute the complete preparation from the real header and signed matrices. Every output
record refers to the actual computed query chunk, followed by its raw zero/one matrix pair.
The only resource premises concern the original signed values and the explicit numeric budget;
neither a catalogue nor a layout or execution certificate is an input. The final halt is
excluded here and added by the initialized flat-program client. -/
theorem exec_at_with_prefix {w : ℕ} (n D g p : ℕ) (values : ℕ → ℤ) (initial : Data 64)
    (hDHeader : initial.mem 1 = D) (hgHeader : initial.mem 2 = g)
    (hnHeader : initial.mem 3 = n) (hpHeader : initial.mem 4 = p)
    (hinput : ∀ q < 3 * (n * n), initial.mem (5 + q) = Signed.encode (values q))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (hbudget : Fits (w + 2) (budget n D g p)) :
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let K := ChunkCatalogue.before C (queryCap n D) p
    let H := numPieces n D g
    ∃ y, ExecWithin (w + 2) program initial y (timeBound n D p K H - 1) ∧
      Output n D g p values initial y ∧
      ∃ b : Data 64,
        ExecWithin (w + 2) (.seq catalogue setup) initial b (Catalogue.cost n D p + 26) ∧
        b.regs size = n ∧ b.regs dimension = D ∧ b.regs modulus = p ∧
        b.regs pieceLength = pieceSize D g ∧ b.regs pieces = numPieces n D g ∧
        b.regs chunks = K ∧ b.regs descriptors = 5 + 6 * N + p + 2 * N * p ∧
        b.regs output = y.regs output ∧ b.regs produced = 0 ∧
        b.regs total = y.regs produced ∧ b.regs heap = b.regs output ∧
        b.regs stride = 6 + 2 * (n * D) ∧ b.regs one = 1 ∧ b.regs three = 3 ∧
        b.regs srcLeft = 5 + 5 * N ∧ b.regs srcRight = 5 + 4 * N ∧
        Set.EqOn b.mem y.mem (Set.Iio (b.regs output)) ∧
        (∀ u, u < 5 + 3 * N ∨ b.regs output ≤ u → b.mem u = initial.mem u) := by
  let N := n * n
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  let C (rho : ℕ) := Nat.count (fun q => R q = rho) N
  let K := ChunkCatalogue.before C (queryCap n D) p
  let H := numPieces n D g
  let B := pieceSize D g
  let desc := 5 + 6 * N + p + 2 * N * p
  let out := desc + 3 * K
  let S := 6 + 2 * (n * D)
  obtain ⟨-, hBn, hH, hHn, hstart⟩ := parameter_bounds hD hDn hg
  have hK : K ≤ p * N := ChunkCatalogue.before_le (one_le_queryCap hD hDn)
    (fun _ _ => Nat.count_le _) le_rfl
  have hHB : H * B ≤ N := Nat.mul_le_mul hHn hBn
  obtain ⟨v, hcatOriginal, b, hprefixExec, hbmem, hbn, hbD, hbp, hbB, hbH, hbK,
      hbd, hbo', hbzero, hbt', hbh', hbs, hb1, hb3, hbL, hbR⟩ :=
    exec_prefix n D g p values initial hDHeader hgHeader hnHeader hpHeader hinput
      hD hDn hg hp hmod hvalues hbudget
  have hbo : b.regs output = out := by rw [hbo', hbK]
  have hbt : b.regs total = K * H := by rw [hbt', hbK, hbH]
  have hbh : b.regs heap = out := hbh'.trans hbo
  have hcatSave := hcatOriginal
  obtain ⟨-, -, -, -, -, -, -, -, hvK, -, hvres, -, -, hvdesc, hvframe⟩ := hcatOriginal
  change ∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
    v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
      v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
        5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
      v.mem (desc + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
        min (queryCap n D) (C rho - k * queryCap n D) at hvdesc
  dsimp only at hvK hvres
  have hres (q : ℕ) : R q < p := Int.natMod_lt (by omega)
  have hmat (m : ℕ) (hm : m ≤ 2) (i : ℕ) (hi : i < N) :
      b.mem (5 + (3 + m) * N + i) = R (m * N + i) := by
    rw [hbmem, show 5 + (3 + m) * N + i = 5 + 3 * N + (m * N + i) by
      rw [Nat.add_mul]; omega]
    exact hvres _ (by
      have := Nat.mul_le_mul_right N hm
      omega)
  obtain ⟨y, hy, hycount, hyheap, hywritten, hyframe⟩ := exec_loop b
    (fun q => R (2 * N + q)) (fun q => R (N + q)) hbzero (hbh.trans hbo.symm)
    (by rw [hbt, hbK, hbH]) hb1 hb3 (by rw [hbH]; exact hH)
    (by rw [hbs, hbn, hbD])
    (by rw [hbH, hbB, hbn]; exact hstart)
    (by rw [hbd, hbK, hbo])
    (by
      rw [hbK, hbd, hbp]
      intro k hk
      obtain ⟨idx, hidx, -⟩ := ChunkCatalogue.before_index C (queryCap n D) p k hk
      rw [hbmem, show k * 3 + desc = desc + 3 * k by omega, hidx,
        (hvdesc idx.1.val idx.1.isLt idx.2.val idx.2.isLt).1]
      exact idx.1.isLt)
    (by rw [hbn, hbp]; exact fun q _ => hres (2 * N + q))
    (by rw [hbn, hbp]; exact fun q _ => hres (N + q))
    (by rw [hbL, hbn]; exact hmat 2 (by omega))
    (by rw [hbR, hbn]; simpa only [Nat.one_mul] using hmat 1 (by omega))
    (by rw [hbL, hbn, hbo]; dsimp [out, desc, N]; omega)
    (by rw [hbR, hbn, hbo]; dsimp [out, desc, N]; omega)
    (hbudget.of_le (by
      rw [hbo, hbt, hbs, hbL, hbR, hbn, hbp, hbd, hbK, hbH, hbB]
      change out + K * H * S + (5 + 5 * N) + (5 + 4 * N) + 2 * N + 2 * p +
        desc + 3 * K + n + H + H * B + K * H + 16 ≤ _
      calc
        _ = 2 * out + K * H * S + 11 * N + 2 * p + n + H + H * B + K * H + 26 := by
          dsimp only [out]
          ring
        _ ≤ _ := budget_covers_loop hK hHn hHB))
  rw [hbn, hbD, hbt] at hy
  rw [hbt] at hycount hywritten
  rw [hbo, hbt, hbs] at hyheap
  have hyreg (i : Fin 64)
      (hi : 32 ≤ i.val ∧ i.val < 50 ∧ i ≠ heap ∧ i ≠ produced := by decide) :
      y.regs i = b.regs i := hy.regs_eq (visit_preserves i hi)
  refine ⟨y, ?_, ?_, b, hprefixExec, hbn, hbD, hbp, hbB, hbH, hbK, hbd,
    (hyreg output).symm, hbzero, by rw [hbt, hycount], hbh'.trans rfl, hbs, hb1, hb3, hbL, hbR,
    fun q hq => (hyframe q (by change q < b.regs output at hq; omega)).symm, ?_⟩
  · apply ExecWithin.seq_assoc.mp ((hprefixExec.seq hy).mono ?_)
    change Catalogue.cost n D p + 26 + (K * H * (40 * (n * D) + 68) + 2) ≤
      Catalogue.cost n D p + K * H * (40 * (n * D) + 68) + 29 - 1
    omega
  · exact output_of_loop values initial v b y hcatSave hbmem
      ⟨hbn, hbD, hbp, hbB, hbH, hbd, hbo, hbs, hbL, hbR⟩
      ⟨(hyreg size).trans hbn, (hyreg dimension).trans hbD, (hyreg modulus).trans hbp,
        hyreg output⟩
      hycount (by rw [hbo, hycount, hbs]; exact hyheap) hH
      (by rw [hycount]; exact hywritten) hyframe
  · intro u hu
    rw [hbmem]
    refine hvframe u ?_
    rw [hvK]; exact hu.imp id fun h => by rw [hbo] at h; exact h

/-- Complete native preparation from the real original input, preserving the standalone
all-record producer contract and halt-exclusive allowance. -/
theorem exec_at {w : ℕ} (n D g p : ℕ) (values : ℕ → ℤ) (initial : Data 64)
    (hDHeader : initial.mem 1 = D) (hgHeader : initial.mem 2 = g)
    (hnHeader : initial.mem 3 = n) (hpHeader : initial.mem 4 = p)
    (hinput : ∀ q < 3 * (n * n), initial.mem (5 + q) = Signed.encode (values q))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (hbudget : Fits (w + 2) (budget n D g p)) :
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let K := ChunkCatalogue.before C (queryCap n D) p
    let H := numPieces n D g
    ∃ y, ExecWithin (w + 2) program initial y (timeBound n D p K H - 1) ∧
      Output n D g p values initial y := by
  obtain ⟨y, he, hout, _⟩ := exec_at_with_prefix n D g p values initial
    hDHeader hgHeader hnHeader hpHeader hinput hD hDn hg hp hmod hvalues hbudget
  exact ⟨y, he, hout⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.Instances
