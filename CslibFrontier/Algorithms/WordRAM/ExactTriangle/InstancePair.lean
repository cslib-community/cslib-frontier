/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.WriteMatrices
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Tactic.UpdateSimp
import Mathlib.Tactic.FinCases

/-!
# Native matrix pairs and instance records

One call writes a six-word record `(rho,piece,queries,count,X,Y)` and the actual raw unsigned
zero/one matrices `X : n×D` and `Y : D×n` immediately after it. Both matrices reuse
`WriteMatrices.program`; all pointer arithmetic, argument delivery and record stores are charged.
The query words remain in the earlier computed catalogue and are shared by reference.

`setup`, `writeHeader`, `deliverLeft`, `deliverRight` and `matrix` are internal program stages.
They are exposed so that the complete catalogue controller can reuse the same fixed program.

## Main definitions

* `InstancePair.program`: fixed thirty-two-register matrix-pair and record writer.
* `InstancePair.leftArgs`, `InstancePair.rightArgs`: existing matrix-writer arguments read
  directly from the runtime registers.

## Main results

* `InstancePair.exec`: both exact matrices and the real record, with a combined outside frame
  and a `40nD+38` charged instruction bound before halt.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.InstancePair

open Cslib.WordRAM

/-- Computed A–C residue-array pointer. -/
abbrev srcLeft : Fin 32 := 17
/-- Computed B–C residue-array pointer. -/
abbrev srcRight : Fin 32 := 18
/-- First word of the instance record. -/
abbrev base : Fin 32 := 19
/-- Outer matrix dimension. -/
abbrev size : Fin 32 := 20
/-- Padded middle matrix dimension. -/
abbrev dimension : Fin 32 := 21
/-- Positive residue modulus. -/
abbrev modulus : Fin 32 := 22
/-- First original vertex in the piece. -/
abbrev first : Fin 32 := 23
/-- Actual number of vertices in the piece. -/
abbrev length : Fin 32 := 24
/-- Query residue. -/
abbrev rho : Fin 32 := 25
/-- Actual query-pair pointer. -/
abbrev queries : Fin 32 := 26
/-- Actual number of query pairs. -/
abbrev count : Fin 32 := 27
/-- Index of the original piece. -/
abbrev piece : Fin 32 := 28
/-- Constant one, preserved by both matrix calls. -/
abbrev one : Fin 32 := 29
/-- Header cursor. -/
abbrev addr : Fin 32 := 30
/-- Number of words in one matrix. -/
abbrev area : Fin 32 := 31

/-- Existing left-matrix arguments, with its output following the six-word record. -/
@[expose]
def leftArgs (x : Data 32) : WriteMatrices.Args where
  src := x.regs srcLeft
  dst := x.regs base + 6
  n := x.regs size
  D := x.regs dimension
  p := x.regs modulus
  first := x.regs first
  length := x.regs length
  rho := x.regs rho

/-- Existing right-matrix arguments, immediately following the left matrix. -/
@[expose]
def rightArgs (x : Data 32) : WriteMatrices.Args :=
  { leftArgs x with
    src := x.regs srcRight
    dst := x.regs base + 6 + x.regs size * x.regs dimension }

/-- Compute the left output pointer and matrix area with native arithmetic. -/
@[expose]
def setup : Code .standard 32 :=
  let dst : Fin 32 := 1
  ram[ one ← #1; addr ← #6; dst ← base + addr; area ← size * dimension ]

/-- Write the actual query reference and both computed matrix pointers. -/
@[expose]
def writeHeader : Code .standard 32 :=
  let dst : Fin 32 := 1
  let scratch : Fin 32 := 0
  ram[ addr ← base; *addr ← rho; addr ← addr + one; *addr ← piece;
    addr ← addr + one; *addr ← queries; addr ← addr + one; *addr ← count;
    addr ← addr + one; *addr ← dst; addr ← addr + one;
    scratch ← dst + area; *addr ← scratch ]

/-- Deliver the seven remaining left-matrix arguments; its destination is already computed. -/
@[expose]
def deliverLeft : Code .standard 32 :=
  let src : Fin 32 := 0
  let n : Fin 32 := 2
  let D : Fin 32 := 3
  let p : Fin 32 := 4
  let start : Fin 32 := 5
  let len : Fin 32 := 6
  let residue : Fin 32 := 7
  ram[ src ← srcLeft; n ← size; D ← dimension; p ← modulus;
    start ← first; len ← length; residue ← rho ]

/-- The left writer preserves its argument registers, so only the source and output pointer
change for the right call. -/
@[expose]
def deliverRight : Code .standard 32 :=
  let src : Fin 32 := 0
  let dst : Fin 32 := 1
  ram[ src ← srcRight; dst ← dst + area ]

/-- Reuse either native matrix writer in the lower seventeen registers. -/
@[expose]
def matrix (side : Bool) : Code .standard 32 :=
  (WriteMatrices.program side).rename (Fin.castLE (by decide))

/-- Complete record and matrix-pair construction. -/
@[expose]
def program : Code .standard 32 :=
  .seq (.seq setup writeHeader) (.seq deliverLeft (.seq (matrix false)
    (.seq deliverRight (matrix true))))

/-- Finite code independent of every runtime dimension and physical width. -/
theorem program_fixed : program.size ≤ 160 ∧ ¬program.ReadsWidth := by decide

private abbrev bank : Fin 17 → Fin 32 := Fin.castLE (by decide)

private theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

private theorem header_preserves : ∀ i : Fin 32,
    17 ≤ i.val → i.val < 29 → (Code.seq setup writeHeader).Preserves i := by decide +kernel

/-- Six raw unsigned record words: residue, piece index, shared query pointer/count, then the
two computed matrix pointers. Matrix entries themselves are raw zero/one words. -/
@[expose]
def recordWords (x : Data 32) : Fin 6 → ℕ :=
  ![x.regs rho, x.regs piece, x.regs queries, x.regs count, (leftArgs x).dst, (rightArgs x).dst]

private theorem exec_header {w : ℕ} (x : Data 32)
    (hfit : Fits w (x.regs base + 6 + 2 * (x.regs size * x.regs dimension) + 7)) :
    ∃ y, ExecWithin w (.seq setup writeHeader) x y 17 ∧
      y.regs 1 = x.regs base + 6 ∧ y.regs area = x.regs size * x.regs dimension ∧
      (∀ i : Fin 32, 17 ≤ i.val → i.val < 29 → y.regs i = x.regs i) ∧
      (Block.mk (x.regs base) 6).Realizes y.mem (recordWords x) ∧
      (∀ a, ¬(x.regs base ≤ a ∧ a < x.regs base + 6) → y.mem a = x.mem a) := by
  refine WP.exists_execWithin_preserves
    (P := fun i => 17 ≤ i.val ∧ i.val < 29) (fun i hi => header_preserves i hi.1 hi.2) ?_
  unfold setup writeHeader
  wram_exec
  intro hpres
  refine ⟨by wram_simp, by wram_simp, fun i hi hi' => hpres i ⟨hi, hi'⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      (simp only [Block.read, recordWords, leftArgs, rightArgs]; wram_simp; rfl)
  · intro j hj
    simp only [Data.set_mem, Data.write_mem]
    update_simp

/-- Write both actual matrices and their shared-query instance record. The source arrays are
ordinary residue words before the output region. Existing `WriteMatrices.entry` supplies the
semantics; no adjacency array, execution or time contract is an input. Halt is excluded. -/
theorem exec {w : ℕ} (x : Data 32) (L R : ℕ → ℕ)
    (hrho : x.regs rho < x.regs modulus)
    (hpiece : x.regs first + x.regs length ≤ x.regs size)
    (hL : ∀ i < x.regs size * x.regs size, L i < x.regs modulus)
    (hR : ∀ i < x.regs size * x.regs size, R i < x.regs modulus)
    (hleft : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcLeft + i) = L i)
    (hright : ∀ i < x.regs size * x.regs size, x.mem (x.regs srcRight + i) = R i)
    (hsL : x.regs srcLeft + x.regs size * x.regs size ≤ x.regs base)
    (hsR : x.regs srcRight + x.regs size * x.regs size ≤ x.regs base)
    (hfit : Fits w (x.regs base + 6 + 2 * (x.regs size * x.regs dimension) +
      x.regs srcLeft + x.regs srcRight + 2 * (x.regs size * x.regs size) +
        2 * x.regs modulus + 7)) :
    ∃ y, ExecWithin w program x y (40 * (x.regs size * x.regs dimension) + 38) ∧
      (Block.mk (x.regs base) 6).Realizes y.mem (recordWords x) ∧
      (Block.mk (leftArgs x).dst (x.regs size * x.regs dimension)).Realizes y.mem
        (fun i => WriteMatrices.entry false (leftArgs x) L i) ∧
      (Block.mk (rightArgs x).dst (x.regs size * x.regs dimension)).Realizes y.mem
        (fun i => WriteMatrices.entry true (rightArgs x) R i) ∧
      (∀ a, ¬(x.regs base ≤ a ∧
        a < x.regs base + 6 + 2 * (x.regs size * x.regs dimension)) → y.mem a = x.mem a) := by
  let M := x.regs size * x.regs dimension
  let A := leftArgs x
  let B := rightArgs x
  refine WP.exists_execWithin ?_
  unfold program deliverLeft deliverRight matrix
  refine WP.seq ?_
  wram_call (exec_header x (hfit.of_le (by omega))) with a ⟨ha1, haM, hameta, harecord, haframe⟩
  have har (i : Fin 32) (hi : 17 ≤ i.val ∧ i.val < 29) : a.regs i = x.regs i :=
    hameta i hi.1 hi.2
  wram_exec [har srcLeft (by decide), har size (by decide), har dimension (by decide),
    har modulus (by decide), har first (by decide), har length (by decide), har rho (by decide)]
  wram_call (WriteMatrices.exec false A L _
    ⟨by wram_simp; rfl, by wram_simp; exact ha1, by wram_simp; rfl, by wram_simp; rfl,
     by wram_simp; rfl, by wram_simp; rfl, by wram_simp; rfl, by wram_simp; rfl⟩
    hrho hpiece hL
    (fun i hi => by
      wram_simp
      rw [haframe _ (by dsimp [A, leftArgs] at hi ⊢; omega)]
      exact hleft i hi)
    (hfit.of_le (by dsimp [A, leftArgs]; omega))
    (hfit.of_le (by dsimp [A, leftArgs]; omega))
    (hfit.of_le (by dsimp [A, leftArgs]; omega))
    (by dsimp [A, leftArgs]; omega))
    canonical bank_injective with v ⟨hvEntry, -, hvleft, hvframe⟩
  wram_simp at hvframe
  have hv1 : v.regs WriteMatrices.dst = A.dst := hvEntry.dst
  have hrightDst : Fits w (A.dst + M) := hfit.of_le (by dsimp [A, leftArgs, M]; omega)
  wram_exec [har srcRight (by decide), hv1, haM]
  wram_call (WriteMatrices.exec true B R _
    ⟨by wram_simp; rfl, by wram_simp; rfl, by wram_simp; exact hvEntry.size,
     by wram_simp; exact hvEntry.dimension, by wram_simp; exact hvEntry.modulus,
     by wram_simp; exact hvEntry.first, by wram_simp; exact hvEntry.length,
     by wram_simp; exact hvEntry.rho⟩
    hrho hpiece hR
    (fun i hi => by
      wram_simp
      rw [hvframe _ (by dsimp [Block.Owns, B, rightArgs, leftArgs, A, M] at hi ⊢; omega),
          haframe _ (by dsimp [B, rightArgs, leftArgs] at hi ⊢; omega)]
      exact hright i hi)
    (hfit.of_le (by dsimp [B, rightArgs, leftArgs]; omega))
    (hfit.of_le (by dsimp [B, rightArgs, leftArgs]; omega))
    (hfit.of_le (by dsimp [B, rightArgs, leftArgs]; omega))
    (by dsimp [B, rightArgs, leftArgs]; omega))
    canonical bank_injective with z ⟨-, -, hzright, hzframe⟩
  wram_simp at hzframe
  refine ⟨by wram_simp; dsimp [A, B, rightArgs, leftArgs, M]; omega, ?_, ?_, hzright, ?_⟩
  · intro i
    wram_simp
    change z.mem (x.regs base + i.val) = recordWords x i
    have hi : i.val < 6 := i.isLt
    rw [hzframe _ (by dsimp [Block.Owns, B, rightArgs, leftArgs]; omega),
        hvframe _ (by dsimp [Block.Owns, A, leftArgs]; omega)]
    exact harecord i
  · intro i
    wram_simp
    change z.mem (A.dst + i.val) = WriteMatrices.entry false A L i
    have hi : i.val < M := i.isLt
    rw [hzframe _ (by dsimp [Block.Owns, B, rightArgs, leftArgs, A, M] at hi ⊢; omega)]
    exact hvleft i
  · intro j hj
    wram_simp
    rw [hzframe _ (by dsimp [Block.Owns, B, rightArgs, leftArgs, M]; omega),
        hvframe _ (by dsimp [Block.Owns, A, leftArgs, M]; omega),
        haframe _ (by omega)]

end Cslib.Algorithms.WordRAM.ExactTriangle.InstancePair
