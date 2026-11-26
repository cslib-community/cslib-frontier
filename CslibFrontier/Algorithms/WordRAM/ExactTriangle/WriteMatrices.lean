/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Allocation
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Native zero/one matrices for an Exact Triangle instance

The input contains ordinary unsigned residues. Each output cell computes its row, middle vertex
and label through charged division/remainder instructions. Cells outside the selected piece are
zero; all other cells test the required modular adjacency. The same seventeen registers serve
the left `n×D` and right `D×n` matrices, with no supplied indexing table.

The X/Y output entries are raw unsigned words `0` and `1`. A consumer using canonical
`Signed.encode` matrix entries must double each entry while copying it into that input and
charge the conversion instruction. Scalar headers, pointers and query coordinates remain raw
unsigned words.

This directly adapts the adjacency formulas in the pinned
[Theorem 17 instance builder](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean).
The native implementation visits each output cell once; the source clears and then marks cells.

## Main definitions

* `WriteMatrices.Args`: matrix dimensions, residue/piece parameters and memory blocks.
* `WriteMatrices.entry`: the zero/one value at a flat output position.
* `WriteMatrices.program`: fixed native left/right matrix builders.

## Main results

* `WriteMatrices.exec`: complete charged execution and the output/input frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WriteMatrices

open Cslib.WordRAM

/-- Runtime arguments of one matrix-building call. -/
structure Args where
  /-- Residue matrix base. -/
  src : ℕ
  /-- Output matrix base. -/
  dst : ℕ
  /-- Number of vertices in each outer part. -/
  n : ℕ
  /-- Padded middle dimension. -/
  D : ℕ
  /-- Positive modulus. -/
  p : ℕ
  /-- First vertex of the selected piece. -/
  first : ℕ
  /-- Number of vertices in the piece. -/
  length : ℕ
  /-- A–B query residue. -/
  rho : ℕ

/-- Raw unsigned zero/one row-major adjacency. A true side chooses the right `D×n` matrix;
false chooses the left `n×D` matrix. The source residue matrix has shape `n×n`. A signed-matrix
consumer encodes these entries by doubling them. -/
def entry (rightSide : Bool) (A : Args) (R : ℕ → ℕ) (q : ℕ) : ℕ :=
  let line := if rightSide then q % A.n else q / A.D
  let middle := if rightSide then q / A.n else q % A.D
  let label := middle % A.p
  let vertex := middle / A.p
  if vertex < A.length then
    let r := R (line * A.n + A.first + vertex)
    let wanted := if rightSide then (A.p - r) % A.p else (r + A.rho) % A.p
    if label = wanted then 1 else 0
  else 0

/-- Every raw adjacency entry is a zero/one word, including padding. -/
theorem entry_le_one (side : Bool) (A : Args) (R : ℕ → ℕ) (q : ℕ) :
    entry side A R q ≤ 1 := by
  cases side <;> dsimp only [entry] <;> split_ifs <;> omega

/-- Residue input pointer. -/
abbrev src : Fin 17 := 0
/-- Output matrix pointer. -/
abbrev dst : Fin 17 := 1
/-- Outer dimension. -/
abbrev size : Fin 17 := 2
/-- Middle dimension. -/
abbrev dimension : Fin 17 := 3
/-- Modulus. -/
abbrev modulus : Fin 17 := 4
/-- First vertex of the piece. -/
abbrev first : Fin 17 := 5
/-- Piece length. -/
abbrev length : Fin 17 := 6
/-- Query residue. -/
abbrev rho : Fin 17 := 7
/-- Flat output cursor. -/
abbrev idx : Fin 17 := 8
/-- Number of output cells. -/
abbrev area : Fin 17 := 9
/-- Selected source row. -/
abbrev line : Fin 17 := 10
/-- Selected vertex within the piece. -/
abbrev vertex : Fin 17 := 11
/-- Middle label. -/
abbrev label : Fin 17 := 12
/-- Address temporary. -/
abbrev addr : Fin 17 := 13
/-- Residue and output value temporary. -/
abbrev value : Fin 17 := 14
/-- Constant zero. -/
abbrev zero : Fin 17 := 15
/-- Constant one. -/
abbrev one : Fin 17 := 16

/-- The eight runtime arguments occupy registers 0–7. -/
structure Entry (A : Args) (x : Data 17) : Prop where
  /-- Source pointer. -/
  src : x.regs src = A.src
  /-- Destination pointer. -/
  dst : x.regs dst = A.dst
  /-- Outer dimension. -/
  size : x.regs size = A.n
  /-- Middle dimension. -/
  dimension : x.regs dimension = A.D
  /-- Modulus. -/
  modulus : x.regs modulus = A.p
  /-- First vertex. -/
  first : x.regs first = A.first
  /-- Piece length. -/
  length : x.regs length = A.length
  /-- Query residue. -/
  rho : x.regs rho = A.rho

/-- Compute the source row and decode the middle label using actual arithmetic instructions. -/
def indices (rightSide : Bool) : Code .standard 17 :=
  if rightSide then ram[
    line ← idx % size; vertex ← idx / size; label ← vertex % modulus;
    vertex ← vertex / modulus ]
  else ram[
    line ← idx / dimension; vertex ← idx % dimension; label ← vertex % modulus;
    vertex ← vertex / modulus ]

/-- Read the selected residue and form its required label. -/
def readLabel (rightSide : Bool) : Code .standard 17 :=
  .seq (ram[ addr ← line * size; addr ← addr + first; addr ← addr + vertex;
    addr ← src + addr; value ← *addr ])
    (if rightSide then ram[ value ← modulus - value; value ← value % modulus ]
    else ram[ value ← value + rho; value ← value % modulus ])

/-- Write one zero/one cell and increment the flat cursor. -/
def body (rightSide : Bool) : Code .standard 17 :=
  .seq (indices rightSide)
    (.seq (.branch (.lt vertex length)
      (.seq (readLabel rightSide)
        (.branch (.eq label value) (.op (.copy value one)) (.op (.copy value zero))))
      (.op (.copy value zero)))
      (ram[ addr ← dst + idx; *addr ← value; idx ← idx + one ]))

/-- The complete builder initializes constants and visits all output positions once. -/
def program (rightSide : Bool) : Code .standard 17 :=
  .seq (ram[ zero ← #0; one ← #1; idx ← #0; area ← size * dimension ])
    (.loop (.lt idx area) (body rightSide))

/-- The instruction graph has fixed size and never reads the physical word width. -/
theorem program_fixed (rightSide : Bool) :
    (program rightSide).size ≤ 64 ∧ ¬(program rightSide).ReadsWidth := by
  cases rightSide <;> decide

private theorem entry_of_regs {A : Args} {x y : Data 17} (hx : Entry A x)
    (h : ∀ i : Fin 17, i.val < 8 → y.regs i = x.regs i) : Entry A y := by regs_frame

private theorem exec_indices {w q : ℕ} (side : Bool) (A : Args) (x : Data 17)
    (hx : Entry A x) (hq : x.regs idx = q) (hfit : Fits w q) :
    ∃ y, ExecWithin w (indices side) x y 4 ∧ Entry A y ∧
      y.regs idx = q ∧ y.regs line = (if side then q % A.n else q / A.D) ∧
      y.regs vertex = (if side then q / A.n else q % A.D) / A.p ∧
      y.regs label = (if side then q / A.n else q % A.D) % A.p ∧
      y.regs one = x.regs one ∧ y.regs zero = x.regs zero ∧ y.mem = x.mem := by
  refine WP.exists_execWithin ?_
  cases side <;>
    (simp only [indices, Bool.false_eq_true, ↓reduceIte]
     wram_exec [hq, hx.size, hx.dimension, hx.modulus]
     exact ⟨by regs_frame, by wram_simp [hq], by wram_simp, by wram_simp, by wram_simp,
       by wram_simp, by wram_simp, rfl⟩)

private theorem exec_readLabel {w row v : ℕ} (side : Bool) (A : Args) (R : ℕ → ℕ)
    (x : Data 17) (hx : Entry A x)
    (hrow : x.regs line = row) (hv : x.regs vertex = v)
    (hpoint : row * A.n + A.first + v < A.n * A.n)
    (hR : ∀ i < A.n * A.n, R i < A.p)
    (hinput : ∀ i < A.n * A.n, x.mem (A.src + i) = R i)
    (hs : Fits w (A.src + A.n * A.n)) (hp : Fits w (2 * A.p)) (hrho : A.rho < A.p) :
    ∃ y, ExecWithin w (readLabel side) x y 7 ∧
      y.regs value = (if side then (A.p - R (row * A.n + A.first + v)) % A.p
        else (R (row * A.n + A.first + v) + A.rho) % A.p) ∧
      (∀ i, i ≠ addr → i ≠ value → y.regs i = x.regs i) ∧ y.mem = x.mem := by
  have hkey := hR _ hpoint
  refine WP.exists_execWithin ?_
  cases side <;>
    (simp only [readLabel, Bool.false_eq_true, ↓reduceIte]
     wram_exec [hrow, hv, hx.size, hx.first, hx.src, hx.modulus, hx.rho, hinput _ hpoint]
     exact ⟨by wram_simp, fun i ha hval => by wram_simp [ha, hval], rfl⟩)

private theorem body_preserves (side : Bool) : ∀ i : Fin 17,
    (i.val < 8 ∨ i = area ∨ i = one ∨ i = zero) → (body side).Preserves i := by
  cases side <;> decide

private theorem exec_body {w q : ℕ} (side : Bool) (A : Args) (R : ℕ → ℕ)
    (x : Data 17) (hx : Entry A x) (hq : x.regs idx = q)
    (ho : x.regs one = 1) (hz : x.regs zero = 0) (hlt : q < A.n * A.D)
    (hrho : A.rho < A.p) (hpiece : A.first + A.length ≤ A.n)
    (hR : ∀ i < A.n * A.n, R i < A.p)
    (hinput : ∀ i < A.n * A.n, x.mem (A.src + i) = R i)
    (hsrc : Fits w (A.src + A.n * A.n)) (hdst : Fits w (A.dst + A.n * A.D))
    (hmod : Fits w (2 * A.p)) :
    ∃ y, ExecWithin w (body side) x y 18 ∧ y.regs idx = q + 1 ∧
      y.mem = Function.update x.mem (A.dst + q) (entry side A R q) := by
  refine WP.exists_execWithin ?_
  unfold body
  wram_exec
  wram_call (exec_indices side A x hx hq (hdst.of_le (by omega))) with
    b ⟨hba, hbi, hbl, hbv, hbb, hbo, hbz, hbm⟩
  by_cases hv : (if side then q / A.n else q % A.D) / A.p < A.length
  · have hrow : (if side then q % A.n else q / A.D) < A.n := by
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> stride_omega
    have hpoint : (if side then q % A.n else q / A.D) * A.n + A.first +
        (if side then q / A.n else q % A.D) / A.p < A.n * A.n := by stride_omega
    wram_exec [hbv, hba.length, hv]
    wram_call (exec_readLabel side A R b hba hbl hbv hpoint hR
      (by simpa only [hbm] using hinput) hsrc hmod hrho) with c ⟨hcv, hcr, hcm⟩
    have : c.regs dst = A.dst := by regs_frame
    have : c.regs idx = q := by regs_frame
    have : c.regs one = 1 := by regs_frame
    have : c.regs zero = 0 := by regs_frame
    have : c.regs label = (if side then q / A.n else q % A.D) % A.p := by regs_frame
    wram_exec [hcv, this, ‹c.regs dst = A.dst›, ‹c.regs idx = q›, ‹c.regs one = 1›,
      ‹c.regs zero = 0›]
    all_goals exact ⟨by wram_simp, by
      simp only [entry, hv, hc, ↓reduceIte, hcm, hbm, Data.write_mem, Data.set_mem]⟩
  · wram_exec [hbv, hba.length, hv, hbz, hz, hba.dst, hbi, hbo, ho]
    exact ⟨by wram_simp, by simp only [entry, hv, ↓reduceIte, hbm, Data.write_mem, Data.set_mem]⟩

/-- Construct every entry of a left or right instance matrix in `20nD+6` native instructions,
excluding the halt. The source is an actual residue array below the output. All cells outside
the output block and all eight arguments are preserved. No adjacency table is supplied. -/
theorem exec {w : ℕ} (side : Bool) (A : Args) (R : ℕ → ℕ) (x : Data 17)
    (hx : Entry A x) (hrho : A.rho < A.p) (hpiece : A.first + A.length ≤ A.n)
    (hR : ∀ i < A.n * A.n, R i < A.p)
    (hinput : ∀ i < A.n * A.n, x.mem (A.src + i) = R i)
    (hsrc : Fits w (A.src + A.n * A.n)) (hdst : Fits w (A.dst + A.n * A.D))
    (hmod : Fits w (2 * A.p)) (hdisj : A.src + A.n * A.n ≤ A.dst) :
    ∃ y, ExecWithin w (program side) x y (20 * (A.n * A.D) + 6) ∧ Entry A y ∧
      y.regs idx = A.n * A.D ∧
      (Block.mk A.dst (A.n * A.D)).Realizes y.mem (fun i => entry side A R i) ∧
      (∀ a, ¬(Block.mk A.dst (A.n * A.D)).Owns a → y.mem a = x.mem a) := by
  let I (y : Data 17) : Prop := Entry A y ∧ y.regs area = A.n * A.D ∧
    y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs idx ≤ A.n * A.D ∧
    (∀ j < y.regs idx, y.mem (A.dst + j) = entry side A R j) ∧
    (∀ a, ¬(A.dst ≤ a ∧ a < A.dst + y.regs idx) → y.mem a = x.mem a)
  have hbody (y : Data 17) (hy : I y) (hc : (Cond.lt idx area).Holds y) :
      ∃ z, ExecWithin w (body side) y z 18 ∧ I z ∧
        A.n * A.D - z.regs idx < A.n * A.D - y.regs idx := by
    obtain ⟨hyp, hya, hyo, hyz, hyi, hym, hyout⟩ := hy
    have hlt : y.regs idx < A.n * A.D := by
      simpa only [Cond.holds_lt, hya] using hc
    have hyinput : ∀ i < A.n * A.n, y.mem (A.src + i) = R i := fun i hi => by
      rw [hyout _ (by omega)]; exact hinput i hi
    obtain ⟨z, he, hzi, hzm⟩ := exec_body side A R y hyp rfl hyo hyz hlt
      hrho hpiece hR hyinput hsrc hdst hmod
    have hpres (i : Fin 17) (hi : i.val < 8 ∨ i = area ∨ i = one ∨ i = zero) :
        z.regs i = y.regs i := he.regs_eq (body_preserves side i hi)
    refine ⟨z, he, ⟨entry_of_regs hyp (fun i hi => hpres i (Or.inl hi)),
      (hpres area (by simp)).trans hya, (hpres one (by simp)).trans hyo,
      (hpres zero (by simp)).trans hyz, by omega, ?_, ?_⟩, by omega⟩
    · intro j hj; rw [hzm]
      by_cases h : j = y.regs idx
      · subst j; update_simp
      · update_simp; exact hym j (by omega)
    · intro a ha; rw [hzm]; update_simp; exact hyout a (by omega)
  refine WP.exists_execWithin ?_
  unfold program
  wram_exec [hx.size, hx.dimension]
  have hx₀ : I (((x.set zero 0).set one 1).set idx 0 |>.set area (A.n * A.D)) :=
    ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp; exact Nat.zero_le _, fun _ hj => by wram_simp at hj, fun _ _ => rfl⟩
  wram_call (ExecWithin.loop_invariant I (fun y => A.n * A.D - y.regs idx) hbody hx₀)
    with y ⟨⟨hyp, hya, -, -, hyi, hym, hyout⟩, hc⟩
  have hend : y.regs idx = A.n * A.D := by simp only [Cond.holds_lt, hya] at hc; omega
  refine ⟨by wram_simp; omega, hyp, hend,
    fun i => hym i (by simpa only [hend] using i.isLt),
    fun a ha => hyout a (by simpa only [hend, Block.Owns] using ha)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.WriteMatrices
