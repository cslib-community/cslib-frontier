/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.NatSqrt
public import CslibFrontier.Algorithms.ExactTriangle.Splitting
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall

/-!
# Native ExactTriangle splitting parameters

The program computes the existing integer parameters `sOf`, `queryCap`, `pieceSize` and
`numPieces`. Both square roots call the charged native successive-squares program; all products,
quotients and ceilings are native instructions. The modulus is supplied separately by the outer
prime-selection host.

## Main definitions

* `Parameters.program`: fixed fifteen-register parameter computation.

## Main results

* `Parameters.exec`: exact outputs, explicit word fits, cost and an unchanged-memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Parameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Square-root input and arithmetic scratch. -/
abbrev arg : Fin 15 := 0
/-- Square-root result. -/
abbrev root : Fin 15 := 1
/-- Input matrix side. -/
abbrev size : Fin 15 := 6
/-- Target middle dimension. -/
abbrev dimension : Fin 15 := 7
/-- Piece-size divisor. -/
abbrev divisor : Fin 15 := 8
/-- Output floor square root of the middle dimension. -/
abbrev middleRoot : Fin 15 := 9
/-- Output query chunk capacity. -/
abbrev capacity : Fin 15 := 10
/-- Output maximum piece length. -/
abbrev pieceLength : Fin 15 := 11
/-- Output number of pieces. -/
abbrev pieces : Fin 15 := 12
/-- Square of the outer dimension. -/
abbrev area : Fin 15 := 13
/-- Constant one, outside the square-root register bank. -/
abbrev one : Fin 15 := 14

private abbrev sqrtReg : Fin 6 → Fin 15 := Fin.castLE (by decide)

private theorem sqrtReg_injective : Function.Injective sqrtReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 15 => k.val) h)

/-- Reused charged integer square root. -/
def squareRoot : Code .standard 15 := NatSqrt.program.rename (Fin.castLE (by decide))

/-- Runtime arithmetic between the square roots. -/
def between : Code .standard 15 := ram[
  middleRoot ← root; area ← size * size; arg ← area * area; arg ← arg / dimension ]

/-- Both natural ceilings use the existing `(a+b-1)/b` convention, including zero divisors. -/
def finish : Code .standard 15 := ram[
  capacity ← root; pieceLength ← middleRoot + divisor; pieceLength ← pieceLength - one;
  pieceLength ← pieceLength / divisor; pieces ← size + pieceLength;
  pieces ← pieces - one; pieces ← pieces / pieceLength ]

/-- Fixed code; only the square-root loops depend on the runtime inputs. -/
def program : Code .standard 15 :=
  .seq (ram[ one ← #1; arg ← dimension ])
    (.seq squareRoot (.seq between (.seq squareRoot finish)))

/-- Fixed native code and no physical-width reads. -/
theorem program_fixed : program.size ≤ 64 ∧ ¬program.ReadsWidth := by decide

/-- Compute the finite splitting parameters from actual runtime dimensions. The two explicit
ceiling-addition fits cover their temporary sums, and the fourth-power bound covers the square
formed before dividing by `D`. The final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 15)
    (hD : Fits w (4 * x.regs dimension + 4))
    (hN : Fits w (4 * ((x.regs size * x.regs size) * (x.regs size * x.regs size)) + 4))
    (hB : Fits w (sOf (x.regs dimension) + x.regs divisor))
    (hH : Fits w (x.regs size + pieceSize (x.regs dimension) (x.regs divisor))) :
    ∃ y, ExecWithin w program x y
        (5 * sOf (x.regs dimension) + 5 * queryCap (x.regs size) (x.regs dimension) + 27) ∧
      y.regs middleRoot = sOf (x.regs dimension) ∧
      y.regs capacity = queryCap (x.regs size) (x.regs dimension) ∧
      y.regs pieceLength = pieceSize (x.regs dimension) (x.regs divisor) ∧
      y.regs pieces = numPieces (x.regs size) (x.regs dimension) (x.regs divisor) ∧
      y.regs size = x.regs size ∧ y.regs dimension = x.regs dimension ∧
      y.regs divisor = x.regs divisor ∧ y.mem = x.mem := by
  let n := x.regs size
  let D := x.regs dimension
  let g := x.regs divisor
  have hnarea : n * n ≤ (n * n) * (n * n) := by
    by_cases h : n * n = 0
    · simp [h]
    · exact Nat.le_mul_of_pos_right _ (by omega)
  have hquot : (n * n) * (n * n) / D ≤ (n * n) * (n * n) := Nat.div_le_self ..
  have hdivB : (sOf D + g - 1) / g ≤ sOf D + g := (Nat.div_le_self ..).trans (Nat.sub_le ..)
  have hdivH : (n + pieceSize D g - 1) / pieceSize D g ≤ n + pieceSize D g :=
    (Nat.div_le_self ..).trans (Nat.sub_le ..)
  refine WP.exists_execWithin ?_
  unfold program squareRoot between finish
  wram_exec
  wram_call (NatSqrt.exec _ (by wram_simp; exact hD))
    canonical sqrtReg_injective with b ⟨hbroot, -, hbm, -⟩
  wram_simp at hbroot hbm
  have hbroot' : b.regs 1 = sOf D := hbroot
  wram_exec [hbroot']
  wram_call (NatSqrt.exec _ (by wram_simp; exact hN.of_le (by dsimp [n, D] at hquot ⊢; omega)))
    canonical sqrtReg_injective with d ⟨hdroot, -, hdm, -⟩
  wram_simp at hdroot hdm
  have hdroot' : d.regs 1 = queryCap n D := by
    simpa only [queryCap, pow_two] using hdroot
  have hH' : Fits w (n + (sOf D + g - 1) / g) := by
    simpa only [pieceSize, Nat.ceilDiv_eq_add_pred_div] using hH
  have hdivH' : (n + (sOf D + g - 1) / g - 1) / ((sOf D + g - 1) / g) ≤
      n + (sOf D + g - 1) / g := (Nat.div_le_self ..).trans (Nat.sub_le ..)
  wram_exec [hdroot', hbroot']
  refine ⟨?_, by wram_simp [hbroot']; rfl, by wram_simp [hdroot']; rfl,
    by wram_simp [pieceSize, Nat.ceilDiv_eq_add_pred_div]; rfl,
    by wram_simp [numPieces, pieceSize, Nat.ceilDiv_eq_add_pred_div]; rfl,
    by wram_simp, by wram_simp, by wram_simp, hdm.trans hbm⟩
  wram_simp [hbroot']
  simp only [sOf, queryCap, pow_two]
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.Parameters
