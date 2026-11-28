/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Program
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Strassen.Exec

/-!
# Actual low-bank CountPrime multiplication call

The counter copies six real arguments and invokes the complete native 64-register Strassen
program in its low bank. Its 64-and-above metadata survives the existing native register
renaming semantics. Monomial inputs have coefficient magnitude at most one; all recursive
signed fits therefore follow from the explicit original cyclic-length/depth envelope.

This is an internal stage contract. The complete counter derives its monomial readback and
pointer separation from preceding native setup and matrix construction, rather than taking
a layout or multiplication certificate as an algorithm input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Invoke the actual complete native Strassen program, charging argument copies, all
coefficient arithmetic/recursion and loop exit. No multiplication/run/time contract is assumed. -/
theorem exec_product {w p k : ℕ} (x : Data 128) (u v : ℕ → ℤ)
    (hp : 0 < p) (hpr : x.regs Reg.modulus = p) (hkr : x.regs Reg.depth = k)
    (hPQ : x.regs Reg.matrixP + 4 ^ k * p ≤ x.regs Reg.matrixQ)
    (hQR : x.regs Reg.matrixQ + 4 ^ k * p ≤ x.regs Reg.matrixR)
    (hRS : x.regs Reg.matrixR + 4 ^ k * p ≤ x.regs Reg.productScratch)
    (hu : ∀ i < 4 ^ k * p, (u i).natAbs ≤ 1)
    (hv : ∀ i < 4 ^ k * p, (v i).natAbs ≤ 1)
    (hleft : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixP + i) = encode (u i))
    (hright : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixQ + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w ((2 * (p + 4) * 16 ^ k : ℕ) : ℤ))
    (haddr : Fits (w + 2) (Strassen.addressBound (x.regs Reg.productScratch + 4 ^ k * p)
      (x.regs Reg.productScratch + 4 ^ k * p) k)) :
    ∃ y, ExecWithin (w + 2) product x y (Strassen.traceBudget p k + 4 * k + 38) ∧
      (∀ i < 4 ^ k * p, y.mem (x.regs Reg.matrixR + i) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.multiply p k u v i)) ∧
      (∀ d, ¬Strassen.NodeWrites p k (x.regs Reg.matrixR) (x.regs Reg.productScratch)
        (x.regs Reg.productScratch + 4 ^ k * p) (x.regs Reg.productScratch + 4 ^ k * p) d →
        y.mem d = x.mem d) ∧
      ∀ i, 64 ≤ i.val → y.regs i = x.regs i := by
  have hmag' : GenericRAM.Signed.Fits w (Strassen.magnitudeBound p 1 1 k : ℤ) := by
    convert hmag using 1
    simp [Strassen.magnitudeBound,
      CyclicConvolution.magnitudeBound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  refine WP.exists_execWithin ?_
  wram_exec [product, hpr, hkr]
  wram_call (Strassen.exec _ u v hp (by wram_simp) (by wram_simp)
    (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
    (by omega) (by omega) hRS (Or.inl (by omega)) (Or.inl hQR)
    hu hv hleft hright hmag' haddr)
    canonical (Fin.castLE_injective _) with s result
  refine ⟨by omega, result.values, result.outside, fun i hi => ?_⟩
  refine (Data.extend_castLE_regs_of_le s _ i hi).trans ?_
  have hne : i ≠ Reg.low32 ∧ i ≠ Reg.low33 ∧ i ≠ Reg.low34 ∧ i ≠ Reg.low35 ∧
      i ≠ Reg.low36 ∧ i ≠ Reg.low46 := by revert i hi; decide
  wram_simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
