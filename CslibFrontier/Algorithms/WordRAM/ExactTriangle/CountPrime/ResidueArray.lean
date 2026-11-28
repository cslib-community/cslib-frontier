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

/-!
# Real counter residue-array calls

Four charged argument copies invoke the existing signed-remainder loop. Every resulting
residue is an unsigned key; canonical signed decoding is performed inside the actual callee.
The original high-bank metadata and all memory outside the destination are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Complete actual residue call for a matrix, with source and destination parameters in the
protected metadata bank. No residue array is supplied to the algorithm. -/
theorem exec_residues {w n p a b : ℕ} (src dst : Fin 128) (x : Data 128)
    (hsrc : 64 ≤ src.val) (hdst : 64 ≤ dst.val) (values : ℕ → ℤ)
    (hp : 0 < p) (hc : x.regs Reg.cells = n * n)
    (ha : x.regs src = a) (hb : x.regs dst = b)
    (hm : x.regs Reg.encodedModulus = encode (p : ℤ))
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hv : ∀ i < n * n, GenericRAM.Signed.Fits w (values i))
    (haf : Fits (w + 2) (a + n * n)) (hbf : Fits (w + 2) (b + n * n))
    (hdisjoint : a + n * n ≤ b)
    (hinput : ∀ i < n * n, x.mem (a + i) = encode (values i)) :
    ∃ y, ExecWithin (w + 2) (residues src dst) x y (23 * (n * n) + 8) ∧
      (∀ i < n * n, y.mem (b + i) = (values i % (p : ℤ)).toNat) ∧
      (∀ d, d < b ∨ b + n * n ≤ d → y.mem d = x.mem d) ∧
      ∀ j, 16 ≤ j.val → y.regs j = x.regs j := by
  have hs : src ≠ Reg.low9 := fun h => by subst h; contradiction
  have hd9 : dst ≠ Reg.low9 := fun h => by subst h; contradiction
  have hd10 : dst ≠ Reg.low10 := fun h => by subst h; contradiction
  refine WP.exists_execWithin ?_
  unfold residues
  wram_exec [ha, hb, hc, hm, hs, hd9, hd10]
  wram_call (ThreeSum.ChanHe.Residues.exec _ values hp hmod
    (by wram_simp) (by wram_simp; exact hv) (by wram_simp; exact haf)
    (by wram_simp; exact hbf) (by wram_simp; exact hdisjoint)
    (by wram_simp; exact hinput))
    canonical (Fin.castLE_injective _) with s ⟨memory, -⟩
  wram_simp at memory
  refine ⟨by wram_simp; omega, ?_, ?_, ?_⟩
  · intro i hi
    wram_simp [memory, ThreeSum.ChanHe.Residues.memory]
    exact ite_eq_left (by omega)
  · intro d hd
    wram_simp [memory, ThreeSum.ChanHe.Residues.memory]
    exact ite_eq_right (by omega)
  · intro j hj
    refine (Data.extend_castLE_regs_of_le s _ j hj).trans ?_
    have hne : j ≠ Reg.low9 ∧ j ≠ Reg.low10 ∧ j ≠ Reg.low11 ∧ j ≠ Reg.low12 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro h; subst j; contradiction)
    wram_simp [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
