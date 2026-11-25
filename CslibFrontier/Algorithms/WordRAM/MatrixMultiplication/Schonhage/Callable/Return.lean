/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Program

/-!
# Exact physical input and answer words

The callable compiler relates clipped memory to source memory. Two actual in-place span loops
make the restored input and returned answers exact physical words. These are internal execution
interfaces; both loops charge their setup, address calculations, remainders and stores.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM

private theorem frame_high_regs {x y : Data 163} {a b c : ℕ}
    (yf : ∀ i : Fin 163, (∀ j : Fin 7, normalizeBank j ≠ i) →
      y.regs i = (((x.set Reg.result a).set Reg.second b).set Reg.third c).regs i) :
    ∀ i : Fin 163, 7 ≤ i.val → y.regs i = x.regs i := fun i hi => by
  rw [yf i (fun j hj => by have h := congrArg Fin.val hj; change j.val = i.val at h; omega)]
  repeat rw [Data.set_regs_of_ne (by intro h; subst h; exact absurd hi (by decide))]

/-- Normalize precisely the local original input; high product/caller registers survive. -/
theorem exec_restoreInput {W b n M : ℕ} (x : Data 163) (hb : x.regs Reg.base = b)
    (hn : x.regs Reg.inputSize = n) (hm : x.regs Reg.modulus = M) (hM : 0 < M)
    (hfit : Fits W (b + n + M + 2)) :
    ∃ y, ExecWithin W restoreInput x y (7 * n + 7) ∧
      y.mem = ArrayNormalize.normalizePrefix x.mem b M n ∧
      ∀ i : Fin 163, 7 ≤ i.val → y.regs i = x.regs i := by
  refine WP.exists_execWithin ?_
  unfold restoreInput
  wram_exec [hb, hn, hm]
  wram_call ArrayNormalize.exec renamed with y ⟨⟨ym, _, _, _⟩, yf⟩
  exact ⟨by omega, ym, frame_high_regs yf⟩

/-- Normalize the answer span, preserving all high registers, and return its absolute pointer. -/
theorem exec_returnOutput {W b o n M : ℕ} (x : Data 163) (hb : x.regs Reg.base = b)
    (ho : x.regs Reg.output = o) (hn : x.regs Reg.queryCount = n)
    (hm : x.regs Reg.modulus = M) (hM : 0 < M) (hfit : Fits W (b + o + n + M + 2)) :
    ∃ y, ExecWithin W returnOutput x y (7 * n + 7) ∧
      y.mem = ArrayNormalize.normalizePrefix x.mem (b + o) M n ∧
      y.regs Reg.result = b + o ∧
      ∀ i : Fin 163, 7 ≤ i.val → y.regs i = x.regs i := by
  have hfit' : Fits W ((b + o) + n + M + 2) := by simpa only [Nat.add_assoc] using hfit
  refine WP.exists_execWithin ?_
  unfold returnOutput
  wram_exec [hb, ho, hn, hm]
  wram_call ArrayNormalize.exec renamed [hfit'] with y ⟨⟨ym, yr, _, _⟩, yf⟩
  exact ⟨by omega, ym, yr, frame_high_regs yf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
