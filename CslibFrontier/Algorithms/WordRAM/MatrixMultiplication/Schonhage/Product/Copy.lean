/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Program

/-!
# Charged copies across the producer/consumer boundary

## Main results

* `QueriedProduct.exec_copyCall`: real argument setup and the unchanged dynamic native copy,
  with both address orders, equality, complete memory meaning and caller-register frame.

These are internal execution interfaces. Complete product clients derive the numerical fits
and separation from the original input and the explicit computed layout.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Each existing 96-register callee has exactly its original register semantics. -/
public theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 160 => i.val) h)

/-- Dynamic native argument setup and every copy instruction are charged. The caller's
source/destination/length registers, and every register beyond the seven-register callee,
are preserved. Source and destination separation is a numerical layout obligation. -/
public theorem exec_copyCall {w : ℕ} (x : Data 160) (h1 : Fits w 1)
    (hs : Fits w (x.regs Reg.source + x.regs Reg.length))
    (hd : Fits w (x.regs Reg.destination + x.regs Reg.length))
    (hsep : x.regs Reg.source + x.regs Reg.length ≤ x.regs Reg.destination ∨
      x.regs Reg.destination + x.regs Reg.length ≤ x.regs Reg.source ∨
      x.regs Reg.source = x.regs Reg.destination) :
    ∃ y, ExecWithin w copyCall x y (7 * x.regs Reg.length + 7) ∧
      y.mem =
        ArrayCopy.copyPrefix x.mem (x.regs Reg.source) (x.regs Reg.destination)
          (x.regs Reg.length) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [copyCall]
  wram_call @ArrayCopy.exec_of_separated_or_eq renamed [h1, hs, hd, hsep]
    with y ⟨⟨hm, _⟩, hframe⟩
  wram_simp at hm ⊢
  refine ⟨by omega, hm, fun i hi => ?_⟩
  rw [hframe i (fun j hj => by have hv := congrArg Fin.val hj; change j.val = i.val at hv; omega)]
  wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
