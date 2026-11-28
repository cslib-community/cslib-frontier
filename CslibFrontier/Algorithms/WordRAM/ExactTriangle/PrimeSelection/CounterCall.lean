/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Exec

/-!
# Actual modular counting inside the selector register bank

Six real copies deliver the original side, current prime, matrix pointers and workspace to
the complete native counter. The entire counter runs in its low 128-register bank. This
rule composes its actual execution and memory frame; it assumes no counter answer, run,
layout, multiplication or time contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Execute the real counter, including argument delivery, from original signed arrays and
numerical admission. Sources may alias below scratch; the scratch region may be dirty.
Selector metadata is outside the low counter bank. -/
theorem exec_count {w n p scratch a b c A : ℕ} (x : Data 160) (u v z : ℕ → ℤ)
    (hp0 : 0 < p) (hn : x.regs Reg.side = n) (hp : x.regs Reg.cursor = p)
    (hAB : x.regs Reg.inputAB = a) (hBC : x.regs Reg.inputBC = b)
    (hAC : x.regs Reg.inputAC = c) (hs : x.regs Reg.scratch = scratch)
    (ha : a + n * n ≤ scratch) (hb : b + n * n ≤ scratch) (hc : c + n * n ≤ scratch)
    (hu : ∀ i < n * n, (u i).natAbs ≤ A)
    (hv : ∀ i < n * n, (v i).natAbs ≤ A)
    (hz : ∀ i < n * n, (z i).natAbs ≤ A)
    (hinU : ∀ i < n * n, x.mem (a + i) = encode (u i))
    (hinV : ∀ i < n * n, x.mem (b + i) = encode (v i))
    (hinZ : ∀ i < n * n, x.mem (c + i) = encode (z i))
    (hmag : GenericRAM.Signed.Fits w (CountPrime.magnitudeBudget p (Nat.clog 2 n) A : ℤ))
    (hw : Fits (w + 2) (CountPrime.addressBudget n p (Nat.clog 2 n) scratch a b c)) :
    ∃ y, ExecWithin (w + 2) (count CountPrime.program) x y (CountPrime.cost n p + 6) ∧
      y.regs Reg.countResult = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => u (α.val * n + β.val))
        (fun α β : Fin n => v (α.val * n + β.val))
        (fun α β : Fin n => z (α.val * n + β.val)) p ∧
      ∀ d, d < scratch ∨ CountPrime.memoryEnd n p (Nat.clog 2 n) scratch ≤ d →
        y.mem d = x.mem d := by
  have hinj : Function.Injective counterRegisters :=
    fun _ _ h => Fin.ext (congrArg (fun i : Fin 160 => i.val) h)
  refine WP.exists_execWithin ?_
  wram_exec [count, hn, hp, hAB, hBC, hAC, hs]
  wram_call (CountPrime.exec (n := n) (p := p) (a := a) (b := b) (c := c) (scratch := scratch)
    _ u v z hp0 rfl rfl rfl rfl rfl rfl
    ha hb hc hu hv hz hinU hinV hinZ hmag hw)
    renamed hinj with y ⟨⟨_, hresult, frame⟩, -⟩
  exact ⟨by wram_simp; omega, hresult, frame⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
