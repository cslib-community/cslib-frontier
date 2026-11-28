/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.InputProgram
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Exec

/-!
# Real original-input header execution and input admission

The raw input is n,F followed by canonical-signed AB/BC/AC in row-major order. The existing
counter input representation is reused only as this two-scalar encoding; F is not interpreted
as a supplied prime. All pointers and the workspace boundary are computed by actual code.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

/-- Read original n,F, compute all original pointers and deliver the host protocol in15 steps. -/
theorem exec_entryHeader {W n F : ℕ} (x : Data 640) (hn : x.mem 1 = n) (hF : x.mem 2 = F)
    (hfit : Fits W (3 + 3 * (n * n) + 8)) :
    ∃ y, ExecWithin W entryHeader x y 15 ∧ y.mem = x.mem ∧
      y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = 3 ∧
      y.regs Reg.bc = 3 + n * n ∧ y.regs Reg.ac = 3 + 2 * (n * n) ∧
      y.regs Reg.free = 3 + 3 * (n * n) := by
  let bank := selectorBank ∘ PrimeSelection.counterRegisters
  have inj : Function.Injective bank := fun _ _ h => Fin.ext (congrArg (Fin.val : Fin 640 → ℕ) h)
  wram_exec [entryHeader]
  wram_call (CountPrime.exec_header (x.comap bank) hn hF hfit) renamed inj with
    a ⟨⟨sm, an, aF, aa, ab, ac, af⟩, _⟩
  wram_exec [an, aF, aa, ab, ac, af]
  wram_simp [sm, Reg.side, Reg.bound, Reg.ab, Reg.bc, Reg.ac, Reg.free]
  exact ⟨an, aF, aa, ab, ac, af⟩

/-- Original scalar words and all original signed matrix words fit before the first instruction. -/
theorem input_fits {W n F : ℕ} (values : List ℤ) (hlen : values.length = 3 * (n * n))
    (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hW : executionWidth n F (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n)) values ≤ W) :
    InputFits W (CountPrime.inputWords n F values) := by
  have fit := envelope_fits values hW
  have := Nat.le_mul_self n
  refine ⟨?_, fun v hm => ?_⟩
  · simpa [CountPrime.inputWords, hlen] using fit.of_le (by dsimp only [envelope]; omega)
  · rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> exact fit.of_le (by dsimp only [envelope]; omega)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
      have := hv z hz
      refine fit.of_le ?_
      unfold Signed.encode
      dsimp only [envelope]
      split_ifs <;> omega

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
