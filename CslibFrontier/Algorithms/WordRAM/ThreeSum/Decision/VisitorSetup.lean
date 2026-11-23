/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Program
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Width
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Scalar
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Registers
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Actual polynomial-envelope initialization for the fused visitor

The six native preparation instructions initialize the existing exponentiation loop from the
actual saved input length. The loop performs every multiplication and decrement, preserving
all traversal registers, the accumulated Boolean and all memory.

## Main results

* `exec_prepareEnvelope`: exact charged argument setup and complete traversal/memory frames.
* `exec_initializeEnvelope`: polynomial envelope from the uniform ordinary decision width.

These native composition and frame proofs are original; the power loop is reused unchanged.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM

/-- Prepare the actual native power-loop registers without publishing any traversal metadata. -/
theorem exec_prepareEnvelope {r κ n w : ℕ} (x : Data (registerCount r))
    (hn : x.regs (controllerRegisters r inputLength) = n)
    (hB : Fits w (n + 2)) (hE : Fits w (envelopeExponent κ)) :
    ∃ y, ExecWithin w (prepareEnvelope κ) x y 6 ∧
      y.regs (controllerRegisters r scale) = n + 2 ∧
      y.regs (controllerRegisters r envelope) = 1 ∧
      y.regs (controllerRegisters r remaining) = envelopeExponent κ ∧
      y.regs (controllerRegisters r one) = 1 ∧
      y.regs (controllerRegisters r zero) = 0 ∧
      y.regs (controllerRegisters r answer) = x.regs (controllerRegisters r answer) ∧
      (∀ i, y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i)) ∧
      y.mem = x.mem := by
  have hne {i j : Fin 16} : controllerRegisters r i = controllerRegisters r j ↔ i = j :=
    (controller_injective r).eq_iff
  have hp (i : Fin 128) (j : Fin 16) : preprocessingRegisters r i ≠ controllerRegisters r j :=
    (controller_ne_preprocessing j i).symm
  refine WP.exists_execWithin ?_
  unfold prepareEnvelope
  wram_exec (disch := (
    (try simp +decide only [Data.set_regs, Function.update_apply, hne, hn, ↓reduceIte])
    fits))
  simp +decide [Data.set_regs, Data.set_mem, hne, hp, hn]

/-- Compute the actual envelope at the same uniform width used by every native node call. -/
theorem exec_initializeEnvelope {r κ n w d : ℕ} (x : Data (registerCount r))
    (hw : width κ d n ≤ w)
    (hn : x.regs (controllerRegisters r inputLength) = n) :
    ∃ y, ExecWithin w (.seq (prepareEnvelope κ) (power.rename (controllerRegisters r))) x y
        (4 * envelopeExponent κ + 8) ∧
      y.regs (controllerRegisters r envelope) = (n + 2) ^ envelopeExponent κ ∧
      y.regs (controllerRegisters r one) = 1 ∧
      y.regs (controllerRegisters r answer) = x.regs (controllerRegisters r answer) ∧
      (∀ i, y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i)) ∧
      y.mem = x.mem := by
  obtain ⟨hV, hE, hB, _⟩ := envelope_fits hw
  obtain ⟨a, ha, has, hav, har, hao, haz, haa, hap, ham⟩ :=
    exec_prepareEnvelope x hn hB hE
  obtain ⟨y, hb, ⟨hbV, _, hbr, hbm⟩, hframe⟩ :=
    ExecWithin.rename_post (controller_injective r) (exec_power (a.comap (controllerRegisters r))
      (by omega : 1 ≤ n + 2) has har hav hao haz hV hE)
  refine ⟨y, (ha.seq hb).mono (by omega), hbV, ?_, ?_, ?_, hbm.trans ham⟩
  · exact (hbr _ (by decide) (by decide)).trans hao
  · exact (hbr _ (by decide) (by decide)).trans haa
  · intro i
    exact (hframe _ (fun j => controller_ne_preprocessing j i)).trans (hap i)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
