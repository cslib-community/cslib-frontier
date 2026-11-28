/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Signed.ArrayArithmetic.Body
public import CslibFrontier.Computability.WordRAM.Signed.Fits

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Complete native signed array arithmetic with exact aliases

Each input is either separated from the output or has the identical base. Earlier writes
then preserve every unread source entry. This supports both disjoint Strassen operand forms
and in-place additions/subtractions into output quadrants.
-/

public section

namespace Cslib.WordRAM.Signed.ArrayArithmetic

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Actual native array addition/subtraction, including setup and all loop/access work.
The source-width envelope concerns only original input magnitudes. Dirty output and exact
input/output aliases are permitted. The bound excludes the final halt. -/
theorem exec {w n A B : ℕ} (subtract : Bool) (x : Data 16) (u v : ℕ → ℤ)
    (hlen : x.regs Reg.length = n) (hbound : GenericRAM.Signed.Fits w ((A + B : ℕ) : ℤ))
    (hu : ∀ i < n, (u i).natAbs ≤ A) (hv : ∀ i < n, (v i).natAbs ≤ B)
    (hA : ∀ i < n, x.mem (x.regs Reg.inputA + i) = encode (u i))
    (hB : ∀ i < n, x.mem (x.regs Reg.inputB + i) = encode (v i))
    (ha : Fits (w + 2) (x.regs Reg.inputA + n))
    (hb : Fits (w + 2) (x.regs Reg.inputB + n))
    (hout : Fits (w + 2) (x.regs Reg.output + n))
    (hsepA : x.regs Reg.inputA + n ≤ x.regs Reg.output ∨
      x.regs Reg.output + n ≤ x.regs Reg.inputA ∨ x.regs Reg.inputA = x.regs Reg.output)
    (hsepB : x.regs Reg.inputB + n ≤ x.regs Reg.output ∨
      x.regs Reg.output + n ≤ x.regs Reg.inputB ∨ x.regs Reg.inputB = x.regs Reg.output) :
    ∃ y, ExecWithin (w + 2) (program subtract) x y (26 * n + 4) ∧
      (∀ i < n, y.mem (x.regs Reg.output + i) =
        encode (if subtract then u i - v i else u i + v i)) ∧
      (∀ a, a < x.regs Reg.output ∨ x.regs Reg.output + n ≤ a → y.mem a = x.mem a) ∧
      ∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i := by
  wram_exec [program]
  let P (j : ℕ) (y : Data 16) : Prop :=
    (∀ i, 9 ≤ i.val ∧ i.val ≤ 12 → y.regs i = x.regs i) ∧ y.regs Reg.one = 1 ∧
    (∀ i < j, y.mem (x.regs Reg.output + i) =
      encode (if subtract then u i - v i else u i + v i)) ∧
    ∀ a, ¬(x.regs Reg.output ≤ a ∧ a < x.regs Reg.output + j) → y.mem a = x.mem a
  refine WP.of_spec (ExecWithin.loop_count (N := n) (T := 24) P
    (fun y hy => (hy.1 Reg.length (by decide)).trans hlen) ?_ ?_ ?_) ?_
  · rintro y ⟨hregs, h1, hvalues, hframe⟩ hlt
    have hra := hregs Reg.inputA (by decide)
    have hrb := hregs Reg.inputB (by decide)
    have hro := hregs Reg.output (by decide)
    have readA : y.mem (y.regs Reg.inputA + y.regs Reg.index) = encode (u (y.regs Reg.index)) := by
      rw [hra, hframe _ (by rcases hsepA with h | h | h <;> omega)]
      exact hA _ hlt
    have readB : y.mem (y.regs Reg.inputB + y.regs Reg.index) = encode (v (y.regs Reg.index)) := by
      rw [hrb, hframe _ (by rcases hsepB with h | h | h <;> omega)]
      exact hB _ hlt
    obtain ⟨z, hz, hzi, hzmem, hzregs⟩ :=
      exec_body subtract y (u (y.regs Reg.index)) (v (y.regs Reg.index))
        (hbound.of_natAbs_le ((hu _ hlt).trans (by omega)))
        (hbound.of_natAbs_le ((hv _ hlt).trans (by omega))) readA readB
        (by fits) (by fits) (by fits) (by fits) h1
    obtain ⟨hvalues', hframe'⟩ :=
      prefix_write_step (e := fun i => encode (if subtract then u i - v i else u i + v i))
        hvalues hframe (by simpa only [hro] using hzmem)
    refine ⟨z, hz, ⟨fun i hip => ?_, by regs_frame, hvalues', hframe'⟩, hzi⟩
    exact (hzregs i (by simp only [BodyLocal, Reg.index, Reg.address, Fin.ext_iff]; omega)).trans
      (hregs i hip)
  · wram_simp [Nat.zero_le]
  · dsimp only [P]
    wram_simp
    refine ⟨fun i hi => ?_, fun _ => False.elim, fun _ _ => trivial⟩
    exact (Data.set_regs_of_ne (by simp [Fin.ext_iff, Reg.one]; omega) _).trans
      (Data.set_regs_of_ne (by simp [Fin.ext_iff, Reg.index]; omega) _)
  · rintro y ⟨⟨hregs, _, hvalues, hframe⟩, _⟩
    exact ⟨by wram_simp; omega, hvalues, fun a ha' => hframe a (by omega), hregs⟩

/-- Both closed operation choices use fixed standard code and never read physical width. -/
theorem program_fixed (subtract : Bool) :
    ((program subtract).program Reg.output).length ≤ 128 ∧
      ¬((program subtract).program Reg.output).ReadsWidth := by
  cases subtract <;> exact ⟨by decide +kernel, by apply Code.not_readsWidth_program; decide +kernel⟩

end Cslib.WordRAM.Signed.ArrayArithmetic
