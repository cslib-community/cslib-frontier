/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.UpdateSimp

/-!
# Actual canonical signed monomial writes

Each of the p coefficients is stored, so dirty destination words do not become implicit
padding. An out-of-range key (in particular the native padding sentinel p) writes a zero
block. The raw unsigned word two is exactly `Signed.encode 1`; there is no extra conversion
or free ring-coefficient operation. This is an internal counter-stage execution API.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- A whole dirty p-word destination becomes the canonical coefficient block, with every
test, address calculation and store charged. The key may be any unsigned word. -/
theorem exec_writeCoefficients {w : ℕ} (x : Data 128)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (hw : Fits w (x.regs Reg.block + x.regs Reg.modulus + 4)) :
    ∃ y, ExecWithin w writeCoefficients x y (7 * x.regs Reg.modulus + 3) ∧
      (∀ j < x.regs Reg.modulus, y.mem (x.regs Reg.block + j) =
        if j = x.regs Reg.residue then 2 else 0) ∧
      (∀ a, a < x.regs Reg.block ∨ x.regs Reg.block + x.regs Reg.modulus ≤ a →
        y.mem a = x.mem a) ∧
      ∀ i, i ≠ Reg.coefficient → i ≠ Reg.address → y.regs i = x.regs i := by
  let I (y : Data 128) : Prop :=
    (∀ i, i ≠ Reg.coefficient → i ≠ Reg.address → y.regs i = x.regs i) ∧
    y.regs Reg.coefficient ≤ x.regs Reg.modulus ∧
    (∀ j < y.regs Reg.coefficient, y.mem (x.regs Reg.block + j) =
      if j = x.regs Reg.residue then 2 else 0) ∧
    ∀ a, ¬(x.regs Reg.block ≤ a ∧ a < x.regs Reg.block + y.regs Reg.coefficient) →
      y.mem a = x.mem a
  have hbody (y : Data 128) (hy : I y)
      (hcond : (Cond.lt Reg.coefficient Reg.modulus).Holds y) :
      ∃ z, ExecWithin w writeCoefficient y z 5 ∧ I z ∧
        x.regs Reg.modulus - z.regs Reg.coefficient <
          x.regs Reg.modulus - y.regs Reg.coefficient := by
    obtain ⟨hr, hi, hv, hf⟩ := hy
    have hmod := hr Reg.modulus (by decide) (by decide)
    have hbase := hr Reg.block (by decide) (by decide)
    have hres := hr Reg.residue (by decide) (by decide)
    have hy0 := (hr Reg.zero (by decide) (by decide)).trans h0
    have hy1 := (hr Reg.one (by decide) (by decide)).trans h1
    have hy2 := (hr Reg.two (by decide) (by decide)).trans h2
    have hlt : y.regs Reg.coefficient < x.regs Reg.modulus := by
      simpa only [Cond.holds_lt, hmod] using hcond
    unfold writeCoefficient
    wram_exec [hbase, hres, hy0, hy1, hy2] <;>
    · refine ⟨⟨fun i hc' ha' => by wram_simp [hc', ha', hr i hc' ha'],
        by wram_simp; omega, ?_, ?_⟩, by wram_simp; omega⟩
      · intro j hj; wram_simp at hj
        by_cases heq : j = y.regs Reg.coefficient
        · subst j; update_simp [hc]
        · dsimp only [Data.set_mem, Data.write_mem]
          rw [Function.update_of_ne (by omega)]; exact hv j (by omega)
      · intro a ha; wram_simp at ha
        dsimp only [Data.set_mem, Data.write_mem]
        rw [Function.update_of_ne (by omega)]; exact hf a (by omega)
  refine WP.exists_execWithin ?_
  unfold writeCoefficients
  wram_exec
  wram_call (ExecWithin.loop_invariant I
    (fun y => x.regs Reg.modulus - y.regs Reg.coefficient) hbody
    ⟨fun i hc ha => by wram_simp [hc], by wram_simp; exact Nat.zero_le _,
     fun _ hj => by wram_simp at hj, fun _ _ => rfl⟩)
    with z ⟨⟨hr, hi, hv, hf⟩, hstop⟩
  have hi' : z.regs Reg.coefficient = x.regs Reg.modulus := by
    have hm := hr Reg.modulus (by decide) (by decide)
    simp only [Cond.holds_lt, hm] at hstop; omega
  exact ⟨by wram_simp; omega, by simpa only [hi'] using hv,
    fun a ha => hf a (by omega), hr⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
