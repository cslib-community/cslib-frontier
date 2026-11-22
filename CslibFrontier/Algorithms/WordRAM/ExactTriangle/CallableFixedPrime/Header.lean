/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Program
import CslibFrontier.Computability.WordRAM.Record

/-!
# Real scalar-header stores for the caller adapter

The five stores create the existing preparation input convention in caller workspace via
`Cslib.WordRAM.storeRecord_exec`. This is only a fixed-size header, with no array/table
initialization hidden in its specification.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- The memory after the five actual scalar-header stores. -/
@[expose] def headerMemory (mem : ℕ → ℕ) (base n D g p : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update mem
    base (n * n * 3 + 4)) (base + 1) D) (base + 2) g) (base + 3) n) (base + 4) p

/-- Source field registers of `header`. -/
private abbrev headerFields : Fin 5 → Fin 640 :=
  ![Reg.length, Reg.dimension, Reg.groups, Reg.n, Reg.prime]

private theorem header_preserves {j : Fin 640} (hj : j.val < 609) : header.Preserves j := by
  revert hj j
  decide +kernel

/-- The unchanged original scalar registers supply every header store and length computation. -/
theorem exec_header {W : ℕ} (x : Data 640)
    (hfit : Fits W (x.regs Reg.base + 4 * (x.regs Reg.n * x.regs Reg.n) + 1024)) :
    ∃ y, ExecWithin W header x y 17 ∧
      y.regs Reg.area = x.regs Reg.n * x.regs Reg.n ∧ y.regs Reg.constant = 5 ∧
      y.mem = headerMemory x.mem (x.regs Reg.base) (x.regs Reg.n)
        (x.regs Reg.dimension) (x.regs Reg.groups) (x.regs Reg.prime) ∧
      ∀ j : Fin 640, j.val < 609 → y.regs j = x.regs j := by
  have hcode : header = ram[
      Reg.one ← #1; Reg.area ← Reg.n * Reg.n; Reg.constant ← #3;
      Reg.length ← Reg.area * Reg.constant;
      Reg.constant ← #4; Reg.length ← Reg.length + Reg.constant;
      ⟪appendCode (storeRecord Reg.base Reg.address Reg.one headerFields)
        (ram[ Reg.constant ← #5 ])⟫ ] := rfl
  refine WP.exists_execWithin_preserves (fun j hj => header_preserves hj) ?_
  rw [hcode]
  wram_exec [show Fits W (x.regs Reg.n * x.regs Reg.n) from hfit.of_le (by omega),
    show Fits W (x.regs Reg.n * x.regs Reg.n * 3) from hfit.of_le (by omega),
    show Fits W (x.regs Reg.n * x.regs Reg.n * 3 + 4) from hfit.of_le (by omega)]
  refine WP.of_append_exec
    (storeRecord_exec Reg.base Reg.address Reg.one headerFields _
      (by decide) (by decide) (by wram_simp)
      (by wram_simp; exact hfit.of_le (by omega))) ?_
  rintro u ⟨humem, _, _, huregs⟩
  wram_simp at humem
  have humem' : u.mem = writeWords x.mem (x.regs Reg.base)
      ![x.regs Reg.n * x.regs Reg.n * 3 + 4, x.regs Reg.dimension,
        x.regs Reg.groups, x.regs Reg.n, x.regs Reg.prime] := by
    rw [humem]
    congr 1
    funext i
    match i with
    | 0 | 1 => wram_simp
    | 2 | 3 | 4 => wram_simp; rfl
  have uarea : u.regs Reg.area = x.regs Reg.n * x.regs Reg.n :=
    (huregs Reg.area (by decide)).trans (by wram_simp)
  wram_exec
  intro hregs
  wram_simp [uarea]
  exact ⟨humem', hregs⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
