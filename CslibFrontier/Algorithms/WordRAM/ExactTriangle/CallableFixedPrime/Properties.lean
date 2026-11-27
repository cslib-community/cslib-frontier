/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Program
public import CslibFrontier.Computability.WordRAM.FlatEndpoint
public import CslibFrontier.Computability.WordRAM.MemoryWindow.Dynamic

/-!
# Fixed code and selector-register frame

The complete translated solver moves as one bank. Register framing uses its embedding,
without expanding the product or verifier instruction graph. The selector bank and the eight
original caller arguments survive every actual call.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- The entire source bank is embedded injectively, including all compiler temporaries. -/
theorem sourceBank_injective : Function.Injective sourceBank := fun _ _ h =>
  Fin.ext (Nat.add_left_cancel (by simpa only [sourceBank] using congrArg Fin.val h))

private theorem small_preserves : ∀ i : Fin 640,
    i.val < 160 ∨ (600 ≤ i.val ∧ i.val < 608) →
    header.Preserves i ∧ firstCopy.Preserves i ∧
    (nextCopy Reg.bc).Preserves i ∧ (nextCopy Reg.ac).Preserves i ∧
    sizeArgument.Preserves i ∧
    receive.Preserves i ∧ (.op (.copy Reg.total (copyBank 7)) : Code .standard 640).Preserves i :=
  by decide +kernel

/-- Both the selector's low 160 registers and the actual original call arguments are preserved
syntactically, for all executions and every physical word width. -/
theorem program_preserves (i : Fin 640)
    (hi : i.val < 160 ∨ (600 ≤ i.val ∧ i.val < 608)) : program.Preserves i := by
  obtain ⟨hh, hf, hb, ha, hs, hr, ht⟩ := small_preserves i hi
  have hc := Code.preserves_rename_of_offset ArrayCopySum.program copyBank
    (fun _ => rfl) i (.inl (by omega))
  have hsrc_ne (j : Fin 419) : sourceBank j ≠ i := fun hj => by
    have := j.isLt
    have hv := congrArg Fin.val hj
    dsimp only [sourceBank] at hv
    omega
  refine ⟨⟨hh, hf, hc, hb, hc, ha, hc, ht⟩,
    ⟨hs, MemoryWindow.preserves_dynamicSetupBank (r := 416) sourceBank powerBank Reg.base 6166
      (fun k hk => by
        have := k.isLt
        have hv := congrArg Fin.val hk
        dsimp only [powerBank] at hv
        omega) hsrc_ne⟩,
    (MemoryWindow.compile StreamingFixedPrime.program).preserves_rename_of_forall_ne
      sourceBank i hsrc_ne, hr⟩

private theorem adapt_size : adapt.size = 59 := by decide +kernel

private theorem setup_size : setup.size = 446 := by
  change (Code.seq sizeArgument
    (MemoryWindow.dynamicSetupBank (r := 416) sourceBank powerBank Reg.base 6166)).size = 446
  rw [Code.size, show sizeArgument.size = 7 from rfl, MemoryWindow.size_dynamicSetupBank]

/-- Runtime modulus computation, translation and input adaptation never read physical width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth :=
  not_or.mpr ⟨by decide +kernel, not_or.mpr
    ⟨not_or.mpr ⟨by decide +kernel,
      MemoryWindow.dynamicSetupBank_not_readsWidth (r := 416) sourceBank powerBank Reg.base 6166⟩,
    not_or.mpr ⟨by simpa only [solve, Code.readsWidth_rename, MemoryWindow.readsWidth_compile]
      using StreamingFixedPrime.program_not_readsWidth, by decide +kernel⟩⟩⟩

/-- One fixed standard program with 640 registers, at most 400000 slots including halt,
and no reads of the physical width. -/
theorem program_fixed : (program.program Reg.found).length ≤ 400000 ∧
    ¬(program.program Reg.found).ReadsWidth := by
  refine ⟨?_, Code.not_readsWidth_program program_not_readsWidth _⟩
  have hsource := StreamingFixedPrime.program_fixed.1
  have hcompile := MemoryWindow.size_compile StreamingFixedPrime.program
  simp only [Code.length_program, program, Code.size, adapt_size, setup_size, solve,
    Code.size_rename, show receive.size = 5 by decide +kernel] at hsource ⊢
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
