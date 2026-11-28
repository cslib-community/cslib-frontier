/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Signed.Arithmetic
import CslibFrontier.Tactic.FinIndex

/-!
# Representing signed RAM states by unsigned words

Source registers occupy target registers nine and above. The arithmetic workspace is disjoint
from them. Source memory addresses are unchanged; each stored integer is encoded in one word.

## Main definitions

* `ToWordRAM.bank`: the target register representing a source register.
* `ToWordRAM.Represents`: signed register bounds and the register/memory representation.

## Main results

* `ToWordRAM.Represents.set`, `ToWordRAM.Represents.write`: representation after writes.
* `ToWordRAM.Represents.of_frame`: arithmetic blocks preserve represented source data.

## References

This representation is an original implementation choice for the existing signed RAM.
-/

@[expose] public section

namespace Cslib.GenericRAM.Signed.ToWordRAM

variable {r : ℕ}

/-- Source registers follow the nine unsigned arithmetic registers. -/
def bank (i : Fin r) : Fin (r + 9) := ⟨i.val + 9, by omega⟩

/-- Distinct source registers have distinct target registers. -/
theorem bank_injective : Function.Injective (bank (r := r)) := by
  fin_index [bank]

/-- Source register cells are disjoint from the arithmetic workspace. -/
theorem bank_ne_scratch (i : Fin r) {j : Fin (r + 9)} (hj : j.val < 9) : bank i ≠ j := by
  fin_index [bank]

/-- The source registers fit their signed width; target registers and memory encode the
source data. Scratch values are unconstrained at instruction boundaries. -/
structure Represents (w : ℕ) (x : GenericRAM.Data model r) (y : WordRAM.Data (r + 9)) : Prop where
  /-- Every source register is a signed word. -/
  fits : ∀ i, Signed.Fits w (x.regs i)
  /-- The register bank stores canonical signed encodings. -/
  regs : ∀ i, y.regs (bank i) = WordRAM.Signed.encode (x.regs i)
  /-- Memory uses unchanged addresses and encoded values. -/
  mem : ∀ a, y.mem a = WordRAM.Signed.encode (x.mem a)

namespace Represents

variable {w : ℕ} {x : GenericRAM.Data model r} {y z : WordRAM.Data (r + 9)}

/-- Arithmetic scratch writes do not change the represented signed state. -/
theorem scratch (h : Represents w x y) {i : Fin (r + 9)} (hi : i.val < 9) (v : ℕ) :
    Represents w x (y.set i v) := by
  refine ⟨h.fits, fun j => ?_, h.mem⟩
  simpa only [WordRAM.Data.set_regs, Function.update_of_ne (bank_ne_scratch j hi)] using h.regs j

/-- Framed arithmetic preserves all represented source registers and memory. -/
theorem of_frame (h : Represents w x y) (hf : WordRAM.Signed.Frame y z) : Represents w x z :=
  ⟨h.fits, fun i => (hf.2 (bank i) (Or.inr (by dsimp [bank]; omega))).trans (h.regs i),
    fun a => by rw [hf.1]; exact h.mem a⟩

/-- A fitting signed register update is represented by a single bank update. -/
theorem set (h : Represents w x y) (i : Fin r) {v : ℤ} (hv : Signed.Fits w v) :
    Represents w (x.set i v) (y.set (bank i) (WordRAM.Signed.encode v)) := by
  refine ⟨fun j => ?_, fun j => ?_, h.mem⟩
  · by_cases hj : j = i
    · simpa only [hj, GenericRAM.Data.set, Function.update_self] using hv
    · simpa only [GenericRAM.Data.set, Function.update_of_ne hj] using h.fits j
  · by_cases hj : j = i
    · simp only [hj, GenericRAM.Data.set, WordRAM.Data.set_regs, Function.update_self]
    · simpa only [GenericRAM.Data.set, WordRAM.Data.set_regs, Function.update_of_ne hj,
        Function.update_of_ne (bank_injective.ne hj)] using h.regs j

/-- A signed memory update uses the same address and the encoded value. -/
theorem write (h : Represents w x y) (a : ℕ) (v : ℤ) :
    Represents w (x.write a v) (y.write a (WordRAM.Signed.encode v)) := by
  refine ⟨h.fits, h.regs, fun b => ?_⟩
  by_cases hb : b = a
  · simp only [hb, GenericRAM.Data.write, WordRAM.Data.write_mem, Function.update_self]
  · simpa only [GenericRAM.Data.write, WordRAM.Data.write_mem,
      Function.update_of_ne hb] using h.mem b

end Represents

end Cslib.GenericRAM.Signed.ToWordRAM
