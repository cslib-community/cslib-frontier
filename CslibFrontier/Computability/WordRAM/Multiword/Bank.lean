/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Mul
import CslibFrontier.Tactic.WramOmega

/-!
# Fixed banks of multiword registers

Each bank entry contains eighteen little-endian half-word digits. The first forty-four
physical registers are reserved for arithmetic and transfer workspaces. Register indices
are part of the code, so even width two requires no address large enough to name the bank.

## Main definitions

* `Bank.capacity`: number of non-workspace registers in a bank of `n` entries.
* `Bank.regs`: the eighteen registers of a bank entry.
* `Bank.Encodes`: bounded digits with specified reconstructed bank values.

## Main results

* `Bank.encodes_update`: composition through a framed update of one bank entry.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bank

open Workspace
open Schoolbook (registers registers_bounds nodup_registers)

variable {n : ℕ}

/-- Number of non-workspace registers in a bank with `n` entries. -/
def capacity (n : ℕ) : ℕ := 18 * n + 40

/-- The fixed eighteen-digit register list for entry `j`. -/
def regs (j : Fin n) : List (Fin (capacity n + 4)) :=
  registers (40 + 18 * j.val) 18 (by dsimp [capacity]; omega)

/-- Every bank entry has exactly 18 physical registers. -/
theorem length_regs (j : Fin n) : (regs j).length = 18 := by
  simp [regs, registers]

/-- Physical register indices in `regs j` lie in `[44 + 18 * j, 44 + 18 * j + 18)`. -/
theorem mem_regs {j : Fin n} {i : Fin (capacity n + 4)} (hi : i ∈ regs j) :
    44 + 18 * j.val ≤ i.val ∧ i.val < 44 + 18 * j.val + 18 := by
  have := registers_bounds hi
  omega

/-- Every register of `regs j` is a non-scratch digit register (`IsDigit`). -/
theorem digit_regs (j : Fin n) : ∀ i ∈ regs j, IsDigit i := fun _ hi => by
  have := mem_regs hi
  wram_omega

/-- The register list `regs j` of a bank entry has no duplicates. -/
theorem nodup_regs (j : Fin n) : (regs j).Nodup :=
  nodup_registers _ _ _

/-- Distinct bank entries occupy disjoint lists of physical registers. -/
theorem disjoint_regs {j k : Fin n} (hjk : j ≠ k) : List.Disjoint (regs j) (regs k) :=
  List.disjoint_left.mpr fun _ hi hj => by
    have := mem_regs hi
    have := mem_regs hj
    exact absurd (Fin.ext (by omega)) hjk

/-- Bounded half-word digits and the values of all virtual registers. -/
def Encodes (w : ℕ) (x : Data (capacity n + 4)) (v : Fin n → ℕ) : Prop :=
  ∀ j, Bounded (radix w) x (regs j) ∧ value (radix w) x (regs j) = v j

/-- Updating one entry preserves the encodings of every other entry. Workspace registers
below forty-four may change freely. -/
theorem encodes_update {w : ℕ} {x y : Data (capacity n + 4)} {v : Fin n → ℕ}
    (hx : Encodes w x v) (d : Fin n) (z : ℕ)
    (hy : Bounded (radix w) y (regs d)) (hz : value (radix w) y (regs d) = z)
    (hp : ∀ i, 44 ≤ i.val → i ∉ regs d → y.regs i = x.regs i) :
    Encodes w y (Function.update v d z) := by
  intro j
  by_cases hj : j = d
  · subst j
    simpa only [Function.update_self] using ⟨hy, hz⟩
  · have he (i : Fin (capacity n + 4)) (hi : i ∈ regs j) : y.regs i = x.regs i :=
      hp i (by have := mem_regs hi; omega) (List.disjoint_left.mp (disjoint_regs hj) hi)
    rw [Function.update_of_ne hj]
    exact ⟨fun i hi => he i hi ▸ (hx j).1 i hi, (value_congr he).trans (hx j).2⟩

/-- Every six-word value fits in one bank entry, including odd physical widths. -/
theorem six_word_capacity {w : ℕ} (hw : 2 ≤ w) : 2 ^ (6 * w) ≤ radix w ^ 18 := by
  rw [radix, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end Cslib.WordRAM.Multiword.Bank

end
