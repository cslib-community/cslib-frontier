/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Foundations.Data.Nat.Bits

/-! Ordinary-import clients for native binary shift, including overshifts. -/

open Turing.MultiTapeTM

-- A caller can compute an offset in binary and keep the same workspace budget for the shift.
example {α : Type} {enc : α ↪ List Bool} {value offset : α → ℕ} {S : α → ℕ}
    (hv : ComputableInSpace value enc encNat S) (ho : ComputableInSpace offset enc encNat S) :
    ComputableInSpace (fun a => value a >>> offset a) enc encNat S :=
  ComputableInSpace.budget_comp_linear ComputableInSpace.natShiftRight
    (ComputableInSpace.budget_prod hv ho)

example (n k : ℕ) (h : n.bits.length ≤ k) : encNat (n >>> k) = [] := by
  rw [encNat_apply, Nat.bits_shiftRight, List.drop_eq_nil_of_le h]
