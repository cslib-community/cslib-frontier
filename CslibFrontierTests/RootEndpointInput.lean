/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointInput

open Turing.MultiTapeTM RootEndpointInput

-- All copy and edge fields survive a failed check. The zero count rejects even edge zero.
example (copies edge : ℕ) :
    addressInput 0 ⟨[true, true], copies, edge⟩ = ⟨0, copies, edge⟩ := by
  have h : ScheduleBits.validate 0 [true, true] = false := by decide
  simp [addressInput, h]

-- A complete two-head row supplies its two movements.
example (copies edge : ℕ) :
    addressInput 1 ⟨[false, false, false, true], copies, edge⟩ = ⟨2, copies, edge⟩ := by
  have h : ScheduleBits.validate 1 [false, false, false, true] = true := by decide
  simp [addressInput, h]

-- The address uses at most 64 bits for a million-bit table and two five-bit indices.
example (k : ℕ) (a : RootEndpointQuery.Input) (hraw : a.raw.length = 2 ^ 20)
    (hc : a.copies < 32) (he : a.edge < 32) :
    (RootEndpointAddress.encInput (addressInput k a)).length ≤ 64 := by
  have hc' := Nat.size_le_size (show a.copies ≤ 31 by omega)
  have he' := Nat.size_le_size (show a.edge ≤ 31 by omega)
  have h := length_addressInput_le k a
  unfold shortSize at h
  rw [hraw] at h
  change a.copies.size ≤ 5 at hc'
  change a.edge.size ≤ 5 at he'
  change _ ≤ 2 * (21 + a.copies.size + a.edge.size + 1) at h
  omega
