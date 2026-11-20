/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.Binary
import Mathlib.Tactic.FinCases

/-!
# Ordinary-import callers of canonical scan trace decoding

These tests use only the exported codec and replay interface. Native execution, first-halting
replay and workspace certificates remain separate obligations.
-/

-- This module consists only of checked clients, not exported library declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingScanBinary

open Cslib.DoubleCounting Cslib.DoubleCounting.Scan.Binary

private def edge (u v : Fin 3) : Bool := u == 0 && v == 1

private def branch : Scan.Branch 3 := fun v =>
  if v = 0 then some [] else if v = 1 then some [1] else none

-- Select/stop; select/continue/01/stop; skip. IDs have two bits.
example : encode branch = [true, false, true, true, false, true, false, false] := by
  decide +kernel

example : vertex (1 : Fin 3) = [false, true] := by decide +kernel
example : decodeVertex (N := 3) [true, true] = none := by decide +kernel
example : decodeVertex (N := 3) [true] = none := by decide +kernel
example : decodeVertex (N := 3) [false, false, true] = none := by decide +kernel

-- Budget exhaustion is not a stop, and a continuation must contain a complete ID.
example : readDestinations (N := 3) 0 [true, false, true, false] = none := by decide +kernel
example : readDestinations (N := 3) 1 [true, false] = none := by decide +kernel
example : readDestinations (N := 3) 1 [true, true, true, false] = none := by decide +kernel
example : readDestinations (N := 3) 1 [true, false, true] = none := by decide +kernel

example : decode (N := 3) 1 (encode branch) = some branch := by
  apply decode_encode
  intro v vs hv
  fin_cases v <;> grind [branch]

-- A real successful negative membership answer, proved through the public typed contract.
private def initial : Scan.Branch 3 := fun v => if v = 0 then some [] else none

private theorem initial_passes :
    Passes (fun u v => edge u v = true) 0 0 (Scan.transcript 0 initial) := by
  classical
  apply passes_iff.mpr
  constructor
  · intro v hv
    have hv0 : v = 0 := by simpa [round_zero] using hv
    subst v
    have hd := (distance_spec (r := fun u v => edge u v = true) (s := (0 : Fin 3))
      (k := 0) (v := 0) (mem_round.mp (by simp [round_zero]))).2
    refine ⟨[0], by simp [Scan.transcript, initial], List.isChainFromTo_singleton, ?_⟩
    simp only [List.length_singleton]
    omega
  · intro v hv
    have hv0 : v ≠ 0 := by simpa [round_zero] using hv
    simp [Scan.transcript, initial, hv0]

example : replay edge 0 0 0 ⟨1, 0⟩ (encode initial) = some true := by
  rw [← expected_zero (fun u v => edge u v = true) (0 : Fin 3)]
  apply (replay_expected_eq_some_iff _ _ _ _ _ _).mpr
  exact ⟨initial, rfl, initial_passes, by decide +kernel⟩

example : replay edge 0 2 0 ⟨1, 0⟩ (encode initial) = some false := by
  rw [← expected_zero (fun u v => edge u v = true) (0 : Fin 3)]
  apply (replay_expected_eq_some_iff _ _ _ _ _ _).mpr
  exact ⟨initial, rfl, initial_passes, by decide +kernel⟩

example : replay edge 0 2 0 ⟨2, 1⟩ (encode branch) = none := by decide +kernel

-- Neither zero padding, an extra segment nor truncation is another successful trace.
example : decode (N := 3) 1 (encode branch ++ [false]) = none := by decide +kernel
example : decode (N := 3) 1 (encode branch ++ [true, false]) = none := by decide +kernel
example : decode (N := 3) 1 ((encode branch).take 7) = none := by decide +kernel

-- Degenerate carriers require no choices, but still reject trailing bits.
example : decode (N := 0) 5 [false] = none := by decide +kernel
example : (decode (N := 0) 5 []).isSome = true := by decide +kernel
example : vertex (0 : Fin 1) = [false] := by decide +kernel
example : decodeVertex (N := 1) [true] = none := by decide +kernel

-- Checked ordinary client use of the resource API, without private bodies.
example : (encode branch).length ≤ 3 * (1 * (Nat.size 3 + 1) + 2) := by
  apply length_encode_le
  intro v vs hv
  fin_cases v <;> grind [branch]

end CslibFrontierTests.DoubleCountingScanBinary
