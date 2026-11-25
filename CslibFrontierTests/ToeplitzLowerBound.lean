/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Linear.ToeplitzLowerBound

/-!
# Boundary tests for the binary Toeplitz lower bound

Two interleaved copies of an oriented kernel distinguish the sign of a cyclic difference,
the residue-class test and the extension of a diagonal into the padding. The smallest
nontrivial field tests the executable trace through the matrix entry point. Two identical
XOR outputs check that the circuit model charges a shared gate once.
-/

open Cslib.Circuit.ToeplitzPacking Cslib.Circuit.ToeplitzLowerBound

private def orientedKernel (p : ZMod 3 × ZMod 5) : ZMod 2 := if p = (1, 2) then 1 else 0

example : let A := interleave orientedKernel 2 32
    A 14 0 = 1 ∧ A 0 14 = 0 ∧ A 15 0 = 0 ∧ A 30 16 = 1 := by decide

example : binaryToeplitz 6 4 2 = 1 ∧ binaryToeplitz 6 4 1 = 0 ∧ binaryToeplitz 6 0 0 = 0 := by
  decide

open Cslib.Circuit.Linear

private def twoParities : Matrix Bool Bool (ZMod 2) := fun _ _ => 1

/-- Two copies of the same two-input XOR cost exactly one gate with free reuse. -/
example : complexity twoParities = 1 := by
  apply Nat.le_antisymm
  · apply (complexity_le_iff ..).2
    refine ⟨1, le_rfl, ⟨.step .nil ⟨.inl false, .inl true, 1, 1⟩,
      fun _ => .scaled 1 (.inr 0)⟩, ?_⟩
    ext o i
    rw [LinearCircuit.matrix_apply]
    cases i <;> rfl
  · by_contra! h
    obtain ⟨s, hs, p, hp⟩ := (complexity_le_iff twoParities 0).1 (by lia)
    obtain rfl : s = 0 := by lia
    obtain ⟨q, out⟩ := p
    cases q
    have he (b : Bool) : (out true).eval (Sum.elim (Pi.single b 1) Fin.elim0) = 1 := by
      have he := congrFun (congrFun hp true) b
      simpa [LinearCircuit.matrix_apply, LinearCircuit.eval, Program.value, twoParities] using he
    cases ho : out true with
    | zero => simpa [ho, Readout.eval] using he false
    | scaled c w =>
      cases w with
      | inr j => exact j.elim0
      | inl b =>
        have h := he (!b)
        cases b <;> simp [ho, Readout.eval] at h
