/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.BoundedSTCON.Membership

set_option linter.privateModule false

open Cslib.Complexity Turing.MultiTapeTM

private def edge : STCONInstance where
  n := 2
  adj u v := decide (u.val = 0 ∧ v.val = 1)
  s := 0
  t := 1

-- The generated record encoding keeps the matrix graph framed and the bound binary.
example (I : BoundedSTCONInstance) :
    encBoundedSTCON I = frame (encSTCON I.graph) ++ encNat I.bound := rfl

example : (⟨edge, 1⟩ : BoundedSTCONInstance) ∈ BoundedSTCON := by
  exact Relation.RelatesWithinSteps.single (by rfl)

example : (⟨edge, 0⟩ : BoundedSTCONInstance) ∉ BoundedSTCON := by
  intro h
  have := Relation.RelatesWithinSteps.zero h
  have := congrArg Fin.val this
  contradiction

example : (⟨{ edge with t := edge.s }, 0⟩ : BoundedSTCONInstance) ∈ BoundedSTCON :=
  Relation.RelatesWithinSteps.refl _

-- A bound exponentially larger than the graph does not enlarge the layered instance.
example : (⟨edge, 2 ^ 100⟩ : BoundedSTCONInstance).layered.n = 6 := by decide

example (I : BoundedSTCONInstance) : I.layered ∈ STCON ↔ I ∈ BoundedSTCON :=
  I.layered_mem_iff

example : BoundedSTCON ∈ NL encBoundedSTCON := BoundedSTCON.mem_NL
